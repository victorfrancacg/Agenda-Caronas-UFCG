module agendamentoCaronas
/**
 * Representa um usuário cadastrado no sistema.
 * Cada usuário deve estar associado a um único aluno.
 */
sig Usuario {
    aluno: one Aluno
}
/**
 * Representa uma carona do sistema com seus atributos principais:
 * motorista, passageiros, origem, destino e horário.
 */
sig Carona {
    motorista : one Usuario,
    passageiros : some Usuario,
    origem: one Regiao,
    destino: one Regiao,
    horario: one Horario
}
/**
 * Representa uma região, como um bairro de uma cidade.
 * Contém moradores que são usuários do sistema.
 */
sig Regiao {
    moradores : some Usuario
}
/**
 * Representa uma cidade, composta por uma ou mais regiões.
 */
sig Cidade {
    regioes: some Regiao
}
/**
 * Representa uma aula (disciplina) na qual alunos estão matriculados.
 * Define os alunos frequentes da aula.
 */
sig Aula {
    frequentes: set Aluno
}
/**
 * Representa um horário específico para caronas ou aulas.
 */
sig Horario {
}
/**
 * Representa um aluno do sistema.
 */
sig Aluno {
}
/**
 * Representa a UFCG como uma região especial.
 * Contém alunos matriculados e aulas disponíveis.
 */
one sig ufcg extends Regiao {
    alunos: some Aluno,
    aulas: some Aula
}
/**
 * Fact que define as regras de negócio para caronas.
 */
fact regrasDeCarona{
    some Carona
    /** Máximo de 4 passageiros por carona */
    all c: Carona | #(c.passageiros) <= 4
    /** Um motorista não pode oferecer duas caronas distintas no mesmo horário */
    all c1, c2 : Carona| (c1.horario=c2.horario) && !(c1=c2) implies no(c1.motorista & c2.motorista)
    /** Um passageiro não pode estar em duas caronas distintas no mesmo horário */
    all c1, c2 : Carona| (c1.horario=c2.horario) && !(c1=c2) implies no(c1.passageiros & c2.passageiros)
    /** Um motorista não pode ser passageiro em outra carona no mesmo horário */
    all c1, c2 : Carona| (c1.horario=c2.horario) && !(c1=c2) implies no(c1.motorista & c2.passageiros)
    /** Motorista não pode ser passageiro na própria carona */
    all c: Carona | c.motorista !in c.passageiros
    /** Origem e destino não podem ser iguais */
    all c: Carona | !(c.origem= c.destino)
    /** Pelo menos origem ou destino deve ser a UFCG */
    all c: Carona | (c.origem = ufcg) or (c.destino = ufcg)
    /** Motorista deve estar associado a um aluno */
    all c: Carona | !(c.motorista.aluno = none)
    /** Passageiros devem estar associados a alunos */
    all c: Carona | !(c.passageiros.aluno = none)
    /** Aluno associado a um usuário deve estar na lista de alunos da UFCG */
    all u: Usuario | u.aluno in ufcg.alunos
    /** Aluno associado a um usuário deve ser frequente em pelo menos uma aula */
    all u: Usuario | some aula: ufcg.aulas | u.aluno in aula.frequentes
    /** Cada aluno é associado a no máximo um usuário */
    all a: Aluno | lone (aluno.a)
    /** Dois usuários diferentes não podem compartilhar o mesmo aluno */
    all u1, u2: Usuario | !(u1 = u2)  implies !(u1.aluno = u2.aluno)
}
/**
 * Fact que define a geografia do sistema.
 */
fact Geografia {
    /** Toda região pertence a uma única cidade */
    all r: Regiao | one c: Cidade | r in c.regioes
    /** A UFCG é uma região especial */
    ufcg in Regiao
    /** Todos os moradores de uma região são usuários do sistema */
    all r: Regiao, u: r.moradores | u in Usuario
}
/**
 * Assert que garante que o motorista é frequente em alguma aula
 */
assert MotoristaEFrequente {
    all c: Carona |
        some aula: ufcg.aulas | c.motorista.aluno in aula.frequentes
}
/**
 * Assert que mostra que o motorista não deve necessariamente morar
 * na origem ou no destino
 */
assert MotoristaMoraNaOrigemOuNoDestino {
    all c: Carona |
        (c.motorista in c.origem.moradores) or (c.motorista in c.destino.moradores)
}
/**
 * Assert que garante que passageiros são frequentes em alguma aula
 */
assert PassageirosSaoFrequentes {
    all c: Carona, p: c.passageiros |
        some aula: ufcg.aulas | p.aluno in aula.frequentes
}
/**
 * Assert que garante que caronas são únicas por motorista e horário
 */
assert CaronasUnicasPorMotoristaHorario {
    all c1, c2: Carona |
        (c1.horario = c2.horario) and
        (c1.origem = c2.origem) and
        (c1.destino = c2.destino) and
        (c1.motorista = c2.motorista)
        implies c1 = c2
}
/**
 * Assert que garante que caronas são únicas por passageiro e horário
 */
assert CaronasUnicasPorPassageiroHorario {
    all c1, c2: Carona, p: Usuario |
        (p in c1.passageiros) and (p in c2.passageiros) and
        (c1.horario = c2.horario) and
        (c1.origem = c2.origem) and
        (c1.destino = c2.destino)
        implies c1 = c2
}
/**
 * Assert que garante que caronas são completamente únicas considerando motorista e passageiros
 */
assert CaronasCompletamenteUnicas {
    all c1, c2: Carona |
        (c1.horario = c2.horario) and
        (c1.origem = c2.origem) and
        (c1.destino = c2.destino) and
        (some (c1.passageiros & c2.passageiros) or c1.motorista = c2.motorista)
        implies c1 = c2
}
/**
 * Predicado que verifica se o sistema está em alta demanda.
 * Condições consideradas:
 * 1. Existem pelo menos duas caronas cadastradas.
 * 2. Pelo menos duas caronas ocorrem no mesmo horário.
 * 3. As caronas no mesmo horário possuem origens ou destinos diferentes.
 * 4. Há pelo menos uma carona de ida (destino UFCG) e uma de volta (origem UFCG).
 */
pred sistemaEmAltaDemanda {
    // Existem pelo menos duas caronas
    #Carona > 1
    // Pelo menos duas caronas ocorrem no mesmo horário
    some disj c1, c2: Carona | c1.horario = c2.horario
    // Caronas no mesmo horário têm origens ou destinos diferentes
    some disj c1, c2: Carona | c1.horario = c2.horario and
        (c1.origem != c2.origem or c1.destino != c2.destino)
    // Pelo menos uma carona é de ida (para UFCG)
    some c: Carona | c.destino = ufcg
    // Pelo menos uma carona é de volta (da UFCG)
    some c: Carona | c.origem = ufcg
}
/** Executa o predicado para testar a alta demanda no sistema */
run sistemaEmAltaDemanda for 6
check MotoristaEFrequente for 5
check MotoristaMoraNaOrigemOuNoDestino for 5
check PassageirosSaoFrequentes for 5
check CaronasUnicasPorMotoristaHorario for 5
check CaronasUnicasPorPassageiroHorario for 5
check CaronasCompletamenteUnicas for 5
