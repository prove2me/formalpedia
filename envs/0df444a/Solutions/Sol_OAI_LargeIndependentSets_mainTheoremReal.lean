-- Prove2me | solution 1 for OAI.LargeIndependentSets.mainTheoremReal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T02:16:02.262837+00:00
-- url     : https://prove2.me/submissions/bf3cb68b-0c6b-4225-835d-03312a70ba73

import Mathlib
import Definitions.Def_IndependentSets
import Definitions.Def_OAIQ069A010
import Theorems.Thm_OAI_IndependentSetsGames_Foundations_PCP_TableGapReduction_gapMap_clauseGap
import Theorems.Thm_OAI_LargeIndependentSets_LCInput_uniform_repetition
import Theorems.Thm_OAI_LargeIndependentSets_finite_source_soundness

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringLabels
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

theorem decode_encode {G : PortGraph V D} {t : Nat} {v : V}
    (S : AddressSelector G t v) (ℓ : Ball G t v → A) :
    decode S (encode G t v ℓ) = ℓ := by
  funext u
  change ℓ (wordToBall G t v (S.address u)) = ℓ u
  rw [S.correct]

end IndependentSetsGames.Foundations.PCP.PoweringLabels

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ConstraintGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP

namespace ConstraintGraph

variable {V E A : Type*}

theorem mem_rejectedDarts [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    e ∈ G.rejectedDarts labeling ↔ G.edgeSatisfied labeling e = false := by
  simp [rejectedDarts]

end ConstraintGraph

end IndependentSetsGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_GenericGraphTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GenericGraphTables

open IndependentSetsGames.Foundations.Complexity

variable {q : Nat}

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ (Label q)) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

end IndependentSetsGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AssignmentTester
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AssignmentTester

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

variable {K : Type*} [Fintype K] [Nonempty K]

omit [Fintype A] [DecidableEq A] in
theorem selfCorrect_dictator (a : A) (x r : Cube A) :
    selfCorrect (fun f => f a) x r = x a := by
  change (r a ^^ (r a ^^ x a)) = x a
  cases r a <;> cases x a <;> rfl

theorem truth_not_decide_eq (a b : Bool) : truth (!(decide (a = b))) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_blr (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 0 k f g r₀ r₁ r₂ =
      disagree (F f ^^ F g) (F (cubeXor f g)) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer, truth_not_decide_eq]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_and (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 1 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (cubeAnd f g) r₀)
        (selfCorrect F f r₁ && selfCorrect F g r₂) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_unit (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 2 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (fun _ => true) r₀) true := by
  simp only [eventReject, eventAccepts, eventQueries, oracleAnswer]
  norm_num
  change truth (!(selfCorrect F (fun _ => true) r₀)) =
    disagree (selfCorrect F (fun _ => true) r₀) true
  cases selfCorrect F (fun _ => true) r₀ <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_input (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 3 k f g r₀ r₁ r₂ =
      disagree (σ k) (selfCorrect F (fun a => label a k) r₀) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem event_perfect_completeness (label : A → K → Bool) (a : A)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
      (eventQueries label kind k f g r₀ r₁ r₂ slot)) = true := by
  have hkind : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  have hreject : eventReject label (label a) (fun x => x a) kind k f g r₀ r₁ r₂ = 0 := by
    rcases hkind with h | h | h | h <;> subst kind
    · simp [eventReject_blr, cubeXor, disagree]
    · simp [eventReject_and, selfCorrect_dictator, cubeAnd, disagree]
    · simp [eventReject_unit, selfCorrect_dictator, disagree]
    · simp [eventReject_input, selfCorrect_dictator, disagree]
  unfold eventReject at hreject
  cases h : eventAccepts kind (fun slot => oracleAnswer (label a) (fun x => x a)
    (eventQueries label kind k f g r₀ r₁ r₂ slot)) <;> simp_all [truth]

end IndependentSetsGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_QueryIncidence
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

theorem canonicalSlot_query [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) :
    T.query event (canonicalSlot T event i) = T.query event i :=
  Fin.find_spec (p := fun j => T.query event j = T.query event i) ⟨i, rfl⟩

theorem edgeSatisfied_eq_incidence [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q) (labeling : Vertex E X → Label q)
    (event : E) (slot : Fin q) (orientation : Bool) :
    (graph T positive).edgeSatisfied labeling ((event, slot), orientation) =
      incidenceAccept T positive event slot (labeling (.inl event))
        (labeling (.inr (T.query event slot))) := by
  cases orientation <;> rfl

theorem honest_leftValid (T : Verifier E X q) (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) :
    LeftValid T event (response T assignment event) := by
  refine ⟨accepted, ?_⟩
  intro i j hij
  exact congrArg assignment hij

theorem honest_incidence [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool) (event : E)
    (accepted : T.accepts event (response T assignment event) = true) (slot : Fin q) :
    incidenceAccept T positive event slot
      (honestLabeling T assignment (.inl event))
      (honestLabeling T assignment (.inr (T.query event slot))) = true := by
  simp only [incidenceAccept, Bool.and_eq_true, honestLabeling,
    decode_encodeRight]
  refine ⟨_root_.decide_eq_true (honest_leftValid T assignment event accepted), ?_⟩
  exact _root_.decide_eq_true (congrArg assignment (canonicalSlot_query T event slot))

theorem perfect_completeness [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (assignment : X → Bool)
    (accepted : ∀ event, T.accepts event (response T assignment event) = true) :
    ∀ dart, (graph T positive).edgeSatisfied (honestLabeling T assignment) dart = true := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  rw [edgeSatisfied_eq_incidence]
  exact honest_incidence T positive assignment event (accepted event) slot

theorem satisfiable_of_verifier_satisfiable [DecidableEq X] (T : Verifier E X q)
    (positive : 0 < q)
    (sat : ∃ assignment : X → Bool,
      ∀ event, T.accepts event (response T assignment event) = true) :
    (graph T positive).Satisfiable := by
  obtain ⟨assignment, h⟩ := sat
  exact ⟨honestLabeling T assignment, perfect_completeness T positive assignment h⟩

end IndependentSetsGames.Foundations.PCP.QueryIncidence

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AlphabetGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AlphabetGraph

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem oracleAnswer_globalize (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E)
    (x : AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    assignment (globalizeQuery G e x) =
      AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) x := by
  rcases x with ⟨side, tape⟩ | tape
  · cases side <;> rfl
  · rfl

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem response_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    QueryIncidence.response (verifier G) assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      fun slot => AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e)
        (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
          (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
          (restrictTape G e r₁) (restrictTape G e r₂) slot) := by
  funext slot
  exact oracleAnswer_globalize G assignment e _

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_edgeOracle (G : ConstraintGraph V E A) (labeling : V → A) (e : E)
    (h : G.edgeSatisfied labeling e = true) :
    edgeOracle G (honestAssignment G labeling) e =
      fun tape => tape ⟨(labeling (G.tail e), labeling (G.head e)), h⟩ := by
  funext tape
  exact UniformRestriction.extend_apply_of_mem (legal G e) tape
    (labeling (G.tail e), labeling (G.head e)) h

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem honest_event (G : ConstraintGraph V E A) (labeling : V → A)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) (event : Event E A) :
    (verifier G).accepts event (QueryIncidence.response (verifier G) (honestAssignment G labeling) event) =
      true := by
  rcases event with ⟨e, kind, k, f, g, r₀, r₁, r₂⟩
  rw [response_eq_local, honest_edgeOracle G labeling e (satisfied e)]
  simp only [honest_vertexBlock]
  exact AssignmentTester.event_perfect_completeness (AlphabetReduction.pairEncoding (G.accepts e))
    ⟨(labeling (G.tail e), labeling (G.head e)), satisfied e⟩ kind k
    (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
    (restrictTape G e r₁) (restrictTape G e r₂)

omit [DecidableEq A] [Nonempty A] in
theorem perfect_completeness [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A)
    (satisfied : G.Satisfiable) : (graph G).Satisfiable := by
  obtain ⟨labeling, h⟩ := satisfied
  exact QueryIncidence.satisfiable_of_verifier_satisfiable (verifier G) (by omega)
    ⟨honestAssignment G labeling, honest_event G labeling h⟩

end IndependentSetsGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_GraphTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GraphTables

open IndependentSetsGames.Foundations.Complexity

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

theorem enumeratedGraph_edgeSatisfied {V E A : Type*} {n m : Nat}
    (G : ConstraintGraph V E A) (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m)
    (labelOrder : A ≃ Label) (labeling : V → A) (e : E) :
    (enumeratedGraph G vertexOrder dartOrder labelOrder).edgeSatisfied
      (fun v => labelOrder (labeling (vertexOrder.symm v))) (dartOrder e) =
        G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head, enumeratedGraph]

end IndependentSetsGames.Foundations.PCP.GraphTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_InitialGraph
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.clauseAnswerFintype _root_.OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.clauseAnswerInhabited _root_.OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.slotInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.InitialGraph

open Target

theorem incidenceAccept_true (F : Formula) (event : RandomEvent F) (a b : Label)
    (h : incidenceAccept F event a b = true) :
    localSatisfies (clauseAt F event.1) (toClauseAnswer a) = true ∧
      answerAt (toClauseAnswer a) event.2 = b.1 := by
  simp only [incidenceAccept, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem incidence_honest (F : Formula) (A : Fin F.«variables» → Bool)
    (sat : ∀ c ∈ F.clauses, c.eval A = true) (event : RandomEvent F) :
    incidenceAccept F event (honestLabeling F A (clauseVertex F event.1))
      (honestLabeling F A (variableVertex F (nameAt (clauseAt F event.1) event.2))) = true := by
  have hc : (clauseAt F event.1).eval A = true := sat _ (List.getElem_mem _)
  simp [incidenceAccept, honestLabeling, clauseVertex, variableVertex, variableLabel,
    variableValid, honest_satisfies, honest_answerAt, hc]

theorem raw_completeness (F : Formula) (sat : F.Satisfiable) : (raw F).Satisfiable := by
  rcases sat with ⟨A, hA⟩
  refine ⟨honestLabeling F A, fun d => ?_⟩
  cases d with
  | inl pair =>
    rcases pair with ⟨event, orientation⟩
    cases orientation <;> exact incidence_honest F A hA event
  | inr u => rfl

theorem clauseAnswer_eq_of_slots (a b : ClauseAnswer)
    (h : ∀ s, answerAt a s = answerAt b s) : a = b := by
  rcases a with ⟨a₀, a₁, a₂⟩
  rcases b with ⟨b₀, b₁, b₂⟩
  have h₀ : a₀ = b₀ := h .first
  have h₁ : a₁ = b₁ := h .second
  have h₂ : a₂ = b₂ := h .third
  cases h₀; cases h₁; cases h₂; rfl

theorem raw_reflects (F : Formula) (sat : (raw F).Satisfiable) : F.Satisfiable := by
  rcases sat with ⟨labeling, hlabeling⟩
  let A : Fin F.«variables» → Bool := fun v => (labeling (variableVertex F v)).1
  have slot_correct (i : Fin F.clauses.length) (s : Slot) :
      localSatisfies (clauseAt F i) (toClauseAnswer (labeling (clauseVertex F i))) = true ∧
        answerAt (toClauseAnswer (labeling (clauseVertex F i))) s =
          A (nameAt (clauseAt F i) s) := by
    exact incidenceAccept_true F (i, s) _ _ (hlabeling (.inl ((i, s), false)))
  have clause_correct (i : Fin F.clauses.length) : (clauseAt F i).eval A = true := by
    have equal : toClauseAnswer (labeling (clauseVertex F i)) = honestAnswer (clauseAt F i) A :=
      clauseAnswer_eq_of_slots _ _ (fun s => by
        simpa only [honest_answerAt] using (slot_correct i s).2)
    have satisfied := (slot_correct i .first).1
    rw [equal, honest_satisfies] at satisfied
    exact satisfied
  refine ⟨A, fun c hc => ?_⟩
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hc
  simpa only [clauseAt, heq] using clause_correct ⟨i, hi⟩

theorem raw_satisfiable_iff (F : Formula) : (raw F).Satisfiable ↔ F.Satisfiable :=
  ⟨raw_reflects F, raw_completeness F⟩

end IndependentSetsGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AlphabetRetraction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

theorem satisfiable_pullback_iff (G : ConstraintGraph V E A)
    (decode : B → A) (encode : A → B) (sectionLaw : ∀ a, decode (encode a) = a) :
    (pullback G decode).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, h⟩
    exact ⟨decode ∘ labeling, h⟩
  · rintro ⟨labeling, h⟩
    refine ⟨encode ∘ labeling, fun e => ?_⟩
    change G.accepts e (decode (encode (labeling (G.tail e))))
      (decode (encode (labeling (G.head e)))) = true
    simpa only [ConstraintGraph.edgeSatisfied, sectionLaw] using h e

end IndependentSetsGames.Foundations.PCP.AlphabetRetraction

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Minimum
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

theorem minimumRejections_le (G : ConstraintGraph V E A) (labeling : V → A) :
    G.minimumRejections ≤ G.rejectionCount labeling := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨labeling, Finset.mem_univ _, rfl⟩)

theorem exists_minimizer (G : ConstraintGraph V E A) :
    ∃ labeling : V → A, G.rejectionCount labeling = G.minimumRejections := by
  classical
  have h := Finset.min'_mem G.rejectionCounts G.rejectionCounts_nonempty
  obtain ⟨labeling, _, heq⟩ := Finset.mem_image.mp h
  exact ⟨labeling, heq⟩

omit [Fintype V] [Fintype A] [Nonempty A] in
theorem rejectionCount_eq_zero_iff (G : ConstraintGraph V E A) (labeling : V → A) :
    G.rejectionCount labeling = 0 ↔ ∀ e, G.edgeSatisfied labeling e = true := by
  classical
  constructor
  · intro h e
    have hempty : G.rejectedDarts labeling = ∅ := Finset.card_eq_zero.mp h
    cases he : G.edgeSatisfied labeling e with
    | false =>
        have hm := (G.mem_rejectedDarts labeling e).mpr he
        rw [hempty] at hm
        simp at hm
    | true => rfl
  · intro h
    simp [rejectionCount, rejectedDarts, h]

theorem minimumRejections_eq_zero_iff (G : ConstraintGraph V E A) :
    G.minimumRejections = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    exact ⟨labeling, (G.rejectionCount_eq_zero_iff labeling).mp (heq.trans h)⟩
  · rintro ⟨labeling, h⟩
    have hc := (G.rejectionCount_eq_zero_iff labeling).mpr h
    exact Nat.eq_zero_of_le_zero (hc ▸ G.minimumRejections_le labeling)

end Minimum

variable {W D B : Type*}

theorem reindex_edgeSatisfied (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B)
    (labeling : V → A) (e : E) :
    (G.reindex vertices darts labels).edgeSatisfied (labelingEquiv vertices labels labeling)
      (darts e) = G.edgeSatisfied labeling e := by
  simp [reindex, labelingEquiv, edgeSatisfied, head, Equiv.trans_apply]

theorem reindex_rejectionCount [Fintype E] [Fintype D] (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) (labeling : V → A) :
    (G.reindex vertices darts labels).rejectionCount (labelingEquiv vertices labels labeling) =
      G.rejectionCount labeling := by
  classical
  unfold rejectionCount
  symm
  apply Finset.card_bij (fun e _ => darts e)
  · intro e he
    rw [mem_rejectedDarts, reindex_edgeSatisfied]
    exact (G.mem_rejectedDarts labeling e).mp he
  · intro e _ f _ h
    exact darts.injective h
  · intro d hd
    refine ⟨darts.symm d, ?_, darts.apply_symm_apply d⟩
    rw [mem_rejectedDarts]
    rw [← reindex_edgeSatisfied G vertices darts labels labeling (darts.symm d)]
    rw [darts.apply_symm_apply]
    exact (mem_rejectedDarts _ _ _).mp hd

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]
  [Fintype W] [Fintype D] [Fintype B] [Nonempty B]

omit [Nonempty A] [Nonempty B] in
theorem rejectionCounts_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).rejectionCounts = G.rejectionCounts := by
  classical
  ext n
  simp only [rejectionCounts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨labeling, hn⟩
    refine ⟨(labelingEquiv vertices labels).symm labeling, ?_⟩
    rw [← reindex_rejectionCount G vertices darts labels,
      Equiv.apply_symm_apply]
    exact hn
  · rintro ⟨labeling, hn⟩
    refine ⟨labelingEquiv vertices labels labeling, ?_⟩
    rw [reindex_rejectionCount]
    exact hn

theorem minimumRejections_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).minimumRejections = G.minimumRejections := by
  unfold minimumRejections
  simp only [rejectionCounts_reindex]

theorem satisfiable_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).Satisfiable ↔ G.Satisfiable := by
  rw [← minimumRejections_eq_zero_iff, minimumRejections_reindex,
    minimumRejections_eq_zero_iff]

end IndependentSetsGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_RawInitialTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.IndependentSetsGames.Foundations.Hastad.SourceContexts.slotInhabited _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialTables

open Target GraphTables

theorem raw64_satisfiable_iff (F : Formula) : (raw64 F).Satisfiable ↔ F.Satisfiable :=
  (AlphabetRetraction.satisfiable_pullback_iff (InitialGraph.raw F)
    AlphabetRetraction.decode64 AlphabetRetraction.encode64
      AlphabetRetraction.decode_encode64).trans (InitialGraph.raw_satisfiable_iff F)

theorem table_semantics (F : Formula) :
    GraphTables.semantics (table F) =
      (raw64 F).reindex (vertexOrder F) (dartOrder F) labelOrder := by
  change GraphTables.semantics (GraphTables.ofGraph
    (GraphTables.enumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder)) = _
  rw [GraphTables.semantics_ofGraph]
  rfl

theorem table_satisfiable_iff (F : Formula) :
    (GraphTables.semantics (table F)).Satisfiable ↔ F.Satisfiable := by
  rw [table_semantics]
  exact ((raw64 F).satisfiable_reindex (vertexOrder F) (dartOrder F) labelOrder).trans
    (raw64_satisfiable_iff F)

end IndependentSetsGames.Foundations.PCP.RawInitialTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Semantics2
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Table
variable {q : Nat}

private theorem semantics_rows_congr {n m : Nat} {left right : GraphTables.Rows n m}
    (h : left = right) (hl : GraphTables.Valid left) (hr : GraphTables.Valid right) :
    GraphTables.semantics (⟨n, m, left, hl⟩ : GraphTables.Table) =
      GraphTables.semantics (⟨n, m, right, hr⟩ : GraphTables.Table) := by
  subst right
  rfl

theorem semantics_build (input : GenericGraphTables.Table q) :
    GraphTables.semantics (build input) =
      GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv := by
  exact (semantics_rows_congr (rows_eq_graphRows input) (rows_valid input)
    (GraphTables.graphRows_valid _)).trans (GraphTables.semantics_ofGraph _)

theorem edgeSatisfied_build (input : GenericGraphTables.Table q)
    (labeling : QueryIncidence.Vertex (AlphabetGraph.Event (Fin input.darts) (Fin q))
      (AlphabetGraph.Address (Fin input.vertices) (Fin input.darts) (Fin q)) →
        QueryIncidence.Label 6)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    (GraphTables.semantics (build input)).edgeSatisfied
      (fun v => Enumeration.labelEquiv
        (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)))
      (Enumeration.dartEquiv input.darts q dart) =
        (AlphabetGraph.graph (GenericGraphTables.semantics input)).edgeSatisfied labeling dart := by
  rw [semantics_build]
  exact GraphTables.enumeratedGraph_edgeSatisfied _ _ _ _ labeling dart

theorem perfect_completeness [Nonempty (Fin q)] (input : GenericGraphTables.Table q)
    (satisfied : (GenericGraphTables.semantics input).Satisfiable) :
    (GraphTables.semantics (build input)).Satisfiable := by
  obtain ⟨labeling, accepted⟩ :=
    AlphabetGraph.perfect_completeness (GenericGraphTables.semantics input) satisfied
  refine ⟨fun v => Enumeration.labelEquiv
    (labeling ((Enumeration.vertexEquiv input.vertices input.darts q).symm v)), ?_⟩
  intro index
  have h := edgeSatisfied_build input labeling
    ((Enumeration.dartEquiv input.darts q).symm index)
  have index_eq := (Enumeration.dartEquiv input.darts q).apply_symm_apply index
  rw [index_eq] at h
  exact h.trans (accepted _)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Table

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineFiniteAlphabet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

theorem input_finite (M : FinTM2) : Finite (M.Γ M.k₀) := by
  let := M.Γk₀Fin
  infer_instance

theorem sequential_machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (hfirst : FiniteAlphabet first) (hsecond : FiniteAlphabet second) :
    FiniteAlphabet (MachineSequential.machine first second relabel fallback) := by
  intro tape
  rcases tape with tape | tape | tape
  · exact hfirst tape
  · exact hsecond tape
  · exact input_finite second

theorem compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.compose first second fallback).tm := by
  exact sequential_machine first.tm second.tm
    (fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol))
    (second.inputAlphabet.symm fallback) hfirst hsecond

theorem composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.composeBits first second).tm :=
  compose first second false hfirst hsecond

theorem repeat_machine (body : FinTM2)
    (input : body.Γ body.k₀ ≃ Bool) (output : body.Γ body.k₁ ≃ Bool)
    (hbody : FiniteAlphabet body) :
    FiniteAlphabet (MachineRepeat.machine body input output) := by
  intro tape
  cases tape with
  | inl tape => exact hbody tape
  | inr _ => exact input_finite body

end IndependentSetsGames.Foundations.Complexity.MachineFiniteAlphabet
namespace IndependentSetsGames.Foundations.PCP.AlphabetTable

open IndependentSetsGames.Foundations.Complexity

theorem Driver.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Driver.machine q) := by
  intro k
  change Finite Bool
  infer_instance

theorem Runtime.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Runtime.tablePolynomialTime q).tm :=
  Driver.finiteAlphabet q

end IndependentSetsGames.Foundations.PCP.AlphabetTable

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_BoundedIteration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BoundedIteration
open Turing
open IndependentSetsGames.Foundations.Complexity

variable {α β : Type}

lemma certificate_finiteAlphabet (enc : β → List Bool) (step : β → β) (start : α → β)
    (count : α → ℕ) (body : TM2ComputableInPolyTime enc enc step) (length : Polynomial ℕ)
    (growth) (hbody : MachineFiniteAlphabet.FiniteAlphabet body.tm)
    (k : (certificate enc step start count body length growth).tm.K) :
    Finite ((certificate enc step start count body length growth).tm.Γ k) :=
  MachineFiniteAlphabet.repeat_machine body.tm body.inputAlphabet body.outputAlphabet hbody k
end LargeIndependentSets.BoundedIteration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_DegreeReplacement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.IndependentSetsGames.Foundations.PCP.PoweringLabels.finiteBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace IndependentSetsGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

theorem innerRotation_tail (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (e : E) (d : D) :
    G.tail (innerRotation G H (e, d)).1 = G.tail e := by
  change G.tail (((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.val) = G.tail e
  exact ((H (G.tail e)).rot (⟨e, rfl⟩, d)).1.property

@[simp] theorem replacement_satisfied_inl [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inl d) =
      true := by
  change decide (labeling (G.tail e) =
    labeling (G.tail (innerRotation G H (e, d)).1)) = true
  rw [innerRotation_tail G H e d]
  simp

theorem replacement_complete [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ p, (replacementGraph G H).edgeSatisfied (liftLabel G labeling) p = true := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · exact replacement_satisfied_inl G H labeling e d
  · rw [replacement_satisfied_inr]
    exact h e

theorem rejectionCount_eq_sum [Fintype E] (G : ConstraintGraph V E A)
    (labeling : V → A) :
    G.rejectionCount labeling =
      ∑ e, if G.edgeSatisfied labeling e = false then 1 else 0 := by
  classical
  simp only [ConstraintGraph.rejectionCount, ConstraintGraph.rejectedDarts,
    Finset.card_eq_sum_ones, Finset.sum_filter]

theorem padded_complete (G : ConstraintGraph V E A) (dummy : V → Type*)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ c, (paddedGraph G dummy).edgeSatisfied labeling c = true := by
  intro c
  cases c with
  | inl e => exact h e
  | inr z => rfl

end IndependentSetsGames.Foundations.PCP.DegreeReplacement

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_SpectralReturn
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

noncomputable section

section Averages

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mean_equiv (e : A ≃ B) (f : B → ℝ) :
    mean (fun x => f (e x)) = mean f :=
  Fintype.expect_equiv e _ _ (fun _ => rfl)

end Averages

end
end IndependentSetsGames.Foundations.PCP.SpectralReturn

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Finite
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.PoweringLabels.finiteBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GraphTransport
open PoweringWalks SpectralReturn
variable {V W D E : Type*}

variable [Fintype V] [Fintype W] [Fintype D] [Fintype E]

omit [Fintype V] [Fintype W] in
theorem operator_reindex (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (f : W → ℝ) (w : W) :
    averagingOperator (reindex G vertices ports) f w =
      averagingOperator G (fun v => f (vertices v)) (vertices.symm w) := by
  unfold averagingOperator
  apply Fintype.expect_equiv ports.symm
  intro e
  rfl

theorem energy_reindex (vertices : V ≃ W) (f : W → ℝ) :
    energy (fun v => f (vertices v)) = energy f :=
  mean_equiv vertices (fun w => f w ^ 2)

theorem reindex_spectralCertificate (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (lambda : ℝ) (certificate : SpectralCertificate G lambda) :
    SpectralCertificate (reindex G vertices ports) lambda where
  nonnegative := certificate.nonnegative
  lt_one := certificate.lt_one
  contraction := by
    intro f hf
    have hf' : mean (fun v => f (vertices v)) = 0 :=
      (mean_equiv vertices f).trans hf
    have h := certificate.contraction (fun v => f (vertices v)) hf'
    have hout : energy (averagingOperator (reindex G vertices ports) f) =
        energy (averagingOperator G (fun v => f (vertices v))) := by
      rw [← energy_reindex vertices]
      congr 1
      funext v
      rw [operator_reindex, vertices.symm_apply_apply]
    rw [hout, ← energy_reindex vertices f]
    exact h

end IndependentSetsGames.Foundations.PCP.GraphTransport

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Overlay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.IndependentSetsGames.Foundations.PCP.PoweringLabels.finiteBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace IndependentSetsGames.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

theorem rejectionCount_eq [Fintype V] [Fintype D] [Fintype E]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A) :
    (constraintGraph G H).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp [edgeSatisfied_inl G H htail]

end IndependentSetsGames.Foundations.PCP.Overlay

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringLazy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

theorem rejectionCount_eq [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (constraintGraph G).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [edgeSatisfied_true G htail]

end IndependentSetsGames.Foundations.PCP.LazyConstraint

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

theorem poweredGraph_edgeSatisfied (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (direction : Bool) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) =
      pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) := by
  cases direction <;> rfl

theorem pathAccepts_honest (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true)
    (w : Walk V D (n + 1)) :
    pathAccepts G accepts n selectors w
      (honestLabels G (n + 1) assignment w.1)
      (honestLabels G (n + 1) assignment (endpoint G w)) = true := by
  apply (pathAccepts_eq_true_iff G accepts n selectors w _ _).2
  intro k
  simpa only [honestLabels, decode_encode, tailFromStart_val, headFromEnd_val] using
    satisfies (edgeAt G n w k)

theorem perfect_completeness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true) :
    ∀ d, (poweredGraph G accepts n selectors).edgeSatisfied
      (honestLabels G (n + 1) assignment) d = true := by
  rintro ⟨direction, w⟩
  rw [poweredGraph_edgeSatisfied]
  exact pathAccepts_honest G accepts n selectors assignment satisfies w

theorem preserves_satisfiability (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (h : (baseGraph G accepts reverse_accepts).Satisfiable) :
    (poweredGraph G accepts n selectors).Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := h
  refine ⟨honestLabels G (n + 1) assignment, ?_⟩
  apply perfect_completeness G accepts n selectors assignment
  intro e
  exact satisfies e

end IndependentSetsGames.Foundations.PCP.PoweringTest

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringTableSemantics
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

theorem edgeSatisfied_encoded {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (labels : RawLabeling vertices d n)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    (GenericGraphTables.semantics (table input n)).edgeSatisfied
      (encodeLabeling (vertices := vertices) d n labels) (encodeDart vertices d n e) =
        (mathematicalGraph input n).edgeSatisfied labels e := by
  rw [semantics_table]
  unfold encodeLabeling encodeLabel encodeDart
  exact
    GenericGraphTables.enumeratedGraph_edgeSatisfied (mathematicalGraph input n)
      (Equiv.refl _) (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64) labels e

theorem satisfiable_iff {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    (GenericGraphTables.semantics (table input n)).Satisfiable ↔
      (mathematicalGraph input n).Satisfiable := by
  constructor
  · rintro ⟨labels, satisfies⟩
    refine ⟨decodeLabeling d n labels, ?_⟩
    intro e
    have h := edgeSatisfied_encoded input n (decodeLabeling d n labels) e
    rw [encodeLabeling_decodeLabeling (vertices := vertices) d n labels] at h
    exact h.symm.trans (satisfies (encodeDart vertices d n e))
  · rintro ⟨labels, satisfies⟩
    refine ⟨encodeLabeling d n labels, ?_⟩
    intro i
    have h := edgeSatisfied_encoded input n labels (decodeDart vertices d n i)
    rw [encodeDart_decodeDart vertices d n i] at h
    exact h.trans (satisfies (decodeDart vertices d n i))

theorem preserves_satisfiability {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (h : (PortTables.baseGraph input).Satisfiable) :
    (GenericGraphTables.semantics (table input n)).Satisfiable := by
  apply (satisfiable_iff input n).mpr
  exact PoweringTest.preserves_satisfiability (PortTables.portGraph input)
    (PortTables.accepts input) (PortTables.accepts_rotation input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1)) h

end IndependentSetsGames.Foundations.PCP.PoweringTableSemantics

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ExpanderFamily
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.PoweringLabels.finiteBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

theorem baseOnCloud_certificate : SpectralCertificate baseOnCloud (1 / 100 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (Classical.choose_spec exists_baseGraph)

end IndependentSetsGames.Foundations.PCP.ExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ExpanderTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.PoweringLabels.finiteBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

private theorem graph_ext {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

@[simp] theorem graph_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) :
    graph (ofGraph G) = G := graph_ext (lookup_ofGraph G)

theorem exists_base_table : ∃ H : Table
    ((Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree,
    SpectralCertificate (graph H) (1 / 100 : ℝ) := by
  classical
  have hv : Fintype.card ExpanderFamily.CloudPort =
      (Expanders.baseDegree * Expanders.baseDegree) *
        (Expanders.baseDegree * Expanders.baseDegree) := by
    rw [ExpanderFamily.card_cloudPort]
    unfold ExpanderFamily.growth
    ring
  let vertices := Fintype.equivFinOfCardEq hv
  let ports := Fintype.equivFinOfCardEq Expanders.card_basePort
  let G := GraphTransport.reindex ExpanderFamily.baseOnCloud vertices ports
  refine ⟨ofGraph G, ?_⟩
  rw [graph_ofGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    ExpanderFamily.baseOnCloud_certificate

end IndependentSetsGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingOverlayTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hreverse : ∀ e, G.reverse e = H.reverse e)
    (htail : ∀ e, G.tail e = H.tail e)
    (haccepts : ∀ e a b, G.accepts e a b = H.accepts e a b) : G = H := by
  rcases G with ⟨r, hi, t, p, hp⟩
  rcases H with ⟨r', hi', t', p', hp'⟩
  have hr : r = r' := Equiv.ext hreverse
  cases hr
  have ht : t = t' := funext htail
  cases ht
  have ha : p = p' := funext fun e => funext fun a => funext fun b => haccepts e a b
  cases ha
  rfl

theorem baseGraph_materialize {n d : Nat} {D : Type*}
    (G : ConstraintGraph (Fin n) (Fin n × D) PortTables.Label)
    (ports : D ≃ Fin d) (htail : G.tail = Prod.fst) :
    PortTables.baseGraph (materialize G ports) =
      G.reindex (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) ports) (Equiv.refl _) := by
  apply constraintGraph_ext
  · intro x
    rw [PortTables.baseGraph_reverse, rotation_materialize]
    rfl
  · intro x
    change x.1 = G.tail (x.1, ports.symm x.2)
    rw [htail]
  · intro x a b
    rw [PortTables.baseGraph_accepts, accepts_materialize]
    rfl

theorem overlay_semantics {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.baseGraph (overlay G H) =
      (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (overlayPorts d e))
        (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

theorem lazy_semantics {n d : Nat} (G : PortTables.Table n d) :
    PortTables.baseGraph (lazy G) =
      (LazyConstraint.constraintGraph (PortTables.baseGraph G)).reindex
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (lazyPorts d)) (Equiv.refl _) :=
  baseGraph_materialize _ _ rfl

end IndependentSetsGames.Foundations.PCP.PreprocessingOverlayTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingPaddingTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem baseGraph_pad (table : Table n d) (h : n ≤ m) :
    baseGraph (pad table h) = paddedGraph table h := by
  apply constraintGraph_ext
  · exact rotation_pad table h
  · rfl
  · funext e a b
    exact accepts_pad table h e a b

theorem paddedGraph_edgeSatisfied_equiv (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (paddedGraph table h).edgeSatisfied labeling (dartEquiv h e) =
      (sumGraph table m).edgeSatisfied (fun v => labeling (vertexEquiv h v)) e := by
  change (sumGraph table m).accepts ((dartEquiv h).symm (dartEquiv h e))
    (labeling (dartEquiv h e).1)
    (labeling (dartEquiv h ((sumGraph table m).reverse
      ((dartEquiv h).symm (dartEquiv h e)))).1) =
    (sumGraph table m).accepts e (labeling (vertexEquiv h e.1))
      (labeling (vertexEquiv h ((sumGraph table m).reverse e).1))
  simp only [Equiv.symm_apply_apply]
  rfl

theorem edgeSatisfied_pad_equiv (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (e : (Fin n ⊕ Fin (m - n)) × Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (dartEquiv h e) =
      (sumGraph table m).edgeSatisfied (fun v => labeling (vertexEquiv h v)) e := by
  rw [baseGraph_pad]
  exact paddedGraph_edgeSatisfied_equiv table h labeling e

@[simp] theorem edgeSatisfied_pad_old (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (v : Fin n) (p : Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (v.castLE h, p) =
      (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) (v, p) := by
  simpa only [dartEquiv_apply, vertexEquiv_inl, sumGraph,
    VertexPadding.edgeSatisfied_inl (baseGraph table) rfl] using
    edgeSatisfied_pad_equiv table h labeling (Sum.inl v, p)

@[simp] theorem edgeSatisfied_pad_new (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) (v : Fin (m - n)) (p : Fin d) :
    (baseGraph (pad table h)).edgeSatisfied labeling (vertexEquiv h (Sum.inr v), p) = true := by
  simpa only [dartEquiv_apply, sumGraph, VertexPadding.edgeSatisfied_inr] using
    edgeSatisfied_pad_equiv table h labeling (Sum.inr v, p)

theorem pad_labeling_satisfies_iff (table : Table n d) (h : n ≤ m)
    (labeling : Fin m → Label) :
    (∀ e, (baseGraph (pad table h)).edgeSatisfied labeling e = true) ↔
      ∀ e, (baseGraph table).edgeSatisfied (fun v => labeling (v.castLE h)) e = true := by
  constructor
  · intro hs e
    simpa only [edgeSatisfied_pad_old] using hs (e.1.castLE h, e.2)
  · intro hs e
    obtain ⟨v, hv⟩ := (vertexEquiv h).surjective e.1
    have he : e = (vertexEquiv h v, e.2) := Prod.ext hv.symm rfl
    rw [he]
    cases v with
    | inl v => simpa only [vertexEquiv_inl, edgeSatisfied_pad_old] using hs (v, e.2)
    | inr v => exact edgeSatisfied_pad_new table h labeling v e.2

theorem pad_satisfiable_iff (table : Table n d) (h : n ≤ m) :
    (baseGraph (pad table h)).Satisfiable ↔ (baseGraph table).Satisfiable := by
  constructor
  · rintro ⟨labeling, hs⟩
    exact ⟨fun v => labeling (v.castLE h), (pad_labeling_satisfies_iff table h labeling).1 hs⟩
  · rintro ⟨labeling, hs⟩
    refine ⟨extendLabeling h labeling, (pad_labeling_satisfies_iff table h _).2 ?_⟩
    simpa only [extendLabeling_old] using hs

end IndependentSetsGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingRegularTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.IndependentSetsGames.Foundations.PCP.PoweringLabels.finiteBall _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

theorem edgeSatisfied_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).edgeSatisfied labels
        (vertexOrder t padding v, portOrder q p) =
      (sourceGraph t padding tables).edgeSatisfied
        (fun z => labels (vertexOrder t padding z)) (v, p) := by
  change PortTables.accepts (ofCloudTables t padding tables)
    (vertexOrder t padding v, portOrder q p) (labels (vertexOrder t padding v))
    (labels (PortTables.rotation (ofCloudTables t padding tables)
      (vertexOrder t padding v, portOrder q p)).1) = _
  rw [rotation_ofCloudTables, accepts_ofCloudTables]
  rfl

end IndependentSetsGames.Foundations.PCP.PreprocessingRegularTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingTables
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (regularize H t)).Satisfiable := by
  obtain ⟨labels, hlabels⟩ := h
  refine ⟨liftedLabel t (padding t) labels, ?_⟩
  intro e
  obtain ⟨z, rfl⟩ :=
    (Equiv.prodCongr (vertexOrder t (padding t)) (portOrder internalDegree)).surjective e
  rcases z with ⟨v, p⟩
  change (PortTables.baseGraph (regularize H t)).edgeSatisfied
    (liftedLabel t (padding t) labels)
    (vertexOrder t (padding t) v, portOrder internalDegree p) = true
  rw [regularize, edgeSatisfied_ofCloudTables]
  simp only [liftedLabel, Equiv.symm_apply_apply]
  have hcomplete := replacement_complete
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (cloudGraphs t (padding t) (familyCloudTable H t)) labels
    (padded_complete (GraphTables.semantics t) (fun v => Fin (padding t v)) labels hlabels)
    (v, p)
  convert hcomplete using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end IndependentSetsGames.Foundations.PCP.PreprocessingRegularSoundness

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingTableSpectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree regularize)

variable {n d e : Nat}

theorem overlay_rejectionCount (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.overlay G H)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.overlay_semantics]
  calc
    _ = (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.overlayPorts d e)) (Equiv.refl _) labels using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    _ = _ := Overlay.rejectionCount_eq _ _ rfl labels

theorem lazy_rejectionCount (G : PortTables.Table n d)
    (labels : Fin n → GraphTables.Label) :
    (PortTables.baseGraph (PreprocessingOverlayTables.lazy G)).rejectionCount labels =
      (PortTables.baseGraph G).rejectionCount labels := by
  rw [PreprocessingOverlayTables.lazy_semantics]
  calc
    _ = (LazyConstraint.constraintGraph (PortTables.baseGraph G)).rejectionCount labels := by
      convert ConstraintGraph.reindex_rejectionCount
        (LazyConstraint.constraintGraph (PortTables.baseGraph G))
        (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _)
          (PreprocessingOverlayTables.lazyPorts d)) (Equiv.refl _) labels using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    _ = _ := LazyConstraint.rejectionCount_eq _ rfl labels

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (preprocess H t)).Satisfiable := by
  have hp : (PortTables.baseGraph (padded H t)).Satisfiable :=
    (PreprocessingPaddingTables.pad_satisfiable_iff _ _).mpr
      (PreprocessingRegularSoundness.completeness H t h)
  obtain ⟨labels, hlabels⟩ := hp
  refine ⟨labels, ?_⟩
  apply (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mp
  unfold preprocess PreprocessingTables.degree
  rw [lazy_rejectionCount, overlay_rejectionCount]
  exact (ConstraintGraph.rejectionCount_eq_zero_iff _ labels).mpr hlabels

end IndependentSetsGames.Foundations.PCP.PreprocessingGuarantees
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Gap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.FinalConstants

theorem walkLength_positive : 0 < walkLength := by
  simp [walkLength]

end IndependentSetsGames.Foundations.PCP.FinalConstants
namespace IndependentSetsGames.Foundations.PCP.RoundTables

theorem alphabet_positive : 0 < alphabet := by
  unfold alphabet PoweringTables.labelCount
  exact Nat.pow_pos (by decide)

theorem build_completeness (H : BaseTable) (table : GraphTables.Table)
    (sat : (GraphTables.semantics table).Satisfiable) :
    (GraphTables.semantics (build H table)).Satisfiable := by
  let : Nonempty (Fin alphabet) := ⟨⟨0, alphabet_positive⟩⟩
  exact AlphabetTable.Table.perfect_completeness (powered H table)
    (PoweringTableSemantics.preserves_satisfiability
      (PreprocessingTables.preprocess H table) walkParameter
      (PreprocessingGuarantees.completeness H table sat))

theorem size_positive (input : Input) : 0 < size input :=
  input.property.trans_le (Nat.le_add_left _ _)

theorem initial_satisfiable_iff (F : Target.Formula) : Satisfiable (initial F) ↔ F.Satisfiable :=
  RawInitialTables.table_satisfiable_iff F

theorem step_completeness (H : BaseTable) (input : Input) :
    Satisfiable input → Satisfiable (step H input) := build_completeness H input.val

end IndependentSetsGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Contexts
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceContexts

open Target PCP

theorem pi_honest (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (assignment : Fin F.«variables» → Bool)
    (hsupport : ∀ t, ∃ s, nameAt (clauseAt F (c t)) s = v t) :
    pi F c v (honestJ F c assignment) = honestI F v assignment := by
  funext t
  exact (honest_answerAt _ assignment _).trans
    (congrArg assignment (canonicalSlot_name _ _ (hsupport t)))

end IndependentSetsGames.Foundations.Hastad.SourceContexts

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_Bounds
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceBounds

open Target
open IndependentSetsGames.Reduction

theorem formulaBits_length (F : Formula) :
    (Complexity.formulaBits F).length = F.«variables» + F.clauses.length + 2 +
      (Complexity.encodeWords (F.clauses.flatMap Complexity.clauseWords)).length := by
  simp only [Complexity.formulaBits, Complexity.formulaWords,
    Complexity.encodeWords_append, List.length_append, Complexity.encodeWords,
    Complexity.encodeWord_length, List.length_nil]
  omega

theorem formulaBits_length_ge_clauses (F : Formula) :
    F.clauses.length ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

open SourceContexts

end IndependentSetsGames.Foundations.Hastad.SourceBounds

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_VerifierCNF
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.VerifierToCNF

open Target

theorem chainView_sound (bits ys : List Bool)
    (size : bits.length = ys.length + 3)
    (accepted : (chainView bits ys).all tripleValue = true) : bits.any id = true := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => simpa [chainView, tripleValue, Bool.or_assoc] using accepted
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have accepted' : tripleValue (a, b, y) = true ∧
          (chainView ((!y) :: rest) ys).all tripleValue = true := by
        simpa only [chainView, List.all_cons, Bool.and_eq_true] using accepted
      have tailAccepted := ih ((!y) :: rest) smaller accepted'.2
      cases a <;> cases b <;> cases y <;> simp_all [tripleValue]

theorem fillBits_correct (bits : List Bool) (size : 3 ≤ bits.length) :
    (chainView bits (fillBits bits)).all tripleValue = true ↔ bits.any id = true := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits, chainView, tripleValue, Bool.or_assoc]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_correct ((a || b) :: c :: d :: rest) (by simp)
    have tautology : tripleValue (a, b, !(a || b)) = true := by
      cases a <;> cases b <;> rfl
    rw [fillBits]
    simp only [chainView, List.all_cons, Bool.not_not]
    rw [tautology]
    simp only [Bool.true_and]
    simpa [Bool.or_assoc] using ih
termination_by bits.length
decreasing_by simp_wf

theorem zero_false_count_iff_all (bits : List Bool) :
    bits.count false = 0 ↔ bits.all id = true := by
  induction bits with
  | nil => simp
  | cons b bits ih => cases b <;> simp [ih]

theorem chainView_failed (bits ys : List Bool)
    (size : bits.length = ys.length + 3) (failed : bits.any id = false) :
    1 ≤ ((chainView bits ys).map tripleValue).count false := by
  by_contra none
  have zero : ((chainView bits ys).map tripleValue).count false = 0 := by omega
  have all := (zero_false_count_iff_all _).mp zero
  have accepted : (chainView bits ys).all tripleValue = true := by
    simpa only [List.all_map, Function.comp_def, id_eq] using all
  have impossible := chainView_sound bits ys size accepted
  rw [failed] at impossible
  contradiction

theorem mem_patterns (q : Nat) (p : Pattern q) : p ∈ patterns q := by
  induction q with
  | zero =>
    have h : p = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp [patterns, h]
  | succ q ih =>
    let tail : Pattern q := fun i => p i.succ
    have htail : tail ∈ patterns q := ih tail
    have prefixEquality : Fin.cases (p 0) tail = p := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, htail, ?_⟩
    cases h : p 0 with
    | false =>
      have hp : Fin.cases false tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inl hp.symm)
    | true =>
      have hp : Fin.cases true tail = p := by simpa only [h] using prefixEquality
      exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hp.symm)))

theorem patternAt_surjective (q : Nat) (bits : Pattern q) :
    ∃ p : PatternIndex q, patternAt q p = bits := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem (mem_patterns q bits)
  exact ⟨⟨i, hi⟩, h⟩

theorem forbiddenLiteral_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) (i : Fin q) :
    (forbiddenLiteral V e p i).eval A = false ↔ A (V.query e i) = patternAt q p i := by
  cases hp : patternAt q p i <;> cases ha : A (V.query e i) <;>
    simp [forbiddenLiteral, Literal.eval, hp, ha]

theorem forbiddenClause_values {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (forbiddenClause V e p).map (fun l => l.eval B) =
      mismatchBits V (restrictAssignment V B) e p := by
  simp [forbiddenClause, mismatchBits, List.map_ofFn, Function.comp_def, liftLiteral, Literal.eval,
    restrictAssignment]

theorem mismatchBits_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q)
    (actual : ∀ i, A (V.query e i) = patternAt q p i) :
    (mismatchBits V A e p).any id = false := by
  apply List.any_eq_false.mpr
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h := (forbiddenLiteral_false V A e p i).mpr (actual i)
  simp [h]

theorem mismatchBits_true {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) (honest : eventValue V A e = true)
    (rejected : V.accepts e (patternAt q p) = false) :
    (mismatchBits V A e p).any id = true := by
  cases h : (mismatchBits V A e p).any id with
  | true => rfl
  | false =>
    have none := List.any_eq_false.mp h
    have equal : (fun i => A (V.query e i)) = patternAt q p := by
      funext i
      apply (forbiddenLiteral_false V A e p i).mp
      have hi := none ((forbiddenLiteral V e p i).eval A)
        (List.mem_ofFn.mpr ⟨i, rfl⟩)
      cases hv : (forbiddenLiteral V e p i).eval A <;> simp_all
    have impossible : V.accepts e (patternAt q p) = true := by
      simpa only [eventValue, equal] using honest
    rw [rejected] at impossible
    contradiction

theorem ofFn_getElem_of_length {α : Type*} (xs : List α) (n : Nat) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => xs[i.val]'(by rw [h]; exact i.isLt)) = xs := by
  subst n
  exact List.ofFn_getElem

theorem extended_auxiliary_values {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (auxiliaryNames V e p).map (extendAssignment V hq A) = fillBits (mismatchBits V A e p) := by
  simp only [auxiliaryNames, List.map_ofFn, Function.comp_def, extend_fresh, mismatchFill]
  exact ofFn_getElem_of_length _ _ (mismatchFill_length V hq A e p)

theorem tautology_satisfied {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (B : Fin (outputVariables V) → Bool) :
    (tautology V hq e).eval B = true := by
  simp [tautology, Clause.eval, Literal.eval]

theorem block_honest {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (honest : eventValue V A e = true) :
    (block V hq e p).all (fun c => c.eval (extendAssignment V hq A)) = true := by
  cases accepted : V.accepts e (patternAt q p) with
  | true => simp [block, accepted, tautology_satisfied]
  | false =>
    have good := (fillBits_correct (mismatchBits V A e p) (by simpa using hq)).mpr
      (mismatchBits_true V A e p honest accepted)
    have values := splitLong_values (forbiddenClause V e p) (auxiliaryNames V e p)
      (extendAssignment V hq A)
    rw [forbiddenClause_values, restrict_extend, extended_auxiliary_values] at values
    have all := congrArg (fun bs : List Bool => bs.all id) values
    simp only [List.all_map, Function.comp_def, id_eq] at all
    simpa only [block, accepted, Bool.false_eq_true, ↓reduceIte] using all.trans good

theorem convert_completeness {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (honest : ∀ e, eventValue V A e = true) :
    (convert V hq).Satisfiable := by
  refine ⟨extendAssignment V hq A, fun c hc => ?_⟩
  obtain ⟨e, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, _, hc⟩ := List.mem_flatMap.mp hc
  exact List.all_eq_true.mp (block_honest V hq A e p (honest e)) c hc

theorem clauseFailures_append {n : Nat} (xs ys : List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs ++ ys) A = clauseFailures xs A + clauseFailures ys A := by
  simp [clauseFailures, List.map_append, List.count_append]

theorem clauseFailures_le_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) (x : α) (hx : x ∈ xs) :
    clauseFailures (f x) A ≤ clauseFailures (xs.flatMap f) A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.flatMap_cons, clauseFailures_append]
      omega
    · have h := ih hx
      simp only [List.flatMap_cons, clauseFailures_append]
      omega

theorem block_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q)
    (rejected : V.accepts e (patternAt q p) = false)
    (actual : ∀ i, restrictAssignment V B (V.query e i) = patternAt q p i) :
    1 ≤ clauseFailures (block V hq e p) B := by
  have bitsFalse := mismatchBits_false V (restrictAssignment V B) e p actual
  have size : ((forbiddenClause V e p).map (fun l => l.eval B)).length =
      ((auxiliaryNames V e p).map B).length + 3 := by
    simp only [List.length_map, forbiddenClause, auxiliaryNames, List.length_ofFn]
    omega
  have failed := chainView_failed ((forbiddenClause V e p).map (fun l => l.eval B))
    ((auxiliaryNames V e p).map B) size (by
      rw [forbiddenClause_values]
      exact bitsFalse)
  simpa only [block, rejected, Bool.false_eq_true, ↓reduceIte, clauseFailures,
    splitLong_values] using failed

theorem eventBlock_failed {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events)
    (rejected : eventValue V (restrictAssignment V B) e = false) :
    1 ≤ clauseFailures (eventBlock V hq e) B := by
  obtain ⟨p, hp⟩ := patternAt_surjective q (fun i => restrictAssignment V B (V.query e i))
  have rejectedPattern : V.accepts e (patternAt q p) = false := by
    rw [hp]
    exact rejected
  have failed := block_failed V hq B e p rejectedPattern (fun i => (congrFun hp i).symm)
  exact failed.trans (clauseFailures_le_flatMap (List.finRange (patterns q).length)
    (block V hq e) B p (by simp))

theorem count_false_map_sum {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.map (fun x => if f x then 0 else 1)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

theorem nat_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (bound x (by simp)) (ih (fun y hy => bound y (by simp [hy])))

theorem convert_count_bridge {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (B : Fin (outputVariables V) → Bool) :
    rejectedEventCount V (restrictAssignment V B) ≤ NameCompaction.failedCount (convert V hq) B := by
  change ((List.finRange V.events).map (eventValue V (restrictAssignment V B))).count false ≤
    clauseFailures ((List.finRange V.events).flatMap (eventBlock V hq)) B
  rw [count_false_map_sum, clauseFailures_flatMap]
  apply nat_sum_map_le
  intro e _
  cases rejected : eventValue V (restrictAssignment V B) e with
  | false => simpa only [rejected, Bool.false_eq_true, ↓reduceIte] using
      eventBlock_failed V hq B e rejected
  | true => simp only [↓reduceIte, Nat.zero_le]

end IndependentSetsGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_FinalBooleanVerifier
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

theorem eventValue_eq (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) (e : Fin m) :
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e =
      G.edgeSatisfied (labelsOfBits vertices assignment) (edges.symm e) := by
  simp only [VerifierToCNF.eventValue, Fin.addCases_left, Fin.addCases_right,
    ConstraintGraph.edgeSatisfied]
  rfl

theorem count_false_map_filter {α : Type*} (xs : List α) (f : α → Bool) :
    (xs.map f).count false = (xs.filter (fun x => decide (f x = false))).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h, ih, Nat.add_comm]

theorem count_false_finRange (f : Fin m → Bool) :
    ((List.finRange m).map f).count false =
      (Finset.univ.filter (fun e : Fin m => f e = false)).card := by
  classical
  calc
    _ = ((List.finRange m).filter (fun e => decide (f e = false))).length :=
      count_false_map_filter _ _
    _ = (((List.finRange m).filter (fun e => decide (f e = false))).toFinset).card :=
      (List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)).symm
    _ = _ := by
      congr 1
      ext e
      simp

theorem rejection_count_eq [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : Fin (n * 6) → Bool) :
    VerifierToCNF.rejectedEventCount (verifier G vertices edges) assignment =
      G.rejectionCount (labelsOfBits vertices assignment) := by
  classical
  change ((List.finRange m).map
    (VerifierToCNF.eventValue (verifier G vertices edges) assignment)).count false = _
  rw [count_false_finRange]
  change (Finset.univ.filter (fun e : Fin m =>
    VerifierToCNF.eventValue (verifier G vertices edges) assignment e = false)).card =
      (G.rejectedDarts (labelsOfBits vertices assignment)).card
  apply Finset.card_equiv edges.symm
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    ConstraintGraph.rejectedDarts, eventValue_eq]

theorem verifier_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (labeling : V → Label)
    (satisfied : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ e, VerifierToCNF.eventValue (verifier G vertices edges)
      (bitsOfLabels vertices labeling) e = true := by
  intro e
  rw [eventValue_eq, labelsOfBits_bitsOfLabels]
  exact satisfied (edges.symm e)

theorem cnf_completeness (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (sat : G.Satisfiable) : (cnf G vertices edges).Satisfiable := by
  obtain ⟨labeling, satisfied⟩ := sat
  exact VerifierToCNF.convert_completeness (verifier G vertices edges) (by decide)
    (bitsOfLabels vertices labeling) (verifier_completeness G vertices edges labeling satisfied)

theorem cnf_count_bridge [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) :
    G.rejectionCount (extractLabeling G vertices edges assignment) ≤
      NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have h := VerifierToCNF.convert_count_bridge (verifier G vertices edges) (by decide) assignment
  rw [rejection_count_eq] at h
  exact h

theorem failedCount_zero_of_satisfied (F : Formula) (assignment : Fin F.«variables» → Bool)
    (satisfied : ∀ c ∈ F.clauses, c.eval assignment = true) :
    NameCompaction.failedCount F assignment = 0 := by
  apply (VerifierToCNF.zero_false_count_iff_all _).mpr
  have h := List.all_eq_true.mpr satisfied
  simpa only [NameCompaction.evaluationList, List.all_map, Function.comp_def, id_eq] using h

theorem all_satisfied_of_rejectionCount_zero [Fintype E] (G : ConstraintGraph V E Label)
    (labeling : V → Label) (zero : G.rejectionCount labeling = 0) :
    ∀ e, G.edgeSatisfied labeling e = true := by
  intro e
  cases h : G.edgeSatisfied labeling e with
  | true => rfl
  | false =>
    have member : e ∈ G.rejectedDarts labeling := (G.mem_rejectedDarts labeling e).mpr h
    have positive : 0 < G.rejectionCount labeling := Finset.card_pos.mpr ⟨e, member⟩
    omega

theorem cnf_reflects [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (sat : (cnf G vertices edges).Satisfiable) :
    G.Satisfiable := by
  obtain ⟨assignment, satisfied⟩ := sat
  have zero := failedCount_zero_of_satisfied (cnf G vertices edges) assignment satisfied
  have bound := cnf_count_bridge G vertices edges assignment
  have graphZero : G.rejectionCount (extractLabeling G vertices edges assignment) = 0 := by omega
  exact ⟨extractLabeling G vertices edges assignment,
    all_satisfied_of_rejectionCount_zero G _ graphZero⟩

theorem cnf_satisfiable_iff [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (cnf G vertices edges).Satisfiable ↔ G.Satisfiable :=
  ⟨cnf_reflects G vertices edges, cnf_completeness G vertices edges⟩

end IndependentSetsGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AmplificationIteration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AmplificationIteration

theorem run_preserves {X : Type*} (step : X → X) (P : X → Prop)
    (preserves : ∀ x, P x → P (step x)) (n : Nat) (x : X) (hx : P x) :
    P (run step n x) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact preserves _ ih

theorem run_size {X : Type*} (step : X → X) (size : X → Nat) (C : Nat)
    (blowup : ∀ x, size (step x) ≤ C * size x) (n : Nat) (x : X) :
    size (run step n x) ≤ C ^ n * size x := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have h := (blowup (run step n x)).trans (Nat.mul_le_mul_left C ih)
    simpa [run, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

theorem rounds_power_le {n : Nat} (hn : 0 < n) : 2 ^ rounds n ≤ 2 * n := by
  have h := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  simpa [rounds, Nat.log2_eq_log_two, pow_succ, Nat.mul_comm] using
    (Nat.mul_le_mul_right 2 h)

theorem blowup_rounds_le {C degree n : Nat} (hn : 0 < n) (hC : C ≤ 2 ^ degree) :
    C ^ rounds n ≤ (2 * n) ^ degree := by
  calc
    C ^ rounds n ≤ (2 ^ degree) ^ rounds n := Nat.pow_le_pow_left hC _
    _ = (2 ^ rounds n) ^ degree := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm degree (rounds n)]
    _ ≤ (2 * n) ^ degree := Nat.pow_le_pow_left (rounds_power_le hn) _

theorem run_size_polynomial {X : Type*} (step : X → X) (size : X → Nat)
    {C degree n : Nat} (hn : 0 < n) (hC : C ≤ 2 ^ degree)
    (blowup : ∀ x, size (step x) ≤ C * size x) (x : X) :
    size (run step (rounds n) x) ≤ (2 * n) ^ degree * size x :=
  (run_size step size C blowup (rounds n) x).trans
    (Nat.mul_le_mul_right _ (blowup_rounds_le hn hC))

end IndependentSetsGames.Foundations.PCP.AmplificationIteration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_PCPIteration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.PCPIteration

theorem finalClauseGap_positive : 0 < finalClauseGap := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast FinalConstants.walkLength_positive)

end IndependentSetsGames.Foundations.PCP.PCPIteration
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_FinalTableFormula
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.FinalTableFormula

open Target Complexity

theorem satisfiable_iff (table : GraphTables.Table) :
    (output table).Satisfiable ↔ (GraphTables.semantics table).Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _)).trans
      ((GraphTables.semantics table).satisfiable_reindex (Equiv.refl _) (Equiv.refl _)
        FinalCNFPattern.labelEquiv.symm)

end IndependentSetsGames.Foundations.PCP.FinalTableFormula

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_TableIteration
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

theorem sizeFactor_le_power : sizeFactor ≤ 2 ^ polynomialDegree :=
  degreeData.property

theorem run_completeness (H : BaseTable) (n : Nat) (input : Input)
    (sat : Satisfiable input) : Satisfiable (run H n input) :=
  AmplificationIteration.run_preserves (step H) Satisfiable (step_completeness H) n input sat

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

theorem output_size (H : BaseTable) (F : Formula) :
    size (output H F) ≤ (2 * size (initial F)) ^ polynomialDegree * size (initial F) :=
  AmplificationIteration.run_size_polynomial (step H) size (size_positive (initial F))
    sizeFactor_le_power (step_size H) (initial F)

theorem initial_size_le (F : Formula) : size (initial F) ≤ 7 * (formulaBits F).length :=
  RawInitialMachineBudget.graph_size_bound F

theorem output_size_le_input (H : BaseTable) (F : Formula) :
    (outputTable H F).vertices + (outputTable H F).darts ≤
      (14 * (formulaBits F).length) ^ polynomialDegree * (7 * (formulaBits F).length) := by
  rw [← output_val]
  have h := initial_size_le F
  exact (output_size H F).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) h)

theorem tableSizePolynomial_eval (N : Nat) :
    tableSizePolynomial.eval N = (14 * N) ^ polynomialDegree * (7 * N) := by
  simp only [tableSizePolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

theorem output_bits_le (H : BaseTable) (F : Formula) :
    (GraphTables.tableBits (outputTable H F)).length ≤ tableBitsPolynomial.eval (formulaBits F).length := by
  rw [tableBitsPolynomial, Polynomial.eval_comp, tableSizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ (output_size_le_input H F)

theorem gapMap_bits_le (H : BaseTable) (F : Formula) :
    (formulaBits (gapMap H F)).length ≤ formulaBitsPolynomial.eval (formulaBits F).length := by
  rw [formulaBitsPolynomial, Polynomial.eval_comp]
  exact (FinalTableFormula.formulaBits_length_le_polynomial (outputTable H F)).trans
    (MachineComposition.natPolynomial_eval_mono _ (output_bits_le H F))

end IndependentSetsGames.Foundations.PCP.TableIteration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_RoundTableGap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

omit certificate in
theorem finalClauseGap_le_one : PCPIteration.finalClauseGap ≤ 1 := by
  have hw : (1 : ℚ) ≤ (FinalConstants.walkLength : ℚ) := by
    exact_mod_cast FinalConstants.walkLength_positive
  have hd : (0 : ℚ) < 40960 * (FinalConstants.walkLength : ℚ) := by positivity
  rw [PCPIteration.finalClauseGap, div_le_one hd]
  linarith

end IndependentSetsGames.Foundations.PCP.TableGapReduction

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_WalkLength
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

lemma nonexpanding_path {X Y : Type*} [PseudoEMetricSpace Y]
    (w : X → X → ℝ≥0∞) (φ : X → Y)
    (hφ : ∀ x y, edist (φ x) (φ y) ≤ w x y) (x y : X) :
    edist (φ x) (φ y) ≤ pathDistance w x y := by
  apply le_iInf
  intro p
  induction p generalizing x with
  | nil => exact hφ x y
  | cons a p ih =>
      exact (edist_triangle (φ x) (φ a) (φ y)).trans (add_le_add (hφ x a) (ih a))

lemma circleRep_nonneg (z : UnitAddCircle) : 0 ≤ circleRep z :=
  (AddCircle.equivIco (1 : ℝ) 0 z).property.1

lemma circleRep_lt_one (z : UnitAddCircle) : circleRep z < 1 := by
  simpa only [circleRep, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).property.2

lemma circleRep_coe (z : UnitAddCircle) : (circleRep z : UnitAddCircle) = z :=
  AddCircle.coe_equivIco

lemma circleColor_bounds (z : UnitAddCircle) :
    ((circleColor z).val : ℝ) / 3 ≤ circleRep z ∧
      circleRep z < ((circleColor z).val + 1 : ℝ) / 3 := by
  unfold circleColor
  split_ifs with h1 h2
  · norm_num only [Fin.val_zero, Nat.cast_zero, zero_div, zero_add]
    exact ⟨circleRep_nonneg z, h1⟩
  · norm_num only [Fin.val_one, Nat.cast_one]
    exact ⟨le_of_not_gt h1, by linarith⟩
  · change (2 : ℝ) / 3 ≤ circleRep z ∧ circleRep z < (2 + 1) / 3
    exact ⟨le_of_not_gt h2, by linarith [circleRep_lt_one z]⟩

lemma circle_dist_le_reps (x y : UnitAddCircle) :
    dist x y ≤ |circleRep x - circleRep y| := by
  have h := QuotientAddGroup.norm_mk_le_norm
    (S := AddSubgroup.zmultiples (1 : ℝ)) (m := circleRep x - circleRep y)
  calc
    dist x y = ‖((circleRep x - circleRep y : ℝ) : UnitAddCircle)‖ := by
      rw [AddCircle.coe_sub, circleRep_coe, circleRep_coe, dist_eq_norm]
    _ ≤ ‖circleRep x - circleRep y‖ := h
    _ = |circleRep x - circleRep y| := Real.norm_eq_abs _

lemma circle_same_color_close {x y : UnitAddCircle}
    (h : circleColor x = circleColor y) : dist x y < 1 / 3 := by
  have hx := circleColor_bounds x
  have hy := circleColor_bounds y
  rw [h] at hx
  apply (circle_dist_le_reps x y).trans_lt
  rw [abs_lt]
  constructor <;> linarith

lemma circle_antipode_distance (x : UnitAddCircle) :
    dist x (x + ((1 / 2 : ℝ) : UnitAddCircle)) = 1 / 2 := by
  rw [dist_self_add_right]
  simpa only [abs_one] using AddCircle.norm_half_period_eq (1 : ℝ)

theorem phase_completeness {X : Type*} (w : X → X → ℝ≥0∞) (T : X → X)
    (φ : X → UnitAddCircle)
    (hφ : ∀ x y, edist (φ x) (φ y) ≤ w x y)
    (hhalf : ∀ x, φ (T x) = φ x + ((1 / 2 : ℝ) : UnitAddCircle)) :
    (∀ x, ¬pathDistance w x (T x) ≤ ENNReal.ofReal (1 / 8)) ∧
    (∀ (V : Type*) (location : V → X), ∀ u v,
      pathDistance w (location u) (T (location v)) ≤ ENNReal.ofReal (1 / 8) →
      circleColor (φ (location u)) ≠ circleColor (φ (location v))) := by
  constructor
  · intro x hx
    have h := (nonexpanding_path w φ hφ x (T x)).trans hx
    rw [hhalf, edist_dist, circle_antipode_distance] at h
    norm_num at h
  · intro V location u v hedge hcolor
    have h := (nonexpanding_path w φ hφ (location u) (T (location v))).trans hedge
    rw [hhalf, edist_dist, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h
    have hclose := circle_same_color_close hcolor
    have htri := dist_triangle (φ (location v)) (φ (location u))
      (φ (location v) + ((1 / 2 : ℝ) : UnitAddCircle))
    rw [circle_antipode_distance, dist_comm (φ (location v)) (φ (location u))] at htri
    linarith

lemma forwardZero_phase {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (a : ∀ q, M q) (ha : S.Consistent a)
    {x y : GridLocation M D} (h : S.ForwardZero D x y) :
    gridPhase a x = gridPhase a y := by
  cases h with
  | link q q' π hπ v => simp only [gridPhase, Function.comp_apply, ha q q' π hπ]

lemma zeroLink_phase {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (a : ∀ q, M q) (ha : S.Consistent a)
    {x y : GridLocation M D} (h : S.ZeroLink D x y) :
    gridPhase a x = gridPhase a y := by
  rcases h with h | h
  · exact forwardZero_phase S a ha h
  · exact (forwardZero_phase S a ha h).symm

lemma gridPhase_nonexpanding {Q : Type*} {M : Q → Type*} (S : ProjectionSystem Q M)
    {D : ℕ} [NeZero D] (a : ∀ q, M q) (ha : S.Consistent a)
    (x y : GridLocation M D) :
    edist (gridPhase a x) (gridPhase a y) ≤ S.linkLength x y := by
  classical
  unfold ProjectionSystem.linkLength
  split_ifs with hz
  · rw [zeroLink_phase S a ha hz, edist_self]
  · rcases x with ⟨q, f⟩
    rcases y with ⟨q', g⟩
    by_cases hq : q = q'
    · subst q'
      rw [copyLength_same]
      exact le_iSup_of_le (a q) le_rfl
    · simp [copyLength, hq]

lemma grid_half_real (D : ℕ) [NeZero D] (hD : Even D) :
    ((D / 2 : ℕ) : ℝ) / D = 1 / 2 := by
  have htwo : (D / 2) + (D / 2) = D := by
    obtain ⟨n, hn⟩ := hD
    omega
  have htwoR : ((D / 2 : ℕ) : ℝ) + ((D / 2 : ℕ) : ℝ) = D := by exact_mod_cast htwo
  apply (div_eq_iff (show (D : ℝ) ≠ 0 by exact_mod_cast NeZero.ne D)).mpr
  linarith

lemma gridPhase_antipode {Q : Type*} {M : Q → Type*} {D : ℕ} [NeZero D]
    (hD : Even D) (a : ∀ q, M q) (x : GridLocation M D) :
    gridPhase a (gridAntipode x) = gridPhase a x + ((1 / 2 : ℝ) : UnitAddCircle) := by
  simp only [gridPhase, gridAntipode, map_add, ZMod.toAddCircle_natCast, grid_half_real D hD]

theorem projection_grid_completeness {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (a : ∀ q, M q) (ha : S.Consistent a) :
    (∀ x : GridLocation M D,
      ¬pathDistance S.linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1 / 8)) ∧
    (∀ (V : Type*) (location : V → GridLocation M D), ∀ u v,
      pathDistance S.linkLength (location u) (gridAntipode (location v)) ≤
        ENNReal.ofReal (1 / 8) →
      circleColor (gridPhase a (location u)) ≠ circleColor (gridPhase a (location v))) :=
  phase_completeness S.linkLength gridAntipode (gridPhase a)
    (gridPhase_nonexpanding S a ha) (gridPhase_antipode hD a)

theorem gridGraph_three_coloring {Q : Type*} {M : Q → Type*}
    (S : ProjectionSystem Q M) {D : ℕ} [NeZero D] (hD : Even D)
    (a : ∀ q, M q) (ha : S.Consistent a)
    {V : Type*} (location : V → GridLocation M D) :
    ∃ color : V → Fin 3, ∀ u v, (gridGraph S hD location).Adj u v →
      color u ≠ color v := by
  refine ⟨fun v => circleColor (gridPhase a (location v)), ?_⟩
  intro u v h
  exact (projection_grid_completeness S hD a ha).2 V location u v h.2

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_LabelCoverData
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq _root_.OAI.LargeIndependentSets.mixedTupleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped ENNReal NNReal

theorem productLabeling_consistent {U V L R C : Type*}
    (lc : LabelCoverData U V L R C) (n : ℕ) (ℓ : U → L) (ρ : V → R)
    (hsat : lc.Satisfied ℓ ρ) :
    (layeredSystem lc n).Consistent (productLabeling ℓ ρ) := by
  intro q q' π hπ
  cases hπ with
  | adjacent h q q' c hleft hright houtside =>
      apply Subtype.ext
      funext k
      by_cases hk : k = h
      · subst k
        simp [mixedProject, productLabeling, MixedTuple.map,
          hleft, hright, hsat c]
      · simp only [mixedProject, productLabeling, MixedTuple.map, ite_eq_right hk,
          houtside k hk]

theorem layered_completeness {U V L R C : Type*}
    (lc : LabelCoverData U V L R C) (n : ℕ) (ℓ : U → L) (ρ : V → R)
    (hsat : lc.Satisfied ℓ ρ) {D : ℕ} [NeZero D] (hD : Even D) :
    (∀ x : GridLocation (LayerAnswer L R (U := U) (V := V) (n := n)) D,
      ¬pathDistance (layeredSystem lc n).linkLength x (gridAntipode x) ≤
        ENNReal.ofReal (1 / 8)) ∧
    (∀ (W : Type*) (location : W → GridLocation (LayerAnswer L R
      (U := U) (V := V) (n := n)) D),
      ∃ color : W → Fin 3, ∀ u v, (gridGraph (layeredSystem lc n) hD location).Adj u v →
        color u ≠ color v) := by
  have h := productLabeling_consistent lc n ℓ ρ hsat
  exact ⟨(projection_grid_completeness.{_, _, 0} (layeredSystem lc n) hD _ h).1,
    fun W location => gridGraph_three_coloring (layeredSystem lc n) hD _ h location⟩

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FrameNonempty
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.LCInput
open IndependentSetsGames.Foundations
open Target PCP Hastad.SourceContexts Hastad.SourceGame Games
open scoped BigOperators Classical
noncomputable section

lemma repair_honest {n : ℕ} (cl : Target.Clause n) (a : Fin n → Bool) (ha : cl.eval a = true) :
    repair cl (honestAnswer cl a) = honestAnswer cl a := by
  simp [repair, honest_satisfies, ha, honest_consistent]

lemma complete (F : Target.Formula) (u : ℕ) (hs : F.Satisfiable) :
    ∃ ℓ ρ, (labelCover F u).Satisfied ℓ ρ := by
  obtain ⟨a,ha⟩ := hs
  refine ⟨fun c => honestJ F c a, fun v => honestI F v a, ?_⟩
  intro e
  change pi F _ _ (repaired F _ (honestJ F _ a)) = _
  have he : repaired F (fun t => (e t).1) (honestJ F (fun t => (e t).1) a) =
      honestJ F (fun t => (e t).1) a := by
    funext t
    exact repair_honest _ a (ha _ (List.getElem_mem _))
  dsimp only [labelCover]
  rw [he]
  exact pi_honest F _ _ a (fun t => ⟨(e t).2,rfl⟩)

end
end LargeIndependentSets.LCInput

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_SamplerParameters
attribute [-instance] _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators
open MeasureTheory PhaseTest

namespace SamplerParameters

theorem completeness (p : SamplerParameters) {U V L R C : Type} [Fintype L] [Fintype R]
    (lc : LabelCoverData U V L R C) (ℓ : U → L) (ρ : V → R) (h : lc.Satisfied ℓ ρ) :
    (∀ x : GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=p.n)) (p.m*2^p.k),
      ¬pathDistance (layeredSystem lc p.n).linkLength x (gridAntipode x) ≤ ENNReal.ofReal (1/8)) ∧
    ∃ color : p.Vertices L R C → Fin 3, ∀ u v, (p.graph lc).Adj u v → color u ≠ color v := by
  have hC := layered_completeness lc p.n ℓ ρ h p.even
  exact ⟨hC.1, hC.2 _ (p.location lc)⟩

end SamplerParameters

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Simple
attribute [-instance] _root_.OAI.LargeIndependentSets.NamedReduction.cubeDecidableEq _root_.OAI.LargeIndependentSets.ShortestPaths.forwardZero_decidable _root_.OAI.LargeIndependentSets.ShortestPaths.zeroLink_decidable _root_.OAI.LargeIndependentSets.mixedTupleComputableFintype _root_.OAI.LargeIndependentSets.mixedTupleDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

namespace Graph

theorem ofSimple_colorable {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    (h : ∃ color : W → Fin 3, ∀ u v, H.Adj u v → color u ≠ color v) :
    (ofSimple H).ThreeColorable := by
  obtain ⟨color,hcolor⟩ := h
  refine ⟨fun u => color ((Fintype.equivFin W).symm u),?_⟩
  intro u v h
  exact hcolor _ _ (of_decide_eq_true h)

theorem ofSimple_independent {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    (A : Finset (Fin (ofSimple H).vertices)) (hA : (ofSimple H).Independent A) :
    H.IsIndepSet (A.image (Fintype.equivFin W).symm : Set W) := by
  intro u hu v hv hne hadj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
  have hne' : a ≠ b := fun h => hne (congrArg _ h)
  have hh := hA a ha b hb hne'
  have ht : (ofSimple H).adj a b = true := by exact decide_eq_true hadj
  exact Bool.false_ne_true (hh.symm.trans ht)

lemma exists_max_independent (G : Graph) :
    ∃ A : Finset (Fin G.vertices), G.Independent A ∧ G.independenceNumber = A.card := by
  let all := ((Finset.univ : Finset (Fin G.vertices)).powerset.filter G.Independent)
  have hne : all.Nonempty := by
    refine ⟨∅,?_⟩
    simp [all, Independent]
  obtain ⟨A,hA,he⟩ := Finset.exists_mem_eq_sup all hne Finset.card
  exact ⟨A,(Finset.mem_filter.mp hA).2,he⟩

theorem ofSimple_alpha {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    {δ : ℝ} (h : ∀ A : Finset W, H.IsIndepSet (A : Set W) →
      (A.card : ℝ) / Fintype.card W < δ) :
    ((ofSimple H).independenceNumber : ℝ) < δ * (ofSimple H).vertices := by
  obtain ⟨A,hA,he⟩ := (ofSimple H).exists_max_independent
  have hh := h (A.image (Fintype.equivFin W).symm) (ofSimple_independent H A hA)
  have hc : (A.image (Fintype.equivFin W).symm).card = A.card := by
    apply Finset.card_image_iff.mpr
    exact (Fintype.equivFin W).symm.injective.injOn
  rw [hc] at hh
  rw [he]
  exact (div_lt_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)).mp hh

lemma clique_alpha_le (q : ℕ) (hq : 0 < q) : (clique q hq).independenceNumber ≤ 1 := by
  obtain ⟨A,hA,he⟩ := (clique q hq).exists_max_independent
  rw [he]
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra hne
  have hh := hA u hu v hv hne
  let : DecidableEq (Fin q) := instDecidableEqFin q
  have hh' : decide (u ≠ v) = false := hh
  exact (of_decide_eq_false hh') hne

lemma clique_sound (q : ℕ) (hq : 0 < q) {δ : ℝ} (hδq : 1 < δ*q) :
    ((clique q hq).independenceNumber : ℝ) < δ*(clique q hq).vertices :=
  lt_of_le_of_lt (by exact_mod_cast clique_alpha_le q hq) hδq

end Graph

namespace SamplerParameters

lemma output_complete (p : SamplerParameters) (q : ℕ) (hq : 0 < q)
    {U V L R C : Type} [Fintype L] [Fintype R] [Fintype C] [Nonempty C]
    (lc : LabelCoverData U V L R C) (ℓ : U → L) (ρ : V → R) (h : lc.Satisfied ℓ ρ) :
    (p.output q hq lc).ThreeColorable := by
  obtain ⟨hn,hcol⟩ := p.completeness lc ℓ ρ h
  have ht : ¬p.CliqueTest lc := by
    rintro ⟨x,hx⟩
    exact hn x hx
  rw [output,ite_eq_right ht]
  exact Graph.ofSimple_colorable _ hcol

end SamplerParameters

theorem finite_graph_reduction {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : SamplerParameters, ∃ σ : ℚ, ∃ q : ℕ, ∃ hq : 0 < q,
    0 < σ ∧ σ < 1 ∧
    ∀ (U V L R C : Type) [Fintype L] [Fintype R] [Fintype C]
      [Nonempty L] [Nonempty R] [Nonempty C] (lc : LabelCoverData U V L R C),
    ((∃ ℓ ρ, lc.Satisfied ℓ ρ) → (p.output q hq lc).ThreeColorable) ∧
    (lc.Sound (σ:ℝ) → ((p.output q hq lc).independenceNumber : ℝ) <
      δ*(p.output q hq lc).vertices) := by
  obtain ⟨p,σ,hσ,hσ1,H⟩ := finite_source_soundness hδ
  obtain ⟨q,hq⟩ := exists_nat_gt (max (1:ℝ) (1/δ))
  have hq0 : 0 < q := by exact_mod_cast lt_trans (by norm_num : (0:ℝ) < 1) ((le_max_left _ _).trans_lt hq)
  have hδq : 1 < δ*(q:ℝ) := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hq)
    nlinarith
  refine ⟨p,σ,q,hq0,hσ,hσ1,?_⟩
  intro U V L R C _ _ _ _ _ _ lc
  constructor
  · rintro ⟨ℓ,ρ,h⟩
    exact p.output_complete q hq0 lc ℓ ρ h
  · intro hs
    by_cases ht : p.CliqueTest lc
    · rw [SamplerParameters.output,ite_eq_left ht]
      exact Graph.clique_sound q hq0 hδq
    · rw [SamplerParameters.output,ite_eq_right ht]
      apply Graph.ofSimple_alpha
      apply H U V L R C lc hs
      intro x hx
      exact ht ⟨x,hx⟩

end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ClausePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open scoped Classical
noncomputable section

lemma graphBits_length (G : Graph) : (graphBits G).length = 2*G.vertices.bits.length+1+G.vertices^2 := by
  have h : ∀ vs : List (Fin G.vertices),
      (vs.flatMap (fun u => (List.finRange G.vertices).map (G.adj u))).length =
        vs.length*G.vertices := by
    intro vs
    induction vs with
    | nil => simp
    | cons v vs ih => simp only [List.flatMap_cons,List.length_append,List.length_map,
        List.length_finRange,ih,List.length_cons]; nlinarith
  simp only [graphBits,nameBits,List.length_append,frame_length,h,List.length_finRange,pow_two]

lemma graphBits_bound (G : Graph) : (graphBits G).length ≤ 4*(G.vertices+1)^2 := by
  have h : G.vertices.bits.length ≤ G.vertices := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr G.vertices.lt_two_pow_self
  rw [graphBits_length]
  nlinarith

end
end LargeIndependentSets

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_TableIterationFiniteAlphabet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

theorem initial : FiniteAlphabet MachineRawInitialTable.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem finalCNF : FiniteAlphabet FinalCNFMachine.Program.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem counter : FiniteAlphabet MachineTableIteration.counterCertificate.tm := by
  intro k
  change Finite Bool
  infer_instance

variable (H : RoundTables.BaseTable)
  (body : Turing.TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (RoundTables.build H))
  (finiteBody : FiniteAlphabet body.tm)

include finiteBody

theorem counted : FiniteAlphabet (MachineTableIteration.countedCertificate H body).tm :=
  repeat_machine body.tm body.inputAlphabet body.outputAlphabet finiteBody

theorem iteration : FiniteAlphabet (MachineTableIteration.computableInPolyTime H body).tm :=
  composeBits MachineTableIteration.counterCertificate
    (MachineTableIteration.countedCertificate H body) counter (counted H body finiteBody)

theorem table : FiniteAlphabet (MachineTableIteration.tableCertificate H body).tm :=
  composeBits MachineTableIteration.initialCertificate
    (MachineTableIteration.computableInPolyTime H body) initial (iteration H body finiteBody)

theorem gapMap : FiniteAlphabet (MachineTableIteration.gapMapCertificate H body).tm :=
  composeBits (MachineTableIteration.tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime (table H body finiteBody) finalCNF

end IndependentSetsGames.Foundations.Complexity.TableIterationFiniteAlphabet

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Printer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine
open Turing Polynomial Command

 theorem tableComputer_finiteAlphabet (len bit : Expr) (k : (tableComputer len bit).tm.K) :
    Finite ((tableComputer len bit).tm.Γ k) := inferInstanceAs (Finite Bool)

end IndependentSetsCut.CounterMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Represented
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine.UnaryTables

section
open scoped BigOperators
open Finset

open scoped BigOperators
open Finset
open IndependentSetsCut.CounterMachine.Expr

lemma computer_finiteAlphabet (n v : Expr) (k : (computer n v).tm.K) :
    Finite ((computer n v).tm.Γ k) := by
  exact tableComputer_finiteAlphabet (totalLength n v) (wordBit n v) k
end

lemma encodedComputer_finiteAlphabet {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (n v : Expr) (spec) (k : (encodedComputer ea eb f n v spec).tm.K) :
    Finite ((encodedComputer ea eb f n v spec).tm.Γ k) := computer_finiteAlphabet n v k
end IndependentSetsCut.CounterMachine.UnaryTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FiniteScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.FiniteScan
open IndependentSetsCut.CounterMachine
open IndependentSetsGames.Foundations.Complexity
open Turing
open scoped BigOperators

lemma body_finiteAlphabet {m : ℕ} (δ : Fin m → Bool → Fin m) :
    MachineFiniteAlphabet.FiniteAlphabet (body δ).tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

lemma countedCertificate_finiteAlphabet {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) :
    MachineFiniteAlphabet.FiniteAlphabet (countedCertificate δ q).tm :=
  BoundedIteration.certificate_finiteAlphabet _ _ _ _ _ _ _ (body_finiteAlphabet δ)

lemma initialCertificate_finiteAlphabet {m : ℕ} (q : Fin m) :
    MachineFiniteAlphabet.FiniteAlphabet (initialCertificate q).tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

lemma finiteAlphabet {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) :
    MachineFiniteAlphabet.FiniteAlphabet (certificate δ q).tm :=
  MachineFiniteAlphabet.composeBits _ _ (initialCertificate_finiteAlphabet q)
    (countedCertificate_finiteAlphabet δ q)
end LargeIndependentSets.FiniteScan

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinarySyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinarySyntax

lemma run_append (q : Phase) (a b : List Bool) : run q (a++b) = run (run q a) b :=
  List.foldl_append

lemma run_header (s : List Bool) : run .headerMark (frame s) = .widthStart := by
  induction s with
  | nil => rfl
  | cons b bs ih => simpa only [frame,run_cons,transition] using ih

lemma run_name (r : Fin 3) (s : List Bool) : run (.mark r) (frame s) = after r := by
  induction s with
  | nil => rfl
  | cons b bs ih => simpa only [frame,run_cons,transition] using ih

lemma run_literal (r : Fin 3) (first : Bool) (l : Literal) :
    run (.sign r first) (literalBits l) = after r := by
  simpa only [literalBits,nameBits,run_cons,transition] using run_name r l.name.bits

lemma run_width (n : Fin 4) : run .widthStart (nameBits n.val) = width n := by
  fin_cases n <;> rfl

lemma run_clause (C : List Literal) (hw : C.length ≤ 3) :
    run .widthStart (clauseBits C) = .widthStart := by
  unfold clauseBits
  rw [run_append,run_width ⟨C.length,by omega⟩]
  cases C with
  | nil => rfl
  | cons a C =>
    cases C with
    | nil =>
        change run (.sign 0 true) (literalBits a ++ []) = .widthStart
        simpa [after] using run_literal 0 true a
    | cons b C =>
      cases C with
      | nil =>
        simp only [List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
          List.append_nil]
        change run (.sign 1 true) (literalBits a ++ literalBits b) = _
        rw [run_append,run_literal]
        exact run_literal 0 false b
      | cons c C =>
        have hc : C=[] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hw
          omega
        subst C
        simp only [List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
          List.append_nil]
        change run (.sign 2 true) (literalBits a ++ (literalBits b ++ literalBits c)) = _
        rw [run_append,run_literal]
        change run (.sign 1 false) (literalBits b ++ literalBits c) = _
        rw [run_append,run_literal]
        exact run_literal 0 false c

lemma run_clauses (Cs : List (List Literal)) (hw : ∀ C ∈ Cs, C.length ≤ 3) :
    run .widthStart (Cs.flatMap clauseBits) = .widthStart := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih =>
    rw [List.flatMap_cons,run_append,run_clause C (hw C (by simp))]
    exact ih (fun D hD => hw D (by simp [hD]))

lemma finiteAlphabet : IndependentSetsGames.Foundations.Complexity.MachineFiniteAlphabet.FiniteAlphabet
    certificate.tm := FiniteScan.finiteAlphabet _ _

end LargeIndependentSets.BinarySyntax

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinaryEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinarySyntax

lemma events_append (q : Phase) (a b : List Bool) :
    events q (a++b)=events q a++shift a.length (events (run q a) b) := by
  induction a generalizing q with
  | nil => simp [events]
  | cons x a ih =>
    simp only [List.cons_append,events,ih,shift_append,shift_shift,List.length_cons,run_cons,
      List.append_assoc,Nat.add_comm 1]

lemma events_header (s : List Bool) : events .headerMark (frame s)=[] := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [frame,events,transition,event,ih]

lemma events_name (r : Fin 3) (s : List Bool) : events (.mark r) (frame s)=[] := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [frame,events,transition,event,ih]

lemma events_literal (r : Fin 3) (first : Bool) (l : Literal) :
    events (.sign r first) (literalBits l)=if first then [(0,.first r)] else [] := by
  cases first <;> simp [literalBits,nameBits,events,event,transition,events_name]

lemma events_clause (C : List Literal) (hw : C.length ≤ 3) :
    events .widthStart (clauseBits C)=[clauseMark C] := by
  cases C with
  | nil => rfl
  | cons a C =>
    cases C with
    | nil =>
      simp only [clauseMark,clauseBits,List.cons_ne_nil,ite_false,List.length_cons,List.length_nil,
        List.flatMap_cons,List.flatMap_nil]
      change events .widthStart ([true,true,false]++(literalBits a++[])) = [(3,.first 0)]
      rw [events_append,events_append]
      simp [events,event,transition,run,events_literal]
    | cons b C =>
      cases C with
      | nil =>
        simp only [clauseMark,clauseBits,List.cons_ne_nil,ite_false,List.length_cons,List.length_nil,
          List.flatMap_cons,List.flatMap_nil]
        change events .widthStart ([true,false,true,true,false]++(literalBits a++(literalBits b++[]))) = [(5,.first 1)]
        rw [events_append]
        change [] ++ shift 5 (events (.sign 1 true) (literalBits a++(literalBits b++[]))) = _
        rw [events_append,events_append,run_literal]
        simp [events_literal,events,after]
      | cons c C =>
        have hc : C=[] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hw; omega
        subst C
        simp only [clauseMark,clauseBits,List.cons_ne_nil,ite_false,List.length_cons,List.length_nil,
          List.flatMap_cons,List.flatMap_nil]
        change events .widthStart ([true,true,true,true,false]++(literalBits a++(literalBits b++(literalBits c++[])))) = [(5,.first 2)]
        rw [events_append]
        change [] ++ shift 5 (events (.sign 2 true) (literalBits a++(literalBits b++(literalBits c++[])))) = _
        rw [events_append,run_literal]
        change shift 5 (events (.sign 2 true) (literalBits a) ++
          shift (literalBits a).length (events (.sign 1 false) (literalBits b++(literalBits c++[])))) = _
        rw [events_append,events_append,run_literal]
        simp [events_literal,events,after]

lemma mem_shift (k p : ℕ) (e : Mark) (xs : List (ℕ × Mark)) :
    (p,e) ∈ shift k xs ↔ ∃ j, (j,e) ∈ xs ∧ p=k+j := by
  simp only [shift,List.mem_map,Prod.exists,Prod.mk.injEq]
  constructor
  · rintro ⟨j,d,h,he,hd⟩; subst d; exact ⟨j,h,he.symm⟩
  · rintro ⟨j,h,rfl⟩; exact ⟨j,e,h,rfl,rfl⟩

lemma events_complete (q : Phase) (s : List Bool) (p : ℕ) (hp : p < s.length) (e : Mark) :
    (p,e) ∈ events q s ↔ event (run q (s.take p)) s[p]=some e := by
  induction s generalizing q p with
  | nil => simp at hp
  | cons b s ih =>
    cases p with
    | zero =>
      simp only [events,List.mem_append,List.mem_map,Option.mem_toList,Prod.mk.injEq,
        true_and,mem_shift,List.take_zero,run_nil,List.getElem_cons_zero]
      constructor
      · rintro (⟨e',he',rfl⟩|⟨j,hj,he⟩)
        · exact he'
        · omega
      · intro h; exact Or.inl ⟨e,h,rfl⟩
    | succ p =>
      have hp' : p < s.length := by simpa using hp
      simp only [events,List.mem_append,List.mem_map,Option.mem_toList,Prod.mk.injEq,
        show ¬(0=p+1) by omega,false_and,and_false,exists_false, false_or,mem_shift,
        List.take_succ_cons,run_cons,List.getElem_cons_succ]
      rw [← ih (transition q b) p hp']
      constructor
      · rintro ⟨j,hj,he⟩
        have : j=p := by omega
        subst j
        exact hj
      · intro h; exact ⟨p,h,by omega⟩

lemma event_clause_location (Cs : List (List Literal)) (hw : ∀ C ∈ Cs, C.length ≤ 3)
    (p : ℕ) (e : Mark) (he : (p,e) ∈ events .widthStart (Cs.flatMap clauseBits)) :
    ∃ pre C post, Cs=pre++C::post ∧
      p=(pre.flatMap clauseBits).length+(clauseMark C).1 ∧ e=(clauseMark C).2 := by
  induction Cs generalizing p with
  | nil => simp [events] at he
  | cons C Cs ih =>
    rw [List.flatMap_cons,events_append,events_clause C (hw C (by simp)),
      run_clause C (hw C (by simp))] at he
    rcases List.mem_append.mp he with h | h
    · have hh : (p,e)=clauseMark C := List.mem_singleton.mp h
      refine ⟨[],C,Cs,rfl,?_,?_⟩
      · simpa using congrArg Prod.fst hh
      · exact congrArg Prod.snd hh
    · obtain ⟨j,hj,hp⟩ := (mem_shift _ _ _ _).mp h
      obtain ⟨pre,D,post,hs,hj',he'⟩ := ih (fun D hD => hw D (by simp [hD])) j hj
      refine ⟨C::pre,D,post,by simp [hs],?_,he'⟩
      simp [hp,hj',List.flatMap_cons,Nat.add_assoc]

lemma events_bound (q : Phase) (s : List Bool) (p : ℕ) (e : Mark)
    (hp : (p,e) ∈ events q s) : p < s.length := by
  induction s generalizing q p with
  | nil => simp [events] at hp
  | cons b s ih =>
    rw [events,List.mem_append] at hp
    rcases hp with h | h
    · obtain ⟨e',_he,he'⟩ := List.mem_map.mp h
      have : p=0 := (congrArg Prod.fst he').symm
      simp [this]
    · obtain ⟨j,hj,hp⟩ := (mem_shift _ _ _ _).mp h
      have := ih (transition q b) j hj
      simp only [List.length_cons]
      omega

lemma clause_event_location (pre : List (List Literal)) (C : List Literal) (post : List (List Literal))
    (hw : ∀ D ∈ pre++C::post, D.length ≤ 3) :
    ((pre.flatMap clauseBits).length+(clauseMark C).1,(clauseMark C).2) ∈
      events .widthStart ((pre++C::post).flatMap clauseBits) := by
  rw [List.flatMap_append,events_append,run_clauses pre (fun D hD => hw D (by simp [hD]))]
  apply List.mem_append_right
  apply (mem_shift _ _ _ _).mpr
  refine ⟨(clauseMark C).1,?_,rfl⟩
  rw [List.flatMap_cons,events_append,events_clause C (hw C (by simp))]
  apply List.mem_append_left
  simp

lemma event_formula_location (F : Formula) (p : ℕ) (e : Mark)
    (he : (p,e) ∈ events .headerMark (formulaBits F)) :
    ∃ pre C post, F.clauses=pre++C::post ∧
      p=(nameBits F.clauses.length).length+(pre.flatMap clauseBits).length+(clauseMark C).1 ∧
      e=(clauseMark C).2 := by
  rw [formulaBits,events_append] at he
  simp only [nameBits,events_header,run_header,List.nil_append] at he
  obtain ⟨j,hj,hp⟩ := (mem_shift _ _ _ _).mp he
  obtain ⟨pre,C,post,hs,hj',he'⟩ := event_clause_location F.clauses F.width j e hj
  exact ⟨pre,C,post,hs,by dsimp [nameBits]; omega,he'⟩

lemma formula_clause_event (F : Formula) (pre : List (List Literal)) (C : List Literal)
    (post : List (List Literal)) (hF : F.clauses=pre++C::post) :
    ((nameBits F.clauses.length).length+(pre.flatMap clauseBits).length+(clauseMark C).1,
      (clauseMark C).2) ∈ events .headerMark (formulaBits F) := by
  rw [formulaBits,events_append]
  simp only [nameBits,events_header,run_header,List.nil_append]
  apply (mem_shift _ _ _ _).mpr
  refine ⟨(pre.flatMap clauseBits).length+(clauseMark C).1,?_,by omega⟩
  rw [hF]
  exact clause_event_location pre C post (fun D hD => F.width D (hF ▸ hD))

end LargeIndependentSets.BinarySyntax

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinaryNameTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinaryNames
open IndependentSetsCut.CounterMachine
open scoped BigOperators

lemma key_payload (s : List Bool) (p : ℕ) (hp : p ≤ s.length) :
    payload s (key s p) = payload s p := by
  simpa only [key,Nat.min_eq_left hp] using (Nat.find_spec (key_exists s p)).2
lemma key_eq (s : List Bool) (p q : ℕ) (hp : p ≤ s.length) (hq : q ≤ s.length)
    (he : payload s p = payload s q) : key s p = key s q := by
  apply le_antisymm
  · apply Nat.find_min'
    exact ⟨key_le s q,by rw [Nat.min_eq_left hp,key_payload s q hq,he]⟩
  · apply Nat.find_min'
    exact ⟨key_le s p,by rw [Nat.min_eq_left hq,key_payload s p hp,he]⟩

lemma raw_middle (pre mid post : List Bool) (i : ℕ) (hi : i < mid.length) :
    raw (pre++mid++post) (pre.length+i) = raw mid i := by
  rw [show pre++mid++post=pre++(mid++post) by rw [List.append_assoc]]
  unfold raw
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]

lemma literal_marker (l : Literal) (j : ℕ) (hj : j ≤ l.name.bits.length) :
    raw (literalBits l) (1+2*j) = decide (j<l.name.bits.length) := by
  simp only [raw,literalBits,nameBits,frame_eq,show 1+2*j=2*j+1 by omega,
    List.getElem?_cons_succ,IndependentSetsCut.CounterMachine.frame_get]
  simp [show 2*j%2=0 by omega,show 2*j<2*l.name.bits.length ↔ j<l.name.bits.length by omega]

lemma literal_payload (l : Literal) (j : ℕ) (hj : j<l.name.bits.length) :
    raw (literalBits l) (2+2*j) = raw l.name.bits j := by
  simp only [raw,literalBits,nameBits,frame_eq,show 2+2*j=(2*j+1)+1 by omega,
    List.getElem?_cons_succ,IndependentSetsCut.CounterMachine.frame_get]
  simp [show 2*j+1<2*l.name.bits.length by omega,
    show (2*j+1)/2=j by omega]

lemma nameLength_literal (pre post : List Bool) (l : Literal) :
    nameLength (pre++literalBits l++post) pre.length = l.name.bits.length := by
  apply (Nat.find_eq_iff _).mpr
  have hl : (literalBits l).length=2*l.name.bits.length+2 := by
    simp [literalBits,nameBits,LargeIndependentSets.frame_length]
  constructor
  · rw [show pre.length+1+2*l.name.bits.length=pre.length+(1+2*l.name.bits.length) by omega,
      raw_middle _ _ _ _ (by omega),literal_marker l _ le_rfl]
    simp
  · intro j hj
    rw [show pre.length+1+2*j=pre.length+(1+2*j) by omega,
      raw_middle _ _ _ _ (by omega),literal_marker l j hj.le]
    simp [hj]

lemma payload_literal (pre post : List Bool) (l : Literal) :
    payload (pre++literalBits l++post) pre.length = l.name.bits := by
  unfold payload
  rw [nameLength_literal]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range]
    have hl : (literalBits l).length=2*l.name.bits.length+2 := by
      simp [literalBits,nameBits,LargeIndependentSets.frame_length]
    rw [show pre.length+2+2*i=pre.length+(2+2*i) by omega,
      raw_middle _ _ _ _ (by omega),literal_payload l i hi']
    simp [raw,List.getElem?_eq_getElem hi']

lemma next_literal (pre post : List Bool) (l : Literal) :
    next (pre++literalBits l++post) pre.length = (pre++literalBits l).length := by
  rw [next,nameLength_literal]
  simp [literalBits,nameBits,LargeIndependentSets.frame_length]
  omega

end LargeIndependentSets.BinaryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinaryNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.BinaryNormalize
open BinarySyntax BinaryNames
open IndependentSetsGames.Foundations

lemma foldr_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih => simp [Nat.bits_append_bit n b h,ih]

lemma eventAt_iff (s : List Bool) (p : ℕ) (hp : p < s.length) (e : Mark) :
    eventAt s p = some e ↔ (p,e) ∈ events .headerMark s := by
  simpa [eventAt,raw,List.getElem?_eq_getElem hp] using
    (events_complete .headerMark s p hp e).symm

lemma raw_literal (pre post : List Bool) (l : Literal) :
    raw (pre++literalBits l++post) pre.length = l.positive := by
  rw [show pre.length=pre.length+0 by omega,raw_middle _ _ _ 0 (by simp [literalBits])]
  rfl

lemma dense_eval_iff {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (l : Literal)
    (hs : s=pre++literalBits l++post) :
    (dense s pre.length).eval σ = true ↔ θ l.name=l.positive := by
  rw [literal_eval_iff]
  change σ ⟨key s pre.length,_⟩ = raw s pre.length ↔ _
  rw [h pre l post hs,hs,raw_literal]

lemma exists_realizes_forward (s : List Bool) (θ : ℕ → Bool) :
    ∃ σ, Realizes s σ θ := by
  refine ⟨fun x => θ ((payload s x.val).foldr Nat.bit 0),?_⟩
  intro pre l post hs
  have hp : pre.length ≤ s.length := by simp only [hs,List.length_append]; omega
  change θ ((payload s (key s pre.length)).foldr Nat.bit 0)=θ l.name
  rw [key_payload s pre.length hp,hs,payload_literal,foldr_bits]

lemma exists_realizes_backward (s : List Bool) (σ : Fin (varCount s) → Bool) :
    ∃ θ, Realizes s σ θ := by
  classical
  let occurs (v : ℕ) := ∃ p, p ≤ s.length ∧ payload s p=v.bits
  let pos (v : ℕ) (h : occurs v) : ℕ := Classical.choose h
  let θ : ℕ → Bool := fun v => if h : occurs v then
    σ ⟨key s (pos v h),Nat.lt_succ_of_le (key_le s _)⟩ else false
  refine ⟨θ,?_⟩
  intro pre l post hs
  have hp : pre.length ≤ s.length := by simp only [hs,List.length_append]; omega
  have hv : payload s pre.length=l.name.bits := by rw [hs,payload_literal]
  have ho : occurs l.name := ⟨pre.length,hp,hv⟩
  dsimp only [θ]
  rw [dite_eq_left ho]
  have hpos := Classical.choose_spec ho
  have hkey : key s pre.length=key s (pos l.name ho) :=
    key_eq s _ _ hp hpos.1 (hv.trans hpos.2.symm)
  congr 1
  exact Fin.ext hkey

lemma sourceClause_one {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (a : Literal)
    (hs : s=pre++literalBits a++post) :
    (sourceClause s pre.length 0).eval σ=true ↔ θ a.name=a.positive := by
  simp only [sourceClause,Fin.val_zero,show ¬1≤0 by omega,show ¬2≤0 by omega,ite_false,
    triple_eval,or_self]
  exact dense_eval_iff h pre post a hs

lemma sourceClause_two {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (a b : Literal)
    (hs : s=pre++literalBits a++literalBits b++post) :
    (sourceClause s pre.length 1).eval σ=true ↔
      θ a.name=a.positive ∨ θ b.name=b.positive := by
  have ha : s=pre++literalBits a++(literalBits b++post) := by simpa [List.append_assoc] using hs
  have hb : s=(pre++literalBits a)++literalBits b++post := hs
  have hn : next s pre.length=(pre++literalBits a).length := by rw [ha,next_literal]
  simp only [sourceClause,show (1 : Fin 3).val=1 from rfl,le_refl,show ¬2≤1 by omega,
    ite_true,ite_false,triple_eval,hn,dense_eval_iff h pre _ a ha,
    dense_eval_iff h _ post b hb]
  tauto

lemma sourceClause_three {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (a b c : Literal)
    (hs : s=pre++literalBits a++literalBits b++literalBits c++post) :
    (sourceClause s pre.length 2).eval σ=true ↔
      θ a.name=a.positive ∨ θ b.name=b.positive ∨ θ c.name=c.positive := by
  have ha : s=pre++literalBits a++(literalBits b++literalBits c++post) := by
    simpa [List.append_assoc] using hs
  have hb : s=(pre++literalBits a)++literalBits b++(literalBits c++post) := by
    simpa [List.append_assoc] using hs
  have hc : s=(pre++literalBits a++literalBits b)++literalBits c++post := hs
  have hn : next s pre.length=(pre++literalBits a).length := by rw [ha,next_literal]
  have hn' : next s (pre++literalBits a).length=(pre++literalBits a++literalBits b).length := by
    rw [hb,next_literal]
  simp only [sourceClause,show (2 : Fin 3).val=2 from rfl,show 1≤2 by omega,le_refl,ite_true,
    triple_eval,hn,hn',dense_eval_iff h pre _ a ha,dense_eval_iff h _ _ b hb,
    dense_eval_iff h _ post c hc]

lemma pair_first (s : List Bool) (p : ℕ) (σ : Fin (varCount s) → Bool) (r : Fin 3)
    (he : eventAt s p=some (.first r)) :
    PairSatisfied s p σ ↔ (sourceClause s p r).eval σ=true := by
  simp [PairSatisfied,row,he]

lemma pair_empty (s : List Bool) (p : ℕ) (σ : Fin (varCount s) → Bool)
    (he : eventAt s p=some .empty) : ¬ PairSatisfied s p σ := by
  simp [PairSatisfied,row,he]

lemma pair_none (s : List Bool) (p : ℕ) (σ : Fin (varCount s) → Bool)
    (he : eventAt s p=none) : PairSatisfied s p σ := by
  simp [PairSatisfied,row,he]

lemma atClause {s : List Bool} {σ : Fin (varCount s) → Bool} {θ : ℕ → Bool}
    (h : Realizes s σ θ) (pre post : List Bool) (C : List Literal) (hw : C.length ≤ 3)
    (hs : s=pre++clauseBits C++post)
    (he : eventAt s (pre.length+(clauseMark C).1)=some (clauseMark C).2) :
    PairSatisfied s (pre.length+(clauseMark C).1) σ ↔
      ∃ l ∈ C, θ l.name=l.positive := by
  cases C with
  | nil =>
    have hn := pair_empty s _ σ he
    simp only [List.not_mem_nil,false_and,exists_false,iff_false]
    exact hn
  | cons a C =>
    cases C with
    | nil =>
      have hp : pre.length+(clauseMark [a]).1=(pre++nameBits 1).length := by
        simp [clauseMark]
      have he' : eventAt s (pre.length+(clauseMark [a]).1)=some (.first 0) := he
      rw [pair_first _ _ _ _ he',hp]
      have hs' : s=(pre++nameBits 1)++literalBits a++post := by
        simpa [clauseBits,List.append_assoc] using hs
      simpa using sourceClause_one h (pre++nameBits 1) post a hs'
    | cons b C =>
      cases C with
      | nil =>
        have hp : pre.length+(clauseMark [a,b]).1=(pre++nameBits 2).length := by
          simp [clauseMark]
        have he' : eventAt s (pre.length+(clauseMark [a,b]).1)=some (.first 1) := he
        rw [pair_first _ _ _ _ he',hp]
        have hs' : s=(pre++nameBits 2)++literalBits a++literalBits b++post := by
          simpa [clauseBits,List.append_assoc] using hs
        simpa [List.mem_cons,or_and_right,exists_or] using
          sourceClause_two h (pre++nameBits 2) post a b hs'
      | cons c C =>
        have hc : C=[] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hw
          omega
        subst C
        have hp : pre.length+(clauseMark [a,b,c]).1=(pre++nameBits 3).length := by
          simp [clauseMark]
        have he' : eventAt s (pre.length+(clauseMark [a,b,c]).1)=some (.first 2) := he
        rw [pair_first _ _ _ _ he',hp]
        have hs' : s=(pre++nameBits 3)++literalBits a++literalBits b++literalBits c++post := by
          simpa [clauseBits,List.append_assoc] using hs
        simpa [List.mem_cons,or_and_right,exists_or,or_assoc] using
          sourceClause_three h (pre++nameBits 3) post a b c hs'

lemma pairs_iff (s : List Bool) (σ : Fin (varCount s) → Bool) :
    (∀ C ∈ (normalize s).clauses, C.eval σ=true) ↔
      ∀ p < s.length, PairSatisfied s p σ := by
  change (∀ C ∈ (List.range s.length).flatMap (fun p => [row s p false,row s p true]),
    C.eval σ=true) ↔ _
  constructor
  · intro h p hp
    have hm (b : Bool) : row s p b ∈ (normalize s).clauses := by
      apply List.mem_flatMap.mpr
      refine ⟨p,List.mem_range.mpr hp,?_⟩
      cases b <;> simp
    exact ⟨h _ (hm false),h _ (hm true)⟩
  · intro h C hC
    obtain ⟨p,hp,hC⟩ := List.mem_flatMap.mp hC
    have hh := h p (List.mem_range.mp hp)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with rfl | rfl
    · exact hh.1
    · exact hh.2

lemma formula_atClause (F : Formula) {σ : Fin (varCount (formulaBits F)) → Bool}
    {θ : ℕ → Bool} (h : Realizes (formulaBits F) σ θ)
    (pre : List (List Literal)) (C : List Literal) (post : List (List Literal))
    (hF : F.clauses=pre++C::post) :
    let p := (nameBits F.clauses.length).length+(pre.flatMap clauseBits).length+(clauseMark C).1
    p < (formulaBits F).length ∧
      (PairSatisfied (formulaBits F) p σ ↔ ∃ l ∈ C, θ l.name=l.positive) := by
  dsimp only
  have hm := formula_clause_event F pre C post hF
  have hp := events_bound .headerMark (formulaBits F) _ _ hm
  refine ⟨hp,?_⟩
  have he := (eventAt_iff _ _ hp _).mpr hm
  have hh : F.clauses.length=(pre++C::post).length := congrArg List.length hF
  have hs : formulaBits F=(nameBits F.clauses.length++pre.flatMap clauseBits)++
      clauseBits C++post.flatMap clauseBits := by
    simp only [formulaBits,hF,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  have hc : C ∈ F.clauses := by rw [hF]; simp
  simpa only [List.length_append] using atClause h
    (nameBits F.clauses.length++pre.flatMap clauseBits) (post.flatMap clauseBits) C
    (F.width C hc) hs (by simpa only [List.length_append] using he)

theorem satisfiable_iff (F : Formula) :
    (normalize (formulaBits F)).Satisfiable ↔ F.Satisfiable := by
  constructor
  · rintro ⟨σ,hσ⟩
    obtain ⟨θ,hθ⟩ := exists_realizes_backward (formulaBits F) σ
    refine ⟨θ,?_⟩
    intro C hC
    obtain ⟨pre,post,hF⟩ := List.mem_iff_append.mp hC
    have hp := formula_atClause F hθ pre C post hF
    exact hp.2.mp ((pairs_iff _ σ).mp hσ _ hp.1)
  · rintro ⟨θ,hθ⟩
    obtain ⟨σ,hσ⟩ := exists_realizes_forward (formulaBits F) θ
    refine ⟨σ,(pairs_iff _ σ).mpr ?_⟩
    intro p hp
    cases he : eventAt (formulaBits F) p with
    | none => exact pair_none _ _ _ he
    | some e =>
      obtain ⟨pre,C,post,hF,hp',he'⟩ := event_formula_location F p e
        ((eventAt_iff _ _ hp _).mp he)
      rw [hp']
      exact (formula_atClause F hσ pre C post hF).2.mpr
        (hθ C (by rw [hF]; simp))

end LargeIndependentSets.BinaryNormalize

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_GraphPrinter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GraphPrinter
open IndependentSetsCut.CounterMachine
open IndependentSetsGames.Foundations.Complexity
open scoped Classical
noncomputable section

lemma encodedComputer_finiteAlphabet {α : Type} (ea : α → List Bool) (f : α → Graph)
    (n adj : Expr) (hn) (ha) :
    MachineFiniteAlphabet.FiniteAlphabet (encodedComputer ea f n adj hn ha).tm :=
  tableComputer_finiteAlphabet _ _

end
end LargeIndependentSets.GraphPrinter

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineRuntime
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRuntime

open Turing MachineComposition PCP PoweringMachineGlobal

variable {vertices d : Nat}

theorem computableInPolyTime_finite_alphabet (d n : Nat) :
    ∀ k, Finite ((computableInPolyTime d n).tm.Γ k) := by
  intro k
  change Finite Bool
  infer_instance

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRuntime

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_RoundComputation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RoundComputation

open Turing
open IndependentSetsGames.Foundations.Complexity

theorem powered_finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (poweredPolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits preprocessing powering hpreprocessing hpowering

theorem finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits
    (poweredPolynomialTimeOfCertificates H preprocessing powering)
    (AlphabetTable.Runtime.tablePolynomialTime RoundTables.alphabet)
    (powered_finiteAlphabet H preprocessing powering hpreprocessing hpowering)
    (AlphabetTable.Runtime.finiteAlphabet RoundTables.alphabet)

theorem tablePolynomialTime_finite_alphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTime H preprocessing).tm :=
  finiteAlphabet H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter) hpreprocessing
    (PoweringMachineRuntime.computableInPolyTime_finite_alphabet
      PreprocessingTables.degree RoundTables.walkParameter)

end IndependentSetsGames.Foundations.PCP.RoundComputation

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_FloydLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.FloydCarry
open IndependentSetsCut.CounterMachine
open ShortestPaths
open Turing
open scoped BigOperators
open IndependentSetsGames.Foundations.Complexity

lemma body_finiteAlphabet (B : ℕ) : MachineFiniteAlphabet.FiniteAlphabet (body B).tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

lemma certificate_finiteAlphabet (B : ℕ) (k : (certificate B).tm.K) :
    Finite ((certificate B).tm.Γ k) :=
  BoundedIteration.certificate_finiteAlphabet State.bits State.step Input.initial Input.count
    (body B) (lengthPolynomial B) intermediate_bound (body_finiteAlphabet B) k

end LargeIndependentSets.FloydCarry

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryInitialize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

lemma initializer_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (initializer L R n D).tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

lemma distanceComputer_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (distanceComputer L R n D).tm :=
  MachineFiniteAlphabet.composeBits _ _ (initializer_finiteAlphabet L R n D) (FloydCarry.certificate_finiteAlphabet D)

end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_Mixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.Graph

namespace Renaming
variable {G H : Graph}

lemma vertices_eq (e : Renaming G H) : G.vertices = H.vertices := by
  simpa using Fintype.card_congr e.equiv

lemma independent (e : Renaming G H) (A : Finset (Fin G.vertices)) (hA : G.Independent A) :
    H.Independent (A.image e.equiv) := by
  intro u hu v hv huv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
  rw [← e.adj_eq]
  exact hA i hi j hj (fun h => huv (congrArg e.equiv h))

lemma independent_card_le (G : Graph) (A : Finset (Fin G.vertices)) (hA : G.Independent A) :
    A.card ≤ G.independenceNumber := by
  unfold Graph.independenceNumber
  exact Finset.le_sup (f:=Finset.card) (Finset.mem_filter.mpr ⟨by simp,hA⟩)

lemma alpha_le (e : Renaming G H) : G.independenceNumber ≤ H.independenceNumber := by
  obtain ⟨A,hA,he⟩ := G.exists_max_independent
  rw [he,← Finset.card_image_of_injective A e.equiv.injective]
  exact independent_card_le H _ (e.independent A hA)

lemma alpha_eq (e : Renaming G H) : G.independenceNumber = H.independenceNumber :=
  le_antisymm e.alpha_le e.symm.alpha_le

lemma colorable (e : Renaming G H) (h : G.ThreeColorable) : H.ThreeColorable := by
  obtain ⟨c,hc⟩ := h
  refine ⟨fun v => c (e.equiv.symm v),?_⟩
  intro i j hij
  apply hc
  simpa only [e.adj_eq,Equiv.apply_symm_apply] using hij

lemma strict_density {δ : ℝ} (e : Renaming G H)
    (h : (G.independenceNumber:ℝ) < δ*G.vertices) :
    (H.independenceNumber:ℝ) < δ*H.vertices := by
  simpa only [e.alpha_eq,e.vertices_eq] using h

end Renaming
end LargeIndependentSets.Graph

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Geometry_GeometryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section
attribute [-instance] mixedTupleComputableFintype mixedTupleDecidableEq

variable (L R : Type) [Fintype L] [Fintype R] (p : SamplerParameters) (q : ℕ) (hq : 0<q)

lemma graphSerializer_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (graphSerializer L R p q hq).tm :=
  GraphPrinter.encodedComputer_finiteAlphabet _ _ _ _ _ _

lemma graphComputer_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (graphComputer L R p q hq).tm :=
  MachineFiniteAlphabet.composeBits (distanceView L R p) (graphSerializer L R p q hq)
    (distanceComputer_finiteAlphabet L R p.n (p.m*2^p.k)) (graphSerializer_finiteAlphabet L R p q hq)

attribute [instance 1100] mixedTupleComputableFintype
attribute [instance] mixedTupleDecidableEq
end
end LargeIndependentSets.GeometryNames

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Structural
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineCanonicalOutput
open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

theorem finiteAlphabet (P : Program K Λ σ) (chosen : List K) :
    MachineFiniteAlphabet.FiniteAlphabet (completedMachine P chosen) := by
  intro k
  exact inferInstanceAs (Finite Bool)

theorem computableInPolyTime_finite_alphabet {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computableInPolyTime P chosen complete encodeIn encodeOut f rawTime run).tm :=
  finiteAlphabet P chosen

end IndependentSetsGames.Foundations.Complexity.MachineCanonicalOutput

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineRegularTableRuntime
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)

theorem finite_alphabet (H : PreprocessingRegularTables.BaseTable) :
    ∀ k, Finite ((computableInPolyTime H).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

end IndependentSetsGames.Foundations.Complexity.MachineRegularTableRuntime

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachinePaddedOverlayRuntime
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

theorem finite_alphabet (H : BaseTable) (d : Nat) (hd : 0 < d) :
    ∀ k, Finite ((computableInPolyTime H d hd).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

end IndependentSetsGames.Foundations.Complexity.MachinePaddedOverlayRuntime

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.IndependentSetsGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

theorem finite_alphabet (d : Nat) (positive : 0 < d) :
    ∀ k, Finite ((computableInPolyTime d positive).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end IndependentSetsGames.Foundations.Complexity.MachineLazyTableRuntime
namespace IndependentSetsGames.Foundations.PCP.PreprocessingFinishRuntime

open Turing IndependentSetsGames.Foundations.Complexity
open PreprocessingRegularTables

theorem finite_alphabet (H : PreprocessingTables.BaseTable) (d : Nat) (hd : 0 < d) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime H d hd).tm :=
  MachineFiniteAlphabet.composeBits
    (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))
    (MachinePaddedOverlayRuntime.finite_alphabet H d hd)
    (MachineLazyTableRuntime.finite_alphabet (d + internalDegree)
      (finish_degree_positive d hd))

end IndependentSetsGames.Foundations.PCP.PreprocessingFinishRuntime
namespace IndependentSetsGames.Foundations.PCP.PreprocessingRuntime
open Turing IndependentSetsGames.Foundations.Complexity
open PreprocessingRegularTables

theorem finiteAlphabet (H : PreprocessingTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (tablePolynomialTime H).tm :=
  MachineFiniteAlphabet.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))
    (MachineRegularTableRuntime.finite_alphabet H)
    (PreprocessingFinishRuntime.finite_alphabet H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

end IndependentSetsGames.Foundations.PCP.PreprocessingRuntime

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PCPGapMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.PCPGapMachine
open IndependentSetsGames.Foundations
open Complexity PCP

lemma round_finiteAlphabet (H : RoundTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (round H).tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet H
    (PreprocessingRuntime.tablePolynomialTime H) (PreprocessingRuntime.finiteAlphabet H)

lemma finiteAlphabet (H : RoundTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (certificate H).tm :=
  TableIterationFiniteAlphabet.gapMap H (round H) (round_finiteAlphabet H)
end LargeIndependentSets.PCPGapMachine
namespace LargeIndependentSets.BinaryNormalize
open BinarySyntax BinaryNames
open IndependentSetsGames.Foundations
open IndependentSetsCut.CounterMachine
open scoped BigOperators

lemma serializer_finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet serializer.tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

lemma finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet certificate.tm :=
  Complexity.MachineFiniteAlphabet.composeBits annotator serializer
    BinarySyntax.finiteAlphabet serializer_finiteAlphabet

lemma gap_finiteAlphabet (H : PCP.RoundTables.BaseTable) :
    Complexity.MachineFiniteAlphabet.FiniteAlphabet (gapCertificate H).tm :=
  Complexity.MachineFiniteAlphabet.composeBits certificate (PCPGapMachine.certificate H)
    finiteAlphabet (PCPGapMachine.finiteAlphabet H)

end LargeIndependentSets.BinaryNormalize

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_TargetLC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace LargeIndependentSets.LabelCoverData
open scoped Classical
variable {U V L R C U' V' C' : Type}

lemma reindex_complete (lc : LabelCoverData U V L R C) (eu : U ≃ U') (ev : V ≃ V') (ec : C ≃ C')
    (h : ∃ l r, lc.Satisfied l r) : ∃ l r, (lc.reindex eu ev ec).Satisfied l r := by
  obtain ⟨l,r,hr⟩ := h
  refine ⟨fun u => l (eu.symm u),fun v => r (ev.symm v),?_⟩
  intro c
  simpa only [reindex,Equiv.symm_apply_apply] using hr (ec.symm c)

lemma reindex_sound [Fintype C] [Fintype C'] (lc : LabelCoverData U V L R C)
    (eu : U ≃ U') (ev : V ≃ V') (ec : C ≃ C') {σ : ℝ} (h : lc.Sound σ) :
    (lc.reindex eu ev ec).Sound σ := by
  intro l r
  have hs := h (fun u => l (eu u)) (fun v => r (ev v))
  have he : (Finset.univ.filter (fun c : C => lc.project c (l (eu (lc.left c)))=r (ev (lc.right c)))).card =
      (Finset.univ.filter (fun c : C' => (lc.reindex eu ev ec).project c (l ((lc.reindex eu ev ec).left c))=
        r ((lc.reindex eu ev ec).right c))).card := by
    apply Finset.card_bij (fun c _ => ec c)
    · intro c hc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change lc.project (ec.symm (ec c)) (l (eu (lc.left (ec.symm (ec c))))) =
        r (ev (lc.right (ec.symm (ec c))))
      simpa only [Equiv.symm_apply_apply] using (Finset.mem_filter.mp hc).2
    · intro c hc d hd he; exact ec.injective he
    · intro c hc
      refine ⟨ec.symm c,?_,Equiv.apply_symm_apply _ _⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp hc).2⟩
  simpa only [he,Fintype.card_congr ec] using hs

end LargeIndependentSets.LabelCoverData

namespace LargeIndependentSets.TargetLC
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame UniformLC
open scoped Classical BigOperators

variable (u : ℕ)

lemma table_lc (F : Input) : (table u F).lc =
    (LCInput.labelCover F.val u).reindex finFunctionFinEquiv finFunctionFinEquiv (eventEquiv u F.val) := rfl

lemma complete (F : Input) (h : F.val.Satisfiable) : ∃ l r, (table u F).lc.Satisfied l r := by
  rw [table_lc]
  exact LabelCoverData.reindex_complete _ _ _ _ (LCInput.complete F.val u h)

lemma sound (F : Input) {σ : ℝ} (h : (LCInput.labelCover F.val u).Sound σ) : (table u F).lc.Sound σ := by
  rw [table_lc]
  exact LabelCoverData.reindex_sound _ _ _ _ h

end LargeIndependentSets.TargetLC

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_TargetLCMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.TargetLC
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame UniformLC
open TargetRead TargetRepair
open scoped Classical BigOperators
noncomputable section
variable (u : ℕ)

lemma finiteAlphabet (k : (certificate u).tm.K) : Finite ((certificate u).tm.Γ k) :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _ k

end
end LargeIndependentSets.TargetLC

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open scoped Classical
noncomputable section

namespace CompleteReduction
open PCP Hastad.SourceContexts Hastad.SourceGame
open Complexity

lemma lcComputer_finiteAlphabet (H : RoundTables.BaseTable) (u : ℕ) :
    MachineFiniteAlphabet.FiniteAlphabet (lcComputer H u).tm :=
  MachineFiniteAlphabet.composeBits (gapView H) (TargetLC.certificate u)
    (BinaryNormalize.gap_finiteAlphabet H) (TargetLC.finiteAlphabet u)

lemma finiteAlphabet (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q) :
    MachineFiniteAlphabet.FiniteAlphabet (certificate H p u q hq).tm :=
  MachineFiniteAlphabet.composeBits (lcComputer H u) (GeometryNames.graphComputer (J u) (I u) p q hq)
    (lcComputer_finiteAlphabet H u) (GeometryNames.graphComputer_finiteAlphabet (J u) (I u) p q hq)

lemma normalize_bits (b : List Bool) :
    (Complexity.formulaBits (BinaryNormalize.normalize b)).length ≤ 100*(b.length+1)^2 := by
  have h := Complexity.formulaBits_length_le (BinaryNormalize.normalize b)
  rw [BinaryNormalize.clauses_length] at h
  change (Complexity.formulaBits (BinaryNormalize.normalize b)).length ≤
    b.length+1+2*b.length+2+2*b.length*(3*(b.length+1+2)) at h
  nlinarith [Nat.zero_le b.length]

lemma clauses_bound (H : RoundTables.BaseTable) (b : List Bool) :
    (gapInput H b).val.clauses.length ≤ clausePolynomial.eval b.length := by
  have h0 := Hastad.SourceBounds.formulaBits_length_ge_clauses (gapInput H b).val
  have h1 := TableIteration.gapMap_bits_le H (BinaryNormalize.normalize b)
  have h2 := MachineComposition.natPolynomial_eval_mono TableIteration.formulaBitsPolynomial (normalize_bits b)
  apply h0.trans (h1.trans _)
  simpa only [clausePolynomial,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X] using h2

lemma vertices_bound (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (b : List Bool) : (reduce H p u q hq b).vertices ≤
      (vertexPolynomial p u q).eval b.length := by
  have hs : (reduce H p u q hq b).vertices ≤ q+
      ((gapInput H b).val.clauses.length*3)^(u*p.n)*GeometryNames.outcomeCount (J u) (I u) p := by
    unfold reduce GeometryNames.output
    split
    · change q ≤ _
      omega
    · change (TargetLC.table u (gapInput H b)).ne^p.n*GeometryNames.outcomeCount (J u) (I u) p ≤ _
      simp only [TargetLC.table,← pow_mul]
      omega
  apply hs.trans
  simp only [vertexPolynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_pow]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_left
  nlinarith [clauses_bound H b]

lemma output_bound (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (b : List Bool) : (graphBits (reduce H p u q hq b)).length ≤
      (outputPolynomial p u q).eval b.length := by
  apply (graphBits_bound _).trans
  simp only [outputPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_pow]
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
    (Nat.add_le_add_right (vertices_bound H p u q hq b) 1) 2)

lemma complete (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (F : Formula) (hF : F.Satisfiable) : (reduce H p u q hq (formulaBits F)).ThreeColorable := by
  have hgap : (gapInput H (formulaBits F)).val.Satisfiable :=
    TableIteration.gapMap_completeness H _ ((BinaryNormalize.satisfiable_iff F).mpr hF)
  obtain ⟨l,r,hr⟩ := TargetLC.complete u (gapInput H (formulaBits F)) hgap
  exact (GeometryNames.outputRenaming (J u) (I u) p q hq (TargetLC.table u (gapInput H (formulaBits F)))).symm.colorable
    (p.output_complete q hq _ l r hr)

end CompleteReduction

theorem mainTheoremReal_oai :
    ∀ δ : ℝ, 0 < δ → δ < 1 / 3 → Nonempty (RealGraphReduction δ) := by
  intro δ hδ _hδ3
  obtain ⟨H,hH⟩ := PCP.ExpanderTables.exists_base_table
  obtain ⟨p,σ,q,hq,hσ,_hσ1,hp⟩ := finite_graph_reduction hδ
  obtain ⟨u,_hu,hrep⟩ := LCInput.uniform_repetition
    PCP.PCPIteration.finalClauseGap_positive PCP.TableGapReduction.finalClauseGap_le_one hσ
  refine ⟨{
    reduce := CompleteReduction.reduce H p u q hq
    computation := CompleteReduction.certificate H p u q hq
    finiteAlphabets := CompleteReduction.finiteAlphabet H p u q hq
    outputBound := CompleteReduction.outputPolynomial p u q
    outputSize := CompleteReduction.output_bound H p u q hq
    completeness := CompleteReduction.complete H p u q hq
    soundness := ?_ }⟩
  intro F hF
  have hg : Hastad.SourceGap.ClauseGap (CompleteReduction.gapInput H (formulaBits F)).val
      PCP.PCPIteration.finalClauseGap :=
    PCP.TableGapReduction.gapMap_clauseGap H hH _
      (fun h => hF ((BinaryNormalize.satisfiable_iff F).mp h))
  have hs := TargetLC.sound u (CompleteReduction.gapInput H (formulaBits F)) (hrep _ hg)
  have hout := (hp _ _ _ _ _ (TargetLC.table u (CompleteReduction.gapInput H (formulaBits F))).lc).2 hs
  exact (GeometryNames.outputRenaming (Hastad.SourceContexts.J u) (Hastad.SourceContexts.I u) p q hq
    (TargetLC.table u (CompleteReduction.gapInput H (formulaBits F)))).symm.strict_density hout

end
end LargeIndependentSets

end OAI
end

theorem solution : type_of% @OAI.LargeIndependentSets.mainTheoremReal_oai := @OAI.LargeIndependentSets.mainTheoremReal_oai
