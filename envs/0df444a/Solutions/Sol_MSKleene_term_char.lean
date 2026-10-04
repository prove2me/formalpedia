-- Prove2me | solution 1 for MSKleene.term_char
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T12:48:04.539539+00:00
-- url     : https://prove2.me/submissions/5598af95-40f1-47df-8045-05e114dfa98d

import Definitions.Def_MSKleene_Term

private def termCode {S : Type} {sig : MSKleene.Signature S}
    {X : MSKleene.SSet S} {s : S} (P : MSKleene.Term sig X s) :
    X s ⊕ (sig [] s ⊕ ((w : List S) × sig w s × MSKleene.TermVec sig X w)) :=
  match P with
  | .var x => .inl x
  | .app (w := []) σ .nil => .inr (.inl σ)
  | .app (w := _ :: _) σ (.cons t ts) => .inr (.inr ⟨_, σ, .cons t ts⟩)

/-- Every many-sorted term has a unique tagged outermost decomposition. -/
theorem solution {S : Type} (sig : MSKleene.Signature S) (X : MSKleene.SSet S)
    {s : S} (P : MSKleene.Term sig X s) :
    ∃! c : X s ⊕ (sig [] s ⊕ ((w : List S) × sig w s × MSKleene.TermVec sig X w)),
      match c with
      | .inl x => P = MSKleene.Term.var x
      | .inr (.inl σ) => P = MSKleene.Term.app σ MSKleene.TermVec.nil
      | .inr (.inr p) => p.1 ≠ [] ∧ P = MSKleene.Term.app p.2.1 p.2.2 := by
  refine ⟨termCode P, ?_, ?_⟩
  · cases P with
    | var x => rfl
    | app σ ts =>
      cases ts with
      | nil => rfl
      | cons t ts => exact ⟨List.cons_ne_nil _ _, rfl⟩
  · intro c hc
    cases c with
    | inl x =>
      simpa [termCode] using congrArg termCode hc.symm
    | inr c =>
      cases c with
      | inl σ =>
        simpa [termCode] using congrArg termCode hc.symm
      | inr p =>
        rcases p with ⟨w, σ, ts⟩
        rcases hc with ⟨hw, hP⟩
        cases ts with
        | nil => exact (hw rfl).elim
        | cons t ts =>
          simpa [termCode] using congrArg termCode hP.symm
