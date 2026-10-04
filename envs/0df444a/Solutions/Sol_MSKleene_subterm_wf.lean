-- Prove2me | solution 1 for MSKleene.subterm_wf
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T13:00:32.247276+00:00
-- url     : https://prove2.me/submissions/bd585073-efb3-4c80-8bba-d203458df34d

import Definitions.Def_MSKleene_Subterm

open MSKleene

private theorem term_acc {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {s : S} (t : Term sig X s),
      Acc (ImmSub (sig := sig) (X := X)) ⟨s, t⟩ :=
  @Term.rec _ _ _
    (motive_1 := fun s t => Acc (ImmSub (sig := sig) (X := X)) ⟨s, t⟩)
    (motive_2 := fun _ ts => ∀ {s : S} (t : Term sig X s),
      TermVec.Mem t ts → Acc (ImmSub (sig := sig) (X := X)) ⟨s, t⟩)
    (fun x => Acc.intro _ (by
      intro a ha
      rcases ha with ⟨w, σ, ts, heq, _⟩
      cases heq))
    (fun σ ts ih => Acc.intro _ (by
      intro a ha
      rcases ha with ⟨w, τ, us, heq, hmem⟩
      cases heq
      exact ih a.2 hmem))
    (by intro s t h; cases h)
    (fun t ts iht ihs _ p hp => by
      cases hp with
      | head => exact iht
      | tail _ hmem => exact ihs p hmem)

/-- The proper-subterm relation is well-founded, and its minimal terms are
precisely variables and nullary applications. -/
theorem solution {S : Type} (sig : Signature S) (X : SSet S) :
    WellFounded (SubtermLT (sig := sig) (X := X))
  ∧ ∀ b : STerm sig X, Min b ↔
      ((∃ x : X b.1, b.2 = Term.var x)
       ∨ (∃ σ : sig [] b.1, b.2 = Term.app σ TermVec.nil)) := by
  constructor
  · have himm : WellFounded (ImmSub (sig := sig) (X := X)) :=
      ⟨fun b => term_acc b.2⟩
    exact himm.transGen
  · rintro ⟨s, t⟩
    cases t with
    | var x =>
        constructor
        · intro _
          exact Or.inl ⟨x, rfl⟩
        · intro _ a ha
          rcases ha with ⟨w, σ, ts, heq, _⟩
          cases heq
    | app σ ts =>
        cases ts with
        | nil =>
            constructor
            · intro _
              exact Or.inr ⟨σ, rfl⟩
            · intro _ a ha
              rcases ha with ⟨w, τ, us, heq, hmem⟩
              cases heq
              cases hmem
        | @cons s' w' t ts =>
            constructor
            · intro hmin
              exact (hmin ⟨s', t⟩ ⟨s' :: w', σ, .cons t ts, rfl,
                TermVec.Mem.head t ts⟩).elim
            · intro hshape
              rcases hshape with ⟨x, heq⟩ | ⟨τ, heq⟩
              · cases heq
              · cases heq

