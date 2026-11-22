-- Prove2me | solution 1 for IterationSequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:14:46.908798+00:00
-- url     : https://prove2.me/submissions/8b30020c-7d65-4b71-8e68-f9bc06d83979

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_IterationSequence

set_option autoImplicit false

theorem _root_.solution (Good Cont : ℝ → Prop) (θ : ℝ)
    (hGood1 : Good 1)
    (hstep : ∀ R : ℝ, Good R → Cont R → ∃ R' : ℝ, Good R' ∧ θ * R ≤ R' ∧ R' ≤ R / 4) :
    ∃ R : ℕ → ℝ, R 0 = 1 ∧ (∀ l : ℕ, Good (R l)) ∧
      ∀ l : ℕ, Cont (R l) → (θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) := by
  have hstep' : ∀ R : ℝ, ∃ R' : ℝ,
      (Good R → Cont R → (Good R' ∧ θ * R ≤ R' ∧ R' ≤ R / 4))
        ∧ (¬ (Good R ∧ Cont R) → R' = R) := by
    intro R
    by_cases hGC : Good R ∧ Cont R
    · obtain ⟨R', hR'⟩ := hstep R hGC.1 hGC.2
      exact ⟨R', fun _ _ => hR', fun h => absurd hGC h⟩
    · exact ⟨R, fun hG hC => absurd ⟨hG, hC⟩ hGC, fun _ => rfl⟩
  choose f hf1 hf2 using hstep'
  set seq : ℕ → ℝ := fun l => Nat.rec (1 : ℝ) (fun _ r => f r) l with hseq
  have hsucc : ∀ l : ℕ, seq (l + 1) = f (seq l) := fun l => rfl
  have hGoodAll : ∀ l, Good (seq l) := by
    intro l
    induction l with
    | zero => exact hGood1
    | succ n ih =>
      rw [hsucc]
      by_cases hC : Cont (seq n)
      · exact (hf1 _ ih hC).1
      · rw [hf2 _ (fun h => hC h.2)]; exact ih
  refine ⟨seq, rfl, hGoodAll, ?_⟩
  intro l hC
  rw [hsucc]
  exact ⟨(hf1 _ (hGoodAll l) hC).2.1, (hf1 _ (hGoodAll l) hC).2.2⟩
