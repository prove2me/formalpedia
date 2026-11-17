-- Prove2me | solution 1 for Height.exists_logHeight_le_restrict_add_of_bezout
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:21:58.400297+00:00
-- url     : https://prove2.me/submissions/adc553f8-055f-49e5-8ba0-abb73c536661

import Mathlib

set_option autoImplicit false
noncomputable section

namespace Height

theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι ι' : Type}
    [Finite ι] [Fintype ι'] [Nonempty ι'] (inc : ι' → ι) {D : ℕ}
    (q : ι × ι' → MvPolynomial ι K) (hq : ∀ a, (q a).IsHomogeneous D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ι → K,
      (∀ k, ∑ j, (q (k, j)).eval z * z (inc j) = z k ^ (D + 1)) →
      Height.logHeight z ≤ Height.logHeight (z ∘ inc) + C  := by
  obtain ⟨C, hC⟩ := Height.logHeight_eval_ge' (N := 1) hq
  refine ⟨max 0 (-C), le_max_left _ _, ?_⟩
  intro z hz
  have hz' : ∀ k, ∑ j, (q (k, j)).eval z *
      (MvPolynomial.X (inc j) : MvPolynomial ι K).eval z = z k ^ (D + 1) := by
    simpa only [MvPolynomial.eval_X] using hz
  have h := hC (fun j => MvPolynomial.X (inc j)) hz'
  simp only [Nat.cast_one, one_mul, MvPolynomial.eval_X] at h
  change C + Height.logHeight z ≤ Height.logHeight (z ∘ inc) at h
  have hm := le_max_right (0 : ℝ) (-C)
  linarith

end Height
