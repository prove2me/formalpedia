-- Prove2me | solution 1 for Kyprianou.Ch04.tsumJumpHorizonRestrictV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:42:08.535117+00:00
-- url     : https://prove2.me/submissions/7ef11f7b-8b8c-4af2-8380-6412edb3830d

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- Restrict a compact jump sum to a smaller horizon by an indicator. -/
theorem solution (j : ℝ≥0 → ℝ) (t T : ℝ≥0) (ht : t ≤ T) :
    (∑' s : Ioc (0 : ℝ≥0) t, j s) =
      ∑' s : Ioc (0 : ℝ≥0) T,
        ((fun z : Ioc (0 : ℝ≥0) T => ((z : ℝ≥0) : ℝ)) ⁻¹' Iic (t : ℝ)).indicator
          (fun z => j z) s := by
  let S : Set (Ioc (0 : ℝ≥0) T) := (fun z => ((z : ℝ≥0) : ℝ)) ⁻¹' Iic (t : ℝ)
  let e : Ioc (0 : ℝ≥0) t ≃ S :=
    { toFun := fun z => ⟨⟨z, z.property.1, z.property.2.trans ht⟩, by
        change ((z : ℝ≥0) : ℝ) ≤ (t : ℝ)
        exact_mod_cast z.property.2⟩
      invFun := fun z => ⟨z.val, z.val.property.1, by
        have hz : ((z.val : ℝ≥0) : ℝ) ≤ (t : ℝ) := z.property
        exact_mod_cast hz⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }
  change (∑' s : Ioc (0 : ℝ≥0) t, j s) = ∑' s, S.indicator (fun z => j z) s
  rw [← tsum_subtype S]
  exact e.tsum_eq (fun z : S => j z.val)
