-- Prove2me | solution 1 for LindelofHypothesis.lindelof_iff_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T02:36:58.30448+00:00
-- url     : https://prove2.me/submissions/9c7cfed6-b2d6-42ab-828d-89f3b40c26d9

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

set_option autoImplicit false
open Complex Filter Asymptotics
open scoped ENNReal

namespace LindelofHypothesis.LHB

/-- For `0 < δ`, `t ^ δ → ∞`, so `1 = o(t ^ δ)`. -/
theorem one_isLittleO_rpow {δ : ℝ} (hδ : 0 < δ) :
    (fun _ : ℝ => (1 : ℝ)) =o[atTop] (fun t : ℝ => t ^ δ) := by
  rw [isLittleO_one_left_iff]
  refine (tendsto_rpow_atTop hδ).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht δ)]

/-- For `0 < ε`, `t ^ (ε / 2) = o(t ^ ε)` as `t → ∞`. -/
theorem rpow_half_isLittleO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ => t ^ (ε / 2)) =o[atTop] (fun t : ℝ => t ^ ε) := by
  have h1 : (fun t : ℝ => t ^ (ε / 2) * 1) =o[atTop] (fun t : ℝ => t ^ (ε / 2) * t ^ (ε / 2)) :=
    (isBigO_refl (fun t : ℝ => t ^ (ε / 2)) atTop).mul_isLittleO (one_isLittleO_rpow (by linarith))
  refine h1.congr' (Eventually.of_forall fun t => mul_one _) ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [← Real.rpow_add' ht (by linarith), add_halves]

end LindelofHypothesis.LHB

open LindelofHypothesis in
theorem solution :
    RiemannVonMangoldt.LindelofHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        (fun t : ℝ => riemannZeta (1 / 2 + t * I)) =o[atTop] (fun t : ℝ => t ^ ε) := by
  constructor
  · intro h ε hε
    exact (h (ε / 2) (by linarith)).trans_isLittleO (LHB.rpow_half_isLittleO_rpow hε)
  · intro h ε hε
    exact (h ε hε).isBigO
