-- Prove2me | solution 1 for Kyprianou.Ch04.lipschitzMartingaleZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:41:08.8397+00:00
-- url     : https://prove2.me/submissions/737e53d4-8a47-4522-b6e0-4c9df947142f

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_lipschitzMartingaleSquareGridBound
open MeasureTheory Filter Set Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A uniformly Lipschitz martingale starting at zero is zero at every deterministic time. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → ℝ) (hM : Martingale M F P)
    (h0 : ∀ᵐ w ∂P, M 0 w = 0) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ s t : NNReal, s ≤ t → ∀ᵐ w ∂P,
      |M t w - M s w| ≤ C * ((t : ℝ) - (s : ℝ))) :
    ∀ t : NNReal, M t =ᵐ[P] 0 := by
  intro t
  have hB (n : ℕ) := lipschitzMartingaleSquareGridBound P F M hM h0 C hC hL t
    (n+1) (Nat.succ_pos n)
  have hlim : Tendsto (fun n : ℕ => (C*(t:ℝ))^2 / ((n:ℝ)+1)) atTop (nhds 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((C*(t:ℝ))^2)
  have hle : (∫ w, (M t w)^2 ∂P) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (Eventually.of_forall fun n => by simpa only [Nat.cast_add,Nat.cast_one] using hB n)
  have hbound : ∀ᵐ w ∂P, ‖M t w‖ ≤ C*(t:ℝ) := by
    filter_upwards [h0,hL 0 t (zero_le : 0 ≤ t)] with w hw h
    simpa only [Real.norm_eq_abs,hw,sub_zero,NNReal.coe_zero] using h
  have hm : MemLp (M t) 2 P :=
    MemLp.of_bound (hM.integrable t).aestronglyMeasurable _ hbound
  have hi := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
  have hz := (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg (M t w)) hi).mp
    (le_antisymm hle (integral_nonneg fun w => sq_nonneg (M t w)))
  filter_upwards [hz] with w hw
  change (M t w)^2 = 0 at hw
  change M t w = 0
  nlinarith [sq_nonneg (M t w)]
