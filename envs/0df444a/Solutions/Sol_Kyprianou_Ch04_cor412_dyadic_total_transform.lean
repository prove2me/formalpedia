-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_dyadic_total_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:26:57.009429+00:00
-- url     : https://prove2.me/submissions/99d51da0-fed9-496d-b80e-004d908a3132

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_reward_eq
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_bounded
import Theorems.Thm_Kyprianou_Ch04_cor412_alltime_measurable
import Theorems.Thm_Kyprianou_Ch04_cor412_extended_perpetual_transform
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The measurable dyadic reward has the perpetual negative infimum transform. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hm : 0 < derivWithin L.ψ (Ici 0) 0)
    (β : ℝ) (hβ : 0 < β) :
    (∫⁻ w, ⨅ q : ℕ × ℕ, ENNReal.ofReal
      (Real.exp (β * L.X ((q.1 : NNReal) / 2 ^ q.2) w)) ∂P) =
      ENNReal.ofReal (derivWithin L.ψ (Ici 0) 0 * β / L.ψ β) := by
  classical
  let : IsProbabilityMeasure P := L.isProbability
  let B : Set Ω := {w | BddBelow (range (fun t : NNReal => L.X t w))}
  let D : Ω → ℝ := B.indicator (fun w => -sInf (range (fun t => L.X t w)))
  obtain ⟨_,hb⟩ := Kyprianou.Ch04.cor412_lower_bounded P F L hm
  obtain ⟨hD,hD0⟩ := Kyprianou.Ch04.cor412_alltime_measurable P F L
  have hme : Measurable (fun w => Real.exp (β * (-D w))) :=
    (measurable_const.mul hD.neg).exp
  have hi : Integrable (fun w => Real.exp (β * (-D w))) P := by
    apply (integrable_const (1 : ℝ)).mono hme.aestronglyMeasurable
    exact Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_one]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hβ.le (neg_nonpos.mpr (hD0 w)))
  calc
    _ = ∫⁻ w, ENNReal.ofReal (Real.exp (β * (-D w))) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hb] with w hw
      have hwB : w ∈ B := hw
      rw [Kyprianou.Ch04.cor412_dyadic_reward_eq (fun t => L.X t w) (L.rightCont w) hw β hβ.le]
      simp [D,hwB]
    _ = ENNReal.ofReal (∫ w, Real.exp (β * (-D w)) ∂P) := by
      exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun w => (Real.exp_pos _).le)).symm
    _ = _ := congrArg ENNReal.ofReal (Kyprianou.Ch04.cor412_extended_perpetual_transform P F L hm β hβ)
