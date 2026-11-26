-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_levy_intensity_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:40:28.512935+00:00
-- url     : https://prove2.me/submissions/707eeb7a-5678-47eb-b4e6-60093f3f14ba

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_square_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_frequency_limit
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution (tr : ProbabilityTheory.LevyKhintchineTriple) :
    Tendsto (fun m : ℕ => ∫ z, (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2 ∂tr.levyMeasure)
      atTop (nhds 0) := by
  let q : ℕ → ℝ → ℝ := fun m z =>
    (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
  have hdom : Integrable (fun z : ℝ => 2*min 1 (z^2)) tr.levyMeasure :=
    by
      have h : Integrable (fun x : ℝ => min 1 (x^2)) tr.levyMeasure := by
        refine ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        simp_rw [Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg _))]
        exact tr.levyMeasure_isLevyMeasure.2
      exact h.const_mul 2
  have hm (m : ℕ) : AEStronglyMeasurable (q m) tr.levyMeasure :=
    (show Continuous (q m) by dsimp [q]; fun_prop).aestronglyMeasurable
  have hb (m : ℕ) : ∀ᵐ z ∂tr.levyMeasure, ‖q m z‖ ≤ 2*min 1 (z^2) := by
    filter_upwards [] with z
    have h := Kyprianou.Ch04.ito43_cosine_deficit_square_bound ((m:ℝ)+1) z (by positivity)
    rw [Real.norm_of_nonneg h.1]
    rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    apply le_min
    · exact h.2.2.trans (by
        have hh : (1:ℝ) ≤ ((m:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
        exact (div_le_iff₀ (by positivity)).mpr (by linarith))
    · linarith [h.2.1,sq_nonneg z]
  have hl : ∀ᵐ z ∂tr.levyMeasure, Tendsto (fun m => q m z) atTop (nhds (0:ℝ)) :=
    Eventually.of_forall Kyprianou.Ch04.ito43_cosine_deficit_frequency_limit
  simpa using MeasureTheory.tendsto_integral_of_dominated_convergence _ hm hdom hb hl
