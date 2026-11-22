-- Prove2me | solution 1 for NemytskiiLebesgue.norm_integral_le_eLpNorm_one_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:37.868564+00:00
-- url     : https://prove2.me/submissions/d6d4b3b2-a1ac-41a3-94f2-f4f2a6421c98

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : Ω → ℝ) :
    ‖∫ ω : Ω, g ω ∂μ‖ ≤ (eLpNorm g 1 μ).toReal := by
  by_cases hg : AEStronglyMeasurable g μ
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal _ _] <;> norm_num
    convert! norm_integral_le_lintegral_norm g using 1
    norm_num [Real.enorm_eq_ofReal_abs]
  · rw [integral_non_aestronglyMeasurable hg, norm_zero]
    exact ENNReal.toReal_nonneg
end NemytskiiLebesgue
