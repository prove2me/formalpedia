-- Prove2me | solution 1 for GlobalTheory.Hk.RayCont.LSeries_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:07:00.897157+00:00
-- url     : https://prove2.me/submissions/9d5af105-0f16-4a3c-a03a-1d6700272449

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Theorems.Thm_GlobalTheory_Hk_RayCont_integrableOn_integrand
import Theorems.Thm_GlobalTheory_Hk_RayCont_norm_rem_le
import Theorems.Thm_GlobalTheory_Hk_RayCont_measurable_rem
import Theorems.Thm_GlobalTheory_Hk_RayCont_sum_norm_isBigO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.RayCont
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    LSeries (𝓕.aChi χ) s = s * (𝓕.mel χ s + 𝓕.res χ / (s - 1)) := by
  rw [LSeries_eq_mul_integral' _ zero_le_one hs (sum_norm_isBigO 𝓕 χ)]
  congr 1
  have hlt : (-s).re < -1 := by simpa using hs
  have h1 : ∫ t in Set.Ioi (1 : ℝ), 𝓕.res χ * (t : ℂ) ^ (-s) = 𝓕.res χ / (s - 1) := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hlt zero_lt_one]
    have : -s + 1 = -(s - 1) := by ring
    rw [ofReal_one, one_cpow, this, neg_div_neg_eq, mul_one_div]
  rw [← h1, LFam.mel, ← integral_add
    (integrableOn_integrand (measurable_rem 𝓕 χ) (norm_rem_le 𝓕 χ) (by linarith))
    ((integrableOn_Ioi_cpow_of_lt hlt zero_lt_one).const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (zero_lt_one.trans ht).ne'
  have h2 : (t : ℂ) ^ (-s) = t * (t : ℂ) ^ (-s - 1) := by
    rw [cpow_sub _ _ ht0, cpow_one]
    field_simp
  have h3 : -(s + 1) = -s - 1 := by ring
  rw [h2, h3]
  ring
end GlobalTheory.Hk.RayCont
