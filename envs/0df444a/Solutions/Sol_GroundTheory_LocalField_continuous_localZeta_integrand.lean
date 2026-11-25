-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_localZeta_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:53.026923+00:00
-- url     : https://prove2.me/submissions/ae7ba08e-b250-4cd7-9a7c-94243866f432

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Theorems.Thm_GroundTheory_LocalField_continuous_modulus
import Theorems.Thm_GroundTheory_LocalField_modulus_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}
omit [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) (s : ℂ) :
    Continuous fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s := by
  refine ((hf.1.continuous.comp Units.continuous_val).mul (Units.continuous_val.comp hχ)).mul ?_
  refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)
end GroundTheory.LocalField
