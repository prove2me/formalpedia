-- Prove2me | solution 1 for GroundTheory.LocalField.minpoly_eq_of_isEisensteinAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:47:29.236215+00:00
-- url     : https://prove2.me/submissions/adc5923a-1913-476a-9be6-93371082bc3f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_irreducible_map_of_isEisensteinAt

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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Field L] [Algebra K L]
namespace GroundTheory.LocalField
theorem _root_.solution {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) {α : L}
    (hα : aeval α f = 0) :
    minpoly K α = C (algebraMap 𝒪[K] K f.leadingCoeff)⁻¹ * f.map (algebraMap 𝒪[K] K) := by
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := IsFractionRing.injective 𝒪[K] K
  have hc : algebraMap 𝒪[K] K f.leadingCoeff ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]
    rintro h
    exact hf.leading (by rw [h]; exact zero_mem _)
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · rw [irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hc)))]
    exact irreducible_map_of_isEisensteinAt hf hn
  · rw [map_mul, aeval_map_algebraMap, hα, mul_zero]
  · refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [leadingCoeff_map_of_injective hinj, inv_mul_cancel₀ hc]
end GroundTheory.LocalField
