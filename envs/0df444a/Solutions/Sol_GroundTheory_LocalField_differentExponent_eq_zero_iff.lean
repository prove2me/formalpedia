-- Prove2me | solution 1 for GroundTheory.LocalField.differentExponent_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:00:07.817013+00:00
-- url     : https://prove2.me/submissions/aefe7abe-cbd1-46ed-9abe-0377045bca8e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_differentIdeal_eq_maximalIdeal_pow
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_sub_one_le_differentExponent
import Theorems.Thm_GroundTheory_LocalField_isUnramified_iff
import Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos


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
open ValuativeRel Polynomial
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance high] FaithfulSMul.to_isTorsionFree
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]
variable {K L}
variable [Algebra.IsSeparable K L]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : differentExponent K L = 0 ↔ IsUnramified K L := by
  rw [isUnramified_iff]
  constructor
  · intro h
    have h1 := ramificationIndex_sub_one_le_differentExponent K L
    have h2 := ramificationIndex_pos K L
    omega
  · intro he
    have hmap : 𝓂[L] * 1 = (𝓂[K]).map (algebraMap 𝒪[K] 𝒪[L]) := by
      rw [map_maximalIdeal, he, pow_one, mul_one]
    have hnd := not_dvd_differentIdeal_of_isCoprime 𝒪[K] (p := 𝓂[K])
      (𝓂[L]) 1 isCoprime_one_right hmap
    rw [differentIdeal_eq_maximalIdeal_pow] at hnd
    by_contra hd
    exact hnd (dvd_pow_self _ hd)
end GroundTheory.LocalField
