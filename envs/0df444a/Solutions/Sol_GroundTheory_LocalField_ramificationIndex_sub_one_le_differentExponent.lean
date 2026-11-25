-- Prove2me | solution 1 for GroundTheory.LocalField.ramificationIndex_sub_one_le_differentExponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:59:58.246589+00:00
-- url     : https://prove2.me/submissions/d4f89a92-7484-4f77-b615-227b7c2a7110

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_maximalIdeal_pow_dvd_pow_iff
import Theorems.Thm_GroundTheory_LocalField_differentIdeal_eq_maximalIdeal_pow
import Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal
import Theorems.Thm_GroundTheory_LocalField_maximalIdeal_ne_bot


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
theorem _root_.solution :
    ramificationIndex K L - 1 ≤ differentExponent K L := by
  have h := pow_sub_one_dvd_differentIdeal 𝒪[K] (p := 𝓂[K]) (𝓂[L])
    (ramificationIndex K L) (maximalIdeal_ne_bot K) (by rw [map_maximalIdeal])
  rwa [differentIdeal_eq_maximalIdeal_pow, maximalIdeal_pow_dvd_pow_iff] at h
end GroundTheory.LocalField
