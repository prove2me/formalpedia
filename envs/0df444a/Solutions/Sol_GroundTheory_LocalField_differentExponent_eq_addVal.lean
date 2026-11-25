-- Prove2me | solution 1 for GroundTheory.LocalField.differentExponent_eq_addVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:20.830335+00:00
-- url     : https://prove2.me/submissions/7eb68d12-74d6-4e53-9ac7-6028a2c0ee1d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_span_singleton_eq_maximalIdeal_pow
import Theorems.Thm_GroundTheory_LocalField_differentExponent_eq_iff
import Theorems.Thm_GroundTheory_LocalField_differentIdeal_eq_span_aeval_derivative
import Theorems.Thm_GroundTheory_LocalField_aeval_derivative_ne_zero
import Theorems.Thm_GroundTheory_LocalField_exists_addVal_eq_coe


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
namespace GroundTheory.LocalField
theorem _root_.solution {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    (differentExponent K L : ℕ∞) = IsDiscreteValuationRing.addVal 𝒪[L] (aeval x (derivative (minpoly 𝒪[K] x))) := by
  have h0 := aeval_derivative_ne_zero hx
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe h0
  rw [hk, Nat.cast_inj, differentExponent_eq_iff, differentIdeal_eq_span_aeval_derivative hx]
  exact span_singleton_eq_maximalIdeal_pow h0 hk
end GroundTheory.LocalField
