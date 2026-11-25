-- Prove2me | solution 1 for GroundTheory.LocalField.differentExponent_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:25.893902+00:00
-- url     : https://prove2.me/submissions/bc2bcf43-290d-4f3e-a683-66446a1da290

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_maximalIdeal_pow_injective
import Theorems.Thm_GroundTheory_LocalField_differentIdeal_eq_maximalIdeal_pow

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
variable [Algebra.IsSeparable K L]
namespace GroundTheory.LocalField
theorem _root_.solution {d : ℕ} :
    differentExponent K L = d ↔ differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ d := by
  rw [differentIdeal_eq_maximalIdeal_pow]
  exact ⟨fun h ↦ by rw [h], fun h ↦ maximalIdeal_pow_injective h⟩
end GroundTheory.LocalField
