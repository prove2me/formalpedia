-- Prove2me | solution 1 for GroundTheory.LocalField.differentIdeal_eq_span_aeval_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:43.330725+00:00
-- url     : https://prove2.me/submissions/04877080-5a26-49de-9df5-5088b912ac62

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_adjoin_eq_top_of_integer_adjoin_eq_top

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
    differentIdeal 𝒪[K] 𝒪[L] = Ideal.span {aeval x (derivative (minpoly 𝒪[K] x))} := by
  rw [← conductor_mul_differentIdeal 𝒪[K] K L x (adjoin_eq_top_of_integer_adjoin_eq_top hx),
    conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul]
end GroundTheory.LocalField
