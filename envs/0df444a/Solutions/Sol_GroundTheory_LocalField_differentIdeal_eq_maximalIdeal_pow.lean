-- Prove2me | solution 1 for GroundTheory.LocalField.differentIdeal_eq_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:44.260021+00:00
-- url     : https://prove2.me/submissions/5cfeda4d-fb6b-4e53-9263-f25c287a4d2a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_prime_maximalIdeal

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
theorem _root_.solution :
    differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ differentExponent K L := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal 𝒪[L]
    (IsPrincipalIdealRing.principal _) _ (differentIdeal_ne_bot (A := 𝒪[K]) (B := 𝒪[L]))
  rw [differentExponent, hn, multiplicity_pow_self_of_prime prime_maximalIdeal]
end GroundTheory.LocalField
