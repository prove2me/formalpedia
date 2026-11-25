-- Prove2me | solution 1 for GroundTheory.LocalField.maximalIdeal_pow_dvd_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:26.750077+00:00
-- url     : https://prove2.me/submissions/e1910819-5139-4a76-8f03-38aaf17068bc

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
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GroundTheory.LocalField
theorem _root_.solution {m n : ℕ} :
    IsLocalRing.maximalIdeal R ^ m ∣ IsLocalRing.maximalIdeal R ^ n ↔ m ≤ n :=
  pow_dvd_pow_iff (prime_maximalIdeal (R := R)).ne_zero (prime_maximalIdeal (R := R)).not_isUnit
end GroundTheory.LocalField
