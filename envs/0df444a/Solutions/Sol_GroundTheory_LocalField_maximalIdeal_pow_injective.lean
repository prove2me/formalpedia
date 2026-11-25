-- Prove2me | solution 1 for GroundTheory.LocalField.maximalIdeal_pow_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:58:02.571042+00:00
-- url     : https://prove2.me/submissions/45cc3413-5c1b-4660-860e-c58701a17048

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_maximalIdeal_pow_dvd_pow_iff

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
theorem _root_.solution :
    Function.Injective (fun n : ℕ ↦ IsLocalRing.maximalIdeal R ^ n) := by
  intro m n h
  exact le_antisymm (maximalIdeal_pow_dvd_pow_iff.mp (dvd_of_eq h))
    (maximalIdeal_pow_dvd_pow_iff.mp (dvd_of_eq h.symm))
end GroundTheory.LocalField
