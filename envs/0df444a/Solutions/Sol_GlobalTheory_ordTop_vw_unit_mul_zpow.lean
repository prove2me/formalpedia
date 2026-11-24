-- Prove2me | solution 1 for GlobalTheory.ordTop_vw_unit_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:47.517829+00:00
-- url     : https://prove2.me/submissions/05ee5d7a-03bb-47be-808b-b9b7fe7ef260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_ordTop_vw_zero
import Theorems.Thm_GlobalTheory_ordTop_vw_of_ne_zero
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti
attribute [local simp] GlobalTheory.dlogWedge_empty
attribute [local simp] GlobalTheory.ordTop_vw_zero

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
namespace GlobalTheory
theorem _root_.solution {t : V} (ht : Irreducible t) (u : Vˣ) (m : ℤ) :
    ordTop_vw V (algebraMap V F u * algebraMap V F t ^ m) = m := by
  have h₀ : algebraMap V F t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V F)).mpr ht.ne_zero
  rw [ordTop_vw_of_ne_zero V
      (mul_ne_zero (u.isUnit.map (algebraMap V F)).ne_zero (zpow_ne_zero m h₀)),
    map_mul, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible ht, one_mul,
    WithZero.log_zpow, WithZero.log_exp]
  simp
end GlobalTheory
