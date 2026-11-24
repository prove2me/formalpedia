-- Prove2me | solution 1 for GlobalTheory.topFormGen_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:45.459333+00:00
-- url     : https://prove2.me/submissions/58a89052-cd8d-4fc5-ab64-244743117952

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_ordTop_vw_zero
import Theorems.Thm_GlobalTheory_fracKaehlerBasis_apply
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
attribute [local simp] GlobalTheory.fracKaehlerBasis_apply

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
variable (F) {K : Type*} [CommRing K] [Algebra K V] [Algebra K F] [IsScalarTower K V F] {n : ℕ}
variable {F} (b : Basis (Fin n) V Ω[V⁄K])
omit [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory
theorem _root_.solution : topFormGen F b = exteriorPower.ιMulti F n (fracKaehlerBasis F b) := by
  rw [topFormGen, formMap_ιMulti]
  congr 1
  funext k
  simp
end GlobalTheory
