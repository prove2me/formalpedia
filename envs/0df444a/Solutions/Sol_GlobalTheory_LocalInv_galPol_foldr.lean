-- Prove2me | solution 1 for GlobalTheory.LocalInv.galPol_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:12.748456+00:00
-- url     : https://prove2.me/submissions/1feb7f6a-a92f-4b16-b8e6-f30bac84ff57

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_galPol_tw_sum
import Theorems.Thm_GlobalTheory_LocalInv_galPol_tw_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution {w : PlE H} (a : A.LP w) (ha : A.unr a) (e : ℝ → ℝ) (s : ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) ∧
    galPol A (A.lpTw (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) s) =
      (L.map fun k => galPol A (A.lpTw a (e k + s))).prod := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, by simpa using galPol_tw_zero N A w s⟩
  | cons k L ih =>
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 ha, ih.1⟩, ?_⟩
    rw [List.foldr_cons, galPol_tw_sum N A _ _ ((A.unr_tw _ _).2 ha) ih.1, ih.2, A.lpTw_add,
      List.map_cons, List.prod_cons]
end GlobalTheory.LocalInv
