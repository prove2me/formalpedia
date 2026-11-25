-- Prove2me | solution 1 for GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_eq_of_hasParamX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:12.207445+00:00
-- url     : https://prove2.me/submissions/871f3bb9-ae2f-48be-b769-01c94702a860

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SplitPlaceGoodSignature
import Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_isoLoc_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.SplitPlaceGoodSignature
open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
variable (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.Proof.SplitPlaceGoodSignature
theorem _root_.solution (hL : ParamLaws N A) {i : N.Loc} (hloc : LocOfPt N A i) {x : N.X i}
    {Sig Sig' : List (Part A.CG)} (h : HasParamX N A i x Sig) (h' : HasParamX N A i x Sig')
    (w : PlE H) (hw : IsSplitPl H w) : isoLoc N A Sig w = isoLoc N A Sig' w := by
  obtain ⟨P, hP, hB⟩ := h
  obtain ⟨P', hP', hB'⟩ := h'
  have e := hloc P P' x hP hP' w hw
  rw [← hB.2.2.2.1 w hw, ← hB'.2.2.2.1 w hw, isoLoc_lift N A hL, isoLoc_lift N A hL] at e
  exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)
end GlobalTheory.Proof.SplitPlaceGoodSignature
