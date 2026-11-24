-- Prove2me | solution 1 for GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:15:34.461806+00:00
-- url     : https://prove2.me/submissions/356f7fa7-2cf5-4b09-b7b7-a396e805935b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SplitPlaceGoodSignature
import Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_typePlSplit

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
theorem _root_.solution {i : N.Loc} {σ : what₂.FT} {Sig : List (Part A.CG)}
    (h : ∀ w, IsSplitPl H w → isoLoc N A Sig w = A.locW i σ w) :
    N.goodRow σ ↔ goodSig N A Sig := by
  have hl : ∀ k, (fun v => A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))) = N.lab k σ := by
    intro k
    funext v
    rw [h _ (typePlSplit N A k v), A.lab_loc i k σ v]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [hl k]
end GlobalTheory.Proof.SplitPlaceGoodSignature
