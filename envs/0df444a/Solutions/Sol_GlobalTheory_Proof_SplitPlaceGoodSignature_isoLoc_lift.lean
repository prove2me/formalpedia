-- Prove2me | solution 1 for GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:13.427672+00:00
-- url     : https://prove2.me/submissions/a138d5ac-b713-48a6-bb11-b3823b03dad1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SplitPlaceGoodSignature
import Theorems.Thm_GlobalTheory_ThetaExh_Check_iso_append
import Theorems.Thm_GlobalTheory_ThetaExh_Check_iso_char


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
theorem _root_.solution (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [Check.iso_char N A hL, Check.iso_append]
  rfl
end GlobalTheory.Proof.SplitPlaceGoodSignature
