-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.splitLift_of_liftParam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:39.791512+00:00
-- url     : https://prove2.me/submissions/a9683e7c-9ae4-4bda-9110-60aeb41eaa66

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Theorems.Thm_GlobalTheory_ThetaExh_Check_iso_char
import Theorems.Thm_GlobalTheory_ThetaExh_Check_iso_append

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaExh GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.ThetaExh.Check
theorem _root_.solution (hL : ParamLaws N A) (i : N.Loc) (h : LiftParam N A i) :
    SplitLift N A i := by
  intro σ P hθ w hw
  obtain ⟨Sig, hSig, hBC⟩ := h σ P hθ
  show A.locV i P w =
    A.lpChar (A.lpSum (A.locW i σ w) (spehLoc N A (muPart N A i) w)) (A.locG A.etaTinv w)
  rw [← hBC.2.2.2.1 w hw, iso_char N A hL _ _ w, iso_append N A, hSig.2.2 w hw]
end GlobalTheory.ThetaExh.Check
