-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.iso_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:25:57.768585+00:00
-- url     : https://prove2.me/submissions/5b9724a9-59a7-4ec6-89a4-af427c3f929f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam

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
theorem _root_.solution (S : List (Part A.CG)) (p : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [p]) w = A.lpSum (isoLoc N A S w) (spehLoc N A p w) := by
  induction S with
  | nil => exact A.lpSum_comm _ _
  | cons q S ih =>
    show A.lpSum (spehLoc N A q w) (isoLoc N A (S ++ [p]) w) =
      A.lpSum (A.lpSum (spehLoc N A q w) (isoLoc N A S w)) (spehLoc N A p w)
    rw [ih, A.lpSum_assoc]
end GlobalTheory.ThetaExh.Check
