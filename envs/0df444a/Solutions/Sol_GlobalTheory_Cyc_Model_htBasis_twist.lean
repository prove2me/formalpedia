-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.htBasis_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:08.188536+00:00
-- url     : https://prove2.me/submissions/f814cc46-3cbe-4878-8692-5e85a17b5373

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
theorem _root_.solution (G : Subgroup (GQ l)) : HTBasis actC chi G (Utw (l := l)) {-1} := by
  refine ⟨fun _ _ => 1, fun _ => -1, ?_, fun _ => rfl, fun σ _ k => ?_⟩
  · rw [linearIndependent_unique_iff]
    intro h; exact one_ne_zero (congrFun h 0)
  · ext a
    simp [twAct, Utw, chiC, Matrix.mulVec, dotProduct]
end GlobalTheory.Cyc.Model
