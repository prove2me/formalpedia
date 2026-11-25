-- Prove2me | solution 1 for GlobalTheory.TorusAlg.thetaChar_ofRealVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:28:12.074129+00:00
-- url     : https://prove2.me/submissions/a9262b49-6478-446b-a8f3-1bbc4dbb265d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusAlg
open ReciprocityTheory.PTheta
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
namespace GlobalTheory.TorusAlg
theorem _root_.solution (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) :
    thetaChar τ (ofRealVec a) (ofRealVec b) = fun z => theta a b z τ := by
  funext z
  unfold thetaChar theta thetaTerm eC
  refine tsum_congr fun n => ?_
  have e1 : ((fun i => (n i : ℂ)) + ofRealVec a) = shiftVec a n := rfl
  rw [e1]
  congr 1
  ring
end GlobalTheory.TorusAlg
