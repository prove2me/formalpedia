-- Prove2me | solution 1 for GlobalTheory.TorusAlg.thetaChar_eq_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:34.326547+00:00
-- url     : https://prove2.me/submissions/7722edc9-488c-4df0-abc9-8f3d30707a0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Theorems.Thm_GlobalTheory_TorusAlg_ofRealVec_re
import Theorems.Thm_GlobalTheory_TorusAlg_thetaChar_ofRealVec

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
theorem _root_.solution (τ : Matrix (Fin g) (Fin g) ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) :
    thetaChar τ a b = fun z => theta (fun i => (a i).re) (fun i => (b i).re) z τ := by
  rw [← thetaChar_ofRealVec, ofRealVec_re ha, ofRealVec_re hb]
end GlobalTheory.TorusAlg
