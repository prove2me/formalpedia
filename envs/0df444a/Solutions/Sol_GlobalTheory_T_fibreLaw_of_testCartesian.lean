-- Prove2me | solution 1 for GlobalTheory.T.fibreLaw_of_testCartesian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:00:27.776316+00:00
-- url     : https://prove2.me/submissions/1c52f7f9-7125-490d-81df-e7301eb5045a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesianStatement
import Theorems.Thm_GlobalTheory_ZJ_Core_fibLaw_of_testCart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ C : Core, C.TestCart → C.FibLaw := by
  first | exact @GlobalTheory.ZJ.Core.fibLaw_of_testCart | exact GlobalTheory.ZJ.Core.fibLaw_of_testCart | (intros; apply GlobalTheory.ZJ.Core.fibLaw_of_testCart <;> assumption)
end _root_.GlobalTheory.T
