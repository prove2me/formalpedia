-- Prove2me | solution 1 for GlobalTheory.FunObj.fill_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:30.171837+00:00
-- url     : https://prove2.me/submissions/5e1d11e3-3433-4a24-b3bd-a71bc5a0c4e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
namespace GlobalTheory.FunObj
theorem _root_.solution (x : ColArgs G) (y : RowArgs G) (e : Vars G) (j : ℕ) :
    fill hs x y e (.theta G.m j) = (downMap hs x e j)ᵀ := dif_pos rfl
end GlobalTheory.FunObj
