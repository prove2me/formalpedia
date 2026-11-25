-- Prove2me | solution 1 for GlobalTheory.FunObj.invVol_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:23.101468+00:00
-- url     : https://prove2.me/submissions/1284ce40-3993-4df7-8a7f-a135711e0c06

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
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)
variable {k n c}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.FunObj
theorem _root_.solution : invVol (KO k (n ⊕ Fin c)) = 1 := by
  simp [invVol, Subgroup.relIndex_eq_one.2 inf_le_right]
end GlobalTheory.FunObj
