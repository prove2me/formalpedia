-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Grid.kappa_outer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:18.588282+00:00
-- url     : https://prove2.me/submissions/452d55c6-b155-44b4-8385-5eb591fc83e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open GlobalTheory.SplitFlip.Grid
variable (G : Grid k)
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip.Grid
theorem _root_.solution (i j : ℕ) :
    G.kappa (.theta (i + 1) j) (i + 1, j + 1) / G.kappa (.ex i (j + 1)) (i + 1, j + 1) = G.nu i j := by
  simp [kappa, blockChar, nu]
end GlobalTheory.SplitFlip.Grid
