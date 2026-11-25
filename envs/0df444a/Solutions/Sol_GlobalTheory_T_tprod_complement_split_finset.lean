-- Prove2me | solution 1 for GlobalTheory.T.tprod_complement_split_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:25:24.965096+00:00
-- url     : https://prove2.me/submissions/d5ec771e-e6f4-42dd-94d8-1c46c22dff59

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TprodComplementSplitFinset
import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TprodComplementSplitFinsetStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TailCut_tprod_tail_cut


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι), Summable (fun v => |a v - 1|) → S ⊆ S' → ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | exact GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | (intros; apply GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut <;> assumption)
end _root_.GlobalTheory.T
