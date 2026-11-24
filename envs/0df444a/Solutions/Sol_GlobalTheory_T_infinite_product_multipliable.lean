-- Prove2me | solution 1 for GlobalTheory.T.infinite_product_multipliable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:52:10.070363+00:00
-- url     : https://prove2.me/submissions/5d8b6e67-505d-4a78-bc0b-986ba6c57331

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliableStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_abs_tprod


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
theorem _root_.solution : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod | exact GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod | (intros; apply GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod <;> assumption)
end _root_.GlobalTheory.T
