-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_ne_zero_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:43.2995+00:00
-- url     : https://prove2.me/submissions/6f553c24-8034-41cd-8bd2-73062e30dfa5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsTprod
namespace GlobalTheory.CompanionTheory.SW.AbsTprod
theorem _root_.solution {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (h0 : ∀ v, a v ≠ 0) : ∏' v, a v ≠ 0 := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hne : ∀ v, 1 + (a v - 1) ≠ 0 := fun v => by simpa using h0 v
  have hp := tprod_one_add_ne_zero_of_summable (f := fun v => a v - 1) hne h'
  simpa using hp
end GlobalTheory.CompanionTheory.SW.AbsTprod
