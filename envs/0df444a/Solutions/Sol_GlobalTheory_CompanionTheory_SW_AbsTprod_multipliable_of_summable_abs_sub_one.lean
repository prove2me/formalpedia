-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:41.794388+00:00
-- url     : https://prove2.me/submissions/87ed3876-aa6a-4cce-bfef-7dd2e795ea72

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
    (h : Summable (fun v => |a v - 1|)) : Multipliable a := by
  have h' : Summable (fun v => ‖a v - 1‖) := by simpa [Real.norm_eq_abs] using h
  have hm := multipliable_one_add_of_summable h'
  have hfun : (fun v => 1 + (a v - 1)) = a := funext fun v => by ring
  rwa [hfun] at hm
end GlobalTheory.CompanionTheory.SW.AbsTprod
