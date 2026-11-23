-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:41.8038+00:00
-- url     : https://prove2.me/submissions/61baef71-1e83-46ab-aabb-acedbe5587bf

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
theorem _root_.solution {ι : Type} {a : ι → ℝ} (hm : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v := by
  exact tprod_nonneg h0
end GlobalTheory.CompanionTheory.SW.AbsTprod
