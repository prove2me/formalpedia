-- Prove2me | solution 1 for GlobalTheory.T.lattice_ball_count_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:17:13.512823+00:00
-- url     : https://prove2.me/submissions/a9bfb738-f817-40fe-b535-825bd13dd8d2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_tsum_indicator_norm_le_packing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type) [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) * ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing | exact GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing | (intros; apply GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing <;> assumption)
end _root_.GlobalTheory.T
