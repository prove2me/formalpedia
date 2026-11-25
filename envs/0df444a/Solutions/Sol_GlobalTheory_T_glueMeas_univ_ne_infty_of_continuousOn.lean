-- Prove2me | solution 1 for GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:21:51.896356+00:00
-- url     : https://prove2.me/submissions/b534f2b6-07da-4788-8442-da3293c4efb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueMeasUnivNeTopOfCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueMeasUnivNeTopOfCompactStatement
import Theorems.Thm_GlobalTheory_glueMeas_univ_ne_top_of_compact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type} (e : ι → OpenPartialHomeomorph M (V n)), (∀ y, ∃ i, y ∈ (e i).source) → (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → ∀ (r : ι → V n → ℝ), (∀ i, ContinuousOn (r i) (e i).target) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) → GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by
  first | exact @GlobalTheory.glueMeas_univ_ne_top_of_compact | exact GlobalTheory.glueMeas_univ_ne_top_of_compact | (intros; apply GlobalTheory.glueMeas_univ_ne_top_of_compact <;> assumption)
end _root_.GlobalTheory.T
