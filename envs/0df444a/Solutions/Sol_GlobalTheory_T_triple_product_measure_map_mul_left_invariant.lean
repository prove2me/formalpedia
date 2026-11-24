-- Prove2me | solution 1 for GlobalTheory.T.triple_product_measure_map_mul_left_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:41.338455+00:00
-- url     : https://prove2.me/submissions/ea8042c1-22ae-4c02-aaa3-79d65eb157c5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMeasureIwasawaDecomposition
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMeasureIwasawaDecompositionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_tripleProduct_map_leftInvariant


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
theorem _root_.solution : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant | exact GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant | (intros; apply GlobalTheory.CompanionTheory.Adelic.tripleProduct_map_leftInvariant <;> assumption)
end _root_.GlobalTheory.T
