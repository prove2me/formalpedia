-- Prove2me | solution 1 for GlobalTheory.T.exists_compact_for_measure_preserving_endos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:56.204731+00:00
-- url     : https://prove2.me/submissions/04268dc2-111d-4d9b-9491-0114d77fd121

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCompactForMeasurePreservingEndos
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCompactForMeasurePreservingEndosStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_lattice_pigeonhole_measure_preserving


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
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure], μ Set.univ = ⊤ → ∀ (Λ : Type) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) (C : Set V), IsCompact C → (∀ y, ∃ l, y - j l ∈ C) → ∃ Ω : Set V, IsCompact Ω ∧ ∀ e : V →+ V, Continuous e → μ.map e = μ → ∃ l, l ≠ 0 ∧ e (j l) ∈ Ω := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving | exact GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving | (intros; apply GlobalTheory.CompanionTheory.Adelic.lattice_pigeonhole_measure_preserving <;> assumption)
end _root_.GlobalTheory.T
