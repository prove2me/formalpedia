-- Prove2me | solution 1 for GlobalTheory.T.measurable_embedding_of_injective_proper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:26:44.470171+00:00
-- url     : https://prove2.me/submissions/8218faf4-4352-4e8a-b104-665b9daa5648

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableEmbeddingOfInjectiveProper
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableEmbeddingOfInjectiveProperStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_fibreFamily_eq_inter


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (W : Set V), IsOpen W → ∀ (B B' : Set X), IsOpen B → IsOpen B' → B' ⊆ B → ∀ fib fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib' → ∀ b ∈ B', fib' b = fib b := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter | exact GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter | (intros; apply GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter <;> assumption)
end _root_.GlobalTheory.T
