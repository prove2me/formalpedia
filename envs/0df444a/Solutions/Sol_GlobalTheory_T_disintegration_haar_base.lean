-- Prove2me | solution 1 for GlobalTheory.T.disintegration_haar_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:35.513451+00:00
-- url     : https://prove2.me/submissions/a82a54c1-bfcf-4f41-b2ad-83142687d7cf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationHaarBase
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationHaarBaseStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreShift_fib_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] [ν.IsAddHaarMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U W : Set V), IsOpen W → W ⊆ U → W.Nonempty → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ T : X → V → V, (∀ s, Measurable (T s)) → (∀ s, μ.map (T s) = μ) → (∀ s, ContinuousOn (T s) W) → (∀ s v, T s v ∈ W ↔ v ∈ W) → (∀ s, ∀ v ∈ W, T (-s) (T s v) = v) → (∀ s, ∀ v ∈ W, g (T s v) = g v + s) → ∀ b : X, fib b ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero | exact GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SW.FibreShift.fib_ne_zero <;> assumption)
end _root_.GlobalTheory.T
