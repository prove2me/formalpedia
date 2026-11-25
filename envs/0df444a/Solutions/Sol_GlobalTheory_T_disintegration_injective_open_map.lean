-- Prove2me | solution 1 for GlobalTheory.T.disintegration_injective_open_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:07.15208+00:00
-- url     : https://prove2.me/submissions/6557cde3-0b38-4b6c-91e7-0f3de9eeaee5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMap
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationInjectiveOpenMapStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FibreDensityLimit_fibre_lintegral_eq_density


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
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U : Set V) (fib : X → Measure V), IsOpen U → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ φ : V → ℝ, Continuous φ → (∀ v, 0 ≤ φ v) → ∀ D : X → ℝ, Continuous D → (∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ = ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν) → (∀ ε : ℝ, 0 < ε → ∃ K : Set V, IsCompact K ∧ K ⊆ U ∧ ∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ ≤ ENNReal.ofReal ε * ν A) → ∀ s₀ : X, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s₀) = ENNReal.ofReal (D s₀) := by
  first | exact @GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density | exact GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density | (intros; apply GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density <;> assumption)
end _root_.GlobalTheory.T
