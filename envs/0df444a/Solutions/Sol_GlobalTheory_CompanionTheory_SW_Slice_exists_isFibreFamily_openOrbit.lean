-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:05.947847+00:00
-- url     : https://prove2.me/submissions/1407dbec-abbd-4e20-b0b6-0ab2343a0dd1

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_comap_isLocallyFinite
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_fibFam_support
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_integrable_and_continuous
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_exists_slice_measure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_lintegral_fibFam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
namespace GlobalTheory.CompanionTheory.SW.Slice
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [SecondCountableTopology Q] [T2Space Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X], (∀ (q : Q) (v : V), g (q • v) = q • g v) → ∀ (χ χ' : Q →* ℝ≥0), Continuous χ → Continuous χ' → (∀ q : Q, μ.map (fun v => q • v) = χ q • μ) → (∀ q : Q, ν.map (fun x => q • x) = χ' q • ν) → ∀ b₀ : X, IsOpenEmbedding (fun q : Q => q • b₀) → ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν (Set.range fun q : Q => q • b₀) fib := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf Q _ _ _ _ _ _ _ _ _ _ heq χ χ' hχ hχ'
    hμ hν b₀ ho
  letI : MeasurableSpace Q := borel Q
  haveI : BorelSpace Q := ⟨rfl⟩
  obtain ⟨m, hmf, hm⟩ := exists_slice_measure hg heq ho μ ν χ χ' hχ hχ' hμ hν
  have hcl : IsClosed (g ⁻¹' {b₀}) := isClosed_singleton.preimage hg
  haveI := comap_isLocallyFinite ho ν
  haveI : IsLocallyFiniteMeasure
      ((ν.comap (fun q : Q => q • b₀)).withDensity (fun q => (χ' q : ℝ≥0∞))) :=
    IsLocallyFiniteMeasure.withDensity_coe hχ'
  have hw : Continuous (fun q : Q => χ' q * χ q⁻¹) := hχ'.mul (hχ.comp continuous_inv)
  refine ⟨fibFam g b₀ (fun q => χ' q * χ q⁻¹) m, fibFam_support hι hg hf heq ho _ m, ?_, ?_⟩
  · exact fun φ hφ => lintegral_fibFam hg heq ho μ ν χ χ' hχ hχ' m hm hφ
  · exact fun φ hφ hφc _ => integrable_and_continuous hg ho hw m hφ hφc
end GlobalTheory.CompanionTheory.SW.Slice
