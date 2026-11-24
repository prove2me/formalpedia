-- Prove2me | solution 1 for GlobalTheory.T.fibre_family_integral_isContDensityOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:08:08.256065+00:00
-- url     : https://prove2.me/submissions/e5265246-248e-40e7-9624-ea655f86f289

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUniqueStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_isContDensityOn_fibreIntegral


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → ∀ φ : V → ℂ, Continuous φ → HasCompactSupport φ → HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B φ (fun b => ∫ v, φ v ∂(fib b)) ∧ ∀ b, Integrable φ (fib b) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral | exact GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral | (intros; apply GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral <;> assumption)
end _root_.GlobalTheory.T
