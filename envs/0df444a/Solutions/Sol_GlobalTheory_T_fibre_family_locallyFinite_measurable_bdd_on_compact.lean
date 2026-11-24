-- Prove2me | solution 1 for GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:28:59.739489+00:00
-- url     : https://prove2.me/submissions/2669a108-ee71-4f06-9aeb-9cfa7073b113

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_fibre_family_basic


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
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib → (∀ b, IsLocallyFiniteMeasure (fib b)) ∧ (∀ b, b ∉ B → fib b = 0) ∧ (∀ A : Set V, MeasurableSet A → Measurable fun b => fib b A) ∧ ∀ (C : Set V) (D : Set X), IsCompact C → IsCompact D → D ⊆ B → ∃ c : ℝ≥0, ∀ b ∈ D, fib b C ≤ c := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic | exact GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic | (intros; apply GlobalTheory.CompanionTheory.SW.FibreFam.fibre_family_basic <;> assumption)
end _root_.GlobalTheory.T
