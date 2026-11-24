-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.integral_preimage_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:15:16.947955+00:00
-- url     : https://prove2.me/submissions/6aa513a4-88a7-4b8c-b7b5-aee826314761

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_lintegral_preimage

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreDensity
variable {V X Y : Type}
  [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {B : Set X}
  {fib : X → Measure V}
namespace GlobalTheory.CompanionTheory.SW.FibreDensity
theorem _root_.solution [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (hfin : ∀ b, IsLocallyFiniteMeasure (fib b))
    (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) (hg : Continuous g)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {S : Set X} (hS : IsCompact S) (hSB : S ⊆ B) {u : V → ℝ} (hc : Continuous u)
    (hs : HasCompactSupport u) (hsupp : tsupport u ⊆ g ⁻¹' B) (h0 : ∀ v, 0 ≤ u v) :
    ∫ v in g ⁻¹' S, u v ∂μ = ∫ b in S, ∫ v, u v ∂(fib b) ∂ν := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hcont := (h.2.2 u hc hs hsupp).2
  have hm : AEStronglyMeasurable (fun b => ∫ v, u v ∂(fib b)) (ν.restrict S) :=
    (hcont.mono hSB).aestronglyMeasurable hSm
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0)
      hc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun b => integral_nonneg h0) hm,
    lintegral_preimage hι hf hg h hS hSB (hc.measurable.ennreal_ofReal)]
  congr 1
  refine lintegral_congr fun b => ?_
  haveI := hfin b
  exact (ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hs)
    (Filter.Eventually.of_forall h0)).symm
end GlobalTheory.CompanionTheory.SW.FibreDensity
