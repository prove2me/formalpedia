-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.lintegral_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:48.201393+00:00
-- url     : https://prove2.me/submissions/2e455820-3b24-4e47-97c5-a325a2eca9e4

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_ae_eq_point

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
theorem _root_.solution (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v))
    (hg : Continuous g)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    {S : Set X} (hS : IsCompact S) (hSB : S ⊆ B) {u : V → ℝ≥0∞} (hu : Measurable u) :
    ∫⁻ v in g ⁻¹' S, u v ∂μ = ∫⁻ b in S, ∫⁻ v, u v ∂(fib b) ∂ν := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hgS : MeasurableSet (g ⁻¹' S) := hg.measurable hSm
  have key := h.2.1 ((g ⁻¹' S).indicator u) (hu.indicator hgS)
  have hpt : ∀ b, ∫⁻ v, (g ⁻¹' S).indicator u v ∂(fib b)
      = S.indicator (fun b => ∫⁻ v, u v ∂(fib b)) b := by
    intro b
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_eq_point hι hf h b] with v hv
      exact Set.indicator_of_mem (show v ∈ g ⁻¹' S by simpa [hv] using hb) u
    · rw [Set.indicator_of_notMem hb]
      have : (fun v => (g ⁻¹' S).indicator u v) =ᵐ[fib b] fun _ => 0 := by
        filter_upwards [ae_eq_point hι hf h b] with v hv
        exact Set.indicator_of_notMem (show v ∉ g ⁻¹' S by simpa [hv] using hb) u
      rw [lintegral_congr_ae this]; simp
  simp_rw [hpt] at key
  rw [lintegral_indicator hSm, setLIntegral_indicator hgS] at key
  have hsub : g ⁻¹' S ∩ g ⁻¹' B = g ⁻¹' S :=
    Set.inter_eq_left.mpr (Set.preimage_mono hSB)
  rwa [hsub] at key
end GlobalTheory.CompanionTheory.SW.FibreDensity
