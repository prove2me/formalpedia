-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:49:29.297423+00:00
-- url     : https://prove2.me/submissions/c1e1e0b6-caeb-4bba-bb6b-95e394a16244

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_ae_eq_point
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_continuousOn_fib
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_integral_preimage_complex
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_exists_cutoff
import Theorems.Thm_GlobalTheory_T_fibre_family_locallyFinite_measurable_bdd_on_compact


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
theorem _root_.solution : ∀ (V X Y : Type) [TopologicalSpace V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y)
    (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) →
    ∀ (B : Set X), IsOpen B → ∀ fib : X → Measure V,
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib →
    ∀ φ : V → ℂ, Continuous φ → HasCompactSupport φ →
    HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B φ (fun b => ∫ v, φ v ∂(fib b)) ∧
      ∀ b, Integrable φ (fib b) := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf B hB fib h φ hc hs
  have hfin := (GlobalTheory.T.fibre_family_locallyFinite_measurable_bdd_on_compact V X Y μ ν f g ι hι hg hf B hB fib h).1
  have hcongr : ∀ {ψ : V → ℂ} {K : Set X}, (∀ v, g v ∈ K → ψ v = φ v) → ∀ b ∈ K,
      ∫ v, ψ v ∂(fib b) = ∫ v, φ v ∂(fib b) := by
    intro ψ K hψ b hb
    refine integral_congr_ae ?_
    filter_upwards [ae_eq_point hι hf h b] with v hv
    exact hψ v (hv ▸ hb)
  refine ⟨⟨?_, ?_⟩, fun b => ?_⟩
  · intro b₀ hb₀
    obtain ⟨K, hKn, hKB, hK⟩ := local_compact_nhds (hB.mem_nhds hb₀)
    obtain ⟨ψ, c1, c2, c3, c4⟩ := exists_cutoff hg hB hK hKB hc hs
    have hat : ContinuousAt (fun b => ∫ v, ψ v ∂(fib b)) b₀ :=
      (continuousOn_fib hfin h c1 c2 c3).continuousAt (hB.mem_nhds hb₀)
    refine (hat.congr ?_).continuousWithinAt
    filter_upwards [hKn] with b hb
    exact hcongr c4 b hb
  · intro S hS hSB
    have hpre : f ⁻¹' (ι '' S) = g ⁻¹' S := by
      ext v
      simp only [Set.mem_preimage, Set.mem_image, hf]
      constructor
      · rintro ⟨x, hx, hxv⟩
        exact hι hxv ▸ hx
      · exact fun hv => ⟨g v, hv, rfl⟩
    have hSm : MeasurableSet S := hS.isClosed.measurableSet
    obtain ⟨ψ, c1, c2, c3, c4⟩ := exists_cutoff hg hB hS hSB hc hs
    rw [hpre]
    calc ∫ v in g ⁻¹' S, φ v ∂μ = ∫ v in g ⁻¹' S, ψ v ∂μ :=
          setIntegral_congr_fun (hg.measurable hSm) (fun v hv => (c4 v hv).symm)
      _ = ∫ b in S, ∫ v, ψ v ∂(fib b) ∂ν :=
          integral_preimage_complex hfin hι hf hg h hS hSB c1 c2 c3
      _ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν :=
          setIntegral_congr_fun hSm (fun b hb => hcongr c4 b hb)
  · haveI := hfin b
    exact hc.integrable_of_hasCompactSupport hs
end GlobalTheory.CompanionTheory.SW.FibreDensity
