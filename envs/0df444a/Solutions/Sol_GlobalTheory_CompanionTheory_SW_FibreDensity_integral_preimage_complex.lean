-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.integral_preimage_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:33.559832+00:00
-- url     : https://prove2.me/submissions/1e32adcf-2b50-45b7-a633-5db60cdf9ba6

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_integral_preimage_real
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_re_facts
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_im_facts
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_continuousOn_fib

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
    {S : Set X} (hS : IsCompact S) (hSB : S ⊆ B) {ψ : V → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ g ⁻¹' B) :
    ∫ v in g ⁻¹' S, ψ v ∂μ = ∫ b in S, ∫ v, ψ v ∂(fib b) ∂ν := by
  obtain ⟨r1, r2, r3⟩ := re_facts hc hs hsupp
  obtain ⟨i1, i2, i3⟩ := im_facts hc hs hsupp
  have hR := integral_preimage_real hfin hι hf hg h hS hSB r1 r2 r3
  have hI := integral_preimage_real hfin hι hf hg h hS hSB i1 i2 i3
  have hIv : IntegrableOn ψ (g ⁻¹' S) μ := (hc.integrable_of_hasCompactSupport hs).integrableOn
  have hIb : IntegrableOn (fun b => ∫ v, ψ v ∂(fib b)) S ν :=
    ((continuousOn_fib hfin h hc hs hsupp).mono hSB).integrableOn_compact hS
  have hfre : ∀ b, ∫ v, (ψ v).re ∂(fib b) = (∫ v, ψ v ∂(fib b)).re := fun b => by
    haveI := hfin b
    exact integral_re (𝕜 := ℂ) (hc.integrable_of_hasCompactSupport hs)
  have hfim : ∀ b, ∫ v, (ψ v).im ∂(fib b) = (∫ v, ψ v ∂(fib b)).im := fun b => by
    haveI := hfin b
    exact integral_im (𝕜 := ℂ) (hc.integrable_of_hasCompactSupport hs)
  apply Complex.ext
  · have e1 : ∫ v in g ⁻¹' S, (ψ v).re ∂μ = (∫ v in g ⁻¹' S, ψ v ∂μ).re :=
      integral_re (𝕜 := ℂ) hIv
    have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)).re ∂ν = (∫ b in S, ∫ v, ψ v ∂(fib b) ∂ν).re :=
      integral_re (𝕜 := ℂ) hIb
    rw [← e1, ← e2, hR]
    simp_rw [hfre]
  · have e1 : ∫ v in g ⁻¹' S, (ψ v).im ∂μ = (∫ v in g ⁻¹' S, ψ v ∂μ).im :=
      integral_im (𝕜 := ℂ) hIv
    have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)).im ∂ν = (∫ b in S, ∫ v, ψ v ∂(fib b) ∂ν).im :=
      integral_im (𝕜 := ℂ) hIb
    rw [← e1, ← e2, hI]
    simp_rw [hfim]
end GlobalTheory.CompanionTheory.SW.FibreDensity
