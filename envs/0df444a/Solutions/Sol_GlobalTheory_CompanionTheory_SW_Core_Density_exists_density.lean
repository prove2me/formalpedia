-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.exists_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:38:40.063714+00:00
-- url     : https://prove2.me/submissions/19679ee6-7764-44e9-8e58-9368b86d3239

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_dens_continuous
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_isOpen
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_isCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_setIntegral_dens
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_nonneg_of_cosets
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_eq_of_cosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
namespace GlobalTheory.CompanionTheory.SW.Core.Density
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ (m : Measure V), IsFiniteMeasure m →
    Integrable (fun y => ∫ x, χ x y ∂m) μ → ∃ D : V → ℝ, Continuous D ∧ (∀ x, 0 ≤ D x) ∧
    (∀ x, (D x : ℂ) = ∫ y, (∫ z, χ z y ∂m) * χ (-x) y ∂μ) ∧
    ∀ U : Set V, MeasurableSet U → m U = ∫⁻ x in U, ENNReal.ofReal (D x) ∂μ := by
  intro V _ _ _ χ μ h m hm hint
  obtain ⟨i1, i2, i3, i4, i5, i6, hb, hcov, hc, hs, hn, ha, -⟩ := id h
  have hmi : Integrable (mhat χ m) μ := hint
  have hG : Continuous (dens χ μ m) := dens_continuous hc hn hmi
  have hcos := fun (L : AddSubgroup V) (hK : IsCompact (L : Set V)) (hO : IsOpen (L : Set V)) (a : V) =>
    setIntegral_dens h hc hs hn ha hmi hK hO a
  have hGi : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) →
      IntegrableOn (dens χ μ m) (coset L a) μ := fun L a hK =>
    hG.continuousOn.integrableOn_compact (coset_isCompact hK a)
  have hrei : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      ∫ x in coset L a, (dens χ μ m x).re ∂μ = (m (coset L a)).toReal := fun L a hK hO => by
    have := Complex.reCLM.integral_comp_comm (hGi L a hK)
    simp only [Complex.reCLM_apply] at this
    rw [this, hcos L hK hO a]
    simp
  have himi : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      ∫ x in coset L a, (dens χ μ m x).im ∂μ = 0 := fun L a hK hO => by
    have := Complex.imCLM.integral_comp_comm (hGi L a hK)
    simp only [Complex.imCLM_apply] at this
    rw [this, hcos L hK hO a]
    simp
  have hre : ∀ x, 0 ≤ (dens χ μ m x).re :=
    nonneg_of_cosets (μ := μ) (Complex.continuous_re.comp hG) hb fun L a hK hO => by
      simpa [hrei L a hK hO] using ENNReal.toReal_nonneg
  have him1 : ∀ x, 0 ≤ (dens χ μ m x).im :=
    nonneg_of_cosets (μ := μ) (Complex.continuous_im.comp hG) hb fun L a hK hO => by
      simp [himi L a hK hO]
  have him2 : ∀ x, 0 ≤ -(dens χ μ m x).im :=
    nonneg_of_cosets (μ := μ) (Complex.continuous_im.comp hG).neg hb fun L a hK hO => by
      simp [integral_neg, himi L a hK hO]
  have hD : Continuous fun x => (dens χ μ m x).re := Complex.continuous_re.comp hG
  have hmeq : m = μ.withDensity fun x => ENNReal.ofReal (dens χ μ m x).re := by
    refine eq_of_cosets hb hcov fun L a hK hO => ?_
    have hmeas : MeasurableSet (coset L a) := (coset_isOpen hO a).measurableSet
    rw [withDensity_apply _ hmeas, ← ofReal_integral_eq_lintegral_ofReal
      (hD.continuousOn.integrableOn_compact (coset_isCompact hK a))
      (Filter.Eventually.of_forall fun x => hre x), hrei L a hK hO,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨fun x => (dens χ μ m x).re, hD, hre, fun x => ?_, fun U hU => ?_⟩
  · have him : (dens χ μ m x).im = 0 := le_antisymm (by linarith [him2 x]) (him1 x)
    change (((dens χ μ m x).re : ℝ) : ℂ) = dens χ μ m x
    exact Complex.ext (by simp) (by simp [him])
  · conv_lhs => rw [hmeq]
    exact withDensity_apply _ hU
end GlobalTheory.CompanionTheory.SW.Core.Density
