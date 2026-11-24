-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CharDensity.exists_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:24:55.822796+00:00
-- url     : https://prove2.me/submissions/f8040ed3-3cdb-4ed1-8a75-c6eb17774b38

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_phi_eq_charFun
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_continuous_phi
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_dens_eq_fourier
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_dens_im
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_dens_re_nonneg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharDensity_lintegral_dens_le

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.CharDensity
theorem _root_.solution (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) :
    ∃ D : V → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = dens μ y) ∧
      μ = (volume : Measure V).withDensity (fun y => ENNReal.ofReal (D y)) := by
  have hcF : Continuous (𝓕 (phi μ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hφ
  have hdF : dens μ = 𝓕 (phi μ) := funext (dens_eq_fourier μ)
  have hcd : Continuous (dens μ) := hdF ▸ hcF
  have hof : ∀ y, ((dens μ y).re : ℂ) = dens μ y := fun y =>
    Complex.ext (by simp) (by simp [dens_im μ hφ y])
  have hcD : Continuous (fun y => (dens μ y).re) := Complex.continuous_re.comp hcd
  have hfin : ∫⁻ y, ENNReal.ofReal (dens μ y).re < ∞ :=
    (lintegral_dens_le μ hφ).trans_lt (measure_lt_top μ _)
  have hDi : Integrable (fun y => (dens μ y).re) volume :=
    ⟨hcD.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun y => dens_re_nonneg μ hφ y)).2 hfin⟩
  have hFi : Integrable (𝓕 (phi μ)) volume := by
    rw [← hdF]
    exact hDi.ofReal.congr (Eventually.of_forall hof)
  have hinv : 𝓕⁻ (𝓕 (phi μ)) = phi μ := (continuous_phi μ).fourierInv_fourier_eq hφ hFi
  refine ⟨fun y => (dens μ y).re, hcD, dens_re_nonneg μ hφ, hof, ?_⟩
  set ν := (volume : Measure V).withDensity (fun y => ENNReal.ofReal (dens μ y).re) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin.ne
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : charFun μ t = phi μ ((2 * Real.pi)⁻¹ • t) := by
    rw [phi_eq_charFun, smul_smul, mul_inv_cancel₀ hpi, one_smul]
  rw [h1, ← hinv, Real.fourierInv_eq', charFun_apply, hν,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun y => ENNReal.ofReal (dens μ y).re) from
        ENNReal.measurable_ofReal.comp hcD.measurable)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (dens_re_nonneg μ hφ v), ← hdF, ← hof v, inner_smul_right,
    Complex.real_smul]
  simp only [smul_eq_mul, Complex.ofReal_re]
  rw [mul_comm, mul_inv_cancel_left₀ hpi]
end GlobalTheory.CompanionTheory.SW.CharDensity
