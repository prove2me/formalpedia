-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/202af2a8-71f9-59e3-bf97-bc7dd92dbac6

import Mathlib
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments.LanglandsTunnell.RankinSelberg"
open scoped ENNReal NNReal

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "LDatum LDatum.BoundedOnStrips"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "rsGlobalIntegral"
namespace J2A
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

theorem continuous_embedMat2_val :
    Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => embedMat2 ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
  have hv : Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :=
    Units.continuous_val
  have hij : ∀ i j : Fin 2, Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hv)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> first | exact continuous_const | exact hij _ _

theorem continuous_iota : Continuous (iota (𝓞 ℚ) ℚ : AdelicGL2 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_embedMat2_val
  · have : (fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((((iota (𝓞 ℚ) ℚ g)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))
        = (fun g : AdelicGL2 (𝓞 ℚ) ℚ => embedMat2 ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) ∘
          (fun g => g⁻¹) := by
      funext g
      rw [← map_inv]
      rfl
    rw [this]
    exact continuous_embedMat2_val.comp continuous_inv

theorem continuous_detNorm : Continuous (detNorm : AdelicGL2 (𝓞 ℚ) ℚ → ℝ) :=
  NumberField.TateGlobal.continuous_ideleNorm_det ℚ

theorem detNorm_pos (g : AdelicGL2 (𝓞 ℚ) ℚ) : 0 < detNorm g :=
  NumberField.TateGlobal.ideleNorm_pos _

theorem rpow_le_zpow_add_zpow {x r : ℝ} (hx : 0 < x) {N : ℕ} (hN : |r| ≤ N) :
    x ^ r ≤ x ^ (N : ℤ) + x ^ (-(N : ℤ)) := by
  have h1 : (0 : ℝ) ≤ x ^ (N : ℤ) := (zpow_pos hx _).le
  have h2 : (0 : ℝ) ≤ x ^ (-(N : ℤ)) := (zpow_pos hx _).le
  rcases le_or_gt 1 x with hx1 | hx1
  · calc x ^ r ≤ x ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 ((le_abs_self r).trans hN)
      _ = x ^ (N : ℤ) := by rw [← Real.rpow_intCast]; norm_cast
      _ ≤ x ^ (N : ℤ) + x ^ (-(N : ℤ)) := le_add_of_nonneg_right h2
  · calc x ^ r ≤ x ^ (-(N : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by have := neg_abs_le r; linarith)
      _ = x ^ (-(N : ℤ)) := by rw [← Real.rpow_intCast]; norm_cast
      _ ≤ x ^ (N : ℤ) + x ^ (-(N : ℤ)) := le_add_of_nonneg_left h1

theorem integrableOn
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΘc : Continuous Θ) (hΘ : HasIotaMoments Θ) (s : ℂ) :
    IntegrableOn (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
        φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := by
  obtain ⟨C, hC⟩ := hφb

  have hcont : Continuous (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) := by
    refine (hφc.mul (hΘc.comp continuous_iota)).mul ?_
    refine Continuous.cpow (Complex.continuous_ofReal.comp continuous_detNorm) continuous_const ?_
    intro g
    exact Complex.ofReal_mem_slitPlane.2 (detNorm_pos g)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩

  have hC0 : 0 ≤ C := le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (detNorm_pos 1).le _)) (hC 1)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |s.re| ≤ N := ⟨⌈|s.re|⌉₊, Nat.le_ceil _⟩
  have hbound : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ‖φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)‖
        ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)))) := by
    intro g
    have hd := detNorm_pos g
    have hφg : ‖φ g‖ ≤ C * detNorm g ^ (1 / 2 : ℝ) := by
      have h := hC g
      rw [Real.rpow_neg hd.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hd _)] at h
      exact h
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd, Complex.sub_re,
      show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
    calc ‖φ g‖ * ‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ (s.re - 1 / 2)
        ≤ C * detNorm g ^ (1 / 2 : ℝ) * ‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ (s.re - 1 / 2) := by
          gcongr
      _ = C * ‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (1 / 2 : ℝ) * detNorm g ^ (s.re - 1 / 2)) := by ring
      _ = C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ s.re) := by
          rw [← Real.rpow_add hd, show (1 / 2 : ℝ) + (s.re - 1 / 2) = s.re by ring]
          ring
      _ ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)))) := by
          gcongr
          exact rpow_le_zpow_add_zpow hd hN

  have hfin := hΘ D hD N
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (lt_of_le_of_lt
    (le_of_eq (lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top)) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin))

  rw [← ofReal_norm, show ((‖Θ (iota (𝓞 ℚ) ℚ g)‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖Θ (iota (𝓞 ℚ) ℚ g)‖ by
      rw [ofReal_norm, enorm_eq_nnnorm],
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hC0]
  exact ENNReal.ofReal_le_ofReal (hbound g)

theorem rpow_mul_abs_log_le {x σ : ℝ} (hx : 0 < x) :
    x ^ σ * |Real.log x| ≤ x ^ (σ + 1) + x ^ (σ - 1) := by
  have h1 : (0 : ℝ) ≤ x ^ (σ + 1) := (Real.rpow_pos_of_pos hx _).le
  have h2 : (0 : ℝ) ≤ x ^ (σ - 1) := (Real.rpow_pos_of_pos hx _).le
  have hxσ : (0 : ℝ) ≤ x ^ σ := (Real.rpow_pos_of_pos hx _).le
  rcases le_or_gt 1 x with hx1 | hx1
  · have hlog : |Real.log x| ≤ x := by
      rw [abs_of_nonneg (Real.log_nonneg hx1)]
      linarith [Real.log_le_sub_one_of_pos hx]
    calc x ^ σ * |Real.log x| ≤ x ^ σ * x := by gcongr
      _ = x ^ (σ + 1) := by rw [Real.rpow_add_one hx.ne']
      _ ≤ x ^ (σ + 1) + x ^ (σ - 1) := le_add_of_nonneg_right h2
  · have hlog : |Real.log x| ≤ x⁻¹ := by
      rw [abs_of_neg (Real.log_neg hx hx1), ← Real.log_inv]
      linarith [Real.log_le_sub_one_of_pos (inv_pos.2 hx)]
    calc x ^ σ * |Real.log x| ≤ x ^ σ * x⁻¹ := by gcongr
      _ = x ^ (σ - 1) := by rw [Real.rpow_sub_one hx.ne', div_eq_mul_inv]
      _ ≤ x ^ (σ + 1) + x ^ (σ - 1) := le_add_of_nonneg_left h1

noncomputable def F (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)

noncomputable def F' (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  φ g * Θ (iota (𝓞 ℚ) ℚ g) * (((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2) * Complex.log ((detNorm g : ℝ) : ℂ))

theorem slit (g : AdelicGL2 (𝓞 ℚ) ℚ) : ((detNorm g : ℝ) : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.2 (detNorm_pos g)

theorem continuous_F {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφc : Continuous φ) {Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hΘc : Continuous Θ) (s : ℂ) : Continuous (F φ Θ s) := by
  refine (hφc.mul (hΘc.comp continuous_iota)).mul ?_
  exact Continuous.cpow (Complex.continuous_ofReal.comp continuous_detNorm) continuous_const slit

theorem continuous_F' {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφc : Continuous φ) {Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hΘc : Continuous Θ) (s : ℂ) : Continuous (F' φ Θ s) := by
  refine (hφc.mul (hΘc.comp continuous_iota)).mul ?_
  refine (Continuous.cpow (Complex.continuous_ofReal.comp continuous_detNorm) continuous_const slit).mul ?_
  exact Continuous.clog (Complex.continuous_ofReal.comp continuous_detNorm) slit

theorem hasDerivAt_F (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    HasDerivAt (fun s => F φ Θ s g) (F' φ Θ s g) s := by
  unfold F F'
  have h0 : ((detNorm g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (detNorm_pos g).ne'
  have h := ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_cpow (c := ((detNorm g : ℝ) : ℂ)) (Or.inl h0)
  simp only [id, mul_one] at h
  exact h.const_mul _

theorem norm_F_le {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {C : ℝ}
    (hC : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ‖F φ Θ s g‖ ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ s.re) := by
  have hd := detNorm_pos g
  have hφg : ‖φ g‖ ≤ C * detNorm g ^ (1 / 2 : ℝ) := by
    have h := hC g
    rw [Real.rpow_neg hd.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hd _)] at h
    exact h
  rw [F, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hd, Complex.sub_re,
    show ((1 : ℂ) / 2).re = 1 / 2 by norm_num]
  calc ‖φ g‖ * ‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ (s.re - 1 / 2)
      ≤ C * detNorm g ^ (1 / 2 : ℝ) * ‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ (s.re - 1 / 2) := by
        gcongr
    _ = C * ‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (1 / 2 : ℝ) * detNorm g ^ (s.re - 1 / 2)) := by ring
    _ = C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ s.re) := by
        rw [← Real.rpow_add hd, show (1 / 2 : ℝ) + (s.re - 1 / 2) = s.re by ring]
        ring

theorem norm_F'_eq (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ‖F' φ Θ s g‖ = ‖F φ Θ s g‖ * |Real.log (detNorm g)| := by
  rw [F', F, ← mul_assoc, norm_mul (φ g * _ * _), ← Complex.ofReal_log (detNorm_pos g).le, Complex.norm_real,
    Real.norm_eq_abs]

theorem norm_F'_le {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ‖F' φ Θ s g‖ ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (s.re + 1) + detNorm g ^ (s.re - 1))) := by
  rw [norm_F'_eq]
  calc ‖F φ Θ s g‖ * |Real.log (detNorm g)|
      ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ s.re) * |Real.log (detNorm g)| := by
        gcongr; exact norm_F_le hC Θ s g
    _ = C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ s.re * |Real.log (detNorm g)|)) := by ring
    _ ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (s.re + 1) + detNorm g ^ (s.re - 1))) := by
        gcongr; exact rpow_mul_abs_log_le (detNorm_pos g)

theorem integrable_bound {Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΘc : Continuous Θ) (hΘ : HasIotaMoments Θ)
    {D : Set (AdelicGL2 (𝓞 ℚ) ℚ)}
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (C : ℝ) (hC0 : 0 ≤ C) (N : ℕ) :
    Integrable (fun g : AdelicGL2 (𝓞 ℚ) ℚ => C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)))))
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict D) := by
  have hcont : Continuous (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ))))) := by
    refine continuous_const.mul ((continuous_norm.comp (hΘc.comp continuous_iota)).mul ?_)
    exact (continuous_detNorm.zpow₀ _ fun g => Or.inl (detNorm_pos g).ne').add
      (continuous_detNorm.zpow₀ _ fun g => Or.inl (detNorm_pos g).ne')
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hfin := hΘ D hD N
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (lt_of_le_of_lt
    (le_of_eq (lintegral_const_mul' (ENNReal.ofReal C) _ ENNReal.ofReal_ne_top))
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin))
  have hnn : 0 ≤ ‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ))) :=
    mul_nonneg (norm_nonneg _) (add_nonneg (zpow_pos (detNorm_pos g) _).le (zpow_pos (detNorm_pos g) _).le)
  rw [Real.enorm_eq_ofReal (mul_nonneg hC0 hnn),
    show ((‖Θ (iota (𝓞 ℚ) ℚ g)‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖Θ (iota (𝓞 ℚ) ℚ g)‖ by
      rw [ofReal_norm, enorm_eq_nnnorm],
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hC0]

theorem rpow_le_two_moments {x σ σ₀ : ℝ} (hx : 0 < x) (hσ : |σ - σ₀| ≤ 1) {N : ℕ} (hN : |σ₀| + 2 ≤ N) :
    x ^ σ ≤ x ^ (N : ℤ) + x ^ (-(N : ℤ)) :=
  rpow_le_zpow_add_zpow hx (by
    have := abs_sub_abs_le_abs_sub σ σ₀
    linarith)

theorem differentiable_and_bounded
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΘc : Continuous Θ) (hΘ : HasIotaMoments Θ) :
    Differentiable ℂ (fun s : ℂ => rsGlobalIntegral D s φ Θ) ∧
      LanglandsTunnell.LDatum.BoundedOnStrips (fun s : ℂ => rsGlobalIntegral D s φ Θ) := by
  obtain ⟨C, hC⟩ := hφb
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (detNorm_pos 1).le _)) (hC 1)
  set μ := (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict D with hμ
  have hZ : ∀ s : ℂ, rsGlobalIntegral D s φ Θ = ∫ g, F φ Θ s g ∂μ := fun s => rfl
  constructor
  ·
    intro s₀
    obtain ⟨N, hN⟩ : ∃ N : ℕ, |s₀.re| + 2 ≤ N := ⟨⌈|s₀.re| + 2⌉₊, Nat.le_ceil _⟩
    have hball : Metric.ball s₀ 1 ∈ nhds s₀ := Metric.ball_mem_nhds _ one_pos
    have hre : ∀ s ∈ Metric.ball s₀ 1, |s.re - s₀.re| ≤ 1 := by
      intro s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans hs.le
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F φ Θ) (F' := F' φ Θ)
      (x₀ := s₀) (bound := fun g => (2 * C) * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)))))
      hball
      (Filter.Eventually.of_forall fun s => (continuous_F hφc hΘc s).aestronglyMeasurable)
      (integrableOn D hD φ hφc ⟨C, hC⟩ Θ hΘc hΘ s₀)
      (continuous_F' hφc hΘc s₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g s hs => by
        have hd := detNorm_pos g
        calc ‖F' φ Θ s g‖ ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (s.re + 1) + detNorm g ^ (s.re - 1))) :=
              norm_F'_le hC0 hC Θ s g
          _ ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * ((detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ))) +
                (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ))))) := by
              have hss := abs_le.1 (hre s hs)
              have h0 := le_abs_self s₀.re
              have h0' := neg_abs_le s₀.re
              have h1 : detNorm g ^ (s.re + 1) ≤ detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)) :=
                rpow_le_zpow_add_zpow hd (by rw [abs_le]; constructor <;> linarith)
              have h2 : detNorm g ^ (s.re - 1) ≤ detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)) :=
                rpow_le_zpow_add_zpow hd (by rw [abs_le]; constructor <;> linarith)
              gcongr
          _ = (2 * C) * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)))) := by ring)
      (integrable_bound hΘc hΘ hD (2 * C) (by positivity) N)
      (Filter.Eventually.of_forall fun g s _ => hasDerivAt_F φ Θ s g)
    exact key.2.differentiableAt
  ·
    intro a b
    obtain ⟨N, hN⟩ : ∃ N : ℕ, max |a| |b| ≤ N := ⟨⌈max |a| |b|⌉₊, Nat.le_ceil _⟩
    refine ⟨∫ g, C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)))) ∂μ, ?_⟩
    intro s ha hb
    show ‖rsGlobalIntegral D s φ Θ‖ ≤ _
    rw [hZ]
    refine norm_integral_le_of_norm_le (integrable_bound hΘc hΘ hD C hC0 N) (Filter.Eventually.of_forall fun g => ?_)
    calc ‖F φ Θ s g‖ ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * detNorm g ^ s.re) := norm_F_le hC Θ s g
      _ ≤ C * (‖Θ (iota (𝓞 ℚ) ℚ g)‖ * (detNorm g ^ (N : ℤ) + detNorm g ^ (-(N : ℤ)))) := by
          gcongr
          exact rpow_le_zpow_add_zpow (detNorm_pos g) (by
            have : |s.re| ≤ max |a| |b| := abs_le_max_abs_abs ha hb
            linarith)

end LanglandsTunnell.RankinSelberg.J2A

theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΘc : Continuous Θ) (hΘ : HasIotaMoments Θ) :
    Differentiable ℂ (fun s : ℂ => rsGlobalIntegral D s φ Θ) ∧
      LanglandsTunnell.LDatum.BoundedOnStrips (fun s : ℂ => rsGlobalIntegral D s φ Θ) :=
  LanglandsTunnell.RankinSelberg.J2A.differentiable_and_bounded D hD φ hφc hφb Θ hΘc hΘ

end S_LanglandsTunnell_RankinSelberg_differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_differentiable_rsGlobalIntegral_and_boundedOnStrips_of_hasIotaMoments (solution)
