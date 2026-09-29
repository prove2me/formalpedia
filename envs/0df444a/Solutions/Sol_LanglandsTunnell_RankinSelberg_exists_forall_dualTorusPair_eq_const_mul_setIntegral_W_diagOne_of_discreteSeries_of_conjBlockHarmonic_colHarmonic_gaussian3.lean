-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5079cfca-cc1e-5356-adef-322fbf74833c

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_setIntegral_dualTorusPair_scaling
import Theorems.Thm_LanglandsTunnell_setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable
import Theorems.Thm_LanglandsTunnell_setIntegral_dualFibres_eq_oneSided_torusPair
import Theorems.Thm_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided
import Theorems.Thm_LanglandsTunnell_integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul
import Theorems.Thm_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
import Theorems.Thm_LanglandsTunnell_setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace K8G
open Set Real LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR

section Profile
variable {P₂ : RealArchParam} (D : ArchDatumR P₂)

def Fp (τ : ℝ) : ℂ := D.W (ArchR.diagOne τ)

theorem continuous_diagOneCoords : Continuous fun τ : ℝ => Matrix.of.symm (ArchR.diagOne τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [ArchR.diagOne, continuous_const, continuous_id']

theorem continuousOn_Fp : ContinuousOn (Fp D) {τ : ℝ | τ ≠ 0} := by
  have hW := D.smooth.continuousOn
  have hmap : MapsTo (fun τ : ℝ => Matrix.of.symm (ArchR.diagOne τ)) {τ : ℝ | τ ≠ 0} ArchR.glSet := by
    intro τ hτ
    show (Matrix.of (Matrix.of.symm (ArchR.diagOne τ))).det ≠ 0
    simpa [ArchR.diagOne, Matrix.det_fin_two] using hτ
  have h := hW.comp (continuous_diagOneCoords).continuousOn hmap
  refine h.congr (fun τ _ => ?_)
  simp [Fp, ArchR.asPi]

theorem measurable_Fp : Measurable (Fp D) :=
  measurable_of_continuousOn_compl_singleton 0 (by rw [Set.compl_singleton_eq]; exact continuousOn_Fp D)

theorem exists_bound_Fp : ∃ CF σF : ℝ, 0 ≤ CF ∧ 0 ≤ σF ∧ ∀ τ : ℝ, τ ≠ 0 → ‖Fp D τ‖ ≤ CF * (1 + |τ| ^ (-σF)) := by
  obtain ⟨C₁, hC₁⟩ := D.decay_top 0 0
  obtain ⟨C₂, σ₂, hC₂⟩ := D.decay_zero 0
  have hK1 : ArchR.IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := Submonoid.one_mem _
  have key : ∀ y : ℝ, ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y 1)‖ = ‖Fp D y‖ := by
    intro y; rw [norm_iteratedFDerivWithin_zero]; simp [ArchR.asPi, ArchR.diagOneMulCoords, Fp]
  have h1 : ∀ y : ℝ, 1 ≤ |y| → ‖Fp D y‖ ≤ C₁ := by
    intro y hy; have := hC₁ y 1 hK1 hy; rw [key] at this; simpa using this
  have h2 : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖Fp D y‖ ≤ C₂ * |y| ^ (-σ₂) := by
    intro y hy hy1; have := hC₂ y 1 hK1 hy hy1; rwa [key] at this
  have hC₁0 : 0 ≤ C₁ := le_trans (norm_nonneg _) (h1 1 (by simp))
  have hC₂0 : 0 ≤ C₂ := by
    have := h2 1 one_ne_zero (by simp)
    simp only [abs_one, Real.one_rpow, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨max C₁ C₂, max σ₂ 0, hC₁0.trans (le_max_left _ _), le_max_right _ _, fun τ hτ => ?_⟩
  have hM : 0 ≤ max C₁ C₂ := hC₁0.trans (le_max_left _ _)
  have hτp : 0 < |τ| := abs_pos.2 hτ
  have hr : 0 ≤ |τ| ^ (-max σ₂ 0) := Real.rpow_nonneg hτp.le _
  by_cases h : 1 ≤ |τ|
  · calc ‖Fp D τ‖ ≤ C₁ := h1 τ h
      _ ≤ max C₁ C₂ := le_max_left _ _
      _ ≤ max C₁ C₂ * (1 + |τ| ^ (-max σ₂ 0)) := le_mul_of_one_le_right hM (by linarith)
  · push Not at h
    calc ‖Fp D τ‖ ≤ C₂ * |τ| ^ (-σ₂) := h2 τ hτ h.le
      _ ≤ max C₁ C₂ * |τ| ^ (-max σ₂ 0) := by
          refine mul_le_mul (le_max_right _ _) ?_ (Real.rpow_nonneg hτp.le _) hM
          exact Real.rpow_le_rpow_of_exponent_ge hτp h.le (neg_le_neg (le_max_left _ _))
      _ ≤ max C₁ C₂ * (1 + |τ| ^ (-max σ₂ 0)) := by nlinarith

end Profile
end K8G

end

namespace DualGlue
open MeasureTheory Set

lemma sum_le_prod_one_add (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a + b + c + d ≤ (1 + a) * (1 + b) * (1 + c) * (1 + d) := by
  nlinarith [mul_nonneg ha hb, mul_nonneg hc hd, mul_nonneg (mul_nonneg ha hb) hc,
    mul_nonneg (mul_nonneg ha hb) hd, mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg hb hc, mul_nonneg hb hd,
    mul_nonneg (mul_nonneg ha hc) hd, mul_nonneg (mul_nonneg hb hc) hd,
    mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hd]

lemma norm_bracket_pow_le (m : ℕ) (x z : ℝ) :
    ‖(((x : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m‖ ≤ (|x| + |z|) ^ m := by
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc ‖((x : ℝ) : ℂ) + Complex.I * (z : ℂ)‖ ≤ ‖((x : ℝ) : ℂ)‖ + ‖Complex.I * (z : ℂ)‖ := norm_add_le _ _
    _ = |x| + |z| := by simp [Complex.norm_real, Real.norm_eq_abs]

lemma bracketMinus_bound (m : ℕ) (p q r z : ℝ) :
    ‖(((p - q + r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m‖
      ≤ 1 * (1 + |p|) ^ m * (1 + |q|) ^ m * (1 + |r|) ^ m * (1 + |z|) ^ m := by
  refine (norm_bracket_pow_le m _ z).trans ?_
  rw [one_mul, ← mul_pow, ← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  calc |p - q + r| + |z| ≤ |p| + |q| + |r| + |z| := by
        have := abs_add_le (p - q) r; have := abs_sub p q; linarith
    _ ≤ (1 + |p|) * (1 + |q|) * (1 + |r|) * (1 + |z|) :=
        sum_le_prod_one_add _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)

lemma bracketPlus_bound (m : ℕ) (p q r z : ℝ) :
    ‖(((-p - q - r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m‖
      ≤ 1 * (1 + |p|) ^ m * (1 + |q|) ^ m * (1 + |r|) ^ m * (1 + |z|) ^ m := by
  refine (norm_bracket_pow_le m _ z).trans ?_
  rw [one_mul, ← mul_pow, ← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  calc |-p - q - r| + |z| ≤ |p| + |q| + |r| + |z| := by
        have := abs_sub (-p - q) r; have := abs_sub (-p) q; rw [abs_neg] at this; linarith
    _ ≤ (1 + |p|) * (1 + |q|) * (1 + |r|) * (1 + |z|) :=
        sum_le_prod_one_add _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)

noncomputable def Sg (a₀ : ZMod 2) (y : ℝ) : ℂ := if a₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)

theorem Sg_dil (a₀ : ZMod 2) (c : ℝ) (hc : 0 < c) (y : ℝ) : Sg a₀ (y / c) = Sg a₀ y := by
  unfold Sg; split_ifs
  · rfl
  · congr 2
    rcases lt_trichotomy y 0 with h | h | h
    · rw [sign_neg h, sign_neg (div_neg_of_neg_of_pos h hc)]
    · subst h; simp
    · rw [sign_pos h, sign_pos (div_pos h hc)]

theorem Sg_measurable (a₀ : ZMod 2) : Measurable (Sg a₀) := by
  unfold Sg; split_ifs
  · exact measurable_const
  · have h : (fun y : ℝ => ((SignType.sign y : ℝ) : ℂ)) = fun y => if 0 < y then (1 : ℂ) else if y < 0 then -1 else 0 := by
      funext y; rw [sign_apply]; split_ifs <;> simp
    rw [h]
    exact Measurable.ite measurableSet_Ioi measurable_const (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem Sg_norm_le (a₀ : ZMod 2) (y : ℝ) : ‖Sg a₀ y‖ ≤ 1 := by
  unfold Sg; split_ifs
  · simp
  · rw [sign_apply]; split_ifs <;> simp

theorem Sg_neg_one (a₀ : ZMod 2) : Sg a₀ (-1) = (-1 : ℂ) ^ a₀.val := by
  unfold Sg
  have key : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases key a₀ with h | h
  · subst h; simp
  · subst h
    rw [if_neg (by decide), show ((1 : ZMod 2)).val = 1 from rfl, pow_one, sign_neg (by norm_num : (-1:ℝ) < 0)]
    push_cast
    simp

theorem Sg_one (a₀ : ZMod 2) : Sg a₀ 1 = 1 := by
  unfold Sg; split_ifs
  · rfl
  · rw [sign_pos (by norm_num : (0:ℝ) < 1)]; push_cast; simp

theorem measurable_bracketAvg (m : ℕ) :
    Measurable (fun c : ℝ => ∫ z : ℝ, (((c : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by
  have hF : StronglyMeasurable (fun p : ℝ × ℝ => (((p.1 : ℝ) : ℂ) + Complex.I * (p.2 : ℂ)) ^ m * (Real.exp (-(Real.pi * p.2 ^ 2)) : ℂ)) := by
    refine Continuous.stronglyMeasurable ?_
    fun_prop
  exact (hF.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

theorem measurable_K (A₁ β γ : ℂ) (m n : ℕ) (S : ℝ → ℂ) (hS : Measurable S) (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (fun p : ℝ × ℝ × ℝ =>
      ((|p.1| : ℝ) : ℂ) ^ A₁ * (Real.exp (-(2 * Real.pi * |p.1|)) : ℂ) *
        (((p.2.1⁻¹ : ℝ) : ℂ) ^ n * S p.2.1 * ((|p.2.1| : ℝ) : ℂ) ^ β * ((p.2.2 : ℝ) : ℂ) ^ γ) *
        (Real.exp (-(Real.pi * ((p.2.2 ^ 2)⁻¹ + p.1 ^ 2 * p.2.2 ^ 2 + p.2.1 ^ 2))) : ℂ) *
        g (p.2.1 / p.2.2) *
        (∫ z : ℝ, (((p.1 * p.2.2 - p.2.2⁻¹ + p.2.1 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
          (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by
  have h1 : Measurable fun p : ℝ × ℝ × ℝ => ((|p.1| : ℝ) : ℂ) ^ A₁ :=
    (Complex.measurable_ofReal.comp (measurable_fst.abs)).pow_const A₁
  have h2 : Measurable fun p : ℝ × ℝ × ℝ => ((|p.2.1| : ℝ) : ℂ) ^ β :=
    (Complex.measurable_ofReal.comp (measurable_snd.fst.abs)).pow_const β
  have h3 : Measurable fun p : ℝ × ℝ × ℝ => ((p.2.2 : ℝ) : ℂ) ^ γ :=
    (Complex.measurable_ofReal.comp measurable_snd.snd).pow_const γ
  have h4 : Measurable fun p : ℝ × ℝ × ℝ => S p.2.1 := hS.comp measurable_snd.fst
  have h5 : Measurable fun p : ℝ × ℝ × ℝ => g (p.2.1 / p.2.2) := hg.comp (measurable_snd.fst.div measurable_snd.snd)
  have h6 : Measurable fun p : ℝ × ℝ × ℝ => ∫ z : ℝ, (((p.1 * p.2.2 - p.2.2⁻¹ + p.2.1 : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
      (Real.exp (-(Real.pi * z ^ 2)) : ℂ) :=
    (measurable_bracketAvg m).comp ((measurable_fst.mul measurable_snd.snd).sub measurable_snd.snd.inv |>.add measurable_snd.fst)
  have h7 : Measurable fun p : ℝ × ℝ × ℝ => (((p.2.1⁻¹ : ℝ) : ℂ)) ^ n :=
    (Complex.measurable_ofReal.comp measurable_snd.fst.inv).pow_const n
  have h8 : Measurable fun p : ℝ × ℝ × ℝ => (Real.exp (-(2 * Real.pi * |p.1|)) : ℂ) := by fun_prop
  have h9 : Measurable fun p : ℝ × ℝ × ℝ => (Real.exp (-(Real.pi * ((p.2.2 ^ 2)⁻¹ + p.1 ^ 2 * p.2.2 ^ 2 + p.2.1 ^ 2))) : ℂ) := by fun_prop
  exact ((((h1.mul h8).mul (((h7.mul h4).mul h2).mul h3)).mul h9).mul h5).mul h6

end DualGlue

open DualGlue in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (ha1 : a = -1) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (P : RealArchParam)
    (_hP₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hkw1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par) + signShift (a₂ + par))
    (hkw2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAN : ∀ par : ZMod 2, ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA par (unipotentGL2 x * h) = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * x)) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (hk₀min : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1))
    (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hPdisc : P = RealArchParam.discrete uP nP hnP)
    (m : ℕ) (hm : m = nP + 1)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (hWpos : ∀ t : ℝ, 0 < t → Wr par₀ default t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → Wr par₀ default t = 0) :
    ∃ σa : ℝ, ∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = (Real.pi : ℂ) * Complex.I ^ m * (-1 : ℂ) ^ (m + n + (aR w₀ h₀).val) * (2 : ℂ) ^ m *
              Complex.Gammaℝ (2 * s - P.centralExponent - P₂.centralExponent + (n : ℂ) + 1) *
              (2 * (Real.pi : ℂ)) ^ (-(s - uR w₀ h₀ - uP + (m : ℂ) / 2)) * Complex.Gamma (s - uR w₀ h₀ - uP + (m : ℂ) / 2) *
              (∫ v in Set.Ioi (0 : ℝ), D.W (ArchR.diagOne v) * ((v : ℝ) : ℂ) ^ (s - uP - P₂.centralExponent + (m : ℂ) / 2 - 2) *
                (Real.exp (-(2 * Real.pi * v)) : ℂ)) := by
  classical

  have hε' : ε' = 1 ∨ ε' = -1 := by
    rcases hcol with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inr h
    · exact Or.inl h
  have hm1 : 1 ≤ m := by omega
  have hcP : P.centralExponent = 2 * uP := by rw [hPdisc]; rfl
  have haR : ((a : ℚ) : ℝ) = -1 := by rw [ha1]; push_cast; ring

  obtain ⟨CF, σF, hCF, hσF, hFb⟩ := K8G.exists_bound_Fp D
  have hgm : Measurable (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) :=
    (K8G.measurable_Fp D).comp (measurable_const.mul measurable_id)
  have hgm' : Measurable (fun v : ℝ => (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (-v)) :=
    hgm.comp measurable_neg
  have hgb : ∀ τ : ℝ, τ ≠ 0 → ‖(fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) τ‖ ≤ CF * (1 + |τ| ^ (-σF)) := by
    intro τ hτ
    have := hFb ((a : ℝ) * τ) (mul_ne_zero (by rw [haR]; norm_num) hτ)
    simpa [K8G.Fp, haR, abs_neg] using this
  have hgb' : ∀ τ : ℝ, τ ≠ 0 → ‖(fun v : ℝ => (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (-v)) τ‖ ≤ CF * (1 + |τ| ^ (-σF)) := by
    intro τ hτ
    have := hFb τ hτ
    simpa [K8G.Fp, haR] using this

  have hSg : ∀ c : ℝ, 0 < c → ∀ y : ℝ, (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) (y / c) = (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) y := fun c hc y => Sg_dil (aR w₀ h₀) c hc y
  have hSgm : Measurable (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) := Sg_measurable (aR w₀ h₀)

  obtain ⟨σm, hIm⟩ :=
    LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
      (-(P₂.centralExponent - uR w₀ h₀) - 2) (fun v : ℝ => (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (-v)) hgm' CF σF hσF hgb'
      (fun p q r z => (((p - q + r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m)
      (by fun_prop) 1 m (fun p q r z => bracketMinus_bound m p q r z)
  obtain ⟨σp, hIp⟩ :=
    LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
      (-(P₂.centralExponent - uR w₀ h₀) - 2) (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) hgm CF σF hσF hgb
      (fun p q r z => (((-p - q - r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m)
      (by fun_prop) 1 m (fun p q r z => bracketPlus_bound m p q r z)
  obtain ⟨σ₀, hB⟩ := LanglandsTunnell.setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero
      m hm1 (-(P₂.centralExponent - uR w₀ h₀) - 2)
      (fun v : ℝ => (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (-v)) (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v)))
      hgm' hgm CF σF hσF hgb' CF σF hσF hgb

  set σM : ℝ := max (max σm σp) σ₀ with hσM
  refine ⟨max (max (σM - uP.re - (nP : ℝ) / 2 - 1 + P.centralExponent.re + P₂.centralExponent.re + 5 / 2)
      ((σM + (uR w₀ h₀).re - 1 + P.centralExponent.re + P₂.centralExponent.re) / 2))
      ((-1 + P.centralExponent.re + P₂.centralExponent.re - (n : ℝ)) / 2), fun s hs => ?_⟩
  have hs1 : σM - uP.re - (nP : ℝ) / 2 - 1 + P.centralExponent.re + P₂.centralExponent.re + 5 / 2 < s.re :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hs
  have hs2 : (σM + (uR w₀ h₀).re - 1 + P.centralExponent.re + P₂.centralExponent.re) / 2 < s.re :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hs
  have hs3 : (-1 + P.centralExponent.re + P₂.centralExponent.re - (n : ℝ)) / 2 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hreA : ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1).re = s.re + uP.re + (nP : ℝ) / 2 + 1 - P.centralExponent.re - P₂.centralExponent.re - 5 / 2 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, Complex.one_re, Complex.re_ofNat]
    ring
  have hreG : ((n : ℂ) - ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) - (-(uR w₀ h₀ + 2)) - 3).re = -2 * s.re + P.centralExponent.re + P₂.centralExponent.re + (uR w₀ h₀).re - 1 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.natCast_re, Complex.one_re, Complex.re_ofNat]
    ring
  have hrew : (((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1)).re = 2 * s.re - P.centralExponent.re - P₂.centralExponent.re + (n : ℝ) := by
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.natCast_re, Complex.one_re, Complex.re_ofNat]
    ring
  have hσm : σm ≤ σM := (le_max_left _ _).trans (le_max_left _ _)
  have hσp : σp ≤ σM := (le_max_right _ _).trans (le_max_left _ _)
  have hσ₀ : σ₀ ≤ σM := le_max_right _ _
  have hα : σM < ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1).re := by rw [hreA]; linarith
  have hγ' : ((n : ℂ) - ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) - (-(uR w₀ h₀ + 2)) - 3).re < -σM := by rw [hreG]; linarith
  have hwre : -1 < (((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1)).re := by rw [hrew]; linarith
  have hβ' : (-(P₂.centralExponent - uR w₀ h₀) - 2 : ℂ) = -(P₂.centralExponent - uR w₀ h₀) - 2 := rfl
  have hrel : -2 * ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1) + (-(P₂.centralExponent - uR w₀ h₀) - 2) - ((n : ℂ) - ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) - (-(uR w₀ h₀ + 2)) - 3) - 2 = (1 : ℂ) - (m : ℂ) := by
    rw [hcP, hm]; push_cast; ring

  have hminus := hIm ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1) ((n : ℂ) - ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) - (-(uR w₀ h₀ + 2)) - 3) (lt_of_le_of_lt hσm hα) (lt_of_lt_of_le hγ' (neg_le_neg hσm))
  have hplus := hIp ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1) ((n : ℂ) - ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) - (-(uR w₀ h₀ + 2)) - 3) (lt_of_le_of_lt hσp hα) (lt_of_lt_of_le hγ' (neg_le_neg hσp))
  have hFib2 := LanglandsTunnell.integrable_dualFibres_of_integrable_oneSided (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) (-(uR w₀ h₀ + 2)) (P₂.centralExponent - uR w₀ h₀) ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) m n (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) hSg hSgm
    (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) hgm hminus hplus
  have hKm := measurable_K (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) (-(uR w₀ h₀ + 2)) (P₂.centralExponent - uR w₀ h₀) m n (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) hSgm (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) hgm
  have hInt := LanglandsTunnell.integrable_cpow_mul_exp_mul_of_integrable_abs_cpow_mul ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) hwre (fun t u Y : ℝ => ((|t| : ℝ) : ℂ) ^ (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) * (Real.exp (-(2 * Real.pi * |t|)) : ℂ) *
            (((u⁻¹ : ℝ) : ℂ) ^ n * (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) u * ((|u| : ℝ) : ℂ) ^ (-(uR w₀ h₀ + 2)) * ((Y : ℝ) : ℂ) ^ (P₂.centralExponent - uR w₀ h₀)) *
            (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) : ℂ) *
            (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (u / Y) *
            (∫ z : ℝ, (((t * Y - Y⁻¹ + u : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) hKm hFib2.2
  have hBACK := hB ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1) ((n : ℂ) - ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) - (-(uR w₀ h₀ + 2)) - 3) (lt_of_le_of_lt hσ₀ hα) (lt_of_lt_of_le hγ' (neg_le_neg hσ₀)) hrel

  rw [LanglandsTunnell.RankinSelberg.dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
      K _hdeg μ _hμ _hns uR aR uC kC huR huC ω hω E hE a ha ha1 aInf haInf psiInf hpsiInf ν_add hν_add ν_mul P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R w₀ h₀ P₂ hP₂ D k₀ hDW hDE hDnz hk₀min uP nP hnP hPdisc m hm n ε' hcol par₀ S hS hWpos hWneg s]
  beta_reduce

  rw [LanglandsTunnell.setIntegral_dualTorusPair_scaling (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) (-(uR w₀ h₀ + 2)) (P₂.centralExponent - uR w₀ h₀) m n (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) hSg (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v)))]

  rw [LanglandsTunnell.setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) hwre (fun t u Y : ℝ => ((|t| : ℝ) : ℂ) ^ (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) * (Real.exp (-(2 * Real.pi * |t|)) : ℂ) *
            (((u⁻¹ : ℝ) : ℂ) ^ n * (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) u * ((|u| : ℝ) : ℂ) ^ (-(uR w₀ h₀ + 2)) * ((Y : ℝ) : ℂ) ^ (P₂.centralExponent - uR w₀ h₀)) *
            (Real.exp (-(Real.pi * ((Y ^ 2)⁻¹ + t ^ 2 * Y ^ 2 + u ^ 2))) : ℂ) *
            (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (u / Y) *
            (∫ z : ℝ, (((t * Y - Y⁻¹ + u : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) hKm hInt]

  rw [LanglandsTunnell.setIntegral_dualFibres_eq_oneSided_torusPair (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) (-(uR w₀ h₀ + 2)) (P₂.centralExponent - uR w₀ h₀) ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) m n (fun y : ℝ => if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) hSg (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) hFib2.1]

  rw [hBACK.1, hBACK.2]

  have hI : (∫ v in Set.Ioi (0 : ℝ), (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (-v) * ((v : ℝ) : ℂ) ^ ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1) *
        (Real.exp (-(2 * Real.pi * v)) : ℂ))
      = ∫ v in Set.Ioi (0 : ℝ), D.W (ArchR.diagOne v) * ((v : ℝ) : ℂ) ^ (s - uP - P₂.centralExponent + (m : ℂ) / 2 - 2) *
        (Real.exp (-(2 * Real.pi * v)) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    beta_reduce
    rw [haR, show (-1 : ℝ) * -v = v by ring,
      show ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1 : ℂ) = s - uP - P₂.centralExponent + (m : ℂ) / 2 - 2 by rw [hcP, hm]; push_cast; ring]
  rw [hI, mul_zero, add_zero,
    show (((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) + (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) + (n : ℂ) - (-(uR w₀ h₀ + 2)) - (P₂.centralExponent - uR w₀ h₀) - 1) + 1 : ℂ) = 2 * s - P.centralExponent - P₂.centralExponent + (n : ℂ) + 1 by ring,
    show ((s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) - (P₂.centralExponent - uR w₀ h₀) - 1 - (-(P₂.centralExponent - uR w₀ h₀) - 2) : ℂ) = s - uR w₀ h₀ - uP + (m : ℂ) / 2 by rw [hcP, hm]; push_cast; ring,
    show (if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign (-1 : ℝ) : ℝ) : ℂ)) = (-1 : ℂ) ^ (aR w₀ h₀).val from Sg_neg_one (aR w₀ h₀),
    show (-2 : ℂ) ^ m = (-1 : ℂ) ^ m * (2 : ℂ) ^ m by rw [← mul_pow]; norm_num, pow_add, pow_add]
  ring

end S_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3 (solution)
