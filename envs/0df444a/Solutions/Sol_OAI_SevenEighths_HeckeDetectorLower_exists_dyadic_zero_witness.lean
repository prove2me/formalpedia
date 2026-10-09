-- Prove2me | solution 1 for OAI.SevenEighths.HeckeDetectorLower.exists_dyadic_zero_witness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:52:19.613455+00:00
-- url     : https://prove2.me/submissions/56461881-687d-4c35-9cbf-6909413ea608

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016
import Theorems.Thm_OAI_SevenEighths_GammaZeroDetector_shifted_original_growth

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace DyadicTransfer

theorem partial_partition (φ : ℝ → ℂ) (x : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1),
      annularCutoff φ (x / (2 : ℝ) ^ k)) =
      φ (x / (2 : ℝ) ^ K) - φ (2 * x) := by
  induction K with
  | zero =>
      simp [annularCutoff]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold annularCutoff
      have hpow : (2 : ℝ) ^ (K + 1) ≠ 0 := by positivity
      have hshift : 2 * (x / (2 : ℝ) ^ (K + 1)) = x / (2 : ℝ) ^ K := by
        rw [pow_succ]
        field_simp
      rw [hshift]
      ring

end DyadicTransfer

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace VerticalContourShift
open MeasureTheory Filter Set
open scoped Topology

theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert (preTransparency := .instances) horizontal_integral_tendsto_zero g a b C hab hg using 1 ;
      simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      apply (hdiff z ?_ ?_).differentiableWithinAt
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.1
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.2
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

end VerticalContourShift

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorPresentation
namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

end SevenEighths

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.VerticalContourShift
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicGammaExponential
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

lemma norm_Gamma_le_real (z : ℂ) (hz : 0<z.re) :
    ‖Complex.Gamma z‖≤Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀x∈Set.Icc a b,Real.Gamma x≤C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx=>ha.trans_le hx.1)
  obtain ⟨C,hC⟩:=(isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

end CubicGammaExponential

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open Filter MeasureTheory
open scoped Classical BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem coefficient_norm_le (χ : Character) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact idealCoeff_norm_le_one χ I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (idealCoeff_norm_le_one χ I)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GammaZeroDetector
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex

namespace SevenEighths.GammaZeroDetector

theorem gamma_shift (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Gamma (z + n) = Gamma z * ∏ k ∈ Finset.range n, (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z + n ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, natCast_im, add_zero, zero_im] at this
      exact hz this
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hn, ih, Finset.prod_range_succ]
    ring

theorem gamma_shift_norm_lower (z : ℂ) (n : ℕ) :
    |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ Finset.range n, |z.im| := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro k _
      simpa using Complex.abs_im_le_norm (z + k)

theorem gamma_power_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := CubicGammaExponential.real_Gamma_compact_bound
    (a + n) (b + n) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro z hza hzb hzi
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hzi
  have hzre : 0 < (z + n).re := by simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Gamma z‖ :=
      mul_le_mul_of_nonneg_right (gamma_shift_norm_lower z n) (norm_nonneg _)
    _ = ‖Gamma (z + n)‖ := by rw [gamma_shift z hzne n, norm_mul, mul_comm]
    _ ≤ Real.Gamma (z + n).re := CubicGammaExponential.norm_Gamma_le_real _ hzre
    _ ≤ C := hbound _ (by simp only [add_re, natCast_re]; constructor <;> linarith)

theorem gamma_rapid_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C₁, hC₁, hlarge⟩ := gamma_power_bound a b ha n
  obtain ⟨C₀, hC₀, hsmall⟩ := CubicGammaExponential.real_Gamma_compact_bound a b ha
  refine ⟨2 ^ n * (C₀ + C₁), by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · have hp : (1 + |z.im|) ^ n ≤ 2 ^ n * |z.im| ^ n := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ n * |z.im| ^ n) * ‖Gamma z‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ n * C₁ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlarge z hza hzb ht) (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have hg : ‖Gamma z‖ ≤ C₀ :=
      (CubicGammaExponential.norm_Gamma_le_real z (ha.trans_le hza)).trans (hsmall z.re ⟨hza,hzb⟩)
    have hp : (1 + |z.im|) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
    calc
      _ ≤ 2 ^ n * C₀ := mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; linarith

theorem gamma_differentiableAt_right {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  have h := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem cancelledKernel_eq_literal {f g : ℂ → ℂ} {Y : ℝ} (hf0 : f 0 = 0)
    {z : ℂ} (hz : z ≠ 0) : cancelledKernel f g Y z = literalKernel f g Y z := by
  unfold cancelledKernel literalKernel
  rw [Gamma_add_one z hz, dslope_of_ne f hz]
  simp only [slope, sub_zero, hf0, smul_eq_mul, vsub_eq_sub]
  field_simp

theorem dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 0) := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr hf.differentiableOn

theorem cancelledKernel_differentiableAt {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {Y : ℝ} (hY : 0 < Y) {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ (cancelledKernel f g Y) z := by
  exact ((((differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).mul
    ((gamma_differentiableAt_right (by change 0 < z.re + 1; linarith)).comp z
      (differentiableAt_id.add_const 1))).mul (dslope_entire hf z)).mul (hg z))

theorem literalKernel_norm (f g : ℂ → ℂ) {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    ‖literalKernel f g Y z‖ = Y ^ z.re * ‖Gamma z‖ * ‖f z‖ * ‖g z‖ := by
  simp only [literalKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]

theorem cancelledKernel_large_height_bound {f g : ℂ → ℂ} (hf0 : f 0 = 0)
    {Y a b A B G : ℝ} (hY : 1 ≤ Y) (_ha : -1 < a) (n : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hG : 0 ≤ G)
    (hgamma : ∀ z : ℂ, a + 1 ≤ z.re → z.re ≤ b + 1 →
      (1 + |z.im|) ^ (n + 2) * ‖Gamma z‖ ≤ G)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) (hzi : 1 ≤ |z.im|) :
    ‖cancelledKernel f g Y z‖ ≤ (Y ^ b * G * A * B) / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzi
  have hnorm : 1 ≤ ‖z‖ := hzi.trans (Complex.abs_im_le_norm z)
  have hΓ : ‖Gamma z‖ ≤ ‖Gamma (z + 1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hnorm
  have hga := hgamma (z + 1) (by simpa using hza) (by simpa using hzb)
  simp only [add_im, one_im, add_zero] at hga
  have hweighted : (1 + z.im ^ 2) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) ≤ G := by
    calc
      _ ≤ (1 + |z.im|) ^ 2 * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by
        gcongr
        nlinarith [sq_abs z.im, abs_nonneg z.im]
      _ = (1 + |z.im|) ^ (n + 2) * ‖Gamma (z + 1)‖ := by rw [pow_add]; ring
      _ ≤ _ := hga
  have hgdiv : ‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n ≤ G / (1 + z.im ^ 2) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hweighted)
  rw [cancelledKernel_eq_literal hf0 hz0, literalKernel_norm f g hY0]
  calc
    _ ≤ Y ^ b * ‖Gamma (z + 1)‖ * (A * (1 + |z.im|) ^ n) * B := by
      gcongr
      · exact hf z hza hzb
      · exact hg z hza hzb
    _ = (Y ^ b * A * B) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by ring
    _ ≤ (Y ^ b * A * B) * (G / (1 + z.im ^ 2)) :=
      mul_le_mul_of_nonneg_left hgdiv (by positivity)
    _ = _ := by ring

theorem cancelledKernel_strip_bound {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨G,hG,hgamma⟩ := gamma_rapid_bound (a+1) (b+1) (by linarith) (n+2)
  let S : Set ℂ := Icc a b ×ℂ Icc (-1 : ℝ) 1
  have hc : ContinuousOn (cancelledKernel f g Y) S := by
    intro z hz
    exact (cancelledKernel_differentiableAt hf hg hY0 (ha.trans_le hz.1.1)).continuousAt.continuousWithinAt
  have hw : ContinuousOn (fun z : ℂ => (1 + z.im ^ 2) * ‖cancelledKernel f g Y z‖) S :=
    (continuous_const.add (continuous_im.pow 2)).continuousOn.mul hc.norm
  obtain ⟨K,hK⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact S).bddAbove_image hw
  refine ⟨|K| + Y ^ b * G * A * B + 1, by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · apply (cancelledKernel_large_height_bound hf0 hY ha n hA hB hG.le hgamma
      hfbound hgbound hza hzb ht).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [abs_nonneg K]
  · have hzS : z ∈ S := ⟨⟨hza,hzb⟩, abs_le.mp (le_of_lt (lt_of_not_ge ht))⟩
    have hb := hK (Set.mem_image_of_mem _ hzS)
    apply (le_div_iff₀ (by positivity : 0 < 1 + z.im ^ 2)).mpr
    have hnonneg : 0 ≤ Y ^ b * G * A * B := by positivity
    nlinarith [le_abs_self K]

theorem cancelledKernel_vertical_integrable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {Y a b C x : ℝ}
    (hY : 0 < Y) (ha : -1 < a) (hx : x ∈ Icc a b)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2)) :
    Integrable (fun t : ℝ => cancelledKernel f g Y ((x : ℂ) + t * I)) := by
  have hc : Continuous (fun t : ℝ => cancelledKernel f g Y ((x : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (cancelledKernel_differentiableAt hf hg hY (by simpa using ha.trans_le hx.1)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro t
  simpa [div_eq_mul_inv] using hbound ((x : ℂ) + t * I) (by simpa using hx.1) (by simpa using hx.2)

theorem cancelledKernel_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (hab : a ≤ b) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    (∫ t : ℝ, cancelledKernel f g Y ((a : ℂ) + t * I)) =
      ∫ t : ℝ, cancelledKernel f g Y ((b : ℂ) + t * I) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨C,_,hbnd⟩ := cancelledKernel_strip_bound hf hg hf0 hY ha n hA hB hfbound hgbound
  apply VerticalContourShift.integral_eq_of_strip_decay _ a b C hab
    (fun z hz _ => cancelledKernel_differentiableAt hf hg hY0 (ha.trans_le hz))
    (cancelledKernel_vertical_integrable hf hg hY0 ha ⟨le_rfl,hab⟩ hbnd)
    (cancelledKernel_vertical_integrable hf hg hY0 ha ⟨hab,le_rfl⟩ hbnd)
  intro x hx t
  simpa using hbnd ((x : ℂ) + t * I) (by simpa using hx.1) (by simpa using hx.2)

theorem literal_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y A B : ℝ}
    (hY : 1 ≤ Y) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) :
    (∫ t : ℝ, literalKernel f g Y ((2 : ℂ) + t * I)) =
      ∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ) + t * I) := by
  have h := cancelledKernel_contour_shift hf hg hf0 hY (by norm_num : (-1 : ℝ) < -(1/4))
    (by norm_num : (-(1/4) : ℝ)≤2) n hA hB hfbound hgbound
  have he (x : ℝ) (hx : x ≠ 0) (t : ℝ) :
      cancelledKernel f g Y ((x : ℂ) + t * I) = literalKernel f g Y ((x : ℂ) + t * I) := by
    apply cancelledKernel_eq_literal hf0
    intro hz
    apply hx
    simpa using congrArg Complex.re hz
  simp only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] at h
  have h2 (t : ℝ) := he 2 (by norm_num) t
  have hq (t : ℝ) := he (-(1/4)) (by norm_num) t
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] at h2 hq
  simpa only [h2, hq] using h.symm

theorem gamma_negative_quarter_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ t : ℝ,
      (1 + t ^ 2) * (1 + |t|) ^ n * ‖Gamma ((-(1/4) : ℂ) + t * I)‖ ≤ G := by
  obtain ⟨C,hC,hgamma⟩ := gamma_rapid_bound (3/4) (3/4) (by norm_num) (n+2)
  refine ⟨4*C, by positivity, ?_⟩
  intro t
  let z : ℂ := (-(1/4) : ℂ) + t * I
  have hzre : z.re = -(1/4) := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzre
  have hn : (1/4 : ℝ) ≤ ‖z‖ := by simpa only [hzre, abs_neg, abs_of_pos (by norm_num : (0 : ℝ)<1/4)] using Complex.abs_re_le_norm z
  have hΓ : ‖Gamma z‖ ≤ 4 * ‖Gamma (z+1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    nlinarith [norm_nonneg (Gamma z)]
  have hbound := hgamma (z+1) (by norm_num [hzre]) (by norm_num [hzre])
  simp only [add_im, one_im, add_zero, hzim] at hbound
  have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
  change (1+t^2)*(1+|t|)^n*‖Gamma z‖ ≤ 4*C
  calc
    _ ≤ (1+|t|)^2*(1+|t|)^n*(4*‖Gamma (z+1)‖) := by gcongr
    _ = 4*((1+|t|)^(n+2)*‖Gamma (z+1)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)

theorem literal_shifted_integral_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      0 < Y → 0 ≤ A → 0 ≤ B →
      (∀ t : ℝ, ‖f ((-(1/4) : ℂ)+t*I)‖ ≤ A*(1+|t|)^n) →
      (∀ t : ℝ, ‖g ((-(1/4) : ℂ)+t*I)‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ)+t*I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G,hG,hgamma⟩ := gamma_negative_quarter_bound n
  refine ⟨G,hG,?_⟩
  intro f g Y A B hY hA hB hf hg
  have hbound (t : ℝ) :
      ‖literalKernel f g Y ((-(1/4) : ℂ)+t*I)‖ ≤
        (G*A*B*Y^(-(1/4 : ℝ)))*(1+t^2)⁻¹ := by
    have hga : (1+|t|)^n*‖Gamma ((-(1/4) : ℂ)+t*I)‖ ≤ G/(1+t^2) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hgamma t])
    rw [literalKernel_norm f g hY]
    have hzre : (((-(1/4) : ℂ)+t*I).re) = (-(1/4) : ℝ) := by norm_num
    rw [hzre]
    change Y^(-(1/4 : ℝ))*‖Gamma ((-(1/4) : ℂ)+t*I)‖*
      ‖f ((-(1/4) : ℂ)+t*I)‖*‖g ((-(1/4) : ℂ)+t*I)‖ ≤ _
    calc
      _ ≤ Y^(-(1/4 : ℝ))*‖Gamma ((-(1/4) : ℂ)+t*I)‖*(A*(1+|t|)^n)*B := by gcongr; exact hf t; exact hg t
      _ = (A*B*Y^(-(1/4 : ℝ)))*((1+|t|)^n*‖Gamma ((-(1/4) : ℂ)+t*I)‖) := by ring
      _ ≤ (A*B*Y^(-(1/4 : ℝ)))*(G/(1+t^2)) := mul_le_mul_of_nonneg_left hga (by positivity)
      _ = _ := by ring
  have hint := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (G*A*B*Y^(-(1/4 : ℝ)))) (ae_of_all _ hbound)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hint
  convert (preTransparency := .instances) hint using 1; ring

theorem literal_detector_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      Differentiable ℂ f → Differentiable ℂ g → f 0 = 0 →
      1 ≤ Y → 0 ≤ A → 0 ≤ B →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A*(1+|z.im|)^n) →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((2 : ℂ)+t*I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G,hG,hbound⟩ := literal_shifted_integral_bound n
  refine ⟨G,hG,?_⟩
  intro f g Y A B hf hg hf0 hY hA hB hfb hgb
  rw [literal_contour_shift hf hg hf0 hY n hA hB hfb hgb]
  apply hbound f g Y A B (by linarith) hA hB
  · intro t; simpa using hfb ((-(1/4) : ℂ)+t*I) (by norm_num) (by norm_num)
  · intro t; exact hgb _ (by norm_num) (by norm_num)

open HeckeFamily

theorem mem_cutoffSet {D : ℝ} (hD : 0 ≤ D) {J : Ideal O} :
    J ∈ cutoffSet D ↔ J ≠ 0 ∧ (J.absNorm : ℝ) ≤ 2*D := by
  rw [cutoffSet, ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨?_, ?_⟩
    · intro h; simp [h] at hp
    · exact (by exact_mod_cast hb : (J.absNorm : ℝ) ≤ ⌊2*D⌋₊).trans
        (Nat.floor_le (by positivity))
  · rintro ⟨hp, hb⟩
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp),
      Nat.le_floor hb⟩

theorem cutoffTerm_entire (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) :
    Differentiable ℂ (cutoffTerm χ V D J) := by
  by_cases hJ : J = 0
  · subst J
    have he : cutoffTerm χ V D 0 = fun _ : ℂ => 0 := funext (cutoffTerm_zero χ V D)
    rw [he]
    exact differentiable_const 0
  · have hn : (J.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hJ
    unfold cutoffTerm
    simp only [CubicEisenstein.fullIdealWeight, if_neg hJ]
    exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem cutoff_entire (χ : Character) (V : ℝ → ℂ) (D : ℝ) :
    Differentiable ℂ (cutoff χ V D) := by
  exact Differentiable.fun_sum fun J _ => cutoffTerm_entire χ V D J

theorem cutoffTerm_norm_le (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) (J : Ideal O) :
    ‖cutoffTerm χ V D J s‖ ≤ 1 := by
  by_cases hJ : J = 0
  · subst J
    rw [cutoffTerm_zero, norm_zero]
    norm_num
  · have hnorm : 1 ≤ (J.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
    have hw : ‖CubicEisenstein.fullIdealWeight s J‖ ≤ 1 := by
      rw [CubicEisenstein.fullIdealWeight, if_neg hJ]
      have hn : 0 < (J.absNorm : ℝ) := by linarith
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn, neg_re]
      exact (Real.rpow_le_rpow_of_exponent_le hnorm (neg_nonpos.mpr hs)).trans_eq (Real.rpow_zero _)
    rw [cutoffTerm, norm_mul, norm_mul]
    calc
      _ ≤ (1 : ℝ)*1*1 := by gcongr; exact HeckeDyadic.coefficient_norm_le χ true J; exact hV _
      _ = 1 := by norm_num

theorem cutoff_norm_le (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 1 ≤ D)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖cutoff χ V D s‖ ≤ 256*D := by
  have hcount := DescentFiberCost.finite_ideal_count_real (cutoffSet D) (2*D) (by linarith)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).1)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).2)
  calc
    _ ≤ ∑ J ∈ cutoffSet D, ‖cutoffTerm χ V D J s‖ := norm_sum_le _ _
    _ ≤ ∑ _J ∈ cutoffSet D, (1 : ℝ) := Finset.sum_le_sum (fun J _ => cutoffTerm_norm_le χ V D hV hs J)
    _ = ((cutoffSet D).card : ℝ) := by simp
    _ ≤ 256*D := by linarith

theorem detector_integral_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (χ : Character), χ.residue ≠ 1 →
      ∀ (V : ℝ → ℂ), (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (D Y : ℝ),
      1 ≤ D → 1 ≤ Y → ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 →
      ‖detectorIntegral χ V D Y ρ‖ ≤
        K*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2*D*Y^(-(1/4 : ℝ)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  obtain ⟨G,hG,hgamma⟩ := literal_detector_bound 2
  refine ⟨128*G*C, by positivity, ?_⟩
  intro χ hχ V hV D Y hD hY ρ hρ hzero
  have hb := hgamma (fun z => LFunction χ (ρ+z)) (fun z => cutoff χ V D (ρ+z))
    Y (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (256*D)
    ((LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (by simp only [add_re]; linarith))
  change ‖∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)‖ ≤ _ at hb
  rw [detectorIntegral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (by positivity))).trans_eq
  field_simp
  ring

theorem detector_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (R θ : ℝ), 0 ≤ R → 0 ≤ θ →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (U D : ℝ), 1 ≤ U →
      1 ≤ D → D ≤ U^(3/2 : ℝ) → (χ.modulus.absNorm : ℝ) ≤ R*U →
      ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ ≤ (K*R^2)*U^(-(3/2 : ℝ)+2*θ) := by
  obtain ⟨K,hK,hbound⟩ := detector_integral_bound
  refine ⟨16*K, by positivity, ?_⟩
  intro R θ hR hθ χ hχ V hV U D hU hD hDU hQ ρ hρ hzero ht
  have hU0 : 0 < U := by linarith
  have huθ : 1 ≤ U^θ := Real.one_le_rpow hU hθ
  have hheight : 3+|ρ.im| ≤ 4*U^θ := by linarith
  have hY : 1 ≤ U^20 := one_le_pow₀ hU
  have he : (U^20)^(-(1/4 : ℝ)) = U^(-5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    norm_num
  have hb := hbound χ hχ V hV D (U^20) hD hY ρ hρ hzero
  rw [he] at hb
  calc
    _ ≤ K*(R*U)^2*(4*U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ) := by
      apply hb.trans; gcongr
    _ = (16*K*R^2)*(U^(2 : ℝ)*(U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ)) := by
      rw [Real.rpow_two]; ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hU0.le, ← Real.rpow_add hU0,
        ← Real.rpow_add hU0, ← Real.rpow_add hU0]
      congr 2
      ring

theorem detector_uniform_small (R θ ε : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ D : ℝ, 1 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ < ε := by
  obtain ⟨K,hK,hbound⟩ := detector_power_bound
  have ht : Tendsto (fun U : ℝ => (K*R^2)*U^(-(3/2 : ℝ)+2*θ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < (3/2 : ℝ)-2*θ)).const_mul (K*R^2)
    simpa [neg_sub, sub_eq_add_neg, add_comm] using h
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ hχ V hV D hD hDU hQ ρ hρ hzero ht
  exact (hbound R θ hR hθ χ hχ V hV U D hU hD hDU hQ ρ hρ hzero ht).trans_lt (hU₀ U hU₀')

end SevenEighths.GammaZeroDetector

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessArithmetic
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessArithmetic
open HeckeFamily UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O

theorem fiber_norm_le {I : Ideal O} (hI : I ≠ 0) (p : MulFiber I) :
    Ideal.absNorm p.val.1 ≤ Ideal.absNorm I := by
  apply Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  exact map_dvd Ideal.absNorm ⟨p.val.2, p.property.symm⟩

theorem cutoffCoefficient_small (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (I : Ideal O) (hI : (Ideal.absNorm I : ℝ) ≤ D) :
    cutoffCoefficient V D I = if I = 1 then 1 else 0 := by
  by_cases hI0 : I = 0
  · simp [cutoffCoefficient, hI0]
  · rw [cutoffCoefficient, if_neg hI0]
    have heq : (fun p : MulFiber I => (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)) =
        (fun p : MulFiber I => (moebius p.val.1 : ℂ)) := by
      funext p
      rw [hV _ (div_nonneg (by positivity) hD.le) ((div_le_one hD).mpr ?_), mul_one]
      exact (by exact_mod_cast fiber_norm_le hI0 p : (Ideal.absNorm p.val.1 : ℝ) ≤ Ideal.absNorm I).trans hI
    rw [heq]
    exact mulFiber_moebius_sum I hI0

theorem cutoffCoefficient_tail (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (I : Ideal O) :
    cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      cutoffCoefficient V D I - if I = 1 then 1 else 0 := by
  have hD0 : 0 < D := by linarith
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ D
  · rw [cutoffCoefficient_small V D hD0 hV I hI]
    by_cases hI1 : I = 1
    · subst I
      simp only [map_one, Nat.cast_one, mul_one, ite_true, one_mul, sub_self]
      rw [hV _ (by positivity) ((div_le_one hD0).mpr hD), sub_self]
    · simp only [hI1, ite_false, zero_mul, sub_zero]
  · have hv : V (2 * (Ideal.absNorm I : ℝ) / D) = 0 := by
      apply hVzero
      apply (le_div_iff₀ hD0).mpr
      linarith [lt_of_not_ge hI]
    have hI1 : I ≠ 1 := by
      intro hh
      subst I
      simp only [map_one, Nat.cast_one] at hI
      linarith
    rw [hv, sub_zero, mul_one, if_neg hI1, sub_zero]

theorem weighted_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) *
      IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2)) =
      cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I := by
  by_cases hI : I = 0
  · subst I
    have hz (p : MulFiber 0) : IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2) = 0 := by
      rw [p.property, map_zero]
    simp [hz, cutoffCoefficient]
  · rw [cutoffCoefficient, if_neg hI, ← tsum_mul_right]
    apply tsum_congr
    intro p
    rw [p.property]

theorem exponentialTerm_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ) (I : Ideal O) :
    exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      exponentialTerm χ V D s Y I - if I = 1 then Complex.exp (-1 / (Y : ℂ)) else 0 := by
  have h := cutoffCoefficient_tail V D hD hV hVzero I
  unfold exponentialTerm
  calc
    _ = (cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) *
        IdealEuler.weighted (idealCoeff χ) s I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ)) := by ring
    _ = _ := by
      rw [h]
      by_cases hI : I = 1
      · subst I
        simp only [ite_true, map_one, Nat.cast_one, Complex.ofReal_one, mul_one]
        ring
      · simp only [hI, ite_false, sub_zero]

theorem exponential_sum_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ)
    (hsum : Summable (exponentialTerm χ V D s Y)) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1 / (Y : ℂ)) := by
  simp_rw [exponentialTerm_tail χ V D hD hV hVzero s Y]
  rw [hsum.tsum_sub ((hasSum_ite_eq (1 : Ideal O) (Complex.exp (-1 / (Y : ℂ)))).summable)]
  simp only [tsum_ite_eq]

end SevenEighths.HeckeDetectorWitnessArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GammaDetectorExpansion
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace SevenEighths.GammaDetectorExpansion
open GammaZeroDetector HeckeFamily

theorem gamma_line_integrable : Integrable (fun t : ℝ => Gamma (line t)) := by
  obtain ⟨C,hC,hbound⟩ := gamma_rapid_bound 2 2 (by norm_num) 2
  apply (integrable_inv_one_add_sq.const_mul C).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    exact fun t => (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp
      (by unfold line; fun_prop)
  · filter_upwards [] with t
    have hb := hbound (line t) (by simp) (by simp)
    simp only [line_im] at hb
    have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [norm_nonneg (Gamma (line t))]

theorem gamma_mellin_inverse {x : ℝ} (hx : 0 < x) :
    ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t : ℝ, (x : ℂ)^(-line t)*Gamma (line t)) = Complex.exp (-(x : ℂ)) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ)
  have hm (s : ℂ) (hs : 0 < s.re) : mellin f s = Gamma s := by
    rw [Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  have hf : MellinConvergent f (2 : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (GammaIntegral_convergent (by norm_num : 0 < (2 : ℂ).re))
  have hline (t : ℝ) : mellin f (line t) = Gamma (line t) := hm _ (by simp)
  have hv : VerticalIntegrable (mellin f) 2 := by
    change Integrable (fun t : ℝ => mellin f (line t))
    simpa only [hline] using gamma_line_integrable
  have hi := mellinInv_mellin_eq 2 f hx hf hv (by unfold f; fun_prop)
  change (1/(2*Real.pi)) • (∫ t : ℝ, (x : ℂ)^(-line t) • mellin f (line t)) = f x at hi
  simp_rw [hline] at hi
  simp only [smul_eq_mul, f, ofReal_exp, ofReal_neg] at hi
  convert (preTransparency := .instances) hi using 1; simp [one_div, Complex.real_smul]

theorem gammaTerm_separate (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    gammaTerm a N ρ Y t = (a*(N : ℂ)^(-ρ))*
      (((N/Y : ℝ) : ℂ)^(-line t)*Gamma (line t)) := by
  rw [gammaTerm, neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hN.ne'),
    ofReal_div, div_cpow_ofReal_nonneg hN.le hY.le, cpow_neg (Y : ℂ), div_inv_eq_mul]
  ring

theorem gammaTerm_integral (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    ((2*Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, gammaTerm a N ρ Y t) =
      a*(N : ℂ)^(-ρ)*Complex.exp (-(N : ℂ)/(Y : ℂ)) := by
  simp_rw [gammaTerm_separate a hN hY ρ]
  rw [integral_const_mul]
  calc
    _ = (a*(N : ℂ)^(-ρ))*(((2*Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, ((N/Y : ℝ) : ℂ)^(-line t)*Gamma (line t)) := by ring
    _ = _ := by rw [gamma_mellin_inverse (div_pos hN hY)]; push_cast; rw [neg_div]

theorem gammaTerm_norm (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y)
    (ρ : ℂ) (t : ℝ) :
    ‖gammaTerm a N ρ Y t‖ = (Y^2 * (‖a‖*N^(-(ρ.re+2)))) * ‖Gamma (line t)‖ := by
  simp only [gammaTerm, norm_mul, norm_cpow_eq_rpow_re_of_pos hY,
    norm_cpow_eq_rpow_re_of_pos hN, neg_re, add_re, line_re, Real.rpow_two]
  ring

theorem gammaTerm_integrable (a : ℂ) {N Y : ℝ} (hN : 0 < N) (hY : 0 < Y) (ρ : ℂ) :
    Integrable (gammaTerm a N ρ Y) := by
  apply (gamma_line_integrable.norm.const_mul (Y^2*(‖a‖*N^(-(ρ.re+2))))).mono'
  · apply Continuous.aestronglyMeasurable
    have hl : Continuous line := by unfold line; fun_prop
    have hg : Continuous (fun t : ℝ => Gamma (line t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp hl.continuousAt
    have hy := (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hY.ne'))).continuous.comp hl
    have hn := (((differentiable_const ρ).add differentiable_id).neg.const_cpow
      (Or.inl (ofReal_ne_zero.mpr hN.ne'))).continuous.comp hl
    exact ((hy.mul hg).mul continuous_const).mul hn
  · exact ae_of_all _ (fun t => (gammaTerm_norm a hN hY ρ t).le)

theorem gamma_expansion {ι : Type*} [Countable ι] (a : ι → ℂ) (N : ι → ℝ)
    (hN : ∀ i, 0 ≤ N i) (hzero : ∀ i, N i = 0 → a i = 0)
    (ρ : ℂ) {Y : ℝ} (hY : 0 < Y)
    (hsum : Summable (fun i => ‖a i‖*(N i)^(-(ρ.re+2)))) :
    HasSum (fun i => a i*(N i : ℂ)^(-ρ)*Complex.exp (-(N i : ℂ)/(Y : ℂ)))
      (((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, ∑' i, gammaTerm (a i) (N i) ρ Y t) := by
  have hint (i : ι) : Integrable (gammaTerm (a i) (N i) ρ Y) := by
    by_cases hi : N i = 0
    · rw [hzero i hi]
      have he : gammaTerm 0 (N i) ρ Y = fun _ : ℝ => 0 := funext (gammaTerm_zero _ _ _)
      rw [he]
      exact integrable_zero ℝ ℂ volume
    · exact gammaTerm_integrable _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ
  have hnorm (i : ι) (t : ℝ) :
      ‖gammaTerm (a i) (N i) ρ Y t‖ =
        (Y^2*(‖a i‖*(N i)^(-(ρ.re+2))))*‖Gamma (line t)‖ := by
    by_cases hi : N i = 0
    · simp [hzero i hi]
    · exact gammaTerm_norm _ (lt_of_le_of_ne (hN i) (Ne.symm hi)) hY ρ t
  have hnormsum : Summable (fun i => ∫ t : ℝ, ‖gammaTerm (a i) (N i) ρ Y t‖) := by
    simp_rw [hnorm, integral_const_mul]
    convert (preTransparency := .instances) hsum.mul_left (Y^2*(∫ t : ℝ, ‖Gamma (line t)‖)) using 1
    funext i
    ring
  have hi := (hasSum_integral_of_summable_integral_norm hint hnormsum).mul_left
    (((2*Real.pi : ℝ) : ℂ)⁻¹)
  have he (i : ι) : (((2*Real.pi : ℝ) : ℂ)⁻¹) * (∫ t : ℝ, gammaTerm (a i) (N i) ρ Y t) =
      a i*(N i : ℂ)^(-ρ)*Complex.exp (-(N i : ℂ)/(Y : ℂ)) := by
    by_cases hn : N i = 0
    · simp [hzero i hn]
    · exact gammaTerm_integral _ (lt_of_le_of_ne (hN i) (Ne.symm hn)) hY ρ
  simpa only [he] using hi

theorem cutoffTerm_weighted (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      V ((J.absNorm : ℝ)/D) * IdealEuler.weighted (idealCoeff χ) s J := by
  simp only [cutoffTerm, HeckeDyadic.coefficient, ite_true,
    IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  ring

theorem cutoffTerm_outside (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (J : Ideal O)
    (hJ : J ∉ cutoffSet D) : cutoffTerm χ V D J s = 0 := by
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_hasSum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    HasSum (fun J : Ideal O => cutoffTerm χ V D J s) (cutoff χ V D s) :=
  hasSum_sum_of_ne_finset_zero (cutoffTerm_outside χ V hD hV s)

theorem pairCoefficient_zero_norm (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (p : Ideal O × Ideal O) (hp : pairNorm p = 0) : pairCoefficient χ V D p = 0 := by
  have hn : (p.1*p.2).absNorm = 0 := by unfold pairNorm at hp; exact_mod_cast hp
  have hzero := Ideal.absNorm_eq_zero_iff.mp hn
  rw [pairCoefficient, hzero]
  rw [show (⊥ : Ideal O) = 0 from rfl, HeckeFamily.idealCoeff_zero, mul_zero]

theorem pairTerm_eq (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ)
    (p : Ideal O × Ideal O) :
    pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s) =
      cutoffTerm χ V D p.1 s * IdealEuler.weighted (idealCoeff χ) s p.2 := by
  rw [cutoffTerm_weighted]
  by_cases hp : p.1*p.2 = 0
  · have he : pairNorm p = 0 := by simp [pairNorm, hp]
    rw [pairCoefficient_zero_norm χ V D p he, zero_mul]
    rw [mul_assoc, ← map_mul, hp, map_zero, mul_zero]
  · rw [mul_assoc, ← map_mul]
    simp only [pairCoefficient, pairNorm, Complex.ofReal_natCast,
      IdealEuler.weighted, IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      CubicEisenstein.fullIdealWeight, if_neg hp]
    ring

theorem pairTerm_summable_norm (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)‖) := by
  simpa only [pairTerm_eq] using
    (cutoffTerm_hasSum χ V hD hV s).summable.norm.mul_norm
      (IdealEuler.weighted_summable_norm _ (idealCoeff_norm_le_one χ) s hs)

theorem pairSeries_eq (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 1 < s.re) :
    (∑' p : Ideal O × Ideal O, pairCoefficient χ V D p * (pairNorm p : ℂ)^(-s)) =
      cutoff χ V D s * LFunction χ s := by
  simp_rw [pairTerm_eq]
  rw [← tsum_mul_tsum_of_summable_norm (cutoffTerm_hasSum χ V hD hV s).summable.norm
    (IdealEuler.weighted_summable_norm _ (idealCoeff_norm_le_one χ) s hs)]
  rw [(cutoffTerm_hasSum χ V hD hV s).tsum_eq, LFunction_eq_series χ hs]
  rfl

theorem pairMajorant_summable (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re) :
    Summable (fun p : Ideal O × Ideal O =>
      ‖pairCoefficient χ V D p‖*(pairNorm p)^(-(ρ.re+2))) := by
  have h := pairTerm_summable_norm χ V hD hV (ρ+2) (by norm_num; linarith)
  apply h.congr
  intro p
  by_cases hp : pairNorm p = 0
  · simp [pairCoefficient_zero_norm χ V D p hp]
  · have hn : 0 < pairNorm p := lt_of_le_of_ne (by unfold pairNorm; positivity) (Ne.symm hp)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hn]
    simp only [neg_re, add_re]
    norm_num

theorem pairGamma_tsum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) {ρ : ℂ} (hρ : -1 < ρ.re)
    (Y t : ℝ) :
    (∑' p : Ideal O × Ideal O, gammaTerm (pairCoefficient χ V D p) (pairNorm p) ρ Y t) =
      detectorIntegrand χ V D Y ρ (line t) := by
  have hs : 1 < (ρ+line t).re := by simp only [add_re, line_re]; linarith
  calc
    _ = (Y : ℂ)^(line t)*Gamma (line t)*
        (∑' p : Ideal O × Ideal O, pairCoefficient χ V D p*(pairNorm p : ℂ)^(-(ρ+line t))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      unfold gammaTerm
      ring
    _ = _ := by rw [pairSeries_eq χ V hD hV _ hs]; unfold detectorIntegrand; ring

theorem detector_hasSum_pairs (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (pairExponential χ V D ρ Y) (detectorIntegral χ V D Y ρ) := by
  have h := gamma_expansion (pairCoefficient χ V D) pairNorm
    (fun p => by unfold pairNorm; positivity) (pairCoefficient_zero_norm χ V D)
    ρ hY (pairMajorant_summable χ V hD hV hρ)
  unfold pairExponential detectorIntegral
  simpa only [pairGamma_tsum χ V hD hV hρ, line] using h

theorem pairExponential_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (ρ : ℂ) (Y : ℝ) (J : Ideal O) :
    (∑' p : CompletedGauss.MulFiber J, pairExponential χ V D ρ Y p.val) =
      HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y J := by
  have he (p : CompletedGauss.MulFiber J) :
      pairExponential χ V D ρ Y p.val =
        ((UniqueFactorizationMonoid.moebius p.val.1 : ℂ)*V ((p.val.1.absNorm : ℝ)/D)*
          IdealEuler.weighted (idealCoeff χ) ρ (p.val.1*p.val.2))*
          Complex.exp (-((J.absNorm : ℝ) : ℂ)/(Y : ℂ)) := by
    rw [pairExponential, pairTerm_eq, cutoffTerm_weighted, mul_assoc _ _
      (IdealEuler.weighted (idealCoeff χ) ρ p.val.2), ← map_mul]
    congr 2
    rw [pairNorm, p.property]
  simp_rw [he]
  rw [tsum_mul_right, HeckeDetectorWitnessArithmetic.weighted_fiber]
  rfl

theorem detector_hasSum_convolution (χ : Character) (V : ℝ → ℂ) {D Y : ℝ}
    (hD : 0 < D) (hY : 0 < Y) (hV : ∀ x : ℝ, 2 ≤ x → V x = 0)
    {ρ : ℂ} (hρ : -1 < ρ.re) :
    HasSum (HeckeDetectorWitnessArithmetic.exponentialTerm χ V D ρ Y)
      (detectorIntegral χ V D Y ρ) := by
  have h := (detector_hasSum_pairs χ V hD hY hV hρ).tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun J : Ideal O => ∑' p : CompletedGauss.MulFiber J,
    pairExponential χ V D ρ Y p.val) _ at h
  simpa only [pairExponential_fiber] using h

end SevenEighths.GammaDetectorExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorPartition
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorPartition
open DyadicTransfer

theorem partition (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (n J : ℕ) (hn : 1 ≤ n) (hJ : (n : ℝ) ≤ (2 : ℝ)^J) :
    (∑ j ∈ Finset.range (J+1), annularCutoff V ((n : ℝ)/(2 : ℝ)^j)) = 1 := by
  rw [partial_partition]
  rw [hsmall _ (by positivity) ((div_le_one (by positivity)).mpr hJ)]
  rw [hlarge _ (by exact_mod_cast (show 2 ≤ 2*n by omega))]
  ring

theorem finite_pair_reassembly {A : Type*} (S : Finset A) (a : A → ℂ)
    (n m : A → ℕ) (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (J K : ℕ)
    (hn : ∀ p ∈ S, 1 ≤ n p ∧ (n p : ℝ) ≤ (2 : ℝ)^J)
    (hm : ∀ p ∈ S, 1 ≤ m p ∧ (m p : ℝ) ≤ (2 : ℝ)^K) :
    (∑ p ∈ S, a p) =
      ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), ∑ p ∈ S,
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
  symm
  calc
    _ = ∑ p ∈ S, ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1),
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
      calc
        _ = ∑ j ∈ Finset.range (J+1), ∑ p ∈ S, ∑ k ∈ Finset.range (K+1),
            a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
              annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp_rw [← Finset.mul_sum]
      rw [partition V hsmall hlarge (m p) K (hm p hp).1 (hm p hp).2]
      simp only [mul_one]
      rw [← Finset.mul_sum, partition V hsmall hlarge (n p) J (hn p hp).1 (hn p hp).2,
        mul_one]

theorem norm_le_last_scale (X : ℝ) (hX : 0 < X) : X ≤ (2 : ℝ)^(length X) := by
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hX).mp
    (Nat.le_ceil (Real.logb 2 X))
  simpa only [Real.rpow_natCast, length] using h

theorem length_bound (X : ℝ) (hX : 1 ≤ X) :
    (length X : ℝ) + 1 < Real.logb 2 X + 2 := by
  have hlog : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  have h := Nat.ceil_lt_add_one hlog
  change (⌈Real.logb 2 X⌉₊ : ℝ) + 1 < _
  linarith

theorem pair_scale_bounds (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (hterm : ∀ y : ℝ, 2 ≤ y → T y = 0)
    (x y D U : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hD : 0 < D) (hU : 0 < U)
    (j k : ℕ)
    (hj : annularCutoff V (x/(2 : ℝ)^j) ≠ 0)
    (hk : annularCutoff V (y/(2 : ℝ)^k) ≠ 0)
    (hfirst : V (x/D) ≠ 0)
    (hproduct : 1 - V (2*(x*y)/D) ≠ 0)
    (hterminal : T (x*y/U) ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨hjlo,hjhi⟩ := annular_support V hsmall hlarge x hx j hj
  obtain ⟨hklo,hkhi⟩ := annular_support V hsmall hlarge y hy k hk
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have hK : 0 < (2 : ℝ)^k := by positivity
  have hxd : x < 2*D := by
    by_contra h
    apply hfirst
    apply hlarge
    exact (le_div_iff₀ hD).mpr (le_of_not_gt h)
  have hprod : D < 2*(x*y) := by
    by_contra h
    apply hproduct
    rw [hsmall _ (by positivity) ((div_le_one hD).mpr (le_of_not_gt h))]
    ring
  have hxyU : x*y < 2*U := by
    by_contra h
    apply hterminal
    apply hterm
    exact (le_div_iff₀ hU).mpr (le_of_not_gt h)
  have hlo : (2 : ℝ)^j*(2 : ℝ)^k/4 < x*y := by
    have h1 := mul_lt_mul_of_pos_right hjlo (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hklo (show 0 < (2 : ℝ)^j/2 by positivity)
    nlinarith
  have hhi : x*y < 4*((2 : ℝ)^j*(2 : ℝ)^k) := by
    have h1 := mul_lt_mul_of_pos_right hjhi (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hkhi (show 0 < 2*(2 : ℝ)^j by positivity)
    nlinarith
  constructor
  · linarith
  constructor <;> linarith

theorem actual_pair_reassembly (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (D Y U X Z : ℝ) (hX : 0 < X) (hZ : 0 < Z) (s : ℂ)
    (S : Finset (Ideal HeckeFamily.O × Ideal HeckeFamily.O))
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      (Ideal.absNorm p.1 : ℝ) ≤ X ∧ (Ideal.absNorm p.2 : ℝ) ≤ Z) :
    (∑ p ∈ S, pairCoefficient χ V T D Y U s p) =
      ∑ j ∈ Finset.range (length X+1), ∑ k ∈ Finset.range (length Z+1), ∑ p ∈ S,
        pairCoefficient χ V T D Y U s p *
          annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k) := by
  apply finite_pair_reassembly S _ _ _ V hsmall hlarge
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).1),
      (hS p hp).2.2.1.trans (norm_le_last_scale X hX)⟩
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).2.1),
      (hS p hp).2.2.2.trans (norm_le_last_scale Z hZ)⟩

theorem exists_large_pair (J K : ℕ) (F : ℕ → ℕ → ℂ) :
    ∃ j ∈ Finset.range (J+1), ∃ k ∈ Finset.range (K+1),
      ‖∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), F j k‖ ≤
        ((J+1 : ℕ) : ℝ)*((K+1 : ℕ) : ℝ)*‖F j k‖ := by
  let S := (Finset.range (J+1)) ×ˢ (Finset.range (K+1))
  have hS : S.Nonempty := ⟨(0,0), by simp [S]⟩
  obtain ⟨p,hp,hmax⟩ := S.exists_max_image (fun p => ‖F p.1 p.2‖) hS
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hp
  refine ⟨p.1,hj,p.2,hk,?_⟩
  calc
    _ = ‖∑ q ∈ S, F q.1 q.2‖ := by rw [Finset.sum_product]
    _ ≤ ∑ q ∈ S, ‖F q.1 q.2‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, ‖F p.1 p.2‖ := Finset.sum_le_sum (fun q hq => hmax q hq)
    _ = _ := by simp [S, Finset.card_product, mul_assoc]

end SevenEighths.HeckeDetectorPartition

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorTail
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorTail
open HeckeFamily HeckeDetectorWitnessArithmetic CompletedGauss
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma exponential_cubic_bound (x Y : ℝ) (hx : 0 < x) (hY : 0 < Y) :
    x * Real.exp (-x/Y) ≤ 6*Y^3/x^2 := by
  have he := Real.pow_div_factorial_le_exp (x/Y) (show 0 ≤ x/Y by positivity) 3
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at he
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(x/Y))).le
  have hex : Real.exp (x/Y)*Real.exp (-(x/Y))=1 := by rw [←Real.exp_add]; simp
  rw [hex] at hh
  have hb : (x/Y)^3*Real.exp (-(x/Y)) ≤ 6 := by nlinarith
  calc
    _ = (Y^3/x^2)*((x/Y)^3*Real.exp (-(x/Y))) := by
      rw [neg_div]
      field_simp
    _ ≤ (Y^3/x^2)*6 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

lemma divisor_count (I : Ideal O) (hI : I ≠ 0) :
    ((idealDivisors I).card : ℝ) ≤ 128*(Ideal.absNorm I : ℝ) := by
  apply DescentFiberCost.finite_ideal_count_real
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  · intro J hJ
    exact ne_zero_of_dvd_ne_zero hI ((mem_idealDivisors hI).mp hJ)
  · intro J hJ
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm ((mem_idealDivisors hI).mp hJ))

theorem cutoffCoefficient_bound (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D : ℝ) (I : Ideal O) :
    ‖cutoffCoefficient V D I‖ ≤ 128*B*(Ideal.absNorm I : ℝ) := by
  by_cases hI : I = 0
  · simp [cutoffCoefficient,hI]
  rw [cutoffCoefficient,if_neg hI]
  let e := mulFiberDivisorEquiv I hI
  have he : (∑' p : MulFiber I, (moebius p.val.1 : ℂ)*V ((Ideal.absNorm p.val.1 : ℝ)/D)) =
      ∑' J : {J : Ideal O // J ∈ idealDivisors I},
        (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D) :=
    e.tsum_eq (fun J => (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D))
  rw [he,tsum_fintype]
  calc
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I},
        ‖(moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D)‖ := norm_sum_le _ _
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I}, B := by
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one _)).trans (hV _)
    _ = ((idealDivisors I).card : ℝ)*B := by simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (divisor_count I hI) hB]

lemma norm_weight_two (I : Ideal O) (hI : I ≠ 0) :
    ‖CubicEisenstein.fullIdealWeight 2 I‖ = 1/(Ideal.absNorm I : ℝ)^2 := by
  rw [CubicEisenstein.fullIdealWeight,if_neg hI,Complex.cpow_neg,Complex.cpow_ofNat,
    norm_inv,norm_pow,Complex.norm_natCast]
  simp [one_div]

lemma weighted_norm_le_one (χ : Character) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖IdealEuler.weighted (idealCoeff χ) s I‖ ≤ 1 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, norm_zero]
    norm_num
  have hN : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  change ‖idealCoeff χ I*CubicEisenstein.fullIdealWeight s I‖ ≤ 1
  rw [norm_mul,CubicEisenstein.fullIdealWeight,if_neg hI]
  have hc : (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) := by norm_cast
  rw [hc,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ)<Ideal.absNorm I)]
  calc
    _ ≤ (1 : ℝ)*(Ideal.absNorm I : ℝ)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one χ I) (by positivity)
    _ ≤ 1 := by
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)

theorem exponentialTerm_bound (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖exponentialTerm χ V D s Y I‖ ≤
      (768*B*Y^3)*‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : I = 0
  · simp [hI,exponentialTerm,cutoffCoefficient,CubicEisenstein.fullIdealWeight]
  have hN : (0 : ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(Y : ℂ))‖ =
      Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [exponentialTerm,norm_mul,norm_mul,he,norm_weight_two I hI]
  calc
    _ ≤ (128*B*(Ideal.absNorm I : ℝ))*Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mul_le_mul (cutoffCoefficient_bound V B hB hV D I)
        (weighted_norm_le_one χ s hs I) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ (128*B)*(6*Y^3/(Ideal.absNorm I : ℝ)^2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (exponential_cubic_bound _ Y hN hY) (by positivity)
    _ = _ := by ring

theorem exponentialTerm_summable (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) : Summable (exponentialTerm χ V D s Y) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (768*B*Y^3)).of_norm_bounded (exponentialTerm_bound χ V B hB hV D Y hY s hs)

lemma cutoff_defect_bound (V : ℝ → ℂ) (B : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (x : ℝ) : ‖1-V x‖ ≤ 1+B :=
  (norm_sub_le _ _).trans (by simpa using add_le_add_left (hV x) 1)

lemma exponentialTerm_half (χ : Character) (V : ℝ → ℂ) (D Y : ℝ)
    (_hY : 0 < Y) (s : ℂ) (I : Ideal O) :
    exponentialTerm χ V D s Y I = exponentialTerm χ V D s (2*Y) I *
      Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))) := by
  unfold exponentialTerm
  rw [mul_assoc (cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I),
    ←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem terminalRemainder_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re)
    (I : Ideal O) :
    ‖terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ U
  · rw [terminalRemainder,hTone _ (by positivity) ((div_le_one hU).mpr hI)]
    simp only [sub_self,mul_zero,norm_zero]
    positivity
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ)))‖ ≤
      Real.exp (-U/(2*Y)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hc : (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))).re =
        -(Ideal.absNorm I : ℝ)/(2*Y) := by
      rw [show (2 : ℂ)*(Y : ℂ) = ((2*Y : ℝ) : ℂ) by push_cast; rfl,
        ←Complex.ofReal_neg,←Complex.ofReal_div,Complex.ofReal_re]
    rw [hc]
    exact div_le_div_of_nonneg_right (by linarith [lt_of_not_ge hI]) (by positivity)
  rw [terminalRemainder,exponentialTerm_half χ V D Y hY s I]
  simp only [norm_mul]
  have h1 := mul_le_mul
    (exponentialTerm_bound χ V B hB hV D (2*Y) (by positivity) s hs I) he
    (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul h1 (cutoff_defect_bound V B hV (2*(Ideal.absNorm I : ℝ)/D))
    (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul h2 (cutoff_defect_bound T BT hT ((Ideal.absNorm I : ℝ)/U))
    (norm_nonneg _) (by positivity)
  apply h3.trans_eq
  ring

theorem terminalRemainder_summable (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    Summable (terminalRemainder χ V T D Y U s) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))).of_norm_bounded
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)

theorem terminalRemainder_tsum_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∑' I, terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  have hsum := terminalRemainder_summable χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  rw [←tsum_mul_left]
  exact hsum.norm.tsum_le_tsum
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)
    ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left _)

theorem terminalRemainder_uniform_small (B BT ε : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character) (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ B) → (∀ x : ℝ, ‖T x‖ ≤ BT) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ (D : ℝ) (s : ℂ), 0 ≤ s.re →
      ‖∑' I, terminalRemainder χ V T D (U^20) (U^21) s I‖ < ε := by
  let C : ℝ := 6144*B*(1+B)*(1+BT)*(∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖)
  have ht : Tendsto (fun U : ℝ => C*(U^60*Real.exp (-U/2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 60 (1/2) (by norm_num)).const_mul C
    convert (preTransparency := .instances) h using 1
    · ext U
      rw [show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
      congr 2
      ring_nf
    · ring_nf
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ V T hV hT hTone D s hs
  have hUpos : 0 < U := by linarith
  have hb := terminalRemainder_tsum_bound χ V T B BT hB hBT hV hT hTone
    D (U^20) (U^21) (by positivity) (by positivity) s hs
  have he : -(U^21)/(2*U^20) = -U/2 := by
    rw [show U^21 = U^20*U by ring]
    field_simp
  have hp : (U^20)^3 = U^60 := by ring
  rw [he,hp] at hb
  have hC : (6144*B*U^60*(1+B)*(1+BT)*Real.exp (-U/2))*
      (∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖) = C*(U^60*Real.exp (-U/2)) := by
    dsimp [C]
    ring
  rw [hC] at hb
  exact hb.trans_lt (hU₀ U hU₀')

theorem exponential_sum_tail_unconditional (χ : Character) (V : ℝ → ℂ)
    (B D Y : ℝ) (hB : 0 ≤ B) (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) :=
  exponential_sum_tail χ V D hD hV hVzero s Y
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs)

private lemma summable_mul_bounded {A : Type*} (f g : A → ℂ)
    (hf : Summable f) (B : ℝ) (hg : ∀ a, ‖g a‖ ≤ B) :
    Summable (fun a => f a*g a) :=
  (hf.norm.mul_right B).of_norm_bounded (fun a => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hg a) (norm_nonneg _))

theorem terminal_sum_identity (χ : Character) (V T : ℝ → ℂ)
    (B BT D Y U : ℝ) (hB : 0 ≤ B)
    (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B) (hTbound : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) -
        ∑' I : Ideal O, terminalRemainder χ V T D Y U s I := by
  let f := fun I : Ideal O => exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))
  have hf : Summable f := summable_mul_bounded _ _
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs) (1+B)
    (fun I => cutoff_defect_bound V B hVbound _)
  have hr : Summable (terminalRemainder χ V T D Y U s) :=
    summable_mul_bounded f _ hf (1+BT) (fun I => cutoff_defect_bound T BT hTbound _)
  have hi : terminalTerm χ V T D Y U s = fun I => f I-terminalRemainder χ V T D Y U s I := by
    funext I
    dsimp [f,terminalTerm,terminalRemainder]
    ring
  rw [hi,hf.tsum_sub hr]
  rw [show (∑' I, f I) = (∑' I, exponentialTerm χ V D s Y I)-Complex.exp (-1/(Y : ℂ)) from
    exponential_sum_tail_unconditional χ V B D Y hB hVbound hD hY hV hVzero s hs]

end SevenEighths.HeckeDetectorTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFinite
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorFinite
open HeckeFamily HeckeDetectorWitnessArithmetic HeckeDetectorTail HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma pairCoefficient_zero_left (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (0,J) = 0 := by
  simp only [pairCoefficient,zero_mul,map_zero,mul_zero]

lemma pairCoefficient_zero_right (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (J,0) = 0 := by
  simp only [pairCoefficient,mul_zero,map_zero,zero_mul]

theorem pairCoefficient_support (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ)
    (p : Ideal O × Ideal O) (hp : p ∉ pairSet U) :
    pairCoefficient χ V T D Y U s p = 0 := by
  by_cases h1 : p.1 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h1]
    exact pairCoefficient_zero_left χ V T D Y U s p.2
  by_cases h2 : p.2 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h2]
    exact pairCoefficient_zero_right χ V T D Y U s p.1
  have hprod : p.1*p.2 ≠ 0 := mul_ne_zero h1 h2
  have hnpos : 0 < Ideal.absNorm (p.1*p.2) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hprod)
  have hnorm : 2*U ≤ (Ideal.absNorm (p.1*p.2) : ℝ) := by
    by_contra h
    have hb : Ideal.absNorm (p.1*p.2) ≤ ⌈2*U⌉₊ := by
      exact_mod_cast (le_trans (lt_of_not_ge h).le (Nat.le_ceil (2*U)))
    have hh1 : Ideal.absNorm p.1 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_right p.1 p.2))
    have hh2 : Ideal.absNorm p.2 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_left p.2 p.1))
    apply hp
    exact Finset.mem_product.mpr
      ⟨mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h1),hh1.trans hb⟩,
       mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h2),hh2.trans hb⟩⟩
  have hz := hT ((Ideal.absNorm (p.1*p.2) : ℝ)/U) ((le_div_iff₀ hU).mpr hnorm)
  simp only [pairCoefficient,hz,mul_zero]

theorem pair_fiber (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val) =
      terminalTerm χ V T D Y U s I := by
  have h := weighted_fiber χ V D s I
  unfold terminalTerm exponentialTerm
  rw [←h,←tsum_mul_right,←tsum_mul_right,←tsum_mul_right]
  apply tsum_congr
  intro p
  simp only [pairCoefficient,p.property]

theorem terminal_sum_eq_pair_sum (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p := by
  have hfinite : Function.HasFiniteSupport (pairCoefficient χ V T D Y U s) := by
    apply (pairSet U).finite_toSet.subset
    intro p hp
    by_contra hn
    exact hp (pairCoefficient_support χ V T D Y U hU hT s p hn)
  have hsum := (summable_of_hasFiniteSupport hfinite).hasSum.tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun I : Ideal O => ∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val)
    (∑' p, pairCoefficient χ V T D Y U s p) at hsum
  simp_rw [pair_fiber] at hsum
  rw [hsum.tsum_eq]
  exact tsum_eq_sum (pairCoefficient_support χ V T D Y U hU hT s)

theorem terminal_sum_eq_dyadic (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        ∑ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1), dyadicBlock χ V T D Y U s j k := by
  have hX : (0 : ℝ) < ⌈2*U⌉₊ := lt_of_lt_of_le (by positivity) (Nat.le_ceil (2*U))
  rw [terminal_sum_eq_pair_sum χ V T D Y U hU hT s]
  apply actual_pair_reassembly χ V T hV hVzero D Y U _ _ hX hX s
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp1,hp1b⟩ := mem_idealsUpTo.mp h1
  obtain ⟨hp2,hp2b⟩ := mem_idealsUpTo.mp h2
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mp (by omega),
    Ideal.absNorm_eq_zero_iff.not.mp (by omega),by exact_mod_cast hp1b,by exact_mod_cast hp2b⟩

theorem exists_dyadic_block (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (c : ℝ)
    (hc : c ≤ ‖∑' I : Ideal O, terminalTerm χ V T D Y U s I‖) :
    ∃ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
      ∃ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        c ≤ (((length (⌈2*U⌉₊ : ℝ)+1 : ℕ) : ℝ)^2)*‖dyadicBlock χ V T D Y U s j k‖ := by
  rw [terminal_sum_eq_dyadic χ V T D Y U hU hT hV hVzero s] at hc
  obtain ⟨j,hj,k,hk,hb⟩ := exists_large_pair (length (⌈2*U⌉₊ : ℝ))
    (length (⌈2*U⌉₊ : ℝ)) (dyadicBlock χ V T D Y U s)
  exact ⟨j,hj,k,hk,by simpa only [pow_two] using hc.trans hb⟩

theorem nonzero_block_scale_bounds (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hD : 0 < D) (hU : 0 < U)
    (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (j k : ℕ)
    (hb : dyadicBlock χ V T D Y U s j k ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨p,hp,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hk := (mul_ne_zero_iff.mp hne).2
  have hj := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
  simp only [pairCoefficient,ne_eq,mul_eq_zero,not_or] at hc
  obtain ⟨⟨⟨⟨⟨hmu,hfirst⟩,hweight⟩,hexp⟩,hproduct⟩,hterminal⟩ := hc
  apply pair_scale_bounds V T hV hVzero hT
    (Ideal.absNorm p.1) (Ideal.absNorm p.2) D U (by positivity) (by positivity)
    hD hU j k hj hk hfirst
  · simpa only [map_mul,Nat.cast_mul] using hproduct
  · simpa only [map_mul,Nat.cast_mul] using hterminal

end SevenEighths.HeckeDetectorFinite

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBudget
open HeckeDetectorPartition

lemma source_length_bound (U : ℝ) (hU : 2 ≤ U) :
    ((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ) ≤ 25*Real.logb 2 U := by
  have hUp : 0 < U := by linarith
  have hp : 1 ≤ U^21 := one_le_pow₀ (by linarith) (n := 21)
  have hc : (1 : ℝ) ≤ ⌈2*U^21⌉₊ := le_trans (by linarith) (Nat.le_ceil (2*U^21))
  have hcu : (⌈2*U^21⌉₊ : ℝ) ≤ 4*U^21 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2*U^21 by positivity)
    linarith
  have hl : 1 ≤ Real.logb 2 U := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by norm_num : (0 : ℝ)<2) hU
    simpa using h
  have hb := length_bound (⌈2*U^21⌉₊ : ℝ) hc
  have hm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by linarith : (0 : ℝ)<⌈2*U^21⌉₊) hcu
  have he : Real.logb 2 (4*U^21) = 2+21*Real.logb 2 U := by
    rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_pow]
    have hfour : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,Real.logb_pow]
      norm_num
    rw [hfour]
    norm_num
  rw [he] at hm
  push_cast
  linarith

lemma source_pair_count_bound (U : ℝ) (hU : 2 ≤ U) :
    (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)^2) ≤ 625*(Real.logb 2 U)^2 := by
  have h := source_length_bound U hU
  have hl : 0 ≤ Real.logb 2 U := Real.logb_nonneg (by norm_num) (by linarith)
  nlinarith [sq_nonneg (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)-25*Real.logb 2 U)]

end SevenEighths.HeckeDetectorBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorLower
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorLower
open HeckeFamily HeckeDetectorTail HeckeDetectorFinite HeckeDetectorPartition
open GammaZeroDetector
local notation "O" => HeckeFamily.O

lemma unit_term_lower (U : ℝ) (hU : 2 ≤ U) :
    (3/4 : ℝ) ≤ ‖Complex.exp (-1/((U^20 : ℝ) : ℂ))‖ := by
  have hUp : 0 < U := by linarith
  have hp : 4 ≤ U^20 := by
    calc
      4 ≤ U^2 := by nlinarith
      _ ≤ U^20 := pow_le_pow_right₀ (by linarith : 1 ≤ U) (by norm_num : 2 ≤ 20)
  have hi : 1/(U^20) ≤ (1/4 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hp
  rw [Complex.norm_exp]
  have he : (-1/((U^20 : ℝ) : ℂ)).re = -1/(U^20) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,←Complex.ofReal_div,Complex.ofReal_re]
  rw [he]
  have hh := Real.add_one_le_exp (-1/(U^20))
  simp only [neg_div] at hh ⊢
  linarith

theorem terminal_uniform_lower (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      (1/2 : ℝ) ≤ ‖∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I‖ := by
  obtain ⟨UG,hUG⟩ := detector_uniform_small R θ (1/8) hR hθ hθ' (by norm_num)
  obtain ⟨UT,hUT⟩ := terminalRemainder_uniform_small 1 1 (1/8) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max 2 (max UG UT),?_⟩
  intro U hU χ hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  have hg := hUG U ((le_max_left UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ hχ V hVb D (by linarith) hDU hQ ρ hρ hzero hheight
  have ht := hUT U ((le_max_right UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ V T hVb hTb hTone D ρ (by linarith)
  have hi := terminal_sum_identity χ V T 1 1 D (U^20) (U^21) (by norm_num)
    hVb hTb hD (by positivity) hVone hVzero ρ (by linarith)
  rw [(GammaDetectorExpansion.detector_hasSum_convolution χ V
    (by linarith : 0 < D) (by positivity : 0 < U^20) hVzero (by linarith : -1 < ρ.re)).tsum_eq] at hi
  have he : Complex.exp (-1/((U^20 : ℝ) : ℂ)) =
      detectorIntegral χ V D (U^20) ρ -
        (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I) -
        (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I) := by
    rw [hi]
    ring
  have hn := norm_sub_le
    (detectorIntegral χ V D (U^20) ρ - ∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
    (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I)
  rw [←he] at hn
  have hn' := norm_sub_le (detectorIntegral χ V D (U^20) ρ)
    (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
  have hu := unit_term_lower U hU2
  linarith

theorem exists_dyadic_zero_witness_oai (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      (∀ x : ℝ, 2 ≤ x → T x = 0) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          (1/2 : ℝ) ≤ 625*(Real.logb 2 U)^2*‖dyadicBlock χ V T D (U^20) (U^21) ρ j k‖ ∧
          (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
          (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨U₁,hU₁⟩ := terminal_uniform_lower R θ hR hθ hθ'
  refine ⟨max 2 U₁,?_⟩
  intro U hU χ hχ V T hVb hTb hVone hVzero hTone hTzero D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hUpos : 0 < U := by linarith
  have ht := hU₁ U ((le_max_right _ _).trans hU) χ hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,hb⟩ := exists_dyadic_block χ V T D (U^20) (U^21)
    (by positivity) hTzero hVone hVzero ρ (1/2) ht
  have hbn : dyadicBlock χ V T D (U^20) (U^21) ρ j k ≠ 0 := by
    intro hz
    rw [hz,norm_zero,mul_zero] at hb
    norm_num at hb
  refine ⟨j,hj,k,hk,?_,nonzero_block_scale_bounds χ V T D (U^20) (U^21)
    (by linarith) (by positivity) hTzero hVone hVzero ρ j k hbn⟩
  exact hb.trans (mul_le_mul_of_nonneg_right
    (HeckeDetectorBudget.source_pair_count_bound U hU2) (norm_nonneg _))

end SevenEighths.HeckeDetectorLower

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckeDetectorLower.exists_dyadic_zero_witness_oai := @OAI.SevenEighths.HeckeDetectorLower.exists_dyadic_zero_witness_oai
