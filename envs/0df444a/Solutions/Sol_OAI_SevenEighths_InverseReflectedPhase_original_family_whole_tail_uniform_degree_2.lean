-- Prove2me | solution 2 for OAI.SevenEighths.InverseReflectedPhase.original_family_whole_tail_uniform_degree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:38:57.057934+00:00
-- url     : https://prove2.me/submissions/6a68df1b-1588-4636-9ff5-5b10ff7de5d7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B028

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ShortDraftGauss

open Complex
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

theorem norm_normalized_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖((Real.sqrt (Fintype.card F) : ℝ) : ℂ)⁻¹ * gaussSum χ ψ‖ = 1 := by
  have hcard : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hsqrt : Real.sqrt (Fintype.card F) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 hcard), norm_gaussSum_eq_sqrt_card χ ψ hχ hψ]
  exact inv_mul_cancel₀ hsqrt

end ShortDraftGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
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

open scoped BigOperators Classical

namespace CompletedGauss

section

open ActualEisensteinCubic

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

open ActualEisensteinCubic

theorem norm_at_least_one (I : Ideal O) (hI : I ≠ 0) :
    (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

end
section

open ActualEisensteinCubic ConcreteTraceCRT

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
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

open scoped BigOperators Classical SchwartzMap

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

namespace CubicReflectionKernel

theorem Gamma_vertical_ne_zero (a u : ℝ) (ha : 0 < a) :
    Complex.Gamma ((a : ℂ) + u * Complex.I) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  simpa using ha

theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

theorem gammaMultiplier_norm_imaginary (u : ℝ) :
    ‖gammaMultiplier (u * Complex.I)‖ = 1 := by
  have ha := Gamma_vertical_ne_zero (7 / 6) u (by norm_num)
  have hb := Gamma_vertical_ne_zero (5 / 6) u (by norm_num)
  have hca := Gamma_vertical_conj (7 / 6) u
  have hcb := Gamma_vertical_conj (5 / 6) u
  push_cast at ha hb hca hcb
  rw [gammaMultiplier, hca, hcb, norm_div, norm_mul, norm_mul, norm_star, norm_star]
  exact div_self (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))

theorem Gamma_vertical_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun u : ℝ => Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · fun_prop
  · intro n hn
    have heq := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.neg_re, Complex.natCast_re] at heq
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem axisMultiplier_norm (u : ℝ) : ‖axisMultiplier u‖ = 1 :=
  gammaMultiplier_norm_imaginary _

theorem axisMultiplier_continuous : Continuous axisMultiplier := by
  have h1 := (Gamma_vertical_continuous (7 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h2 := (Gamma_vertical_continuous (5 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => 2 * Real.pi * u) by fun_prop)
  have h3 := (Gamma_vertical_continuous (7 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have h4 := (Gamma_vertical_continuous (5 / 6) (by norm_num)).comp
    (show Continuous (fun u : ℝ => -(2 * Real.pi * u)) by fun_prop)
  have hd := h3.mul h4
  have hne (u : ℝ) :
      Complex.Gamma ((7 / 6 : ℝ) + (-(2 * Real.pi * u) : ℝ) * Complex.I) *
      Complex.Gamma ((5 / 6 : ℝ) + (-(2 * Real.pi * u) : ℝ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Gamma_vertical_ne_zero _ _ (by norm_num)) (Gamma_vertical_ne_zero _ _ (by norm_num))
  convert (preTransparency := .instances) (h1.mul h2).div hd hne using 1
  ext u
  simp only [axisMultiplier, gammaMultiplier, Function.comp_def, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg,
    Pi.div_apply, Pi.mul_apply]

theorem spectralProfile_norm (logSource : SchwartzMap ℝ ℂ) (u : ℝ) :
    ‖spectralProfile logSource u‖ = ‖(𝓕 logSource) u‖ := by
  rw [spectralProfile, norm_mul, axisMultiplier_norm, one_mul]

theorem spectralProfile_continuous (logSource : SchwartzMap ℝ ℂ) : Continuous (spectralProfile logSource) :=
  axisMultiplier_continuous.mul (𝓕 logSource).continuous

theorem spectralProfile_moment_integrable (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => ‖u‖ ^ j * ‖spectralProfile logSource u‖) := by
  simpa only [spectralProfile_norm] using (𝓕 logSource).integrable_pow_mul volume j

theorem spectralProfile_pow_integrable (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    Integrable (fun u : ℝ => u ^ j • spectralProfile logSource u) := by
  apply (spectralProfile_moment_integrable logSource j).mono'
    ((show Continuous (fun u : ℝ => u ^ j • spectralProfile logSource u) by
      exact (continuous_id.pow j).smul (spectralProfile_continuous logSource)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun u => by simp only [norm_smul, norm_pow, le_rfl])

theorem reflectedLogProfile_deriv (logSource : SchwartzMap ℝ ℂ) (j : ℕ) :
    iteratedDeriv j (reflectedLogProfile logSource) =
      𝓕 (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) := by
  simpa only [reflectedLogProfile, smul_eq_mul] using
    (Real.iteratedDeriv_fourier (N := (⊤ : ℕ∞))
      (fun n _ => spectralProfile_pow_integrable logSource n) (by simp : (j : ℕ∞) ≤ ⊤))

end CubicReflectionKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
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

namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem paperScale_pos : 0 < paperScale := by
  unfold paperScale
  positivity

theorem mellin_axis_eq_fourier (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (u : ℝ) :
    mellin V (-((2 * Real.pi * u : ℝ) * Complex.I)) = (𝓕 logSource) u := by
  rw [mellin_eq_fourier]
  have hfreq : (-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).im / (2 * Real.pi) = -u := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    field_simp
  rw [hfreq]
  have hfun : (fun v : ℝ => Real.exp
      (-(-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).re * v) • V (Real.exp (-v))) =
      (logSource : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ := by
    funext v
    simp [hL]
  rw [hfun, Real.fourier_comp_linearIsometry]
  simp
  rfl

theorem paperKernel_eq_logFourier (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    paperKernel V x = reflectedLogProfile logSource (Real.log (paperScale * x)) := by
  unfold paperKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hfun : (fun y : ℝ => mellin V (-(0 + 2 * Real.pi * y * Complex.I)) *
      gammaMultiplier (0 + 2 * Real.pi * y * Complex.I)) = spectralProfile logSource := by
    funext y
    have hy : (0 + 2 * Real.pi * y * Complex.I : ℂ) =
        ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hy, mellin_axis_eq_fourier V logSource hL]
    exact mul_comm _ _
  rw [hfun]
  rfl

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

theorem paperKernel_euler_eq (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    LocalLogFourier.eulerDeriv (paperKernel V) j x =
      iteratedDeriv j (reflectedLogProfile logSource) (Real.log (paperScale * x)) := by
  have hfun : (fun t : ℝ => paperKernel V (x * Real.exp t)) =
      (fun t : ℝ => reflectedLogProfile logSource (Real.log (paperScale * x) + t)) := by
    funext t
    rw [paperKernel_eq_logFourier V logSource hL _ (mul_pos hx (Real.exp_pos t))]
    rw [← mul_assoc, Real.log_mul (ne_of_gt (mul_pos paperScale_pos hx))
      (ne_of_gt (Real.exp_pos t)), Real.log_exp]
  rw [LocalLogFourier.eulerDeriv, hfun, iteratedDeriv_comp_const_add]
  simp

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem gammaMultiplier_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ gammaMultiplier s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert (preTransparency := .instances) ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [gammaMultiplier, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt s hs)

end CubicReflectionKernel

open scoped BigOperators Classical

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
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

open scoped BigOperators Classical

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤
      Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem inverse_Gamma_shift (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n),
      Finset.prod_range_succ]
    push_cast
    ring_nf

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem Gamma_pair_strip_bound (a : ℝ) (ha : 1 / 4 < a) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
        Complex.Gamma ((a : ℂ) - (σ + t * Complex.I))‖ ≤
        C * (1 + |t|) ^ (2 * A + 2) := by
  let n : ℕ := 2 * A + 2
  let I : Set ℝ := Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)
  have hapos (σ : ℝ) (hσ : σ ∈ I) : 0 < a + σ := by
    have := hσ.1
    linarith
  have hdpos (σ : ℝ) (hσ : σ ∈ I) : 0 < (n : ℝ) - 2 * σ := by
    have := hσ.2
    dsimp [n]
    push_cast
    linarith
  have hdenpos (σ : ℝ) (hσ : σ ∈ I) : 0 < a - σ + n := by
    have h1 := hapos σ hσ
    have h2 := hdpos σ hσ
    linarith
  have hc1 : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_const.add continuous_id).continuousOn hapos
  have hc2 : ContinuousOn (fun σ : ℝ => Real.Gamma (a - σ + n)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      ((continuous_const.sub continuous_id).add continuous_const).continuousOn hdenpos
  have hc : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ) / Real.Gamma (a - σ + n)) I :=
    hc1.div hc2 (fun σ hσ => (Real.Gamma_pos_of_pos (hdenpos σ hσ)).ne')
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hc
  let C₁ : ℝ := |C₀| + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal (σ : ℝ) (hσ : σ ∈ I) :
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) ≤ C₁ := by
    exact (hC₀ (Set.mem_image_of_mem _ hσ)).trans (by dsimp [C₁]; linarith [le_abs_self C₀])
  let B : ℝ := |a| + A + 1 + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ n * C₁, mul_pos (pow_pos hB n) hC₁, ?_⟩
  intro σ hσ t
  have hσ' : σ ∈ I := hσ
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(a : ℂ) - (σ + t * Complex.I)‖ ≤ |a| + A + 1 + |t| := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(σ : ℂ) + t * Complex.I‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ = |a| + (|σ| + |t|) := by simp
      _ ≤ _ := by linarith
  have hzB : ‖(a : ℂ) - (σ + t * Complex.I)‖ + n ≤ B * (1 + |t|) := by
    dsimp [B]
    nlinarith [abs_nonneg a, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hprod : ‖∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)‖ ≤
      B ^ n * (1 + |t|) ^ n := by
    apply (norm_Gamma_shift_factor _ n).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hzB n
  have hratio := (Gamma_shifted_pair_bound a σ t n (hapos σ hσ') (hdpos σ hσ')).trans
    (hreal σ hσ')
  have heq : Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I)) =
      (∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)) *
      (Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)) := by
    rw [div_eq_mul_inv, inverse_Gamma_shift _ n, div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ (B ^ n * (1 + |t|) ^ n) * C₁ :=
      mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [n]; ring

theorem gammaMultiplier_strip_bound (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (4 * A + 4) := by
  obtain ⟨C₁, hC₁, h1⟩ := Gamma_pair_strip_bound (7 / 6) (by norm_num) A
  obtain ⟨C₂, hC₂, h2⟩ := Gamma_pair_strip_bound (5 / 6) (by norm_num) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  have heq : gammaMultiplier ((σ : ℂ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2 * A + 2)) * (C₂ * (1 + |t|) ^ (2 * A + 2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

theorem compact_source_mellin_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_weighted_bound
    (mellinLogFamily V) (mellinLogFamily_smooth V hV)
    (Set.Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (mellinLogFamily_support V a b ha hsupp) (Set.Icc lo hi) isCompact_Icc j
  refine ⟨(1 + 2 * Real.pi) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ _) (by positivity)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem mellinData_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellinData V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨CV, hCV, hVb⟩ := compact_source_mellin_strip_decay V a b ha hsupp hV
    (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmb hCγ.le

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

theorem mellinEulerData_strip_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinData_strip_decay V a b ha hsupp hV A (j + 2)
  refine ⟨((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by
      gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ t) (by positivity)

theorem mellinEulerData_differentiableAt (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (mellinEulerData V j) s :=
  (differentiableAt_id.neg.pow j).mul
    (kernelMellinIntegrand_differentiableAt V a b ha hsupp hV s hs)

theorem mellinEulerData_vertical_integrable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    Integrable (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mellinEulerData_differentiableAt V a b ha hsupp hV j _ ?_).continuousAt.comp
    · fun_prop
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hσ.1]
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [div_eq_mul_inv] using hb σ hσ t)

end CubicReflectionKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.InverseContour
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

namespace CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

theorem inverseMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (inverseMellinIntegrand V j y) s := by
  exact (differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    (mellinEulerData_differentiableAt V a b ha hsupp hV j s hs)

theorem inverseMellinIntegrand_vertical_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)) := by
  apply (mellinEulerData_vertical_integrable V a b ha hsupp hV A j σ hσ).bdd_mul
    (c := y ^ (-σ))
  · exact ((show Continuous (fun t : ℝ => -((σ : ℂ) + t * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp

theorem inverseMellinIntegrand_strip_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun σ : ℝ => y ^ (-σ)) :=
    (Real.continuous_const_rpow hy.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))).bddAbove_image hc.continuousOn
  refine ⟨(|B| + 1) * C, by positivity, ?_⟩
  intro σ hσ t
  have hby : y ^ (-σ) ≤ |B| + 1 :=
    (hB (Set.mem_image_of_mem _ hσ)).trans (by linarith [le_abs_self B])
  rw [inverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (|B| + 1) * (C / (1 + t ^ 2)) :=
      mul_le_mul hby (hb σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_shift
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    mellinInv 0 (mellinEulerData V j) y = mellinInv σ (mellinEulerData V j) y := by
  obtain ⟨C, hC, hb⟩ := inverseMellinIntegrand_strip_bound V a b ha hsupp hV A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · norm_num
    · exact Nat.cast_nonneg A
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      (∫ t : ℝ, inverseMellinIntegrand V j y ((-(1 / 4) : ℝ) + t * Complex.I)) =
      ∫ t : ℝ, inverseMellinIntegrand V j y ((ρ : ℂ) + t * Complex.I) := by
    apply VerticalContourShift.integral_eq_of_strip_decay
      (inverseMellinIntegrand V j y) (-(1 / 4)) ρ C hρ.1
    · intro z hzlo hzhi
      apply inverseMellinIntegrand_differentiableAt V a b ha hsupp hV j y hy z
      linarith
    · apply inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j
        (-(1 / 4)) ⟨le_rfl, hρ.1.trans hρ.2⟩ y hy
    · exact inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j ρ hρ y hy
    · intro r hr t
      exact hb r ⟨hr.1, hr.2.trans hρ.2⟩ t
  have heq := (hshift 0 h0).symm.trans (hshift σ hσ)
  simpa only [mellinInv, smul_eq_mul, inverseMellinIntegrand] using
    congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) heq

theorem mellinInv_euler_line_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ),
      ∀ y : ℝ, 0 < y → ‖mellinInv σ (mellinEulerData V j) y‖ ≤ C * y ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  refine ⟨C / 2, by positivity, ?_⟩
  intro σ hσ y hy
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤
      (y ^ (-σ) * C) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * C) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * C) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by field_simp

theorem mellinEulerData_axis (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hlog : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (u : ℝ) :
    mellinEulerData V j (2 * Real.pi * u * Complex.I) =
      (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u := by
  have hu : (2 * Real.pi * u * Complex.I : ℂ) =
      ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [mellinEulerData, mellinData, hu, mellin_axis_eq_fourier V logSource hlog]
  have hb : -(((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) =
      -2 * Real.pi * Complex.I * u := by push_cast; ring
  rw [hb, spectralProfile, axisMultiplier]
  ring

theorem paperEulerKernel_eq_euler (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hlog : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    paperEulerKernel V j x = LocalLogFourier.eulerDeriv (paperKernel V) j x := by
  rw [paperKernel_euler_eq V logSource hlog j x hx, reflectedLogProfile_deriv]
  unfold paperEulerKernel
  rw [mellinInv_eq_fourierInv 0 _ (mul_pos paperScale_pos hx)]
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul,
    Real.fourierInv_eq_fourier_neg, neg_neg, zero_add]
  have hfun : (fun u : ℝ => mellinEulerData V j (2 * Real.pi * u * Complex.I)) =
      (fun u : ℝ => (-2 * Real.pi * Complex.I * u) ^ j * spectralProfile logSource u) := by
    funext u
    exact mellinEulerData_axis V logSource hlog j u
  rw [hfun]

theorem paperKernel_euler_decay_at_line
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := mellinInv_euler_line_bound V a b ha hsupp hV A j
  refine ⟨C * paperScale ^ (-σ), mul_pos hC (Real.rpow_pos_of_pos paperScale_pos _), ?_⟩
  intro x hx
  rw [← paperEulerKernel_eq_euler V (logSchwartz V a b ha hsupp hV) (by intro u; rfl) j x hx]
  unfold paperEulerKernel
  rw [mellinInv_euler_shift V a b ha hsupp hV A j σ hσ _ (mul_pos paperScale_pos hx)]
  have hbound := hb σ hσ (paperScale * x) (mul_pos paperScale_pos hx)
  rw [Real.mul_rpow paperScale_pos.le hx.le] at hbound
  simpa only [mul_assoc] using hbound

theorem paperKernel_euler_power_decay
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x →
      (‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (1 / 4 : ℝ)) ∧
      (‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ C * x ^ (-(A : ℝ))) := by
  have hleft : -(1 / 4 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · rfl
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  have hright : (A : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
    · rfl
  obtain ⟨CL, hCL, hL⟩ := paperKernel_euler_decay_at_line V a b ha hsupp hV A j _ hleft
  obtain ⟨CR, hCR, hR⟩ := paperKernel_euler_decay_at_line V a b ha hsupp hV A j _ hright
  refine ⟨max CL CR, lt_of_lt_of_le hCL (le_max_left _ _), ?_⟩
  intro x hx
  constructor
  · have hh : ‖LocalLogFourier.eulerDeriv (paperKernel V) j x‖ ≤ CL * x ^ (1 / 4 : ℝ) := by
      simpa only [neg_neg] using hL x hx
    exact hh.trans
      (mul_le_mul_of_nonneg_right (le_max_left CL CR) (Real.rpow_nonneg hx.le _))
  · exact (hR x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_right CL CR) (Real.rpow_nonneg hx.le _))

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem logPullbackCLM_apply (a b : ℝ) (W : SchwartzMap ℝ ℂ) (u : ℝ) :
    logPullbackCLM a b W u = logCutoff a b u • W (patchedExp a b u) := by
  rw [logPullbackCLM, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply
    ((logCutoff a b).hasCompactSupport.hasTemperateGrowth (logCutoff a b).contDiff)]
  rfl

theorem logCutoff_eq_one_of_source (a b : ℝ) (ha : 0 < a) (u : ℝ)
    (hu : Real.exp u ∈ Set.Icc a b) : logCutoff a b u = 1 := by
  apply (logCutoff a b).one_of_mem_closedBall
  have hl := Real.log_le_log ha hu.1
  have hr := Real.log_le_log (Real.exp_pos u) hu.2
  simp only [Real.log_exp] at hl hr
  change dist u 0 ≤ logRadius a b
  rw [Real.dist_eq, sub_zero]
  apply abs_le.mpr
  constructor <;> dsimp [logRadius] <;>
    linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem patchedExp_eq_exp_of_cutoff_ne_zero (a b u : ℝ) (hu : logCutoff a b u ≠ 0) :
    patchedExp a b u = Real.exp u := by
  have hmem : u ∈ Function.support (logCutoff a b) := hu
  rw [(logCutoff a b).support_eq] at hmem
  have heta : logOuterCutoff a b u = 1 := by
    apply (logOuterCutoff a b).one_of_mem_closedBall
    change dist u 0 ≤ logRadius a b + 1
    change dist u 0 < logRadius a b + 1 at hmem
    exact le_of_lt hmem
  simp [patchedExp, expCorrection, heta]

theorem logPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    logPullbackCLM a b W u = W (Real.exp u) := by
  rw [logPullbackCLM_apply]
  by_cases hW : W (Real.exp u) = 0
  · by_cases hcut : logCutoff a b u = 0
    · simp [hcut, hW]
    · rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u hcut, hW, smul_zero]
  · have hcut := logCutoff_eq_one_of_source a b ha u (hsupp hW)
    rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u (by rw [hcut]; norm_num), hcut, one_smul]

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem compact_family_deriv_sup_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ u : ℝ, ‖iteratedFDeriv ℝ j (F σ) u‖ ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro σ hσ u
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hu : u ∈ K
  · exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans
      (by linarith [le_abs_self M])
  · have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
      (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
        (closure_minimal (hsupp σ) hK.isClosed))
    have hz : iteratedDeriv j (F σ) u = 0 := by by_contra hn; exact hu (hs hn)
    simp only [hz, norm_zero]
    positivity

theorem compact_family_mul_deriv_L1_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J,
      (∫ u : ℝ, ‖iteratedDeriv j (fun u => F σ u * W u) u‖) ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose c hc hcb using fun i : Fin (j + 1) => compact_family_deriv_sup_bound F hF K hK hsupp J hJ i.val
  let D := (∑ i : Fin (j + 1), c i) + 1
  have hD : 0 < D := by
    have : 0 ≤ ∑ i : Fin (j + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hder (i : ℕ) (hi : i ≤ j) (σ : ℝ) (hσ : σ ∈ J) (u : ℝ) :
      ‖iteratedFDeriv ℝ i (F σ) u‖ ≤ D := by
    let k : Fin (j + 1) := ⟨i, by omega⟩
    have hsum : c k ≤ ∑ l : Fin (j + 1), c l :=
      Finset.single_le_sum (fun l _ => (hc l).le) (Finset.mem_univ k)
    exact (hcb k σ hσ u).trans (by dsimp [D]; linarith)
  let B : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(B + 1) * (volume.real K + 1), by positivity, ?_⟩
  intro W σ hσ
  let S : ℝ := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hWder (k : ℕ) (hk : k ≤ j) (u : ℝ) : ‖iteratedFDeriv ℝ k W u‖ ≤ S := by
    have hle : schwartzSeminormFamily ℝ ℝ ℂ (0, k) ≤
        (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [hk])
    exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ W k u).trans (Seminorm.le_def.mp hle W)
  have hb (u : ℝ) : ‖iteratedDeriv j (fun u => F σ u * W u) u‖ ≤ (B + 1) * S := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hfσ : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
    apply (norm_iteratedFDeriv_mul_le hfσ (W.smooth ⊤) u (n := j) (by simp)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D * S := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hder i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) σ hσ u) (by positivity))
          (hWder (j - i) (Nat.sub_le _ _) u) (norm_nonneg _) (by positivity)
      _ = B * S := by rw [← Finset.sum_mul]
      _ ≤ (B + 1) * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hmul : Function.support (fun u => F σ u * W u) ⊆ K := by
    intro u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : Function.support (iteratedDeriv j (fun u => F σ u * W u)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ j).trans
      (closure_minimal hmul hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (fun u => F σ u * W u) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (fun u => F σ u * W u) u = 0 := by by_contra hn; exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume)
    (f := fun u => ‖iteratedDeriv j (fun u => F σ u * W u) u‖) hK.measure_lt_top
    (C := (B + 1) * S) (fun u _ => by simpa using hb u)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  calc
    _ ≤ ((B + 1) * S) * volume.real K := hi
    _ ≤ ((B + 1) * S) * (volume.real K + 1) := by gcongr; linarith
    _ = _ := by dsimp [S]; ring

end CubicReflectionKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
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

namespace CubicReflectionKernel
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

theorem compact_family_mul_fourier_power_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_deriv_L1_source_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro W σ hσ w
  have hFW : ContDiff ℝ ∞ (Function.uncurry (fun σ u => F σ u * W u)) :=
    hF.mul ((W.smooth ⊤).comp contDiff_snd)
  have hsupport : ∀ σ, Function.support (fun u => F σ u * W u) ⊆ K := by
    intro σ u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : ContDiff ℝ ∞ (fun u => F σ u * W u) :=
    hFW.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable (fun σ u => F σ u * W u) hFW K hK hsupport σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) =
      ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ ≤
      C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (fun u => F σ u * W u)) w).trans
    exact hb W σ hσ
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := mul_comm _ _
    _ ≤ _ := hn

theorem compact_family_mul_fourier_weighted_source_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro W σ hσ w
  let S := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hsubset : Finset.Iic (0, 0) ⊆ Finset.Iic (0, j) := by
    intro p hp
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hp).trans (by simp))
  have hseminorm : (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ S :=
    Seminorm.le_def.mp (Finset.sup_mono hsubset) W
  have hbase : ‖𝓕 (fun u => F σ u * W u) w‖ ≤ C₀ * S := by
    have hh : ‖𝓕 (fun u => F σ u * W u) w‖ ≤ C₀ * (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
      simpa using h0 W σ hσ w
    exact hh.trans (mul_le_mul_of_nonneg_left hseminorm hC₀.le)
  have hpower : |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤ Cj * S := hj W σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * (C₀ * S) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ 2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * (Cj * S) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ 2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring

theorem negativeLogPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    negativeLogPullbackCLM a b W u = W (Real.exp (-u)) := by
  change logPullbackCLM a b W (-u) = _
  exact logPullbackCLM_eq_actual a b ha W hsupp (-u)

theorem logWeight_smooth (a b : ℝ) : ContDiff ℝ ∞ (Function.uncurry (logWeight a b)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((Real.exp (-p.1 * p.2) * logCutoff a b (-p.2) : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).mul
      ((logCutoff a b).contDiff.comp contDiff_snd.neg))

theorem logWeight_support (a b σ : ℝ) :
    Function.support (logWeight a b σ) ⊆ Metric.closedBall 0 (logRadius a b + 1) := by
  intro u hu
  have hc : logCutoff a b (-u) ≠ 0 := by
    intro hc
    exact hu (by simp [logWeight, hc])
  have hm : -u ∈ Function.support (logCutoff a b) := hc
  rw [(logCutoff a b).support_eq] at hm
  change dist (-u) 0 < logRadius a b + 1 at hm
  change dist u 0 ≤ logRadius a b + 1
  simpa only [dist_zero_right, norm_neg] using hm.le

theorem logWeight_mul_pullback (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b) (σ u : ℝ) :
    logWeight a b σ u * negativeLogPullbackCLM a b W u = mellinLogFamily W σ u := by
  rw [negativeLogPullbackCLM_eq_actual a b ha W hsupp]
  by_cases hW : W (Real.exp (-u)) = 0
  · simp [logWeight, mellinLogFamily, hW]
  · have hc := logCutoff_eq_one_of_source a b ha (-u) (hsupp hW)
    simp [logWeight, mellinLogFamily, hc]

theorem mellin_strip_source_bound (a b : ℝ) (ha : 0 < a) (lo hi : ℝ) (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
        (1 + |t|) ^ j * ‖mellin W ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_fourier_weighted_source_bound
    (logWeight a b) (logWeight_smooth a b) (Metric.closedBall 0 (logRadius a b + 1))
    (isCompact_closedBall _ _) (logWeight_support a b) (Set.Icc lo hi) isCompact_Icc j
  obtain ⟨s, D, hD, hDbd⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (negativeLogPullbackCLM a b) (Finset.Iic (0, j))
  refine ⟨s, (1 + 2 * Real.pi) ^ j * C * D, by positivity, ?_⟩
  intro W hsupp σ hσ t
  have hfun : (fun u => logWeight a b σ u * negativeLogPullbackCLM a b W u) = mellinLogFamily W σ :=
    funext (logWeight_mul_pullback a b ha W hsupp σ)
  have hfour := hb (negativeLogPullbackCLM a b W) σ hσ (t / (2 * Real.pi))
  rw [hfun] at hfour
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  rw [mellin_eq_logFamily_fourier]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily W σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily W σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ (1 + 2 * Real.pi) ^ j * (C *
        (D * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) :=
      mul_le_mul_of_nonneg_left (hfour.trans (mul_le_mul_of_nonneg_left (hDbd W) hC.le)) (by positivity)
    _ = _ := by ring

theorem mellinData_strip_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        (1 + |t|) ^ j * ‖mellinData W ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨s, CV, hCV, hVb⟩ := mellin_strip_source_bound a b ha (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨s, Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro W hsupp σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb W hsupp (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ Cγ * (CV * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := mul_le_mul_of_nonneg_left hmb hCγ.le
    _ = _ := by ring

theorem mellinEulerData_strip_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        ‖mellinEulerData W j ((σ : ℂ) + t * Complex.I)‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t ^ 2) := by
  obtain ⟨s, C, hC, hb⟩ := mellinData_strip_source_bound a b ha A (j + 2)
  refine ⟨s, ((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro W hsupp σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData W ((σ : ℂ) + t * Complex.I)‖) := by gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData W ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ ((A : ℝ) + 2) ^ j * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_line_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ y : ℝ, 0 < y →
        ‖mellinInv σ (mellinEulerData W j) y‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * y ^ (-σ) := by
  obtain ⟨s, C, hC, hb⟩ := mellinEulerData_strip_source_bound a b ha A j
  refine ⟨s, C / 2, by positivity, ?_⟩
  intro W hsupp σ hσ y hy
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData W j ((σ : ℂ) + t * Complex.I)‖ ≤
      (y ^ (-σ) * (C * Q)) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, (y ^ (-σ) * (C * Q)) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((y ^ (-σ) * (C * Q)) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by dsimp [Q]; field_simp

theorem paperKernel_euler_source_power_decay (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ x : ℝ, 0 < x →
        (‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (1 / 4 : ℝ)) ∧
        (‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (-(A : ℝ))) := by
  obtain ⟨s, C, hC, hb⟩ := mellinInv_euler_line_source_bound a b ha A j
  let B := max (paperScale ^ (1 / 4 : ℝ)) (paperScale ^ (-(A : ℝ)))
  have hB : 0 < B := lt_of_lt_of_le (Real.rpow_pos_of_pos paperScale_pos _) (le_max_left _ _)
  refine ⟨s, C * B, mul_pos hC hB, ?_⟩
  intro W hsupp x hx
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hline (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      ‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤
        C * Q * (paperScale * x) ^ (-σ) := by
    rw [← paperEulerKernel_eq_euler W (logPullbackCLM a b W)
      (logPullbackCLM_eq_actual a b ha W hsupp) j x hx]
    unfold paperEulerKernel
    rw [mellinInv_euler_shift W a b ha hsupp (W.smooth ⊤) A j σ hσ _ (mul_pos paperScale_pos hx)]
    exact hb W hsupp σ hσ (paperScale * x) (mul_pos paperScale_pos hx)
  have hleft : -(1 / 4 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · rfl
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
  have hright : (A : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · linarith [show (0 : ℝ) ≤ A from Nat.cast_nonneg A]
    · rfl
  constructor
  · have hh := hline _ hleft
    rw [neg_neg, Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤ C * Q * (paperScale ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := hh
      _ = (C * paperScale ^ (1 / 4 : ℝ)) * Q * x ^ (1 / 4 : ℝ) := by ring
      _ ≤ (C * B) * Q * x ^ (1 / 4 : ℝ) := by
        gcongr
        exact le_max_left _ _
  · have hh := hline _ hright
    rw [Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤ C * Q * (paperScale ^ (-(A : ℝ)) * x ^ (-(A : ℝ))) := hh
      _ = (C * paperScale ^ (-(A : ℝ))) * Q * x ^ (-(A : ℝ)) := by ring
      _ ≤ (C * B) * Q * x ^ (-(A : ℝ)) := by
        gcongr
        exact le_max_right _ _

end CubicReflectionKernel

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

section

variable {F : Type*} [Field F] [Fintype F]

theorem rootCard_pos : 0 < rootCard F := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩

theorem rootCard_sq : rootCard F ^ 2 = (Fintype.card F : ℝ) := Real.sq_sqrt (by positivity)

theorem norm_tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχ : χ ^ j ≠ 1) (hψ : ψ.IsPrimitive) : ‖tau χ ψ j‖ = 1 :=
  ShortDraftGauss.norm_normalized_gaussSum (χ ^ j) ψ hχ hψ

theorem bracket_four_split (χ : MulChar F ℂ) (x : F) :
    bracket χ 4 x = -(rootCard F : ℂ)⁻¹ + (rootCard F : ℂ) * if x = 0 then 1 else 0 := by
  have hr : (rootCard F : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard F : ℂ) ^ 2 = (Fintype.card F : ℂ) := by exact_mod_cast (rootCard_sq (F := F))
  simp only [bracket, ↓reduceIte]
  rw [← hsq]
  field_simp

theorem norm_bracket_nonexceptional (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) :
    ‖bracket χ j x‖ = if x = 0 then 0 else 1 := by
  simp only [bracket, if_neg hj4, if_neg hj0]
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ (j + 2))⁻¹) (Units.mk0 x hx)

theorem norm_bracket_zero (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ = (rootCard F)⁻¹ * if x = 0 then 0 else 1 := by
  simp only [bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]
  congr 1
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ 2)⁻¹) (Units.mk0 x hx)

theorem norm_bracket_four_nonzero (χ : MulChar F ℂ) (x : F) (hx : x ≠ 0) :
    ‖bracket χ 4 x‖ = (rootCard F)⁻¹ := by
  rw [bracket_four_split]
  simp [hx, Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]

theorem norm_bracket_four_zero (χ : MulChar F ℂ) :
    ‖bracket χ 4 (0 : F)‖ = ((Fintype.card F : ℝ) - 1) / rootCard F := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  simp only [bracket, ↓reduceIte, mul_one, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg rootCard_pos.le]
  have heq : (-1 + (Fintype.card F : ℂ)) = (((Fintype.card F : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hq)]
  ring

end

section
variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem shifted_power_nontrivial (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4) : χ ^ (j + 2) ≠ 1 := by
  by_cases hj : j = 5
  · subst j
    have heq : χ ^ (5 + 2) = χ ^ 1 := by
      rw [show (5 + 2 : ℕ) = 6 + 1 by decide, pow_add, h6, one_mul]
    rw [heq]
    exact hn 1 (by decide) (by decide)
  · exact hn (j + 2) (by omega) (by omega)

theorem phase_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (h6 : χ ^ 6 = 1) (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj6 : j < 6) (ε : Fˣ) :
    ‖phase χ ψ j ε‖ = 1 := by
  have hψminus : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (hψ (a := (-1 : F)) (by simp))
  by_cases hj4 : j = 4
  · subst j
    simp only [phase, ↓reduceIte]
    exact norm_tau χ _ 4 (hn 4 (by decide) (by decide)) hψminus
  by_cases hj0 : j = 0
  · subst j
    simp only [phase, if_neg hj4, ↓reduceIte, norm_mul, norm_neg]
    rw [norm_tau χ ψ 2 (hn 2 (by decide) (by decide)) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num
  · simp only [phase, if_neg hj4, if_neg hj0, norm_mul]
    rw [norm_tau χ _ j (hn j hj0 hj6) hψminus,
      norm_tau χ ψ (j + 2) (shifted_power_nontrivial χ h6 hn j hj0 hj6 hj4) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num

end

open ActualEisensteinCubic

attribute [local instance] OAI.LocalReflectionBrackets.quotientField
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintype
theorem canonical_phase_norm (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (ε : (O ⧸ P)ˣ) :
    ‖phase (canonicalSextic P hgood) ψ j ε‖ = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  exact phase_norm (canonicalSextic P hgood) ψ (canonicalSextic_pow_six P hgood)
    (fun k hk0 hk6 => canonicalSextic_pow_ne_one P hgood hchar hk0 hk6) hψ j hj6 ε

end LocalReflectionBrackets

open scoped Classical BigOperators
open AddChar MulChar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
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

namespace LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar

section
variable {F : Type*} [Field F] [Fintype F]

theorem norm_bracket_nonexceptional_le_one (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) : ‖bracket χ j x‖ ≤ 1 := by
  rw [norm_bracket_nonexceptional χ j hj4 hj0]
  split_ifs <;> norm_num

theorem norm_bracket_zero_le (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ ≤ (rootCard F)⁻¹ := by
  rw [norm_bracket_zero]
  split_ifs <;> simp only [mul_zero, mul_one, le_refl]
  exact inv_nonneg.mpr rootCard_pos.le

open ActualEisensteinCubic

end

variable {F : Type*} [Field F] [Fintype F]

open ActualEisensteinCubic

end LocalReflectionBrackets

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

lemma derivativeSeminormSum_nonneg (g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [logPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end JointLogSeparation

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.DyadicKernel
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

open scoped BigOperators
namespace CompletedDyadic

theorem ramifiedScale_pos (ρ q : ℝ) (hρ : 0<ρ) (hq : 0<q) (m : ℕ) :
    0< ramifiedScale ρ q m := by unfold ramifiedScale; positivity

end CompletedDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedDyadicRows
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
namespace CompletedGauss

section

open ActualEisensteinCubic

theorem two_pow_clog_le_double (n : ℕ) (hn : 1≤n) : 2^Nat.clog 2 n≤2*n := by
  by_cases h : n=1
  · simp [h]
  have hn1 : 1<n := lt_of_le_of_ne hn (Ne.symm h)
  have hl : 0<Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hn1
  have he : (Nat.clog 2 n).pred+1=Nat.clog 2 n := Nat.succ_pred_eq_of_pos hl
  calc
    _ = 2^(Nat.clog 2 n).pred*2 := by rw [←he,pow_succ]; rfl
    _ ≤ n*2 := Nat.mul_le_mul_right 2 hp.le
    _ = _ := Nat.mul_comm _ _

open ActualEisensteinCubic CanonicalQuadraticSieve

end
section

open CompletedDyadic

theorem completedRamifiedStep_gt_one : 1<completedRamifiedStep := by
  exact Real.one_lt_rpow (by norm_num) (by norm_num)

end

open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.PolynomialHeight
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

open scoped BigOperators Classical

namespace CompletedHeight

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation

lemma sourceTwistCLM_apply (W g : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) (x : ℝ) :
    sourceTwistCLM W a b ha g x = W x*g (patchedLog a b ha x) := by
  change (SchwartzMap.smulLeftCLM ℂ (W : ℝ→ℂ)
    ((SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha)) g)) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply W.hasTemperateGrowth]
  rfl

theorem frequencyTwist_finite_bound (g : 𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ, ∃C : ℝ, 0 < C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤ C*(1+‖t‖)^n := by
  let n := S.sup Prod.snd
  let c : ℕ×ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2
  let C := 1+∑z∈S,c z
  have hc : ∀z,0≤ c z := fun z => by dsimp [c]; exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  have hC : 0<C := by dsimp [C]; have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z); linarith
  refine ⟨n,C,hC,?_⟩
  intro t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z≤C := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]
    linarith
  have hzn : z.2≤n := Finset.le_sup hz
  have hh := frequencyTwist_seminorm_polynomial g t z.1 z.2
  exact hh.trans (mul_le_mul hzC (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hzn)
    (by positivity) hC.le)

theorem normTwistedSource_schwartz (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support (W : ℝ→ℂ) ⊆ Icc a b) :
    ∃ G : ℝ→𝓢(ℝ,ℂ), (∀t x,G t x=normTwistedSource W t x) ∧
      (∀S : Finset (ℕ×ℕ), ∃n : ℕ, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G t)≤C*(1+‖t‖)^n) := by
  let M := |Real.log a|+|Real.log b|+1
  have hM : 0≤M := by dsimp [M]; positivity
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff M hM
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  let G : ℝ→𝓢(ℝ,ℂ) := fun t => sourceTwistCLM W a b ha (frequencyTwist V t)
  refine ⟨G,?_,?_⟩
  · intro t x
    rw [show G t x=sourceTwistCLM W a b ha (frequencyTwist V t) x from rfl,
      sourceTwistCLM_apply,frequencyTwist_apply]
    by_cases hx : W x=0
    · simp only [normTwistedSource,hx,zero_mul,mul_zero]
    · have hxi := hs hx
      rw [patchedLog_eq_log a b ha x hxi]
      have hlog : |Real.log x|≤M := by
        have hlo := Real.log_le_log ha hxi.1
        have hhi := Real.log_le_log (lt_of_lt_of_le ha hxi.1) hxi.2
        rw [abs_le]
        constructor <;> dsimp [M] <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),
          abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
      have hv : V (Real.log x)=1 := hvone _ hlog
      simp only [hv,mul_one,normTwistedSource]
      ring
  · intro S
    obtain ⟨s,C,hC,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
      (sourceTwistCLM W a b ha) S
    obtain ⟨n,D,hD,hbound⟩ := frequencyTwist_finite_bound V s
    refine ⟨n,C*D,mul_pos hC hD,?_⟩
    intro t
    exact (hcontrol _).trans ((mul_le_mul_of_nonneg_left (hbound t) hC.le).trans_eq (by ring))

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay
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

open scoped BigOperators Classical

namespace ShortDraftCusp

open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem norm_embedded_cubic_symbol (x a : Eis)
    (ha : lambda^2∣a-1) (hcop : IsCoprime x a) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol x a)‖=1 := by
  have hcube : ConcreteTraceCRT.eisEmbedding (symbol x a)^3=1 := by
    rw [←map_pow,symbol_cube_of_isCoprime x a ha hcop,map_one]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm hcube

theorem norm_A3_ramified_fixed_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣a-u*b-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b)*symbol c0 a)‖=1 := by
  have hfirst : ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b))‖=1 := by
    apply norm_embedded_cubic_symbol _ _ hA
    refine ⟨b*(c0*r-d),d,?_⟩
    linear_combination hdet
  have hsecond : ‖ConcreteTraceCRT.eisEmbedding (symbol c0 a)‖=1 := by
    apply norm_embedded_cubic_symbol _ _ ha
    refine ⟨-b*u*r,d,?_⟩
    linear_combination hdet
  rw [map_mul,norm_mul,hfirst,hsecond,one_mul]

theorem norm_A3_unramified_fixed_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hc : lambda^2∣c0-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol a c0)‖=1 := by
  apply norm_embedded_cubic_symbol _ _ hc
  refine ⟨d,-b*r,?_⟩
  linear_combination hdet

end ShortDraftCusp

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
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

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma dualIdealDyad_bounds (j : ℕ) (I : Ideal Eis) (hI : I∈dualIdealDyad j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hn,hj⟩:= (mem_dualIdealDyad I j).mp hI
  have hu:=Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl:=two_pow_clog_le_double (Ideal.absNorm I)
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn))
  rw [hj] at hu hl
  refine ⟨hn,?_,by exact_mod_cast hu⟩
  have he : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ):=by exact_mod_cast hl
  linarith

theorem tsum_dualIdealDyads
    (f : ℕ×NonzeroDualIdeal×NonzeroDualIdeal → ℂ) (hf : Summable f) :
    (∑'x, f x) = ∑'i : ℕ×ℕ×ℕ,
      ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
        f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  let g := f ∘ dualDyadicIndexEquiv.symm
  have hg : Summable g := dualDyadicIndexEquiv.symm.summable_iff.mpr hf
  calc
    _ = ∑'x,g x := (dualDyadicIndexEquiv.symm.tsum_eq f).symm
    _ = ∑'i,∑'x,g ⟨i,x⟩ := Summable.tsum_sigma' (fun _=>hasSum_fintype _ |>.summable) hg
    _ = _ := by
      apply tsum_congr
      intro i
      rw [tsum_fintype,Fintype.sum_prod_type]
      rfl

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.DualKernelSummability
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

namespace CompletedGauss
open scoped BigOperators Classical ContDiff
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzeroDualIdeal_norm_pos (I : NonzeroDualIdeal) :
    0<(Ideal.absNorm I.val:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

lemma nonzeroDualIdeal_inv_pow_summable (n : ℕ) (hn : 1<n) :
    Summable (fun I : NonzeroDualIdeal => ((Ideal.absNorm I.val:ℝ)^n)⁻¹) := by
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (n:ℂ)
    (by exact_mod_cast hn)).subtype (fun I : Ideal Eis => I≠0)
  apply hs.congr
  intro I
  simp only [Function.comp_apply,CubicEisenstein.fullIdealWeight,if_neg I.property,
    Complex.cpow_neg,Complex.cpow_natCast,norm_inv,norm_pow,Complex.norm_natCast]

lemma rawDualKernel_inverse_square (scale ρ q : ℝ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ =
      (scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹) := by
  simp only [mul_pow,mul_inv_rev,←pow_mul,←inv_pow]
  ring

theorem rawDualKernelTerm_summable_norm
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (scale ρ q B : ℝ) (hscale : 0<scale) (hρ : 0<ρ) (hq : 1<q)
    (hB : 0≤B) (β : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hβ : ∀m,∀I J : NonzeroDualIdeal,‖β m I.val J.val‖≤B) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm V scale ρ q β x‖) := by
  obtain ⟨C,hC,hdec⟩:=CubicReflectionKernel.paperKernel_euler_power_decay
    V a b ha hsupp hV 2 0
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hij := hi.mul_of_nonneg hj (fun I=>by positivity) (fun J=>by positivity)
  have hs := hg.mul_of_nonneg hij (fun m=>by positivity) (fun IJ=>by positivity)
  have hmajor := hs.mul_left (B*C*(scale^2*ρ^6)⁻¹)
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  have hn:=nonzeroDualIdeal_norm_pos x.2.1
  have hb:=nonzeroDualIdeal_norm_pos x.2.2
  have hx : 0<scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3 := by positivity
  have hk := (hdec _ hx).2
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
  norm_num only [Nat.cast_ofNat] at hk
  have hr : (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^(-(2:ℝ))=
      ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
  rw [hr,rawDualKernel_inverse_square] at hk
  calc
    _ = ‖β x.1 x.2.1.val x.2.2.val‖*
        ‖CubicReflectionKernel.paperKernel V
          (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)‖ := by
        rw [rawDualKernelTerm,norm_mul]
    _ ≤ B*(C*((scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹))) :=
      mul_le_mul (hβ x.1 x.2.1 x.2.2) hk (norm_nonneg _) hB
    _ = _ := by ring

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays
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

namespace CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspCoefficientBound_pos : 0<fixedCuspCoefficientBound :=
  (Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).1

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))

lemma sourceCuspCoefficients_squarefree_cube_bound (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J) :
    ‖(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)‖≤
      fixedCuspCoefficientBound*fixedCuspArrayWeight m J := by
  rcases helig with ⟨hsq,hI,hJ⟩
  have hb:=(Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).2
    I J hI hJ hsq u m
  rw [primaryGenerator_norm J hJ] at hb
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.1
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 false
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 true

lemma fixedCuspArray_zero_of_ineligible (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:¬fixedCuspArrayEligible I J) : fixedCuspArray j u m I J=0 := by
  simp only [fixedCuspArray,if_neg h]

lemma fixedCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedCuspArray j u m I J‖≤1 := by
  by_cases h:fixedCuspArrayEligible I J
  · have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
    rw [fixedCuspArray,if_pos h,norm_div,Complex.norm_real,Real.norm_of_nonneg hpos.le]
    exact (div_le_one hpos).mpr (sourceCuspCoefficients_squarefree_cube_bound j u m I J h)
  · simp only [fixedCuspArray,if_neg h,norm_zero,zero_le_one]

lemma fixedConjugateCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedConjugateCuspArray j u m I J‖≤1 := by
  simpa only [fixedConjugateCuspArray,norm_star] using fixedCuspArray_norm_le_one j u m I J

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.WeylRepresentatives
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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspArrayIndex_ne_zero (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) :
    fixedCuspArrayIndex u m I J≠0 :=
  mul_ne_zero (mul_ne_zero (ramifiedElement_ne_zero u m) hI) (pow_ne_zero _ hJ)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFullFrequency_eq_fixedCuspArrayIndex (p:ThetaFullIndex) :
    thetaFullFrequency p=fixedCuspArrayIndex p.1 p.2.1 p.2.2.1.val p.2.2.2.val := rfl

lemma sourceFrequencyAngle_norm (h:Eis) (hh:h≠0) : ‖sourceFrequencyAngle h‖=1 := by
  rw [sourceFrequencyAngle,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))

end

open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped Classical BigOperators

namespace CubicEisenstein
open scoped Classical BigOperators MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma amplitude_norm (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) : ‖s.amplitude u m I J‖≤1 := by
  by_cases he:fixedCuspArrayEligible I J
  · rw [amplitude,norm_mul,norm_mul,breveE_norm,
      sourceFrequencyAngle_norm _ (fixedCuspArrayIndex_ne_zero u m I J he.2.1 he.2.2),mul_one,mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  · simp only [amplitude,fixedConjugateCuspArray,
      fixedCuspArray_zero_of_ineligible _ _ _ _ _ he,star_zero,zero_mul,norm_zero]
    norm_num

end FixedCuspShape
end CubicEisenstein

open scoped BigOperators Classical Matrix MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.ResiduePhases
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

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4BadPhase_eq (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    A4BadPhase c0 hc0 d U x =
      ShortDraftTrace.breveE (-(eisEmbedding d*eisEmbedding U*(eisEmbedding x/eisLam^4))/eisEmbedding c0) := by
  change ShortDraftTrace.breveE
    (eisEmbedding (-d*U*x)/(eisEmbedding (ramifiedTraceLambda^3*c0)*eisLam))=_
  simp only [map_mul,map_pow,map_neg,ramifiedEmbedding_traceLambda]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc0]

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

attribute [local instance] OAI.ShortDraftCusp.A4frequencyField
lemma A4BadPhase_norm (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    ‖A4BadPhase c0 hc0 d U x‖=1 := by
  rw [A4BadPhase_eq]
  exact breveE_norm _

end ShortDraftCusp

open scoped BigOperators Classical

open scoped Classical BigOperators

open scoped Classical BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedConductor
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

open scoped Classical

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma basePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
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

open scoped Classical BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_ramified_relative_primary (M:SL(2,Eis)) (u:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    lambda^2∣(M 0 0-u*M 0 1)-1 := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  exact hA

end ShortDraftCusp

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property

end ControlledStratumArithmetic
end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedFrequencyExpansion
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

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

theorem fixedFactor_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1) : ‖D.fixedFactor‖=1 := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact norm_A3_unramified_fixed_factor _ _ _ _ _ (D.determinant (fun _=>1)) hbase
  · apply norm_A3_ramified_fixed_factor _ _ 1 (∏i,p i) _ c0
    · simpa only [one_mul] using D.determinant (fun _=>1)
    · exact D.numerator_primary h3N hr hbase (fun _=>1)
    · exact A3_ramified_relative_primary (D.matrix (fun _=>1)) c0
        (D.ramified_relative h3N hr hbase c0 (by simp) (fun _=>1))

end ControlledStratumArithmetic
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence
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

open scoped BigOperators Classical ContDiff

open scoped BigOperators Classical MatrixGroups

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

lemma numeratorFactor_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖(Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
      D.numeratorSupported) n‖≤1 := by
  change ‖Ψ n*numeratorBadTwist _ _ _ _ _ n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (numeratorBadTwist_norm _ _ _ _ _ n)

lemma fixedFactor_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖D.fixedFactor Ψ Q n‖≤1 := by
  change ‖((Ψ*numeratorBadTwist _ _ _ _ _) n)*(basePrimeRow _ _ _ n)‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (D.numeratorFactor_norm Ψ hΨ n)).trans (basePrimeRow_norm _ _ _ n)

end GoodMaskRowData

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MarkedPhase
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseMoment.markedPhaseFintype
theorem mixedActiveBracket_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) :
    mixedActiveBracket hp hg j S D i x = (if i ∈ S then (-1 : ℂ) else 1) *
      ((((actualSextic (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i))
          (markedActiveExponent S j i) (D.epsilon i) *
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (markedActiveExponent S j i)
          (Ideal.Quotient.mk _ x)) := by
  by_cases hi : i ∈ S
  · simp only [mixedActiveBracket, markedActiveExponent, hi,
      phase, bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
    ring
  · simp only [mixedActiveBracket, markedActiveExponent, hi, ite_false, one_mul]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Norms
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.phaseNormField
attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.phaseNormFinite
theorem local_phase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (i : ι) (j : ℕ) (hj : j < 6) :
    ‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i)‖ = 1 := by
  rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
  exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) j hj (D.epsilon i)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Canonical
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι : Type*} (G : PrimeFamily ι)

lemma generator_product [Fintype ι] :
    (∏ i, G.generator i) = primaryGenerator (∏ i, G.ideal i) := by
  change _ = primaryGeneratorHom (∏ i, G.ideal i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact primaryPrime_eq_primaryGenerator (G.ideal i)

end PrimeFamily

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Rows
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι κ : Type*}

lemma sum_product [Fintype ι] [Fintype κ] (G : PrimeFamily ι) (H : PrimeFamily κ) :
    (∏ i, (G.sum H).ideal i) = (∏ i, G.ideal i)*(∏ i, H.ideal i) := by
  simp only [sum,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]

lemma reflected_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i, (F.reflected K hK S).ideal i) = (∏ i, F.ideal i)*K*(∏ i, S.ideal i) := by
  rw [reflected,sum_product,sum_product,residual_product]
  ring

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Shape
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CubicKubota ConcreteTraceCRT CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma shapeArgument_mul (x y : Eis) : shapeArgument (x*y) = shapeArgument x*shapeArgument y := by
  unfold shapeArgument
  rw [← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,Complex.ofReal_mul,map_mul,mul_pow]
  exact mul_div_mul_comm _ _ _ _

lemma shapeArgument_norm (z : Eis) (hz : z ≠ 0) : ‖shapeArgument z‖ = 1 := by
  have hne : ‖eisEmbedding z‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hz))
  rw [shapeArgument,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ← eisEmbedding_norm_sq_eq_absNorm_span]
  exact div_self hne

lemma stratumShapeFactor_mul {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r P : Eis) :
    s.stratumShapeFactor (c*r*P) = s.stratumShapeFactor c*shapeArgument r*shapeArgument P := by
  have he (z : Eis) : s.stratumShapeFactor z =
      (-star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2)*shapeArgument z := by
    unfold FixedCuspShape.stratumShapeFactor shapeArgument
    ring
  rw [he (c*r*P),he c,shapeArgument_mul,shapeArgument_mul]
  ring

lemma actual_shape_separation {φ σ : Type*} [Fintype φ] [Fintype σ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H)
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    s.stratumShapeFactor (c*∏ i, (F.reflected K hK S).generator i) =
      s.stratumShapeFactor (c*primaryGenerator (∏ i, F.ideal i))*
        shapeArgument (primaryGenerator K)*shapeArgument (primaryGenerator (∏ i, S.ideal i)) := by
  rw [(F.reflected K hK S).generator_product,F.reflected_product K hK S,
    primaryGenerator_mul,primaryGenerator_mul]
  rw [show c*(primaryGenerator (∏ i, F.ideal i)*primaryGenerator K*primaryGenerator (∏ i, S.ideal i)) =
    (c*primaryGenerator (∏ i, F.ideal i))*primaryGenerator K*primaryGenerator (∏ i, S.ideal i) by ring]
  exact stratumShapeFactor_mul s _ _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.KernelGeometry
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma PrimeFamily.product_span {ι : Type*} [Fintype ι] (G : PrimeFamily ι) :
    Ideal.span {∏ i, G.generator i} = ∏ i, G.ideal i := by
  have hf (T : Finset ι) : Ideal.span {∏ i ∈ T, G.generator i} = ∏ i ∈ T, G.ideal i := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi,← Ideal.span_singleton_mul_span_singleton,
        G.generator_span,ih]
  exact hf Finset.univ

lemma reflected_conductor_norm {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ) =
      (Ideal.absNorm (Ideal.span {c}*(∏ i, F.ideal i)):ℝ)*
        (Ideal.absNorm K:ℝ)*(Ideal.absNorm (∏ i, S.ideal i):ℝ) := by
  rw [← Ideal.span_singleton_mul_span_singleton,PrimeFamily.product_span,F.reflected_product]
  simp only [map_mul,Nat.cast_mul]
  ring

lemma source_kernel_argument_factor {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (c : Eis) (X tau r : ℝ) (D1 D2 n b : Ideal Eis) :
    (X/(27*tau^2*(Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      r^3*(Ideal.absNorm (D1*n):ℝ)*(Ideal.absNorm (D2*b):ℝ)^3 =
    fixedKernelCoefficient X tau r (Ideal.span {c}*(∏ i, F.ideal i)) D1 D2 *
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 /
      ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2) := by
  rw [reflected_conductor_norm]
  simp only [fixedKernelCoefficient,map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.KernelActual
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma fixedKernelCoefficient_pos (X tau r : ℝ) (C D1 D2 : Ideal Eis)
    (hX : 0<X) (htau : 0<tau) (hr : 0< r) (hC : C≠0) (hD1 : D1≠0) (hD2 : D2≠0) :
    0<fixedKernelCoefficient X tau r C D1 D2 := by
  have hn (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hCn := hn C hC
  have h1 := hn D1 hD1
  have h2 := hn D2 hD2
  unfold fixedKernelCoefficient
  positivity

lemma actualKernelCoefficient_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c≠0) (m : ℕ) (X : ℝ) (hX : 0<X) : 0<actualKernelCoefficient F s m X := by
  apply fixedKernelCoefficient_pos _ _ _ _ _ _ hX (sourceCuspScale_pos _)
    (ramifiedScale_pos _ _ (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _) _ one_ne_zero one_ne_zero
  apply mul_ne_zero
  · exact Ideal.span_singleton_eq_bot.not.mpr hc
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i))

theorem actual_theta_kernel_argument (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (m : ℕ) (X : ℝ) (n b : Ideal Eis) :
    (X/(27*(sourceCuspScale s.index)^2*
      (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 =
    actualKernelCoefficient F s m X*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3/
      ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2) := by
  simpa only [one_mul,actualKernelCoefficient] using source_kernel_argument_factor F K hK S c
    X (sourceCuspScale s.index) (ramifiedScale 1 completedRamifiedStep m) 1 1 n b

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.CrudeCoefficient
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma norm_bracket_le_card {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (j : ℕ) (x : F) : ‖bracket χ j x‖≤(Fintype.card F:ℝ) := by
  have hq : (1:ℝ)≤Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0:F)⟩
  have hr : 1≤ rootCard F := by
    unfold rootCard
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hq)
  have hi : (rootCard F)⁻¹≤1 := (inv_le_one₀ rootCard_pos).mpr hr
  by_cases hj4 : j=4
  · subst j
    by_cases hx : x=0
    · subst x
      rw [norm_bracket_four_zero]
      apply (div_le_iff₀ rootCard_pos).mpr
      nlinarith
    · rw [norm_bracket_four_nonzero χ x hx]
      exact hi.trans hq
  · by_cases hj0 : j=0
    · subst j
      exact (norm_bracket_zero_le χ x).trans (hi.trans hq)
    · exact (norm_bracket_nonexceptional_le_one χ j hj4 hj0 x).trans hq

variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

lemma mixedActiveBracket_crude_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (i : ι) (x : Eis) :
    ‖mixedActiveBracket G.generator_ne_zero G.generator_good j S D i x‖≤(Ideal.absNorm (G.ideal i):ℝ) := by
  rw [mixedActiveBracket_eq_signed]
  have hn : ‖(if i∈S then (-1:ℂ) else 1)‖=1 := by split_ifs <;> simp
  have hjm : markedActiveExponent S j i<6 := by
    unfold markedActiveExponent
    split_ifs
    · norm_num
    · exact hj i
  have hc : ∀ i, ringChar (Eis⧸Ideal.span {G.generator i})≠2 := by
    intro i
    rw [G.generator_span]
    exact hchar i
  rw [norm_mul,hn,one_mul,norm_mul,local_phase_norm D G.generator_ne_zero G.generator_good hc i _ hjm,one_mul]
  apply (norm_bracket_le_card _ _ _).trans_eq
  have he : Fintype.card (Eis⧸Ideal.span {G.generator i})=Ideal.absNorm (Ideal.span {G.generator i}) := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  rw [he,G.generator_span]

lemma literal_mixed_coefficient_crude (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    ‖s.amplitude u m n b *
      (star D.fixedFactor*ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m n b))*
      ∏ i, mixedActiveBracket G.generator_ne_zero G.generator_good j S D i (s.modelDualNumerator u m n b)‖≤
      (Ideal.absNorm (∏ i,G.ideal i):ℝ) := by
  rw [norm_mul,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN G.generator_product_primary hbase,
    ShortDraftCusp.A4BadPhase_norm,one_mul,mul_one]
  apply (mul_le_of_le_one_left (norm_nonneg _) (s.amplitude_norm u m n b)).trans
  rw [norm_prod,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod (fun i hi => norm_nonneg _) (fun i hi => mixedActiveBracket_crude_norm G D hchar j hj S i _)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RawTail
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma rawTailWeight_nonneg (q : ℝ) (x : RawTailIndex) : 0≤ rawTailWeight q x := by
  unfold rawTailWeight
  positivity

lemma rawTailWeight_summable (q : ℝ) (hq : 1<q) : Summable (rawTailWeight q) := by
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hh := hg.mul_of_nonneg (hi.mul_of_nonneg hj (fun I => by positivity) (fun J => by positivity))
    (fun m => by positivity) (fun IJ => by positivity)
  exact hh.congr (fun x => by simp only [rawTailWeight]; ring)

lemma tail_power_gain (A : ℕ) (T x : ℝ) (hT : 0<T) (hTx : T≤x) :
    x^(-((A+2:ℕ):ℝ))≤T^(-(A:ℝ))*(x^2)⁻¹ := by
  have hx : 0<x := lt_of_lt_of_le hT hTx
  rw [show -((A+2:ℕ):ℝ)=-(A:ℝ)+(-2) by push_cast; ring,Real.rpow_add hx]
  rw [show x^(-2:ℝ)=(x^2)⁻¹ by rw [Real.rpow_neg hx.le,Real.rpow_two]]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hT hTx (neg_nonpos.mpr (Nat.cast_nonneg A))) (by positivity)

theorem raw_kernel_tail (a b q : ℝ) (ha : 0<a) (hq : 1<q) (A : ℕ) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a b →
    ∀ (scale ρ B T : ℝ), 0<scale → 0<ρ → 0≤B → 0<T →
    ∀ (β : ℕ→Ideal Eis→Ideal Eis→ℂ),
      (∀ m, ∀ I J : NonzeroDualIdeal, ‖β m I.val J.val‖≤B) →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤ scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
    Summable (fun x => ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖) ∧
      ‖∑' x, if cut x then rawDualKernelTerm V scale ρ q β x else 0‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*B*T^(-(A:ℝ))*(scale^2*ρ^6)⁻¹ := by
  obtain ⟨S,C,hC,hkernel⟩ := CubicReflectionKernel.paperKernel_euler_source_power_decay a b ha (A+2) 0
  let D : ℝ := (∑' x,rawTailWeight q x)+1
  have hsum := rawTailWeight_summable q hq
  have hD : 0<D := by
    have h : 0≤∑' x,rawTailWeight q x := tsum_nonneg (rawTailWeight_nonneg q)
    dsimp only [D]
    linarith
  refine ⟨S,C*D,mul_pos hC hD,?_⟩
  intro V hV scale ρ B T hs hρ hB hT β hβ cut hcut
  let M : ℝ := C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*B*T^(-(A:ℝ))*(scale^2*ρ^6)⁻¹
  have hM : 0≤M := by dsimp only [M]; positivity
  have hmajor : ∀ x : RawTailIndex,
      ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖≤M*rawTailWeight q x := by
    intro x
    by_cases hx : cut x
    · rw [if_pos hx,rawDualKernelTerm,norm_mul]
      let arg := scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3
      have harg : 0<arg := lt_of_lt_of_le hT (hcut x hx)
      have hk := (hkernel V hV arg harg).2
      simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
      have hp := tail_power_gain A T arg hT (hcut x hx)
      have hk' := hk.trans (mul_le_mul_of_nonneg_left hp (by positivity :
        0≤C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V))
      apply (mul_le_mul (hβ x.1 x.2.1 x.2.2) hk' (norm_nonneg _) hB).trans_eq
      dsimp only [M,arg]
      rw [rawDualKernel_inverse_square]
      unfold rawTailWeight
      ring
    · rw [if_neg hx,norm_zero]
      exact mul_nonneg hM (rawTailWeight_nonneg q x)
  have hn := (hsum.mul_left M).of_nonneg_of_le (fun x => norm_nonneg _) hmajor
  refine ⟨hn,?_⟩
  calc
    _ ≤ ∑' x, ‖if cut x then rawDualKernelTerm V scale ρ q β x else 0‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' x, M*rawTailWeight q x := hn.tsum_le_tsum hmajor (hsum.mul_left M)
    _ = M*(∑' x,rawTailWeight q x) := tsum_mul_left
    _ ≤ M*D := mul_le_mul_of_nonneg_left (by dsimp only [D]; linarith) hM
    _ = _ := by dsimp only [M]; ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RawCoefficient
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

lemma literalRawCoefficient_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (u : Eisˣ) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖literalRawCoefficient G D s hc j S u m n.val b.val‖≤(Ideal.absNorm (∏ i,G.ideal i):ℝ) := by
  unfold literalRawCoefficient
  split_ifs
  · have hr : 1≤ ramifiedScale 1 completedRamifiedStep m := by
      simpa only [ramifiedScale,one_mul] using one_le_pow₀ completedRamifiedStep_gt_one.le (n:=m)
    have hn : 1≤Real.sqrt (Ideal.absNorm n.val:ℝ) :=
      (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by simpa using norm_at_least_one n.val n.property)
    have hb := norm_at_least_one b.val b.property
    have hden : 1≤ ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr hn) hb
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (le_trans zero_le_one hden)]
    apply (div_le_div_of_nonneg_right (literal_mixed_coefficient_crude G D s hc hN hbase hchar j hj S u m n.val b.val)
      (le_trans zero_le_one hden)).trans
    exact div_le_self (Nat.cast_nonneg _) hden
  · simp only [norm_zero]
    exact Nat.cast_nonneg _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FullRaw
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

lemma thetaRawIndex_injective : Function.Injective thetaRawIndex := by
  rintro ⟨u,m,⟨n,hn⟩,⟨b,hb⟩⟩ ⟨v,k,⟨n',hn'⟩,⟨b',hb'⟩⟩ h
  simpa only [thetaRawIndex,Prod.mk.injEq,Subtype.mk.injEq] using h

lemma literalRawScale_pos (G : PrimeFamily ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X : ℝ) (hX : 0<X) : 0<literalRawScale G s X := by
  have hn : (0:ℝ)<Ideal.absNorm (Ideal.span {c*∏ i,G.generator i}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => G.generator_ne_zero i)))))
  have hs := sourceCuspScale_pos s.index
  unfold literalRawScale
  positivity

lemma literalRawSeries_support (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    Function.support (literalRawSeries G D s hc j S W X)⊆Set.range thetaRawIndex := by
  intro t ht
  have hp : Squarefree t.2.2.1.val ∧ primaryGenerator t.2.2.1.val≠0 ∧ primaryGenerator t.2.2.2.val≠0 := by
    by_contra hn
    exact ht (by simp only [literalRawSeries,rawDualKernelTerm,literalRawCoefficient,if_neg hn,zero_mul])
  exact ⟨(t.1,t.2.1,⟨t.2.2.1.val,hp.1,hp.2.1⟩,⟨t.2.2.2.val,hp.2.2⟩),rfl⟩

theorem mixedReflectedValue_eq_fullRaw (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        ∑' t : Eisˣ×RawTailIndex, literalRawSeries G D s hc j S W X t := by
  unfold mixedReflectedValue
  congr 1
  refine (tsum_congr ?_).trans (thetaRawIndex_injective.tsum_eq (literalRawSeries_support G D s hc j S W X))
  intro t
  have hx : sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)=
      s.modelDualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  unfold literalRawSeries rawDualKernelTerm literalRawCoefficient thetaRawIndex literalRawScale
  rw [if_pos ⟨t.2.2.1.property.1,t.2.2.1.property.2,t.2.2.2.property⟩,hx]
  dsimp only
  simp only [ramifiedScale, one_mul]
  ring

theorem literalRawSeries_summable_norm (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    Summable (fun t : Eisˣ×RawTailIndex => ‖literalRawSeries G D s hc j S W X t‖) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_,(hasSum_fintype _).summable⟩
  intro u
  exact rawDualKernelTerm_summable_norm (Vstar W) lo hi hlo (Vstar_support W lo hi hWs)
    (Vstar_contDiff W lo hi hlo hWs hW) (literalRawScale G s X) 1 completedRamifiedStep
    (Ideal.absNorm (∏ i,G.ideal i):ℝ) (literalRawScale_pos G s hc X hX) (by norm_num)
    completedRamifiedStep_gt_one (Nat.cast_nonneg _) (literalRawCoefficient G D s hc j S u)
    (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u)
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FullDyadic
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

theorem mixedReflectedValue_eq_dyadic (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    mixedReflectedValue D s G.generator_ne_zero hc G.generator_good j S W X=
      fixedRadialCoefficientScalar*s.stratumShapeFactor (c*∏ i,G.generator i)*
        ∑' u : Eisˣ, ∑' i : ℕ×ℕ×ℕ, literalDyadicBlock G D s hc j S W X u i := by
  have hs := (literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm
  rw [mixedReflectedValue_eq_fullRaw,hs.tsum_prod]
  congr 1
  apply tsum_congr
  intro u
  exact tsum_dualIdealDyads _ (hs.prod_factor u)

lemma dyadic_kernel_argument_lower (scale rho q : ℝ) (hs : 0≤ scale)
    (hr : 0≤ rho) (hq : 0≤q) (i : ℕ×ℕ×ℕ)
    (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
    scale*(ramifiedScale rho q i.1)^3*(2:ℝ)^i.2.2*((2:ℝ)^i.2.1)^3/16 ≤
      scale*(ramifiedScale rho q i.1)^3*(Ideal.absNorm n.val:ℝ)*(Ideal.absNorm b.val:ℝ)^3 := by
  have hn := (dualIdealDyad_bounds _ _ n.property).2.1
  have hb := (dualIdealDyad_bounds _ _ b.property).2.1
  have hp : 0≤ scale*(ramifiedScale rho q i.1)^3 := by
    unfold ramifiedScale
    positivity
  have hh := mul_le_mul hn (pow_le_pow_left₀ (by positivity) hb 3) (by positivity)
    (Nat.cast_nonneg (Ideal.absNorm n.val))
  have hh' := mul_le_mul_of_nonneg_left hh hp
  nlinarith only [hh']

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.DyadicTail
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

lemma rawDyadicCenter_lower (scale : ℝ) (hs : 0≤ scale) (x : RawTailIndex) :
    rawDyadicCenter scale (rawDyadicLabel x)/16 ≤
      scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3 := by
  exact dyadic_kernel_argument_lower scale 1 completedRamifiedStep hs (by norm_num)
    (le_trans zero_le_one completedRamifiedStep_gt_one.le) (rawDyadicLabel x)
    ⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩
    ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩

theorem tsum_cut_dyadic (f : RawTailIndex→ℂ) (cut : (ℕ×ℕ×ℕ)→Prop)
    (hf : Summable (fun x => if cut (rawDyadicLabel x) then f x else 0)) :
    (∑' x, if cut (rawDyadicLabel x) then f x else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
            ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0 := by
  rw [tsum_dualIdealDyads _ hf]
  apply tsum_congr
  intro i
  have hl (n : dualIdealDyad i.2.2) (b : dualIdealDyad i.2.1) :
      rawDyadicLabel (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
        ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩)=i := by
    simp only [rawDyadicLabel,((mem_dualIdealDyad _ _).mp n.property).2,
      ((mem_dualIdealDyad _ _).mp b.property).2]
  by_cases hi : cut i
  · simp only [hl,if_pos hi]
  · simp only [hl,if_neg hi,Finset.sum_const_zero]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.ReflectedArithmeticHeight
namespace OAI

namespace SevenEighths.InverseReflectedArithmeticHeight
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
open InverseReflectedPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v w

theorem literal_reflected_raw_tail_arithmetic_uniform (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤ scale*(ramifiedScale 1 completedRamifiedStep x.1)^3*
        (Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
      Summable (fun x => ‖if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep
        (literalRawCoefficient G D s hc j S u) x else 0‖) ∧
      ‖∑' x, if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep
        (literalRawCoefficient G D s hc j S u) x else 0‖≤
      C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := raw_kernel_tail a₀ b₀ completedRamifiedStep ha₀ completedRamifiedStep_gt_one A
  refine ⟨orders,C,hC,?_⟩
  intro N a c mode V hV ι _ G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  have hh := hb V hV scale 1 (Ideal.absNorm (∏ i,G.ideal i):ℝ) T hs (by norm_num) (Nat.cast_nonneg _) hT
    (literalRawCoefficient G D s hc j S u) (literalRawCoefficient_norm G D s hc hN hbase hchar j hj S u) cut hcut
  simpa only [one_pow,mul_one] using hh

theorem literal_reflected_dyadic_tail_arithmetic_uniform (lo hi : ℝ) (hlo : 0<lo) (A : ℕ) :
    ∃ (orders : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi →
    ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (scale T : ℝ), 0<scale → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤ rawDyadicCenter scale i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          rawDualKernelTerm V scale 1 completedRamifiedStep
            (literalRawCoefficient G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0‖≤
        C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(scale^2)⁻¹ := by
  obtain ⟨orders,C,hC,hb⟩ := literal_reflected_raw_tail_arithmetic_uniform lo hi hlo A
  refine ⟨orders,C,hC,?_⟩
  intro N a c mode V hV ι _ G D s hc hN hbase hchar j hj S u scale T hs hT cut hcut
  obtain ⟨hn,hh⟩ := hb (N:=N) (a:=a) (c:=c) (mode:=mode) V hV G D s hc hN hbase hchar j hj S u scale T hs hT
    (fun x => cut (rawDyadicLabel x)) (fun x hx => by
      have hc' := hcut (rawDyadicLabel x) hx
      have hl := rawDyadicCenter_lower scale hs.le x
      linarith)
  rw [tsum_cut_dyadic _ cut hn.of_norm] at hh
  exact hh

theorem literal_dyadic_tail_height_arithmetic_uniform (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {ι : Type u} [Fintype ι], ∀ (G : PrimeFamily ι) (D : ControlledStratumArithmetic G.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸G.ideal i)≠2) →
    ∀ (j : ι→ℕ), (∀ i, j i<6) → ∀ (S : Finset ι) (u : Eisˣ) (θ X T : ℝ), 0<X → 0<T →
    ∀ cut : (ℕ×ℕ×ℕ)→Prop,
      (∀ i, cut i → 16*T≤ rawDyadicCenter (literalRawScale G s X) i) →
      ‖∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by
  obtain ⟨orders,C,hC,hbound⟩ := literal_reflected_dyadic_tail_arithmetic_uniform lo hi hlo A
  let V := vstarSchwartz W lo hi hlo hWs hW
  have hV : Function.support (V : ℝ→ℂ)⊆Set.Icc lo hi := Vstar_support W lo hi hWs
  obtain ⟨H,hH,hpoly⟩ := CompletedHeight.normTwistedSource_schwartz V lo hi hlo hV
  obtain ⟨degree,C₁,hC₁,hsemi⟩ := hpoly orders
  have hlink (θ : ℝ) : (H θ : ℝ→ℂ)=Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hH θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hHs (θ : ℝ) : Function.support (H θ : ℝ→ℂ)⊆Set.Icc lo hi := by
    intro x hx
    change H θ x≠0 at hx
    rw [hH θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  refine ⟨degree,C*C₁,mul_pos hC hC₁,?_⟩
  intro N a c mode ι _ G D s hc hN hbase hchar j hj S u θ X T hX hT cut hcut
  have hh := hbound (N:=N) (a:=a) (c:=c) (mode:=mode) (H θ) (hHs θ) G D s hc hN hbase hchar j hj S u
    (literalRawScale G s X) T (literalRawScale_pos G s hc X hX) hT cut hcut
  have hleft : (∑' i : ℕ×ℕ×ℕ, if cut i then
        ∑ n : dualIdealDyad i.2.2, ∑ b : dualIdealDyad i.2.1,
          rawDualKernelTerm (H θ) (literalRawScale G s X) 1 completedRamifiedStep
            (literalRawCoefficient G D s hc j S u)
            (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
              ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) else 0)=
      ∑' i : ℕ×ℕ×ℕ, if cut i then
        literalDyadicBlock G D s hc j S (CompletedHeight.normTwistedSource W θ) X u i else 0 := by
    simp only [rawDualKernelTerm,hlink,literalDyadicBlock,literalRawSeries]
  rw [hleft] at hh
  apply hh.trans
  have hsemi' := mul_le_mul_of_nonneg_left (hsemi θ) hC.le
  have hrest : 0≤(Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹ := by positivity
  calc
    _ = (C*orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (H θ))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) := by ring
    _ ≤ (C*(C₁*(1+‖θ‖)^degree))*
        ((Ideal.absNorm (∏ i,G.ideal i):ℝ)*T^(-(A:ℝ))*(literalRawScale G s X^2)⁻¹) :=
      mul_le_mul_of_nonneg_right hsemi' hrest
    _ = _ := by ring

end
end SevenEighths.InverseReflectedArithmeticHeight

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.DyadicBox
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma ramifiedScale_one_cube (m : ℕ) : (ramifiedScale 1 completedRamifiedStep m)^3=(3:ℝ)^m := by
  have hs : completedRamifiedStep^3=(3:ℝ) := by
    unfold completedRamifiedStep
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  simp only [ramifiedScale,one_mul]
  rw [← pow_mul,Nat.mul_comm m 3,pow_mul,hs]

lemma rawDyadicCenter_pow_lower (scale : ℝ) (hs : 0≤ scale) (i : ℕ×ℕ×ℕ) :
    scale*(2:ℝ)^(i.1+i.2.2+3*i.2.1)≤ rawDyadicCenter scale i := by
  unfold rawDyadicCenter
  rw [ramifiedScale_one_cube,pow_add,pow_add,Nat.mul_comm 3 i.2.1,pow_mul]
  simp only [mul_assoc]
  have hm : (2:ℝ)^i.1≤(3:ℝ)^i.1 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  gcongr

lemma center_mem_retainedDyadicBox (scale B : ℝ) (hs : 0<scale)
    (i : ℕ×ℕ×ℕ) (hi : rawDyadicCenter scale i≤B) : i∈retainedDyadicBox scale B := by
  let R := max 1 (B/scale)
  have hR : 1≤R := le_max_left _ _
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤R :=
    ((le_div_iff₀ hs).mpr (by nlinarith only [rawDyadicCenter_pow_lower scale hs.le i,hi])).trans (le_max_right _ _)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(i.1+i.2.2+3*i.2.1)) hp
  rw [Real.log_pow] at hl
  have hc : ((i.1+i.2.2+3*i.2.1:ℕ):ℝ)≤ columnDyadicLength R := by
    apply le_trans ((le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr hl)
    exact Nat.le_ceil _
  have hc' : i.1+i.2.2+3*i.2.1≤ columnDyadicLength R := by exact_mod_cast hc
  simp only [retainedDyadicBox,Finset.mem_product,Finset.mem_range]
  change i.1<columnDyadicLength R+1 ∧ i.2.1<columnDyadicLength R+1 ∧ i.2.2<columnDyadicLength R+1
  omega

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.TruncatedSource
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

lemma mem_retainedDyads (scale B : ℝ) (hs : 0<scale) (i : ℕ×ℕ×ℕ) :
    i∈retainedDyads scale B ↔ rawDyadicCenter scale i≤B := by
  simp only [retainedDyads,Finset.mem_filter]
  exact ⟨And.right,fun hi => ⟨center_mem_retainedDyadicBox scale B hs i hi,hi⟩⟩

lemma literalDyadicBlock_summable (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) (u : Eisˣ) :
    Summable (literalDyadicBlock G D s hc j S W X u) := by
  have hs := ((literalRawSeries_summable_norm G D s hc hN hbase hchar j hj S W lo hi hlo hWs hW X hX).of_norm).prod_factor u
  have hh := (dualDyadicIndexEquiv.symm.summable_iff.mpr hs).sigma
  apply hh.congr
  intro i
  simp only [tsum_fintype,Fintype.sum_prod_type,literalDyadicBlock,Function.comp_apply]
  rfl

lemma tsum_sub_finset_eq_tail {α : Type*} (f : α→ℂ) (hf : Summable f) (A : Finset α) :
    (∑' i,f i)-(∑ i∈A,f i)=∑' i,if i∉A then f i else 0 := by
  have hh := hf.sum_add_tsum_subtype_compl A
  have ht : (∑' x : {x // x∉A}, f x.val)=∑' i,if i∉A then f i else 0 := by
    calc
      _ = ∑' x, ({x | x∉A} : Set α).indicator f x := tsum_subtype {x | x∉A} f
      _ = _ := by
        apply tsum_congr
        intro i
        by_cases hi : i∈A <;> simp [hi]
  rw [ht] at hh
  exact eq_sub_of_add_eq' hh |>.symm

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FamilyTail
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma familyRawScale_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0<X) (hQK : 0<QK) (hQP : 0<QP) : 0<familyRawScale F s X QK QP :=
  div_pos (actualKernelCoefficient_pos F s hc 0 X hX) (mul_pos (sq_pos_of_pos hQK) (sq_pos_of_pos hQP))

lemma literalRawScale_reflected (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X : ℝ) :
    literalRawScale (F.reflected K hK S) s X=
      actualKernelCoefficient F s 0 X/((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i,S.ideal i):ℝ)^2) := by
  have hh := actual_theta_kernel_argument F K hK S s 0 X 1 1
  simpa only [map_one,Nat.cast_one,one_pow,mul_one,ramifiedScale,pow_zero,literalRawScale] using hh

lemma familyRawScale_le_literal (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0<X)
    (hKr : (Ideal.absNorm K:ℝ)≤QK) (hPr : (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP) :
    familyRawScale F s X QK QP≤literalRawScale (F.reflected K hK S) s X := by
  rw [literalRawScale_reflected]
  have hk : (0:ℝ)<Ideal.absNorm K := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hK.1)
  have hp : (0:ℝ)<Ideal.absNorm (∏ i,S.ideal i) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))))
  apply div_le_div_of_nonneg_left (actualKernelCoefficient_pos F s hc 0 X hX).le (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ hk.le hKr 2) (pow_le_pow_left₀ hp.le hPr 2) (sq_nonneg _) (sq_nonneg _)

lemma reflected_norm_le_centers (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (QK QP : ℝ) (hKr : (Ideal.absNorm K:ℝ)≤QK)
    (hPr : (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP) :
    (Ideal.absNorm (∏ i,(F.reflected K hK S).ideal i):ℝ)≤
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP := by
  rw [F.reflected_product]
  simp only [map_mul,Nat.cast_mul]
  have hk : 0≤QK := le_trans (Nat.cast_nonneg _) hKr
  exact mul_le_mul (mul_le_mul_of_nonneg_left hKr (Nat.cast_nonneg _)) hPr
    (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hk)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FamilyTailUniformDegree
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem original_family_dyadic_tail_uniform_degree (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
      (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸(F.reflected K hK S).ideal i)≠2) →
    ∀ jF : φ→ℕ, (∀ i, jF i<6) → ∀ (u : Eisˣ) (θ X T QK QP : ℝ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP →
      ‖∑' i : ℕ×ℕ×ℕ, if i∉retainedDyads (familyRawScale F s X QK QP) (16*T) then
        literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
          (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
  obtain ⟨degree,C,hC,hbound⟩ := InverseReflectedArithmeticHeight.literal_dyadic_tail_height_arithmetic_uniform lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S D s hc hN hbase hchar jF hj u θ X T QK QP hX hT hQK hQP hKr hPr
  have hs := familyRawScale_le_literal F K hK S s hc X QK QP hX hKr hPr
  have hsp := familyRawScale_pos F s hc X QK QP hX hQK hQP
  have hcut (i : ℕ×ℕ×ℕ) (hi : i∉retainedDyads (familyRawScale F s X QK QP) (16*T)) :
      16*T≤ rawDyadicCenter (literalRawScale (F.reflected K hK S) s X) i := by
    have hlt := lt_of_not_ge (fun h => hi ((mem_retainedDyads _ _ hsp i).mpr h))
    apply hlt.le.trans
    unfold rawDyadicCenter
    rw [ramifiedScale_one_cube]
    gcongr
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hh := hbound (N:=N) (a:=a) (c:=c) (mode:=mode) (F.reflected K hK S) D s hc hN hbase hchar (reflectedExponent jF) hj'
    (slotIndices φ (PrimeIndex K) σ) u θ X T hX hT
    (fun i => i∉retainedDyads (familyRawScale F s X QK QP) (16*T)) hcut
  have hleft : ‖∑' i : ℕ×ℕ×ℕ, if i∉retainedDyads (familyRawScale F s X QK QP) (16*T) then
        literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
          (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
      C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ i,(F.reflected K hK S).ideal i):ℝ)*T^(-(A:ℝ))*
        (literalRawScale (F.reflected K hK S) s X^2)⁻¹ := by
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈retainedDyads (familyRawScale F s X QK QP) (16*T) <;> simp [hi]
  apply hleft.trans
  have hnorm := reflected_norm_le_centers F K hK S QK QP hKr hPr
  gcongr
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.WholeRow
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sum_tsum_tsum_finite_middle {α β γ : Type*} [Fintype β]
    (L : Finset α) (f : α→β→γ→ℂ) (hf : ∀ p∈L, ∀ u, Summable (f p u)) :
    (∑ p∈L,∑' u,∑' i,f p u i)=∑' u,∑' i,∑ p∈L,f p u i := by
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact (Summable.tsum_finsetSum (fun p hp => hf p hp u)).symm

theorem literalWholeRow_eq_dyadic (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2)
    (hj : ∀ i,jF i<6) (hprod : ∀ P∈Pset,(∏ j,(S P).ideal j)=P)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo) (hWs : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (θ X : ℝ) (hX : 0<X) (r aw : Ideal Eis→ℂ) :
    literalWholeRow F K hK S jF Pset D s hc W θ X r aw=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X
            (fun K => r K*shapeArgument (primaryGenerator K))
            (fun P => aw P*shapeArgument (primaryGenerator P)) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hts := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) u i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let wt := fun P : L => (r K*shapeArgument (primaryGenerator K))*(aw P.val.val*shapeArgument (primaryGenerator P.val.val))
  have hs (P : L) (u : Eisˣ) : Summable (fun i => wt P*block P u i) :=
    (literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX u).mul_left _
  have hp (P : L) : r K*aw P.val.val*
      mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
        (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
        (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,wt P*block P u i := by
    rw [mixedReflectedValue_eq_dyadic (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX,
      actual_shape_separation,hprod P.val.val P.val.property]
    simp only [tsum_mul_left]
    dsimp only [wt,block]
    ring
  unfold literalWholeRow
  simp_rw [hp]
  rw [←Finset.mul_sum,sum_tsum_tsum_finite_middle Finset.univ (fun P u i => wt P*block P u i) (fun P _ u => hs P u)]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RowTail
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma finite_weighted_truncation {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β)
    (hf : ∀ p, Summable (f p)) :
    (∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)=
      ∑ p,w p*((∑' i,f p i)-∑ i∈J,f p i) := by
  rw [Summable.tsum_finsetSum (fun p _ => (hf p).mul_left (w p)),Finset.sum_comm]
  simp only [tsum_mul_left,←Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]

lemma finite_weighted_truncation_norm {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β) (E : ℝ)
    (hf : ∀ p, Summable (f p)) (hw : ∀ p,‖w p‖≤1)
    (he : ∀ p, ‖(∑' i,f p i)-∑ i∈J,f p i‖≤E) :
    ‖(∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)‖≤Fintype.card α*E := by
  rw [finite_weighted_truncation f w J hf]
  calc
    _ ≤ ∑ p,‖w p*((∑' i,f p i)-∑ i∈J,f p i)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : α,E := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw p) (norm_nonneg _)).trans (by simpa using he p)
    _ = _ := by simp

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.RowTailUniformDegree
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem original_family_row_tail_uniform_degree (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
    ∀ (u : Eisˣ) (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖(∑' i : ℕ×ℕ×ℕ,literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw)-
        ∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw‖≤
        Pset.card*(C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_dyadic_tail_uniform_degree lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod u θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hs (P : L) : Summable (block P) :=
    literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo
      ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  have he (P : L) : ‖(∑' i,block P i)-∑ i∈J,block P i‖≤
      C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
    rw [tsum_sub_finset_eq_tail (block P) (hs P) J]
    have hh := hbound F K hK (S P.val.val) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) jF hj u θ X T QK QP hX hT hQK hQP hKr
      (by rw [hprod P.val.val P.val.property]; exact hPr P.val.val P.val.property)
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈J <;> simp [J] at hi ⊢ <;> simp [hi,block]
  have hw (P : L) : ‖r K*aw P.val.val‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul hr (haw P.val.val P.val.property) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hh := finite_weighted_truncation_norm block (fun P : L => r K*aw P.val.val) J _ hs hw he
  change ‖(∑' i,∑ P : L,r K*aw P.val.val*block P i)-∑ i∈J,∑ P : L,r K*aw P.val.val*block P i‖≤_
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Fintype.card_subtype_le (fun P : Pset => IsCoprime K P.val)).trans_eq (Fintype.card_coe Pset)
  · positivity
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ShapeWeights
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma stratumShapeFactor_mul_one {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r : Eis) :
    s.stratumShapeFactor (c*r)=s.stratumShapeFactor c*shapeArgument r := by
  simpa only [mul_one,shapeArgument_one] using stratumShapeFactor_mul s c r 1

lemma primeFamily_primary_product_ne_zero {φ : Type*} [Fintype φ] (F : PrimeFamily φ) :
    primaryGenerator (∏ i,F.ideal i)≠0 := by
  rw [←F.generator_product]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => F.generator_ne_zero i)

lemma stratumShapeFactor_frozen_norm {φ : Type*} [Fintype φ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H) (c : Eis) (F : PrimeFamily φ) :
    ‖s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i))‖=‖s.stratumShapeFactor c‖ := by
  rw [stratumShapeFactor_mul_one,norm_mul,shapeArgument_norm _ (primeFamily_primary_product_ne_zero F),mul_one]

lemma row_shape_weight_norm (r : Ideal Eis→ℂ) (K : Ideal Eis) (hK : Admissible K) :
    ‖r K*shapeArgument (primaryGenerator K)‖=‖r K‖ := by
  have hk := PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors K hK.1 (fun P hP => (hK.2.2 P hP).1)
  rw [norm_mul,shapeArgument_norm _ hk,mul_one]

lemma slot_shape_weight_norm (aw : Ideal Eis→ℂ) (P : Ideal Eis) (hP : CubicSieve.Admissible P) :
    ‖aw P*shapeArgument (primaryGenerator P)‖=‖aw P‖ := by
  rw [norm_mul,shapeArgument_norm _ hP.2,mul_one]
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.WholeTailUniformDegree
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem original_family_whole_tail_uniform_degree_oai (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,CubicSieve.Admissible P) →
    ∀ (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖literalWholeRow F K hK S jF Pset D s hc W θ X r aw-
        (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
          ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
            literalDyadicRow F K hK S jF Pset D s hc u i W θ X
              (fun K => r K*shapeArgument (primaryGenerator K))
              (fun P => aw P*shapeArgument (primaryGenerator P))‖≤
        (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*Pset.card*
          (C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
            T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_row_tail_uniform_degree lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod hPad θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let E := C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
    T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹
  have hb (v : Eisˣ) :
      ‖(∑' i,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa)-
        ∑ i∈J,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa‖≤Pset.card*E :=
    hbound (N:=N) (a:=a) (c:=c) (mode:=mode) F K hK S jF Pset D s hc hN hbase hchar hj hprod v θ X T QK QP rr aa hX hT hQK hQP hKr hPr
      (by simpa only [rr,row_shape_weight_norm r K hK] using hr)
      (fun P hp => by simpa only [aa,slot_shape_weight_norm aw P (hPad P hp)] using haw P hp)
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  rw [literalWholeRow_eq_dyadic F K hK S jF Pset D s hc hN hbase hchar hj hprod W lo hi hlo hWs hW θ X hX r aw]
  rw [←mul_sub,norm_mul, norm_mul,stratumShapeFactor_frozen_norm]
  simp only [tsum_fintype]
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*
        ∑ v : Eisˣ,‖(∑' i,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa)-
          ∑ i∈J,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*∑ _v : Eisˣ,Pset.card*E := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hb v)) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; dsimp only [E]; ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end

theorem solution.{u, v} : type_of% @OAI.SevenEighths.InverseReflectedPhase.original_family_whole_tail_uniform_degree_oai.{u, v} := @OAI.SevenEighths.InverseReflectedPhase.original_family_whole_tail_uniform_degree_oai.{u, v}
