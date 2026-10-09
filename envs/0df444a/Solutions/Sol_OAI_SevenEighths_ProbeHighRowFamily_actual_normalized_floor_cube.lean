-- Prove2me | solution 1 for OAI.SevenEighths.ProbeHighRowFamily.actual_normalized_floor_cube
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:39:18.132711+00:00
-- url     : https://prove2.me/submissions/97647257-e58c-4be7-81ff-e2d52bc2d24d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_actual_fixed_cube_prime_bound
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_actual_ray_normalizer_inverse
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowAmplitudeOnLines_buffered_bound

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ContinuationPolynomialContour
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
namespace SevenEighths.Continuation

theorem polynomialGaussian_integrable (n : ℕ) : Integrable (polynomialGaussian n) := by
  have hp := (integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ)<1) (show (-1 : ℝ)<(n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).norm
  have hg := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have he : (fun y : ℝ => ‖y^(n : ℝ)*Real.exp (-1*y^2)‖) =
      fun y : ℝ => |y|^n*Real.exp (-(y^2)) := by
    funext y
    simp [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [he] at hp
  convert (preTransparency := .instances) hg.add hp using 1
  funext y
  simp [polynomialGaussian, add_mul]

end SevenEighths.Continuation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
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

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem integral_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (A x)) = inverseJacobian A • ∫ x : ℂ, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure ℂ))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure ℂ) =
      ENNReal.ofReal (inverseJacobian A) • volume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : ℂ, f y ∂Measure.map A volume) = (∫ x : ℂ, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (show 0 ≤ inverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem fourier_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
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

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem paperFourier_comp_mul (f : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0) (u : ℂ) :
    paperFourier (fun z => f (a * z)) u =
      (1 / ‖a‖ ^ 2 : ℝ) • paperFourier f (u / a) := by
  have hd : dualMap (complexMulEquiv a ha) (paperFrequency u) =
      paperFrequency (u / a) := by
    rw [dual_mul_apply]
    unfold paperFrequency
    rw [map_div₀]
    ring
  have hj : inverseJacobian (complexMulEquiv a ha) = 1 / ‖a‖ ^ 2 := by
    rw [inverseJacobian, complexMulEquiv_det, abs_inv,
      abs_of_nonneg (Complex.normSq_nonneg a), Complex.sq_norm]
    ring
  rw [paperFourier_eq_standard, paperFourier_eq_standard]
  have hF := fourier_comp_linearEquiv (complexMulEquiv a ha) f (paperFrequency u)
  simp only [Function.comp_def, complexMulEquiv_apply] at hF
  rw [hF, hd, hj, smul_smul, smul_smul]
  congr 1
  ring

theorem paperFourier_radial (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2)) u =
      paperRadialFourier W (‖u‖ ^ 2) := by
  unfold paperRadialFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let a : ℂ := u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hnC
  have hna : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, hn]
  have hq : u / a = (‖u‖ : ℂ) := by
    dsimp [a]
    field_simp
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) = fun z : ℂ => W (‖z‖ ^ 2) := by
    funext z
    rw [norm_mul, hna, one_mul]
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, hq] at hF
  simpa using hF

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

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

theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

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

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
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
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

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

end CubicReflectionKernel

open scoped BigOperators Classical

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

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

end CubicReflectionKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators
namespace CompletedDyadic

theorem pow_rpow_comm (s : ℝ) (n : ℕ) : ((2:ℝ)^n)^s=((2:ℝ)^s)^n := by
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem kernelTerm_nonneg (t s A : ℝ) (ht : 0<t) (n : ℕ) : 0≤kernelTerm t s A n := by
  unfold kernelTerm
  positivity

theorem kernelTerm_le_head (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤((2:ℝ)^s)^n := by
  rw [kernelTerm,←pow_rpow_comm]
  exact div_le_self (Real.rpow_nonneg (by positivity) _)
    (Real.one_le_rpow (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]) hA)

theorem kernelTerm_le_tail (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤t^(-A)*((2:ℝ)^(s-A))^n := by
  have hn : 0<(2:ℝ)^n := by positivity
  have htA : 0<t^A := Real.rpow_pos_of_pos ht _
  calc
    _ ≤ ((2:ℝ)^n)^s/(t*(2:ℝ)^n)^A := by
      unfold kernelTerm
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) hA)
    _ = t^(-A)*(((2:ℝ)^n)^s/((2:ℝ)^n)^A) := by
      rw [Real.mul_rpow ht.le hn.le,Real.rpow_neg ht.le]
      ring
    _ = _ := by rw [←Real.rpow_sub hn,pow_rpow_comm]

theorem ratio_lt_one (s A : ℝ) (hsA : s<A) : (2:ℝ)^(s-A)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsA)

theorem kernel_summable (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (hsA : s<A) :
    Summable (kernelTerm t s A) := by
  have hq := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s-A)) (ratio_lt_one s A hsA)
  exact (hq.mul_left (t^(-A))).of_nonneg_of_le (kernelTerm_nonneg t s A ht) (kernelTerm_le_tail t s A ht hA)

theorem kernel_sum_cutoff (t s A : ℝ) (ht : 0<t) (hs : 0<s) (hsA : s<A) (N : ℕ) :
    (∑'n : ℕ,kernelTerm t s A n)≤
      ((2:ℝ)^s)^N/((2:ℝ)^s-1)+t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
  have hA : 0≤A := by linarith
  have hp : 1<(2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hq : (2:ℝ)^(s-A)<1 := ratio_lt_one s A hsA
  have hq0 : 0≤(2:ℝ)^(s-A) := by positivity
  have hsum := kernel_summable t s A ht hA hsA
  have hhead : (∑n∈Finset.range N,kernelTerm t s A n)≤((2:ℝ)^s)^N/((2:ℝ)^s-1) := by
    apply (Finset.sum_le_sum (fun n _ => kernelTerm_le_head t s A ht hA n)).trans
    rw [geom_sum_eq hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hp.le)
  have htail : (∑'n : ℕ,kernelTerm t s A (n+N))≤
      t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
    have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A)*((2:ℝ)^(s-A))^N)
    have hb := Summable.tsum_le_tsum (fun n => show kernelTerm t s A (n+N)≤
      (t^(-A)*((2:ℝ)^(s-A))^N)*((2:ℝ)^(s-A))^n by
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using kernelTerm_le_tail t s A ht hA (n+N))
      ((summable_nat_add_iff N).mpr hsum) hgeo
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    simpa only [div_eq_mul_inv] using hb
  rw [←hsum.sum_add_tsum_nat_add N]
  exact add_le_add hhead htail

theorem kernel_sum_bound (s A : ℝ) (hs : 0<s) (hsA : s<A) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      Summable (kernelTerm t s A) ∧ (∑'n : ℕ,kernelTerm t s A n)≤C*t^(-s) := by
  let r : ℝ := (2:ℝ)^s
  let q : ℝ := (2:ℝ)^(s-A)
  have hr : 1< r := Real.one_lt_rpow (by norm_num) hs
  have hq : q<1 := ratio_lt_one s A hsA
  have hq0 : 0≤q := by dsimp [q]; positivity
  let C := r/(r-1)+1/(1-q)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  have hA : 0≤A := by linarith
  have hsum := kernel_summable t s A ht hA hsA
  refine ⟨hsum,?_⟩
  by_cases ht1 : 1≤t
  · have hg := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A))
    have hb := hsum.tsum_le_tsum (fun n => kernelTerm_le_tail t s A ht hA n) hg
    change (∑'n : ℕ,kernelTerm t s A n)≤∑'n : ℕ,t^(-A)*q^n at hb
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    calc
      _ ≤ t^(-A)/(1-q) := by simpa only [div_eq_mul_inv] using hb
      _ ≤ t^(-s)/(1-q) := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by linarith)
      _ ≤ C*t^(-s) := by
        have hp : 0≤ r/(r-1)*t^(-s) := by positivity
        calc
          _ ≤ r/(r-1)*t^(-s)+t^(-s)/(1-q) := le_add_of_nonneg_left hp
          _ = C*t^(-s) := by dsimp [C]; ring
  · have ht_le : t≤1 := le_of_not_ge ht1
    have hit : 1≤1/t := (one_le_div ht).mpr ht_le
    obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hit (by norm_num : (1:ℝ)<2)
    have hheadpow : r^(N+1)≤ r*t^(-s) := by
      change ((2:ℝ)^s)^(N+1)≤(2:ℝ)^s*t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ ((2:ℝ)/t)^s := by
          apply Real.rpow_le_rpow (by positivity) _ hs.le
          rw [pow_succ]
          calc
            _ ≤ (1/t)*2 := mul_le_mul_of_nonneg_right hN (by norm_num)
            _ = 2/t := by ring
        _ = _ := by rw [Real.div_rpow (by norm_num) ht.le,Real.rpow_neg ht.le]; ring
    have htailpow : t^(-A)*q^(N+1)≤t^(-s) := by
      change t^(-A)*((2:ℝ)^(s-A))^(N+1)≤t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ t^(-A)*(1/t)^(s-A) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hN'.le (by linarith)) (by positivity)
        _ = t^(-A)*t^(-(s-A)) := by rw [one_div,Real.inv_rpow ht.le,←Real.rpow_neg ht.le]
        _ = t^(-s) := by rw [←Real.rpow_add ht]; congr 1; ring
    have hb := kernel_sum_cutoff t s A ht hs hsA (N+1)
    change (∑'n : ℕ,kernelTerm t s A n)≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) at hb
    calc
      _ ≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) := hb
      _ ≤ (r*t^(-s))/(r-1)+t^(-s)/(1-q) := add_le_add
        (div_le_div_of_nonneg_right hheadpow (by linarith))
        (div_le_div_of_nonneg_right htailpow (by linarith))
      _ = C*t^(-s) := by dsimp [C]; ring

end CompletedDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem completed_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inl (by simpa using hs₁))

theorem completed_differentiableAt_of_mean_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))

theorem latticeL_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, w a = 0) :
    DifferentiableAt ℂ (latticeL w) s := by
  have hΛ : DifferentiableAt ℂ (completed w) s := by
    rcases hs₁ with hs₁ | hw
    · exact completed_differentiableAt w hs₀ hs₁
    · exact completed_differentiableAt_of_mean_zero w hw hs₀
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul hΛ

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

end SevenEighths.HeckeTheta

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Family
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily

theorem continuedLattice_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.FiniteConductor
namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.mono {χ : MulChar R ℂ} {I J : Ideal R}
    (h : FactorsThroughIdeal χ I) (hJI : J ≤ I) : FactorsThroughIdeal χ J := by
  rw [factorsThroughIdeal_iff] at h ⊢
  exact fun u hu => h u (hJI hu)

end

end SevenEighths.FiniteConductor

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeCharacterAnalytic

theorem continuedLattice_differentiableAt_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (HeckeFamily.continuedLattice χ) s :=
  HeckeFamily.continuedLattice_differentiableAt χ hs₀
    (Or.inr (coefficients_sum_eq_zero χ hχ))

end SevenEighths.HeckeCharacterAnalytic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealBridge
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeFamily

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Reciprocal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

end SevenEighths.HeckeReciprocal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RadialMellin
namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform RealInnerProductSpace Topology
namespace SevenEighths.ProbeRadialMellin

lemma mellinConvergent_real (f : ℝ → ℂ) (s : ℝ) :
    MellinConvergent f (s : ℂ) ↔
      IntegrableOn (fun r : ℝ => (r^(s-1) : ℝ) • f r) (Ioi 0) := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma gamma_scaled_integrable {s r : ℝ} (hs : 0<s) (hr : 0< r) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-(r*t))) (Ioi 0) := by
  have hg : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s : ℂ) := by
    rw [mellinConvergent_real]
    simpa only [Complex.real_smul, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_mul, mul_comm] using!
      (Real.GammaIntegral_convergent hs).ofReal (𝕜 := ℂ)
  have hh := (MellinConvergent.comp_mul_left (f := fun t : ℝ => (Real.exp (-t) : ℂ))
    (s := (s : ℂ)) hr).mpr hg
  rw [mellinConvergent_real] at hh
  simpa only [RCLike.smul_re, RCLike.ofReal_re] using! hh.re

lemma gamma_scaled_integral {s r : ℝ} (hs : 0<s) (hr : 0< r) :
    (∫ t : ℝ in Ioi 0, t^(s-1)*Real.exp (-(r*t))) =
      r^(-s)*Real.Gamma s := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, one_div, Real.inv_rpow hr.le,
    Real.rpow_neg hr.le]

lemma laplace_mellin_integrable (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    Integrable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    exact hf.comp_fst.mul (by fun_prop)
  have hn (r t : ℝ) (ht : 0<t) :
      ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖ =
        ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t))) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_exp]
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re]
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply ((gamma_scaled_integrable hs hr).const_mul ‖f r‖).mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hn r t ht).le
  · have hw : IntegrableOn (fun r : ℝ => r^(-s.re)*‖f r‖) (Ioi 0) := by
      apply hconv.norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
        Complex.sub_re, Complex.one_re]
      congr 2
      ring
    apply (hw.const_mul (Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hi : (fun t : ℝ => ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖) =ᵐ[
      volume.restrict (Ioi 0)] (fun t => ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t)))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hn r t ht
    rw [integral_congr_ae hi]
    rw [integral_const_mul, gamma_scaled_integral hs hr]
    ring

lemma mellin_laplace (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    mellin (laplace f) s = Complex.Gamma s * mellin f (1-s) := by
  have hi := laplace_mellin_integrable f s hs hf hconv
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ r : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) := by
      unfold mellin laplace
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [smul_eq_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [mul_comm r t]
      ring
    _ = ∫ r : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) :=
      integral_integral_swap hi.swap
    _ = ∫ r : ℝ in Ioi 0, f r*((r:ℂ)^(-s)*Complex.Gamma s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [integral_const_mul]
      have hh := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
      simp only [Complex.ofReal_mul] at *
      rw [hh, one_div, Complex.inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
    _ = _ := by
      rw [mellin, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [show 1-s-1 = -s by ring, smul_eq_mul]
      ring

open EisensteinSchwartzPoisson

lemma paperConstant_pos : 0<paperConstant := by
  unfold paperConstant
  positivity

lemma paperConstant_sq : paperConstant^2 = 4*Real.pi^2/3 := by
  unfold paperConstant
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma paperE_norm (z : ℂ) : ‖paperE z‖=1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp

lemma paper_fourier_pairing (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ u : ℂ, paperFourier f u * g u) = ∫ z : ℂ, f z * paperFourier g z := by
  have hi : Integrable (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))*f p.2*g p.1) := by
    apply (hg.norm.mul_prod hf.norm).mono'
    · have hp : Continuous (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))) := by
        simp_rw [paperE_eq_exp]
        fun_prop
      exact (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
        hg.aestronglyMeasurable.comp_fst
    · exact Eventually.of_forall fun p => by
        simp only [norm_mul, paperE_norm, one_mul]
        exact le_of_eq (mul_comm _ _)
  simp only [paperFourier, Complex.real_smul]
  simp_rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (hi.const_mul ((2/Real.sqrt 3:ℝ):ℂ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by dsimp only; rw [mul_comm z u]; ring

lemma paper_gaussian_fourier (t : ℝ) (ht : 0<t) (u : ℂ) :
    paperFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) u =
      (paperConstant/t:ℝ)*Complex.exp (-(paperConstant^2*‖u‖^2/t:ℝ)) := by
  rw [paperFourier_eq_standard,
    fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2:ℂ)≠0), Complex.cpow_one]
  simp only [Complex.real_smul, ← Complex.ofReal_pow, paperFrequency_norm_sq, paperConstant_sq]
  push_cast
  have he : -(Real.pi:ℂ)^2*((4/3:ℝ)*‖u‖^2:ℝ)/(t:ℂ) =
      -((4*Real.pi^2/3*‖u‖^2/t:ℝ):ℂ) := by push_cast; ring
  push_cast at he
  rw [he]
  unfold paperConstant
  push_cast
  ring

lemma radial_continuous (W : SchwartzMap ℝ ℂ) : Continuous (paperRadialFourier W) := by
  rw [paperRadialFourier_eq_ray]
  exact (paperFourierRayCLM W).continuous.comp Real.continuous_sqrt

lemma radial_isBigO_top (W : SchwartzMap ℝ ℂ) (A : ℕ) :
    paperRadialFourier W =O[atTop] (fun r : ℝ => r^(-(A:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W A 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hh := hb 0 (by omega) r hr
  simp only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one] at hh
  have hp : r^A * ‖paperRadialFourier W r‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le (by linarith : r≤1+r) A)
      (norm_nonneg _)).trans hh
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _),
    Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hr A)).mpr (by simpa [mul_comm] using hp)

lemma radial_isBigO_zero (W : SchwartzMap ℝ ℂ) :
    paperRadialFourier W =O[𝓝[>] 0] (fun r : ℝ => r^(-(0:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W 0 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa [LocalLogFourier.eulerDeriv] using hb 0 (by omega) r hr

theorem radial_mellin_convergent (W : SchwartzMap ℝ ℂ) (z : ℂ) (hz : 0<z.re) :
    MellinConvergent (paperRadialFourier W) z := by
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact mellinConvergent_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz

theorem radial_mellin_differentiable (W : SchwartzMap ℝ ℂ) :
    DifferentiableOn ℂ (mellin (paperRadialFourier W)) {z | 0<z.re} := by
  intro z hz
  obtain ⟨A,hA⟩ := exists_nat_gt z.re
  exact (mellin_differentiableAt_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz).differentiableWithinAt

lemma radial_laplace_duality (W : SchwartzMap ℝ ℂ) (t : ℝ) (ht : 0<t) :
    laplace (paperRadialFourier W) t =
      (paperConstant/t:ℝ)*laplace W (paperConstant^2/t) := by
  have hf : Integrable (fun z : ℂ => W (‖z‖^2)) := (radialTestCLM W).integrable
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using ht) 0 (0:ℂ)
  have h := paper_fourier_pairing _ _ hf hg
  have hleft : (∫ u : ℂ, paperFourier (fun z : ℂ => W (‖z‖^2)) u *
      Complex.exp (-(t:ℂ)*‖u‖^2)) = (Real.pi:ℂ)*laplace (paperRadialFourier W) t := by
    simp_rw [paperFourier_radial]
    rw [laplace, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp [Complex.ofReal_mul]
  have hright : (∫ z : ℂ, W (‖z‖^2)*paperFourier
      (fun u : ℂ => Complex.exp (-(t:ℂ)*‖u‖^2)) z) =
      (Real.pi:ℂ)*((paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) := by
    simp_rw [paper_gaussian_fourier t ht]
    rw [laplace, ← integral_const_mul, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      have he : paperConstant^2*‖u‖^2/t = paperConstant^2/t*‖u‖^2 := by ring
      rw [he]
      ring
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h

lemma mellin_reciprocal_laplace (W : ℝ → ℂ) (z : ℂ) :
    mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) =
      (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*mellin (laplace W) z := by
  have hfun : (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) =
      (fun t : ℝ => (paperConstant:ℂ) • ((t:ℂ)^(-1:ℂ) •
        laplace W (paperConstant^2*t⁻¹))) := by
    funext t
    simp [Complex.cpow_neg_one, div_eq_mul_inv, smul_eq_mul, mul_assoc]
  rw [hfun, mellin_const_smul, mellin_cpow_smul]
  rw [show 1-z+(-1) = -z by ring]
  have hh := mellin_comp_inv (fun t : ℝ => laplace W (paperConstant^2*t)) (-z)
  rw [neg_neg] at hh
  rw [hh, mellin_comp_mul_left _ _ (sq_pos_of_pos paperConstant_pos)]
  simp only [smul_eq_mul]
  ring

theorem radial_mellin_gamma (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*Complex.Gamma z /
        Complex.Gamma (1-z))*mellin W (1-z) := by
  have hc := CubicReflectionKernel.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (1-z)
  have hL := mellin_laplace (paperRadialFourier W) (1-z)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    ((radial_continuous W).aestronglyMeasurable)
    (by simpa only [sub_sub_cancel] using radial_mellin_convergent W z hz)
  have hR := mellin_laplace W z hz W.continuous.aestronglyMeasurable hc
  have he : mellin (laplace (paperRadialFourier W)) (1-z) =
      mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [radial_laplace_duality W t ht]
  rw [hL, sub_sub_cancel, mellin_reciprocal_laplace, hR] at he
  have hg : Complex.Gamma (1-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]; linarith)
  apply (mul_left_cancel₀ hg)
  rw [he]
  field_simp

lemma paper_prefactor (z : ℂ) :
    (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z) =
      (paperConstant:ℂ)^(1-2*z) := by
  have hn : (paperConstant:ℂ)≠0 := Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'
  have hh := Complex.cpow_nat_mul' (x := (paperConstant:ℂ)) (n := 2)
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_pos])
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_nonneg]) (-z)
  push_cast
  rw [← hh, show 1-2*z = 1+2*(-z) by ring, Complex.cpow_add _ _ hn,
    Complex.cpow_one]
  norm_num

theorem radial_mellin_identity (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  rw [radial_mellin_gamma W a b ha hW z hz hz1, paper_prefactor]

theorem radial_mellin_identity_right (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  let D : Set ℂ := {z | 0<z.re}
  let G : ℂ → ℂ := fun z =>
    ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
      mellin W (1-z)
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ D := (convex_Ioi (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hf : AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) D :=
    (radial_mellin_differentiable W).analyticOnNhd hop
  have hG : DifferentiableOn ℂ G D := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (paperConstant:ℂ)^(1-2*z)) w :=
      (differentiableAt_const _ |>.sub (differentiableAt_id.const_mul 2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'))
    have h2 := CubicReflectionKernel.Gamma_differentiableAt_of_re_pos w hw
    have h3 := (Complex.differentiable_one_div_Gamma (1-w)).comp w
      (differentiableAt_const _ |>.sub differentiableAt_id)
    have h4 := (CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hW
      (W.smooth ⊤) (1-w)).comp w (differentiableAt_const _ |>.sub differentiableAt_id)
    simpa only [G, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! (((h1.mul h2).mul h3).mul h4).differentiableWithinAt
  have hev : mellin (paperRadialFourier W) =ᶠ[𝓝 (1/2:ℂ)] G := by
    have hstrip : IsOpen {w:ℂ | 0<w.re ∧ w.re<1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds (by norm_num)] with w hw
    exact radial_mellin_identity W a b ha hW w hw.1 hw.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hop)
    hcv.isPreconnected (by norm_num [D]) hev hz

lemma gamma_quotient_strip (lo hi : ℝ) (hlo : 0<lo) :
    ∃ (n : ℕ) (C : ℝ), 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖Complex.Gamma ((σ:ℂ)+t*Complex.I) / Complex.Gamma (1-((σ:ℂ)+t*Complex.I))‖ ≤
        C*(1+|t|)^n := by
  obtain ⟨A,hA⟩ := exists_nat_gt hi
  obtain ⟨C,hC,hb⟩ := CubicReflectionKernel.Gamma_pair_strip_bound 1 (by norm_num) A
  refine ⟨2*A+2,C/lo,div_pos hC hlo,?_⟩
  intro σ hσ t
  have hσ0 : 0<σ := hlo.trans_le hσ.1
  have hz : (σ:ℂ)+t*Complex.I≠0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
    linarith
  have hh := hb σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
  norm_num only [Complex.ofReal_one] at hh
  rw [add_comm (1:ℂ), Complex.Gamma_add_one _ hz, mul_div_assoc, norm_mul] at hh
  have hnorm : lo≤‖(σ:ℂ)+t*Complex.I‖ := by
    apply hσ.1.trans
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
      Complex.re_le_norm ((σ:ℂ)+t*Complex.I)
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hh'

theorem radial_mellin_strip_decay (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0<lo) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      (1+|t|)^N * ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C := by
  obtain ⟨n,Cg,hCg,hg⟩ := gamma_quotient_strip lo hi hlo
  obtain ⟨Cw,hCw,hw⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hW
    (W.smooth ⊤) (1-hi) (1-lo) (n+N)
  have hc : Continuous (fun σ : ℝ => paperConstant^(1-2*σ)) :=
    (Real.continuous_const_rpow paperConstant_pos.ne').comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s := Icc lo hi))
  let Cp := |B|+1
  have hCp : 0<Cp := by dsimp [Cp]; positivity
  refine ⟨Cp*Cg*Cw,by positivity,?_⟩
  intro σ hσ t
  have hp : ‖(paperConstant:ℂ)^(1-2*((σ:ℂ)+t*Complex.I))‖≤Cp := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos paperConstant_pos]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      show (2:ℂ).re=2 by rfl, show (2:ℂ).im=0 by rfl, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact (hB (mem_image_of_mem _ hσ)).trans (by change B≤|B|+1; linarith [le_abs_self B])
  have hwb := hw (1-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
  rw [abs_neg, show ((1-σ:ℝ):ℂ)+(-t:ℝ)*Complex.I = 1-((σ:ℂ)+t*Complex.I) by
    push_cast; ring] at hwb
  rw [radial_mellin_identity_right W a b ha hW _ (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact hlo.trans_le hσ.1), mul_div_assoc, norm_mul, norm_mul]
  calc
    _ ≤ (1+|t|)^N*(Cp*(Cg*(1+|t|)^n)*
        ‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      gcongr
      exact hg σ hσ t
    _ = (Cp*Cg)*((1+|t|)^(n+N)*‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwb (by positivity)

end SevenEighths.ProbeRadialMellin

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MellinBoundary
namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology
namespace SevenEighths.ProbeMellinBoundary
open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

lemma height_pos (t : ℝ) : 0<height t := by unfold height; positivity
lemma height_one_le (t : ℝ) : 1≤height t := by simp [height]

lemma cauchy_nonneg (t : ℝ) : 0≤ cauchy t := by unfold cauchy; positivity
lemma cauchy_integrable : Integrable cauchy := integrable_inv_one_add_sq
lemma jointHeight_pos (t v w : ℝ) : 0<jointHeight t v w := by unfold jointHeight; positivity

lemma gaussianMoment_nonneg (n : ℕ) (u : ℝ) : 0≤gaussianMoment n u := by
  unfold gaussianMoment height
  positivity
lemma gaussianMoment_integrable (n : ℕ) : Integrable (gaussianMoment n) := by
  apply ((Continuation.polynomialGaussian_integrable n).const_mul ((2:ℝ)^(n-1))).mono'
  · unfold gaussianMoment height
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · apply Eventually.of_forall
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianMoment_nonneg n u)]
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg u) n
    simpa [gaussianMoment,height,Continuation.polynomialGaussian,mul_assoc] using
      mul_le_mul_of_nonneg_right h (Real.exp_pos (-(u^2))).le

lemma jointHeight_le_shear (t v w : ℝ) :
    jointHeight t v w≤2*height (t+v)*height v*height w := by
  have ht : |t|≤|t+v|+|v| := by simpa using (abs_sub_le (t+v) 0 v)
  have huv : 1≤height (t+v)*height v := one_le_mul_of_one_le_of_one_le (height_one_le _) (height_one_le _)
  have h1 : 1+|t|+|v|≤2*height (t+v)*height v := by
    unfold height
    nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v), abs_nonneg (t+v),abs_nonneg v]
  unfold jointHeight
  change 1+|t|+|v|+|w|≤2*height (t+v)*height v*(1+|w|)
  calc
    _ ≤ 2*height (t+v)*height v+|w| := by linarith [h1]
    _ ≤ 2*height (t+v)*height v+(2*height (t+v)*height v)*|w| := by
      have hh : 1≤2*height (t+v)*height v := by nlinarith
      have hhh := mul_le_mul_of_nonneg_right hh (abs_nonneg w)
      linarith
    _ = _ := by ring

lemma weighted_to_cauchy {f C : ℝ} (J : ℕ) (t : ℝ) (hf : 0≤f)
    (h : height t^(J+2)*f≤C) : height t^J*f≤C*cauchy t := by
  have hh : (1+|t|)^2*(height t^J*f)≤C := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using h
  exact CubicReflectionKernel.weighted_two_to_cauchy
    (mul_nonneg (pow_nonneg (height_pos t).le _) hf) t hh

lemma weighted_coupled_cauchy (J : ℕ) (t v w A B C D : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (_hD : 0≤D)
    (ha : height v^(J+2)*A≤C) (hb : height w^(J+2)*B≤D) :
    jointHeight t v w^J * Real.exp (-((t+v)^2))*A*B ≤
      (2:ℝ)^J*C*D*(gaussianMoment J (t+v)*cauchy v*cauchy w) := by
  have hpow := pow_le_pow_left₀ (jointHeight_pos t v w).le (jointHeight_le_shear t v w) J
  have ha' := weighted_to_cauchy J v hA ha
  have hb' := weighted_to_cauchy J w hB hb
  calc
    _ ≤ (2*height (t+v)*height v*height w)^J * Real.exp (-((t+v)^2))*A*B := by gcongr
    _ = (2:ℝ)^J * gaussianMoment J (t+v) * (height v^J*A)*(height w^J*B) := by
      simp only [mul_pow,gaussianMoment]
      ring
    _ ≤ (2:ℝ)^J * gaussianMoment J (t+v) * (C*cauchy v)*(D*cauchy w) := by
      have hg := gaussianMoment_nonneg J (t+v)
      have hc := cauchy_nonneg v
      have hd := cauchy_nonneg w
      have hw := (height_pos w).le
      have hv := (height_pos v).le
      gcongr
    _ = _ := by ring

lemma jointEnvelope_integrable (J : ℕ) : Integrable (jointEnvelope J) heightMeasure := by
  have hp : MeasurePreserving (fun p : ℝ×ℝ => (p.1+p.2,p.2))
      (volume.prod volume) (volume.prod volume) := by
    have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
        (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
    have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
    simpa only [Function.comp_def,Prod.swap,add_comm] using! hp1
  have ht := hp.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hi := ((gaussianMoment_integrable J).mul_prod cauchy_integrable).mul_prod cauchy_integrable
  exact ht.integrable_comp_of_integrable hi

lemma onLines_norm (W0 W1 : SchwartzMap ℝ ℂ) (σ ξ υ : ℝ) (p : HeightSpace) :
    ‖onLines W0 W1 σ ξ υ p‖ = Real.exp ((σ+ξ-1)^2)*Real.exp (-((p.1.1+p.1.2)^2))*
      ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ *
      ‖mellin W1 ((υ:ℂ)+p.2*I)‖ := by
  unfold onLines profile
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have hr : ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)^2).re =
      (σ+ξ-1)^2+(-((p.1.1+p.1.2)^2)) := by simp [pow_two]; ring
  rw [hr,Real.exp_add]

lemma onLines_continuous (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (σ ξ υ : ℝ) (hξ : 0<ξ) : Continuous (onLines W0 W1 σ ξ υ) := by
  have hR : Continuous (fun t : ℝ => mellin (paperRadialFourier W0) ((ξ:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t; simpa using hξ)
  have hW := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
    (W1.smooth ⊤)).continuous
  unfold onLines profile
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · exact hR.comp (continuous_snd.comp continuous_fst)
  · exact hW.comp (by fun_prop)

lemma realGaussianBound_pos (slo shi zlo zhi : ℝ) : 0< realGaussianBound slo shi zlo zhi :=
  Real.exp_pos _
lemma realGaussian_le {slo shi zlo zhi σ ξ : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi) :
    Real.exp ((σ+ξ-1)^2)≤ realGaussianBound slo shi zlo zhi := by
  have hs : |σ|≤|slo|+|shi| := by
    rw [abs_le]
    constructor <;> linarith [hσ.1,hσ.2,neg_abs_le slo,le_abs_self shi,abs_nonneg slo,abs_nonneg shi]
  have hz : |ξ|≤|zlo|+|zhi| := by
    rw [abs_le]
    constructor <;> linarith [hξ.1,hξ.2,neg_abs_le zlo,le_abs_self zhi,abs_nonneg zlo,abs_nonneg zhi]
  have hh : |σ+ξ-1|≤|slo|+|shi|+|zlo|+|zhi|+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le σ,le_abs_self σ,neg_abs_le ξ,le_abs_self ξ]
  apply Real.exp_le_exp.mpr
  have hp := pow_le_pow_left₀ (abs_nonneg (σ+ξ-1)) hh 2
  simpa [sq_abs] using hp

lemma profile_moment_majorant (W0 W1 : SchwartzMap ℝ ℂ) (J : ℕ)
    {slo shi zlo zhi σ ξ υ C D : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi)
    (hC : 0≤C) (hD : 0≤D)
    (hR : ∀v : ℝ, height v^(J+2)*‖mellin (paperRadialFourier W0) ((ξ:ℂ)+v*I)‖≤C)
    (hW : ∀w : ℝ, height w^(J+2)*‖mellin W1 ((υ:ℂ)+w*I)‖≤D) (p : HeightSpace) :
    jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ≤
      (realGaussianBound slo shi zlo zhi*2^J*C*D)*jointEnvelope J p := by
  have hb := weighted_coupled_cauchy J p.1.1 p.1.2 p.2
    ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ ‖mellin W1 ((υ:ℂ)+p.2*I)‖ C D
    (norm_nonneg _) (norm_nonneg _) hC hD (hR _) (hW _)
  rw [onLines_norm]
  calc
    _ = Real.exp ((σ+ξ-1)^2) * (jointHeight p.1.1 p.1.2 p.2^J*
        Real.exp (-((p.1.1+p.1.2)^2))*
        ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖*‖mellin W1 ((υ:ℂ)+p.2*I)‖) := by ring
    _ ≤ realGaussianBound slo shi zlo zhi *
        ((2:ℝ)^J*C*D*(gaussianMoment J (p.1.1+p.1.2)*cauchy p.1.2*cauchy p.2)) :=
      mul_le_mul (realGaussian_le hσ hξ) hb
        (by have := (jointHeight_pos p.1.1 p.1.2 p.2).le; positivity)
        (realGaussianBound_pos _ _ _ _).le
    _ = _ := by unfold jointEnvelope; ring

theorem profile_uniform_moments (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖) heightMeasure ∧
      (∫p : HeightSpace, jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤K := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 zlo zhi hzlo (J+2)
  obtain ⟨D,hD,hW⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+2)
  let A := realGaussianBound slo shi zlo zhi*2^J*C*D
  have hA : 0<A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|∫p, jointEnvelope J p ∂heightMeasure|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ
  have hbound := profile_moment_majorant W0 W1 J hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  have hc := onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ (hzlo.trans_le hξ.1)
  have hf : Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
      ‖onLines W0 W1 σ ξ υ p‖) heightMeasure := by
    apply ((jointEnvelope_integrable J).const_mul A).mono'
    · exact ((by unfold jointHeight; fun_prop : Continuous (fun p : HeightSpace =>
        jointHeight p.1.1 p.1.2 p.2^J)).mul hc.norm).aestronglyMeasurable
    · apply Eventually.of_forall
      intro p
      have hn : 0≤jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ :=
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
      rw [Real.norm_eq_abs,abs_of_nonneg hn]
      exact hbound p
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫p, A*jointEnvelope J p ∂heightMeasure := integral_mono hf
      ((jointEnvelope_integrable J).const_mul A) hbound
    _ = A*(∫p, jointEnvelope J p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := le_abs_self (∫p, jointEnvelope J p ∂heightMeasure)
      exact mul_le_mul_of_nonneg_left (by linarith) hA.le

end SevenEighths.ProbeMellinBoundary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RadialIdentity
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma elementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.InitialScales
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

lemma sourceMellinWeight_eq_scale (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z=sourceScale X Y Z x w z*profile W0 W1 x w z := by
  unfold sourceMellinWeight sourceScale profile
  ring

lemma sourceScale_continuous (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Continuous (fun q : (ℂ × ℂ) × ℂ =>sourceScale X Y Z q.1.1 q.1.2 q.2) := by
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceScale
  exact (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>(1/2:ℂ)-q.2)).const_cpow (Or.inl hx)).mul
    (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>q.1.1+q.2-1)).const_cpow (Or.inl hz)))) |>.mul
      ((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>q.1.2-1)).const_cpow (Or.inl hy))

lemma sourceScale_norm (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    ‖sourceScale X Y Z x w z‖=X^(1/2-z.re)*Z^(x.re+z.re-1)*Y^(w.re-1) := by
  simp only [sourceScale,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hY,Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  norm_num [Complex.sub_re,Complex.add_re]

lemma sourceMellinWeight_initial_continuous (W0 W1 : SchwartzMap ℝ ℂ)
    (a1 b1 : ℝ) (ha1 : 0<a1) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Continuous (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)) := by
  have hc := (sourceScale_continuous X Y Z hX hY hZ).comp
    (show Continuous (fun p : HeightSpace=>(((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),
      (ξ:ℂ)+p.1.2*Complex.I)) by fun_prop)
  simpa only [Function.comp_def,Pi.mul_def,sourceMellinWeight_eq_scale,onLines] using
    hc.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.TuplePrime
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.SelectedAgreement
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem ramifiedCorrection_eq_marked (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z=
      1+(1-coordV P.val.absNorm z)*continuedMarkedLocal η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := (supported_prime_data p hp hsp).1
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  change ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)=
    1+(1-coordV P.val.absNorm z)*rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
      ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)
  unfold ramifiedClosed
  rw [hnorm]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma annularPower_nonneg (a b r : ℝ) (ha : 0<a) : 0≤annularPower a b r :=
  (Real.rpow_nonneg ha.le _).trans (le_max_left _ _)

lemma annular_rpow (a b P q r : ℝ) (ha : 0<a) (hb : 0<b) (hP : 0<P)
    (hqa : a*P≤q) (hqb : q≤b*P) : q^r≤annularPower a b r*P^r := by
  have hq : 0<q := (mul_pos ha hP).trans_le hqa
  by_cases hr : 0≤ r
  · calc
      q^r≤(b*P)^r := Real.rpow_le_rpow hq.le hqb hr
      _=b^r*P^r := Real.mul_rpow hb.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hP.le _)
  · calc
      q^r≤(a*P)^r := Real.rpow_le_rpow_of_nonpos (mul_pos ha hP) hqa (by linarith)
      _=a^r*P^r := Real.mul_rpow ha.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hP.le _)

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.RowCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => HeckeFamily.O

lemma frequencyWeight_ideal_norm (z : ℂ) (u : FreeRow) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖=
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-z.re) := by
  have hN : (0:ℝ)<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  unfold frequencyWeight elementNorm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.neg_re]

lemma dyadic_weighted_rows (a r C U : ℝ) (hC : 0≤C) (hU : 1≤U)
    (R : Finset FreeRow)
    (hR : ∀u∈R,U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(1+a-r) := by
  have hU0 : 0<U := by linarith
  have hcard : (R.card:ℝ)≤256*U := by
    have hc := freeRow_count R (2*U) (by linarith) (fun u hu=>(hR u hu).2)
    linarith
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (a-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := hU0.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      calc
        _ ≤ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-r)*
            (C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(a-r) := by
          rw [show a-r=(-r)+a by ring,Real.rpow_add hN]
          ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U
            ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) (a-r) (by norm_num) (by norm_num) hU0
            (by simpa only [one_mul] using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) := by simp
    _ ≤ (256*U)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hp : U*U^(a-r)=U^(1+a-r) := by
        rw [show 1+a-r=1+(a-r) by ring,Real.rpow_add hU0,Real.rpow_one]
      calc
        _ = (256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r))*(U*U^(a-r)) := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Measurable
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

lemma rowClosedMarked_measurable {α : Type*} [MeasurableSpace α]
    (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p}) (η a ρ : ℂ) (j : ℕ)
    (X W V : α→ℂ) (hX : Measurable X) (hW : Measurable W) (hV : Measurable V) :
    Measurable (fun t=>rowClosedMarked p hp hg η a (X t) (W t) (V t) ρ j) := by
  unfold rowClosedMarked rowBaseFinite rowMarkedTerm rowWeightedScalar weightedScalar evenRatio
  simp only [Nat.reduceAdd,Nat.reduceMul,OfNat.ofNat_ne_zero,Nat.one_ne_zero,ite_false]
  fun_prop

lemma continuedMarkedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedMarkedLocal η u P hs (x t) (w t) (z t)) := by
  have hQ : (P.val.absNorm:ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold continuedMarkedLocal
  apply rowClosedMarked_measurable
  · exact measurable_const_cpow _ hQ _ hx.neg
  · exact measurable_const_cpow _ hQ _ hw.neg
  · unfold coordV
    apply measurable_const_cpow _ (by exact_mod_cast hQ)
    fun_prop

lemma ramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>ramifiedCorrection η u P hs (x t) (w t) (z t)) := by
  have hm := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  simp_rw [ramifiedCorrection_eq_marked]
  unfold coordV
  fun_prop (disch := exact hQ)

lemma idealUnramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>idealUnramifiedCorrection η u P (x t) (w t) (z t)) := by
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealUnramifiedCorrection unramifiedClosed ProbeLocal.continuedCorrection markedFactor
    coordV coordR coordW coordD coordK
  fun_prop (disch := exact hQ)

lemma continuedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedCorrection S hS η u (x t) (w t) (z t)) := by
  unfold continuedCorrection ramifiedProduct unramifiedProduct
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro P hP
    exact ramifiedCorrection_measurable η u P.val _ x w z hx hw hz
  · apply Measurable.tprod
    intro P
    unfold unramifiedFactor
    split_ifs
    · exact measurable_const
    · exact idealUnramifiedCorrection_measurable η u P.val x w z hx hw hz

lemma continuedCompensatedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z B q : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z)
    (hB : Measurable B) (hq : Measurable q) :
    Measurable (fun t=>continuedCompensatedLocal η u P hs (x t) (w t) (z t) (B t) (q t)) := by
  have hM := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement coordV coordW coordD
  fun_prop (disch := exact hQ)

lemma LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  apply measurable_of_countable_not_continuousAt
  apply ((Set.finite_singleton (1:ℂ)).insert 0).countable.mono
  intro s hs
  by_contra hn
  have h0 : s≠0 := fun h=>hn (by simp [h])
  have h1 : s≠1 := fun h=>hn (by simp [h])
  exact hs (LFunction_differentiableAt χ h0 (Or.inl h1)).continuousAt

lemma regularizedL_measurable (χ : Character) : Measurable (HeckeReciprocal.regularizedL χ) := by
  apply measurable_of_countable_not_continuousAt
  apply (Set.countable_singleton (0:ℂ)).mono
  intro s hs
  by_contra hn
  exact hs (HeckeReciprocal.regularizedL_differentiableAt χ (by simpa using hn)).continuousAt

lemma reciprocal_measurable (χ : Character) : Measurable (HeckeReciprocal.reciprocal χ) := by
  have hL := LFunction_measurable χ
  have hR := regularizedL_measurable χ
  unfold HeckeReciprocal.reciprocal
  split_ifs <;> fun_prop

lemma continuedL_measurable (χ : Character) : Measurable (HeckeOrigin.continued χ) := by
  have hL := LFunction_measurable χ
  have hR := (HeckeOrigin.poleRemoved_entire χ).continuous.measurable
  unfold HeckeOrigin.continued
  split_ifs <;> fun_prop

lemma physicalCompensatedRow_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>physicalCompensatedRow S hS T hT η u (x t) (w t) (z t)) := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply Measurable.mul
  · exact (((LFunction_measurable _).comp (by fun_prop)).mul
      ((continuedL_measurable _).comp hw)).mul ((reciprocal_measurable _).comp hx)
  · apply Measurable.mul
    · exact continuedCorrection_measurable _ _ η u x w z hx hw hz
    · apply Finset.measurable_prod
      intro P hP
      have hQ : (P.val.val.absNorm:ℂ)≠0 := by
        exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
      apply continuedCompensatedLocal_measurable _ _ _ _ x w z _ _ hx hw hz
      · exact (measurable_const_cpow _ hQ x hx).const_mul _
      · exact measurable_const_cpow _ hQ _ hw.neg

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ProfileIntegral
namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

lemma two_height_bound (t v w : ℝ) :
    (3+|t|)^2*(3+|w|)^2≤81*jointHeight t v w^4 := by
  have ht : 3+|t|≤3*jointHeight t v w := by
    unfold jointHeight
    linarith [abs_nonneg t,abs_nonneg v,abs_nonneg w]
  have hw : 3+|w|≤3*jointHeight t v w := by
    unfold jointHeight
    linarith [abs_nonneg t,abs_nonneg v,abs_nonneg w]
  calc
    _ ≤ (3*jointHeight t v w)^2*(3*jointHeight t v w)^2 := by gcongr
    _ = _ := by ring

theorem source_profile_integral_bound (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) :
    ∃C : ℝ,0<C ∧ ∀σ∈Icc slo shi,∀r∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀A : ℝ,0≤A → ∀F : HeightSpace→ℝ,
      AEStronglyMeasurable F heightMeasure → (∀p,0≤F p) →
      (∀p,F p≤A*(3+|p.1.1|)^2*(3+|p.2|)^2) →
      Integrable (fun p=>‖sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p) heightMeasure ∧
      (∫p,‖sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p ∂heightMeasure)
        ≤C*A*(X^(1/2-r)*Z^(σ+r-1)*Y^(υ-1)) := by
  obtain ⟨D,hD,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo 4
  refine ⟨81*D,by positivity,?_⟩
  intro σ hσ r hr υ hυ X Y Z hX hY hZ A hA F hF hF0 hFb
  let E : ℝ := X^(1/2-r)*Z^(σ+r-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let M : HeightSpace→ℝ := fun p=>jointHeight p.1.1 p.1.2 p.2^4*‖onLines W0 W1 σ r υ p‖
  have hMi : Integrable M heightMeasure := (hM σ hσ r hr υ hυ).1
  have hMb : (∫p,M p ∂heightMeasure)≤D := (hM σ hσ r hr υ hυ).2
  let f : HeightSpace→ℝ := fun p=>‖sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p
  have hfm : AEStronglyMeasurable f heightMeasure :=
    (sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
      σ r υ (hzlo.trans_le hr.1)).norm.aestronglyMeasurable.mul hF
  have hf0 (p : HeightSpace) : 0≤f p := mul_nonneg (norm_nonneg _) (hF0 p)
  have hfb (p : HeightSpace) : f p≤(E*A*81)*M p := by
    have h1 := (hFb p).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (two_height_bound p.1.1 p.1.2 p.2) hA)
    have hs : ‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖=E*‖onLines W0 W1 σ r υ p‖ := by
      rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ]
      simp [E,onLines]
    dsimp only [f]
    rw [hs]
    calc
      _ ≤ (E*‖onLines W0 W1 σ r υ p‖)*(A*(81*jointHeight p.1.1 p.1.2 p.2^4)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hE (norm_nonneg _))
      _ = _ := by dsimp [M];ring
  have hfi : Integrable f heightMeasure := (hMi.const_mul (E*A*81)).mono' hfm
    (Filter.Eventually.of_forall fun p=>by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 p)];exact hfb p)
  refine ⟨hfi,?_⟩
  calc
    (∫p,f p ∂heightMeasure) ≤ ∫p,(E*A*81)*M p ∂heightMeasure :=
      integral_mono hfi (hMi.const_mul _) hfb
    _ = (E*A*81)*(∫p,M p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ (E*A*81)*D := mul_le_mul_of_nonneg_left hMb (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma weightedRowOnLines_eq {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ υ r t=
      (∏i,W i (((P i).val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t := by
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold weightedRowOnLines continuedRowOnLines continuedPhysicalRowKernel calibratedTupleValue
  simp only [hnorm,Finset.prod_mul_distrib]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma rowNorm_ge_one (u : FreeRow) : 1≤ rowNorm u := by
  unfold rowNorm
  have hn : (Ideal.span {u.val}:Ideal O)≠⊥ := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.FirstIntegral
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma continuedRowOnLines_eq_amplitude {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t=
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
        rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t := by
  unfold continuedRowOnLines continuedPhysicalRowKernel rowAmplitudeOnLines
  ring

lemma rowAmplitudeOnLines_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (σ υ r : ℝ) : Measurable (rowAmplitudeOnLines S hS hmax P hPS η u σ υ r) := by
  have hp (i : Fin K) : 0<elementNorm (CompletedGauss.primaryGenerator (P i).val) :=
    elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  have hN : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hphys := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun t : HeightSpace=>(σ:ℂ)+t.1.1*I) (fun t : HeightSpace=>(υ:ℂ)+t.2*I)
    (fun t : HeightSpace=>(r:ℂ)+t.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rowAmplitudeOnLines
  apply Measurable.mul
  · apply Measurable.mul
    · apply Finset.measurable_prod
      intro i hi
      exact measurable_const_cpow _ (Complex.ofReal_ne_zero.mpr (hp i).ne') _ (by fun_prop)
    · unfold frequencyWeight
      exact measurable_const_cpow _ hN _ (by fun_prop)
  · exact hphys.const_mul _

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem continuedPhysicalRowKernel_buffered_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤ r) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)
      {t : HeightSpace | |t.1.1|≤H} heightMeasure := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_buffered_bound e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin σ r hσ hσ2 hr
  have hb (t : HeightSpace) : ‖A t‖≤C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r (1-a-6*e) (1-a-6*e) (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r (1-a-6*e) (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I)
      ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=>by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem cubeWeightedRow_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H) heightMeasure := by
  have hi := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  have hE : MeasurableSet E := ((measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.2|) by fun_prop) measurable_const)
  apply (integrable_indicator_iff hE).mpr
  have heq : weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)=
      fun t=>(∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) t := by
    funext t
    exact weightedRowOnLines_eq ..
  rw [heq]
  exact (hi.mono_set (fun t ht=>ht.1.1)).const_mul _

lemma cubeWeightedRow_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H t ∂heightMeasure)=
      (∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H := by
  have hE : MeasurableSet {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H} :=
    ((measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
      (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)).inter
      (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.2|) by fun_prop) measurable_const)
  unfold cubeWeightedRow
  rw [integral_indicator hE]
  simp_rw [weightedRowOnLines_eq]
  rw [integral_const_mul]
  unfold centralCubeIntegral
  ring

theorem finiteCentralCubeRows_eq_integral {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
      detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      cubeWeightedRow S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z (a u) e (H u) t
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  let f (u : FreeRow) (P : ∀i,T i) := cubeWeightedRow S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z (a u) e (H u)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    rcases hbin u hu with ⟨ha,ha',hB,hH,hzero⟩
    exact cubeWeightedRow_integrable e (a u) (B u) (H u) (idx u) he he' ha ha' hB hH
      S hS hmax hfirst _ _ η u (hR u hu) (ψ u) hzero W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P _=>hi u hu P)
  refine ⟨integrable_finsetSum _ hiu,?_⟩
  change finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu,Finset.mul_sum]
  unfold finiteCentralCubeRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=>hi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  exact (cubeWeightedRow_integral S hS hmax _ _ η u W Yp W0 W1 X Y Z (a u) e (H u)).symm

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem source_cube_height_eventually (τ : ℝ) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ 2<Z^τ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeCommonProfile
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem cube_sum_eq_common_profile {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) (t : HeightSpace) :
    (∑u∈R,∑P:(∀i,T i),cubeWeightedRow S hS hmax (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z a e H t)=
    {v : HeightSpace | (|v.1.1|≤H ∧ |v.2|≤H) ∧ |v.1.2|≤H}.indicator
      (fun v=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+v.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+v.2*Complex.I)
        ((17/50:ℂ)+v.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e v) t := by
  by_cases ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H
  · simp [cubeWeightedRow,ht,weightedRowOnLines,cubeArithmeticSum,
      Finset.mul_sum,mul_assoc]
  · simp [cubeWeightedRow,ht]

theorem cube_common_profile_integral {K : ℕ} {ι : Type*} [Fintype ι]
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1' : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
      (fun t=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
        ((17/50:ℂ)+t.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  have hh := finiteCentralCubeRows_eq_integral e he he' S hS hmax hfirst η R hR T hT
    (fun _=>a) (fun _=>B) (fun _=>H) (fun _=>i) ψ
    (fun u hu=>⟨ha,ha1,hB,hH,hbin u hu⟩) W Yp W0 W1 a0 b0 a1 b1 ha0 ha1' hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh ⊢
  simpa only [cube_sum_eq_common_profile] using hh

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem actual_common_cube_aggregate_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0<e → e<1/1000 → 51/100≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : ℝ,0≤A →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H →
        ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤A) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          A := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := A
  have hm : 0≤ mass := hA
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤ scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤ scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (hb t ht) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring
end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralExponent
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeCentralExponent

lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e)=
      Z^((25/48)*a-181/300+(105/8)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring
end SevenEighths.ProbeCentralExponent

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorPhysicalSelection
open HeckeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

theorem weightedMean_bounds {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ)
    (δ : ℝ) (hw : ∀ s∈slots,0≤w s) (hL : 0<∑ s∈slots,w s)
    (hg : ∀ s∈slots,0≤g s ∧ g s≤δ/2) :
    0≤weightedMean slots w g ∧ weightedMean slots w g≤δ/2 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun s hs => mul_nonneg (hw s hs) (hg s hs).1)) hL.le
  · apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ ∑ s∈slots,w s*(δ/2) := Finset.sum_le_sum (fun s hs =>
        mul_le_mul_of_nonneg_left (hg s hs).2 (hw s hs))
      _ = _ := by rw [←Finset.sum_mul]; ring

end SevenEighths.HeckeDetectorPhysicalSelection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=1/6) :
    (∑j∈slots,ell j/d)=1/(6*d) := by
  rw [←Finset.sum_div,hell]
  ring

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=1/6) :
    weightedMean slots (fun j=>ell j/d) g=6*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,ell j=1/6) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(2/75:ℝ)+weightedMean slots (fun j=>ell j/d) g/6+mesh/6) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorArithmetic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let α : ℝ := 1/100+12*e+eps*(N+8)
  let AA := ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)
  have hAA : 0≤AA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 _ (by norm_num)
  refine ⟨256*C*(AA+1),by positivity,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=>floorPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-1/40+mesh/6)
  have hD : 0≤D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤D*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi (51/100) i hi le_rfl (by norm_num) (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) ((51/100:ℝ)-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hellpos (j : Fin N) : 0≤ell j := by
      exact (mul_nonneg hdmax hrmin.le).trans (hello j)
    have hq := weightedMean_bounds Finset.univ (fun j=>ell j/d) g (1/50)
      (fun j _=>div_nonneg (hellpos j) hd0.le)
      (by rw [source_slot_length_sum _ _ _ hellsum];positivity)
      (fun j _=>⟨(hh.1 j).1,by have hhj := (hh.1 j).2.1;dsimp [g,Y,z];norm_num at hhj ⊢;exact hhj⟩)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))≤Z^(-1/40+mesh/6) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-(2/75:ℝ)+weightedMean Finset.univ (fun j=>ell j/d) g/6+mesh/6) from
        source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      apply Real.rpow_le_rpow_of_exponent_le hZ
      linarith [hq.2]
    have hN : 0≤ rowNorm u := (rowNorm_ge_one u).trans' (by norm_num)
    have h := hh.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    convert (preTransparency := .instances) h using 1 ; dsimp [F,D,α,Y,z,g] ; norm_num ; ring
  have hh := dyadic_weighted_rows α (17/50) D (Z^v) hD (Real.one_le_rpow hZ hv) rows hnorm
    F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  apply (hsum.trans hh).trans
  have hpow : Z^loss*Z^(-1/40+mesh/6)*(Z^v)^(1+α-17/50)=
      Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6) := by
    rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ 256*D*(AA+1)*(Z^v)^(1+α-17/50) := by change 256*D*AA*_≤_;gcongr;linarith
    _ = _ := by
      dsimp [D]
      calc
        _ = (256*C*(AA+1))*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^loss*Z^(-1/40+mesh/6)*(Z^v)^(1+α-17/50)) := by ring
        _ = _ := by rw [hpow]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma bounded_dyadic_power_sum (p : ℝ) (hp : 0<p) :
    ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^p)≤C*H^p := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound p (p+1) hp (by linarith)
  refine ⟨(2:ℝ)^(p+1)*C,by positivity,?_⟩
  intro H hH F hF
  obtain ⟨hs,hb⟩ := hmain H⁻¹ (inv_pos.mpr hH)
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^p≤(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := by
    have hd : 0<1+H⁻¹*(2:ℝ)^n := by positivity
    have hu : H⁻¹*(2:ℝ)^n≤1 := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_le_one hH).mpr (hF n hn)
    have hh : (1+H⁻¹*(2:ℝ)^n)^(p+1)≤(2:ℝ)^(p+1) :=
      Real.rpow_le_rpow hd.le (by linarith) (by linarith)
    unfold CompletedDyadic.kernelTerm
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh
      (Real.rpow_nonneg (show (0:ℝ)≤(2:ℝ)^n by positivity) p)
  calc
    _ ≤ ∑n∈F,(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := Finset.sum_le_sum hpoint
    _ = (2:ℝ)^(p+1)*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := (Finset.mul_sum _ _ _).symm
    _ ≤ (2:ℝ)^(p+1)*∑'n,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by positivity)
    _ ≤ (2:ℝ)^(p+1)*(C*(H⁻¹)^(-p)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

lemma retained_dyadic_partition (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) :
    (smallDyadicIndices H).biUnion (fun n=>rows∩dyadicRows 1 n)=rows := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_inter.mp hu).1
  · intro hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u (hrows u hu).1 (rowNorm_ge_one u)
    refine Finset.mem_biUnion.mpr ⟨n,?_,Finset.mem_inter.mpr ⟨hu,hn⟩⟩
    rw [mem_smallDyadicIndices]
    have hlo := (mem_dyadicRows.mp hn).2.1
    simpa only [one_mul] using hlo.trans (hrows u hu).2

lemma retained_dyadic_sum {A : Type*} [AddCommMonoid A] (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) (f : FreeRow→A) :
    (∑u∈rows,f u)=∑n∈smallDyadicIndices H,∑u∈rows∩dyadicRows 1 n,f u := by
  conv_lhs => rw [←retained_dyadic_partition rows H hrows]
  apply Finset.sum_biUnion
  intro m hm n hn hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.inter_subset_right) (Finset.inter_subset_right)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorGlobal
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_global_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (globalFloorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6) := by
  obtain ⟨C,hC,hbound⟩ := actual_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  let θ : ℝ := 67/100+12*e+eps*(N+8)
  have hθ : 0<θ := by dsimp [θ];positivity
  obtain ⟨Cg,hCg,hgeom⟩ := bounded_dyadic_power_sum θ hθ
  refine ⟨C*Cg,mul_pos hC hCg,?_⟩
  intro η
  filter_upwards [hbound η,eventually_gt_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0<Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let Rn : ℕ→Finset FreeRow := fun k=>rows∩dyadicRows 1 k
  let term : FreeRow→ℂ := fun u=>frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
    ∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=>globalFloorPoolOutside M H S N c b Y j _ (P j).property) W Y
      (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(loss-1/40+mesh/6)
  have hD : 0≤D := by dsimp [D];positivity
  have hdyad (k : ℕ) : ‖∑u∈Rn k,term u‖≤D*((2:ℝ)^k)^θ := by
    let vk := Real.logb Z ((2:ℝ)^k)
    have hvk : 0≤vk := Real.logb_nonneg hZ (one_le_pow₀ (by norm_num))
    have heq : Z^vk=(2:ℝ)^k := Real.rpow_logb hZp hZ.ne' (by positivity)
    have hsub : Rn k⊆rows := Finset.inter_subset_left
    have hn : ∀u∈Rn k,Z^vk≤ rowNorm u ∧ rowNorm u≤2*Z^vk := by
      intro u hu
      have h := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
      simpa only [heq,one_mul] using And.intro h.1 h.2.le
    have hh := hb d hd hd' vk hvk (Rn k) (fun u hu=>hrows u (hsub hu)) hn i hi
      (fun u hu=>hbin u (hsub hu)) t ht
    change ‖∑u∈Rn k,term u‖≤_ at hh
    apply hh.trans_eq
    have hp : Z^(vk*θ+loss-1/40+mesh/6)=Z^(loss-1/40+mesh/6)*((2:ℝ)^k)^θ := by
      rw [show vk*θ+loss-1/40+mesh/6=(loss-1/40+mesh/6)+vk*θ by ring,Real.rpow_add hZp,
        Real.rpow_mul hZp.le,heq]
    change C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(vk*θ+loss-1/40+mesh/6)=_
    rw [hp]
    dsimp [D]
    ring
  have hpart := retained_dyadic_sum rows (Z^v) (fun u hu=>⟨(hrows u hu).1,hnorm u hu⟩) term
  change ‖∑u∈rows,term u‖≤_
  rw [hpart]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^v),‖∑u∈Rn k,term u‖ := norm_sum_le _ _
    _ ≤ ∑k∈smallDyadicIndices (Z^v),D*((2:ℝ)^k)^θ := Finset.sum_le_sum (fun k _=>hdyad k)
    _ = D*∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^θ := (Finset.mul_sum _ _ _).symm
    _ ≤ D*(Cg*(Z^v)^θ) := mul_le_mul_of_nonneg_left
      (hgeom (Z^v) (by positivity) (smallDyadicIndices (Z^v)) (fun k hk=>mem_smallDyadicIndices.mp hk)) hD
    _ = _ := by
      have hp : Z^(loss-1/40+mesh/6)*(Z^v)^θ=Z^(v*θ+loss-1/40+mesh/6) := by
        rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp]
        congr 1
        ring
      dsimp [D]
      calc
        _ = (C*Cg)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^(loss-1/40+mesh/6)*(Z^v)^θ) := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorGlobalIntegral
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_global_floor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      ‖finiteCentralCubeRows S hS hmax η rows T (globalFloorIntegralPoolOutside M H S N c b Yp) W Yp
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
            ProbeCentralExponent.realLoss N v e eps loss mesh) := by
  obtain ⟨Ca,hCa,hbound⟩ := actual_global_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cp*Ca,mul_pos hCp hCa,?_⟩
  intro η
  filter_upwards [hbound η,source_cube_height_eventually τ hτ] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  have hZp : 0<Z := zero_lt_one.trans_le hZ.1
  let Yp : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
  have hheight : (3*i+1:ℕ)*Z^τ≤(3*i+2:ℕ)*Z^τ := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
    exact_mod_cast (show 3*i+1≤3*i+2 by omega)
  let mass : ℝ := Ca*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)
  have hp := hprofile e (51/100) (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 le_rfl (by norm_num)
    hZ.2 hheight S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1) T
    (globalFloorIntegralPoolOutside M H S N c b Yp) (rayCubeFamily M H hH) hbin W Yp
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp mass (by dsimp [mass];positivity)
    (hb d hd hd' v hv rows hrows hnorm i hi hbin)
  apply hp.trans_eq
  rw [ProbeCentralExponent.physical_scale_identity Z (51/100) e hZp]
  have hpowers : Z^((25/48)*(51/100)-181/300+(105/8)*e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)=
      Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
        ProbeCentralExponent.realLoss N v e eps loss mesh) := by
    rw [←Real.rpow_add hZp]
    congr 1
    unfold ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
    ring
  dsimp [mass]
  calc
    _ = (Cp*Ca)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^((25/48)*(51/100)-181/300+(105/8)*e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)) := by ring
    _ = _ := by rw [hpowers]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorNormalized
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_normalized_floor_cube_oai (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (normalizedFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
            ProbeCentralExponent.realLoss N v e eps loss mesh+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨Cg,hCg,hbound⟩ := actual_global_floor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hellpos (j : Fin N) : 0<ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨Cg*Cn,mul_pos hCg hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
    ProbeCentralExponent.realLoss N v e eps loss mesh) nu]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorArithmetic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions_7 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeHighRowFamily.actual_normalized_floor_cube_oai := @OAI.SevenEighths.ProbeHighRowFamily.actual_normalized_floor_cube_oai
