-- Prove2me | solution 1 for OAI.SevenEighths.ProbeHighRowFamily.uniform_original_row_central_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:35:16.607667+00:00
-- url     : https://prove2.me/submissions/1e5b6f10-c776-4f2b-9f8a-e4592a1b4542

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowAmplitudeOnLines_buffered_polynomial
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowAmplitudeOnLines_first_polynomial
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowIntegral_central_decomposition

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
lemma rpow_le_scaleBound {q lo hi x : ℝ} (hq : 0<q) (hx : x∈Icc lo hi) :
    q^x≤ scaleBound q lo hi := by
  rw [Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  by_cases hl : 0≤Real.log q
  · exact (mul_le_mul_of_nonneg_left hx.2 hl).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hl)).trans (le_max_left _ _)
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

lemma outsideBox_measurable (T : ℝ) : MeasurableSet (outsideBox T) := by
  unfold outsideBox
  measurability
lemma height_le_joint_on_tail {T : ℝ} {p : HeightSpace} (hp : p∈outsideBox T) :
    1+T≤jointHeight p.1.1 p.1.2 p.2 := by
  rcases hp with h|h|h <;> unfold jointHeight <;>
    linarith [abs_nonneg p.1.1,abs_nonneg p.1.2,abs_nonneg p.2]

lemma weighted_tail_pointwise (f : HeightSpace → ℂ) (J N : ℕ) {T : ℝ} (hT : 0≤T)
    {p : HeightSpace} (hp : p∈outsideBox T) :
    jointHeight p.1.1 p.1.2 p.2^J*‖f p‖ ≤
      (jointHeight p.1.1 p.1.2 p.2^(J+N)*‖f p‖)/(1+T)^N := by
  apply (le_div_iff₀ (by positivity)).mpr
  have hn := pow_le_pow_left₀ (by linarith : 0≤1+T) (height_le_joint_on_tail hp) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos p.1.1 p.1.2 p.2).le J) (norm_nonneg (f p)))
  convert (preTransparency := .instances) hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi, ∀T : ℝ, 0≤T →
      (∫p : HeightSpace in outsideBox T, jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤K/(1+T)^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo (J+N)
  obtain ⟨K0,hK0,hM0⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ T hT
  obtain ⟨hi,hb⟩ := hM σ hσ ξ hξ υ hυ
  have hi0 := (hM0 σ hσ ξ hξ υ hυ).1
  calc
    _ ≤ ∫p : HeightSpace in outsideBox T,
        (jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖)/(1+T)^N ∂heightMeasure := by
      apply setIntegral_mono_on hi0.integrableOn (hi.div_const _).integrableOn (outsideBox_measurable T)
      intro p hp
      exact weighted_tail_pointwise _ J N hT hp
    _ = (∫p : HeightSpace in outsideBox T,
        jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)/(1+T)^N :=
      integral_div _ _
    _ ≤ (∫p : HeightSpace,
        jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)/(1+T)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply setIntegral_le_integral hi
      exact Eventually.of_forall (fun p => mul_nonneg
        (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

theorem profile_arithmetic_integrable (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ)
    (G : HeightSpace → ℂ) (hG : AEStronglyMeasurable G heightMeasure) (A : ℝ) (J : ℕ)
    (hbound : ∀p, ‖G p‖≤A*jointHeight p.1.1 p.1.2 p.2^J) :
    Integrable (fun p => G p*onLines W0 W1 σ ξ υ p) heightMeasure := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ ξ ξ υ υ hξ J
  have hi := (hM σ ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩).1
  apply (hi.const_mul A).mono'
  · exact hG.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)

lemma sliceMap_continuous (axis : SliceAxis) (T : ℝ) : Continuous (sliceMap axis T) := by
  cases axis <;> unfold sliceMap <;> fun_prop

lemma slice_height_le (axis : SliceAxis) (T : ℝ) (q : ℝ×ℝ) :
    height T≤jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2 := by
  cases axis <;> unfold sliceMap height jointHeight <;>
    linarith [abs_nonneg q.1,abs_nonneg q.2]

lemma cauchy_le_one (t : ℝ) : cauchy t≤1 := by
  simpa [cauchy] using inv_anti₀ (by norm_num : (0:ℝ)<1)
    (show 1≤1+t^2 by nlinarith [sq_nonneg t])

lemma jointEnvelope_slice_le (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointEnvelope J (sliceMap axis T q)≤ sliceEnvelope axis J T q := by
  cases axis
  · change gaussianMoment J (T+q.1)*cauchy q.1*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one q.1) (gaussianMoment_nonneg J (T+q.1))) (cauchy_nonneg q.2)
    simpa using hh
  · change gaussianMoment J (q.1+T)*cauchy T*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one T) (gaussianMoment_nonneg J (q.1+T))) (cauchy_nonneg q.2)
    simpa [add_comm] using hh
  · change gaussianMoment J (q.1+q.2)*cauchy q.2*cauchy T ≤ gaussianMoment J (q.1+q.2)*cauchy q.2
    simpa using mul_le_mul_of_nonneg_left (cauchy_le_one T)
      (mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _))

lemma pairEnvelope_integrable (J : ℕ) :
    Integrable (fun q : ℝ×ℝ => gaussianMoment J (q.1+q.2)*cauchy q.2) (volume.prod volume) := by
  have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
      (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
  have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
  have hi := hp1.integrable_comp_of_integrable ((gaussianMoment_integrable J).mul_prod cauchy_integrable)
  simpa only [Function.comp_def,Prod.swap,add_comm] using! hi

lemma sliceEnvelope_integrable (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    Integrable (sliceEnvelope axis J T) (volume.prod volume) := by
  cases axis
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact pairEnvelope_integrable J

lemma sliceEnvelope_integral (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    (∫q : ℝ×ℝ, sliceEnvelope axis J T q ∂volume.prod volume)=sliceMass J := by
  cases axis
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (q.1+q.2)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_symm _ (pairEnvelope_integrable J)]
    simp_rw [integral_mul_const,integral_add_right_eq_self]
    exact integral_const_mul _ _

lemma weighted_slice_pointwise (f : HeightSpace → ℂ) (axis : SliceAxis) (J N : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
      ‖f (sliceMap axis T q)‖ ≤
    (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
      ‖f (sliceMap axis T q)‖)/height T^N := by
  apply (le_div_iff₀ (pow_pos (height_pos T) N)).mpr
  have hn := pow_le_pow_left₀ (height_pos T).le (slice_height_le axis T q) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos (sliceMap axis T q).1.1
      (sliceMap axis T q).1.2 (sliceMap axis T q).2).le J) (norm_nonneg (f (sliceMap axis T q))))
  convert (preTransparency := .instances) hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T : ℝ,
      Integrable (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)≤K/height T^N := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    zlo zhi hzlo (J+N+2)
  obtain ⟨D,hD,hW⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+N+2)
  let A := realGaussianBound slo shi zlo zhi*2^(J+N)*C*D
  have hA : 0<A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|sliceMass (J+N)|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ axis T
  have hb := profile_moment_majorant W0 W1 (J+N) hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  let f (q : ℝ×ℝ) := jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
    (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖
  have hbound (q : ℝ×ℝ) : f q≤(A/height T^N)*sliceEnvelope axis (J+N) T q := by
    calc
      _ ≤ (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
          ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖)/height T^N :=
        weighted_slice_pointwise _ axis J N T q
      _ ≤ (A*jointEnvelope (J+N) (sliceMap axis T q))/height T^N :=
        div_le_div_of_nonneg_right (hb _) (pow_nonneg (height_pos T).le N)
      _ ≤ (A*sliceEnvelope axis (J+N) T q)/height T^N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (jointEnvelope_slice_le _ _ _ _) hA.le)
          (pow_nonneg (height_pos T).le N)
      _ = _ := by ring
  have hfnonneg (q : ℝ×ℝ) : 0≤f q := mul_nonneg
    (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
  have hf : Integrable f (volume.prod volume) := by
    apply ((sliceEnvelope_integrable axis (J+N) T).const_mul (A/height T^N)).mono'
    · have hc := (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)
      exact ((by cases axis <;> unfold sliceMap jointHeight <;> fun_prop : Continuous (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J)).mul hc.norm).aestronglyMeasurable
    · exact Eventually.of_forall (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (hfnonneg q)]; exact hbound q)
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ, (A/height T^N)*sliceEnvelope axis (J+N) T q ∂volume.prod volume :=
      integral_mono hf ((sliceEnvelope_integrable axis (J+N) T).const_mul _) hbound
    _ = (A/height T^N)*sliceMass (J+N) := by rw [integral_const_mul,sliceEnvelope_integral]
    _ ≤ (A/height T^N)*(1+|sliceMass (J+N)|) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hA.le (pow_nonneg (height_pos T).le N))
      linarith [le_abs_self (sliceMass (J+N))]
    _ = _ := by ring

theorem profile_arithmetic_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀A : ℝ, 0≤A → ∀G : HeightSpace → ℂ,
      AEStronglyMeasurable G heightMeasure →
      (∀p, ‖G p‖≤A*jointHeight p.1.1 p.1.2 p.2^J) →
      Integrable (fun p => G p*onLines W0 W1 σ ξ υ p) heightMeasure ∧
      ∀T : ℝ, 0≤T →
      (∫p : HeightSpace in outsideBox T, ‖G p*onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)
        ≤ A*K/(1+T)^N := by
  obtain ⟨K,hK,hT⟩ := profile_uniform_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  obtain ⟨K0,hK0,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ A hA G hG hbound
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ (hzlo.trans_le hξ.1) G hG A J hbound
  refine ⟨hi,?_⟩
  intro T hT0
  calc
    _ ≤ ∫p : HeightSpace in outsideBox T,
        A*(jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure := by
      apply setIntegral_mono_on hi.norm.integrableOn
        (((hM σ hσ ξ hξ υ hυ).1).const_mul A).integrableOn (outsideBox_measurable T)
      intro p hp
      rw [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)
    _ = A*(∫p : HeightSpace in outsideBox T,
        jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) :=
      integral_const_mul _ _
    _ ≤ A*(K/(1+T)^N) := mul_le_mul_of_nonneg_left (hT σ hσ ξ hξ υ hυ T hT0) hA
    _ = _ := by ring

theorem profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T A : ℝ, 0≤A → ∀G : ℝ×ℝ → ℂ,
      AEStronglyMeasurable G (volume.prod volume) →
      (∀q, ‖G q‖≤A*jointHeight (sliceMap axis T q).1.1
        (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ, ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)
        ≤ A*K/height T^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA G hG hbound
  obtain ⟨hm,hmb⟩ := hM σ hσ ξ hξ υ hυ axis T
  have hdom (q : ℝ×ℝ) : ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖≤
      A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
        (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) := by
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg _)
  have hi : Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q))
      (volume.prod volume) := by
    apply (hm.const_mul A).mono'
    · exact hG.mul (((onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)).aestronglyMeasurable)
    · exact Eventually.of_forall hdom
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ,
        A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) ∂volume.prod volume :=
      integral_mono hi.norm (hm.const_mul A) hdom
    _ = A*(∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume) :=
      integral_const_mul _ _
    _ ≤ A*(K/height T^N) := mul_le_mul_of_nonneg_left hmb hA
    _ = _ := by ring

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

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.FirstTail
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
local notation "O" => HeckeFamily.O

theorem firstPrimeDefectBound_summable (eps : ℝ) (heps : 0<eps) :
    Summable (firstPrimeDefectBound eps) := by
  have ht : 1<(1+min eps (1/50:ℝ) : ℂ).re := by
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re]
    have hm : 0< min eps (1/50:ℝ) := lt_min heps (by norm_num)
    linarith
  have h := (CubicEisenstein.fullIdealWeight_summable_norm
    (1+min eps (1/50:ℝ) : ℂ) ht).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight (1+min eps (1/50:ℝ) : ℂ) P.val‖=_
  unfold firstPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp only [Complex.neg_re,Complex.add_re,Complex.one_re,Complex.ofReal_re]
  congr 2
  ring

theorem FirstTail.summable {eps : ℝ} {S : Finset (Ideal O)} (h : FirstTail eps S) :
    Summable (fun P : {P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=>firstPrimeDefectBound eps P.val) :=
  (firstPrimeDefectBound_summable eps h.positive).subtype _

end SevenEighths.ProbeHighRowFamily

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.SliceIntegral
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀axis : SliceAxis,∀T A : ℝ,0≤A → ∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀G : ℝ×ℝ→ℂ,AEStronglyMeasurable G (volume.prod volume) →
      (∀q,‖G q‖≤A*jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      let F := fun q : ℝ×ℝ=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/height T^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let S := fun q : ℝ×ℝ=>sourceScale X Y Z ((σ:ℂ)+(sliceMap axis T q).1.1*I)
    ((υ:ℂ)+(sliceMap axis T q).2*I) ((ξ:ℂ)+(sliceMap axis T q).1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp (hc.comp (sliceMap_continuous axis T))
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : ℝ×ℝ) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : ℝ×ℝ) : ‖S q*G q‖≤(E*A)*jointHeight
      (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ axis T (E*A) (mul_nonneg hE hA)
    (fun q=>S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : ℝ×ℝ=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ (sliceMap axis T q)) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  have hnorm := congrArg (fun f : ℝ×ℝ→ℂ => ∫q : ℝ×ℝ,‖f q‖ ∂volume.prod volume) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/height T^N := hb
    _ = _ := by dsimp [E];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.HorizontalIntegral
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma continuedRow_horizontal_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (tx υ r : ℝ) (hr : 0< r) :
    Measurable (fun p : ℝ × (ℝ × ℝ)=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
      p.1 υ r ((tx,p.2.1),p.2.2)) := by
  have hR : Continuous (fun t : ℝ=>mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) ((r:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t;simpa using hr)
  have hW := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)).continuous
  have hcoords : Continuous (fun p : ℝ × (ℝ × ℝ)=>(((p.1:ℂ)+tx*I,(υ:ℂ)+p.2.2*I),(r:ℂ)+p.2.1*I)) := by fun_prop
  have hscale := (sourceScale_continuous X Y Z hX hY hZ).comp hcoords
  have hprof : Measurable (fun p : ℝ × (ℝ × ℝ)=>profile W0 W1
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    unfold profile
    apply Measurable.mul
    · apply Measurable.mul
      · fun_prop
      · exact hR.measurable.comp (by fun_prop)
    · exact hW.measurable.comp (by fun_prop)
  have hsource : Measurable (fun p : ℝ × (ℝ × ℝ)=>sourceMellinWeight W0 W1 X Y Z
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    simp_rw [sourceMellinWeight_eq_scale]
    exact hscale.measurable.mul hprof
  have hphysical := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun p : ℝ × (ℝ × ℝ)=>(p.1:ℂ)+tx*I) (fun p : ℝ × (ℝ × ℝ)=>(υ:ℂ)+p.2.2*I)
    (fun p : ℝ × (ℝ × ℝ)=>(r:ℂ)+p.2.1*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold continuedRowOnLines continuedPhysicalRowKernel
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul hsource
      apply Finset.measurable_prod
      intro i hi
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _
          (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero).ne'
      · fun_prop
    · unfold frequencyWeight
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
      · fun_prop
  · exact hphysical.const_mul _

lemma horizontal_integral_bound (F : ℝ→(ℝ×ℝ)→ℂ) (l r C : ℝ) (hlr : l≤ r) (_hC : 0≤C)
    (hm : Measurable (Function.uncurry F))
    (hi : ∀v∈Ioc l r,Integrable (F v) (volume.prod volume))
    (hb : ∀v∈Ioc l r,(∫q : ℝ×ℝ,‖F v q‖ ∂volume.prod volume)≤C) :
    Integrable (fun q : ℝ×ℝ=>∫v : ℝ in l..r,F v q) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖∫v : ℝ in l..r,F v q‖ ∂volume.prod volume)≤(r-l)*C := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let ν : Measure (ℝ×ℝ) := volume.prod volume
  have hm' : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := hm.aestronglyMeasurable
  have hnorm : Integrable (fun v=>∫q,‖F v q‖ ∂ν) μ := by
    apply (integrable_const C).mono' hm'.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
    exact hb v hv
  have hprod : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply (integrable_prod_iff hm').mpr
    refine ⟨?_,hnorm⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hi v hv
  have hj : Integrable (fun q=>∫v,F v q ∂μ) ν := hprod.integral_prod_right
  simp only [intervalIntegral.integral_of_le hlr]
  refine ⟨hj,?_⟩
  calc
    _ ≤ ∫q,∫v,‖F v q‖ ∂μ ∂ν := integral_mono hj.norm hprod.integral_norm_prod_right
      (fun q=>norm_integral_le_integral_norm _)
    _ = ∫v,∫q,‖F v q‖ ∂ν ∂μ := integral_integral_swap hprod.norm.swap
    _ ≤ ∫v,C ∂μ := integral_mono_ae hnorm (integrable_const C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact hb v hv)
    _ = _ := by
      dsimp [μ]
      rw [setIntegral_const,Real.volume_real_Ioc_of_le hlr,smul_eq_mul]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma FirstTail.mono_parameter {eps eps' : ℝ} {S : Finset (Ideal O)}
    (h : FirstTail eps S) (hle : eps≤eps') : FirstTail eps' S := by
  have hp : 0<eps' := h.positive.trans_le hle
  refine ⟨hp,h.norm_four,?_⟩
  apply le_trans _ h.small
  apply ((firstPrimeDefectBound_summable eps' hp).subtype _).tsum_le_tsum _ h.summable
  intro P
  unfold firstPrimeDefectBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le
  · have hn := h.norm_four P.val P.property
    exact_mod_cast (by omega : 1≤P.val.val.absNorm)
  · have hm := min_le_min_right (1/50:ℝ) hle
    linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.TailIntegral
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀A : ℝ,0≤A → ∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀G : HeightSpace→ℂ,AEStronglyMeasurable G heightMeasure →
      (∀q,‖G q‖≤A*jointHeight q.1.1 q.1.2 q.2^J) →
      let F := fun q : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+q.1.1*I) ((υ:ℂ)+q.2*I)
        ((ξ:ℂ)+q.1.2*I)*G q
      Integrable F heightMeasure ∧ ∀T : ℝ,0≤T →
        (∫q : HeightSpace in outsideBox T,‖F q‖ ∂heightMeasure)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/(1+T)^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let S := fun q : HeightSpace=>sourceScale X Y Z ((σ:ℂ)+q.1.1*I)
    ((υ:ℂ)+q.2*I) ((ξ:ℂ)+q.1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp hc
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : HeightSpace) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : HeightSpace) : ‖S q*G q‖≤(E*A)*jointHeight
      q.1.1 q.1.2 q.2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ (E*A) (mul_nonneg hE hA)
    (fun q=>S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+q.1.1*I) ((υ:ℂ)+q.2*I)
        ((ξ:ℂ)+q.1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ q) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  intro T hT
  have hnorm := congrArg (fun f : HeightSpace→ℂ => ∫q : HeightSpace in outsideBox T,‖f q‖ ∂heightMeasure) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/(1+T)^N := hb T hT
    _ = _ := by dsimp [E];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralError
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma scaleBound_eq_rpow_of_one_le {q lo hi : ℝ} (hq : 1≤q) (hl : lo≤hi) :
    scaleBound q lo hi=q^hi := by
  unfold scaleBound
  rw [max_eq_right (mul_le_mul_of_nonneg_left hl (Real.log_nonneg hq)),
    Real.rpow_def_of_pos (by linarith)]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CoarseAmplitude
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma contourArithmeticCost_nonneg {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :
    0≤ contourArithmeticCost η u P := by unfold contourArithmeticCost;positivity

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.UniformSlices
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_buffered_x_slice_decay (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  have hrow := hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow σ hσ r ⟨hr,hr1⟩ ((tx,q.1),q.2) htx.le).trans
    calc
      _ ≤ (A*(3+|H|)^2)*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
      _ = _ := by ring
  have ht := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ .s tx (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤
        (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^(N+2) := by
    simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht
  refine ⟨ht'.1,ht'.2.trans ?_⟩
  have hH0 : 0≤H := htx ▸ abs_nonneg tx
  have hheight : height tx=height H := by simp [height,htx,abs_of_nonneg hH0]
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hden : 0<height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*(height H)^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.UniformJoins
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_buffered_horizontal_join_decay (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*contourArithmeticCost η u P*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound0⟩ := uniform_buffered_x_slice_decay (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N r hr hr1
  refine ⟨2*C,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx
  have hbound := hbound0 η u hu P hP hPS ψ
  have hcost := contourArithmeticCost_nonneg η u P
  let A : ℝ := C*contourArithmeticCost η u P*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (mul_nonneg (mul_nonneg hC hcost) (by unfold scaleBound;positivity)) (pow_nonneg (height_pos _).le _)
  have hslice (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :=
    hbound X Y Z hX hY hZ a B H i ha haTop hB hH hbin v ⟨hv.1.le,hv.2⟩ tx htx
  have hnorm (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        v (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤A := by
    apply (hslice v hv).2.trans
    have hz := rpow_le_scaleBound hZ
      (show v+r-1∈Icc ((51/100)+r-1) (2+r-1) by constructor <;> linarith [hv.1,hv.2])
    dsimp [A]
    gcongr
    exact pow_nonneg (height_pos H).le N
  have hm := continuedRow_horizontal_measurable S hS hmax P hPS η u W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ tx (1-a-6*e) r (by linarith)
  obtain ⟨hi,hb⟩ := horizontal_integral_bound
    (fun v q=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2))
    (a+16*e) 2 A (by linarith) hA hm (fun v hv=>(hslice v hv).1) hnorm
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ 2*A := mul_le_mul_of_nonneg_right (by linarith : 2-(a+16*e)≤2) hA
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.UniformTail
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem uniform_original_x_height_tail (K : ℕ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,∀υ∈Icc (-(1/100:ℝ)) (1/2),∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀H : ℝ,0≤H →
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H}ᶜ,
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+H)^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_first_polynomial K S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r (-(1/100)) (1/2) (by linarith) 2 N
  refine ⟨9*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS υ hυ X Y Z hX hY hZ H hH
  let A := A0*contourArithmeticCost η u P
  have hA := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  have hrow := hrow0 η u hu P hP hPS
  let G := rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r
  have hG : Measurable G := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  have hb (t : HeightSpace) : ‖G t‖≤(9*A)*jointHeight t.1.1 t.1.2 t.2^2 := by
    have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
      unfold jointHeight
      linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
    apply (hrow υ hυ.1 r ⟨hr,hr1⟩ t).trans
    calc
      _ ≤ A*(3*jointHeight t.1.1 t.1.2 t.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ hυ
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
      ∀T : ℝ,0≤T →
      (∫p : HeightSpace in outsideBox T,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        (9*A)*D*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+T)^N := by
    have hfun : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((r:ℂ)+p.1.2*I)*G p) := by
      funext p
      exact continuedRowOnLines_eq_amplitude ..
    rw [hfun]
    exact ht
  apply le_trans _ ((ht'.2 H hH).trans_eq (by dsimp [A];ring))
  apply setIntegral_mono_set ht'.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
  apply Filter.Eventually.of_forall
  intro p hp
  have hx : H < |p.1.1| := by
    change p ∈ {t : _ | |t.1.1| ≤ H}ᶜ at hp
    simpa using hp
  exact Or.inl hx

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.UniformError
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_original_row_central_error_oai (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨Cj,hCj,hjoin0⟩ := uniform_buffered_horizontal_join_decay (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  obtain ⟨Ct,hCt,htail0⟩ := uniform_original_x_height_tail K S hS hmax (hfirst.mono_parameter (by linarith))
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*(2*Cj+Ct),by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hjoin := hjoin0 η u hu P hP hPS ψ
  have htail := htail0 η u hu P hP hPS
  have hcost := contourArithmeticCost_nonneg η u P
  have hZ0 : 0<Z := by linarith
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let J := fun tx : ℝ=>∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) ∂volume.prod volume
  let tail := ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure
  let A : ℝ := contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (by positivity) (pow_nonneg (height_pos _).le _)
  have hj (tx : ℝ) (htx : |tx|=H) : ‖J tx‖≤Cj*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := (hjoin X Y Z hX hY hZ0 a B H i ha haTop hB hH hbin tx htx).2
    rw [scaleBound_eq_rpow_of_one_le hZ (by norm_num)] at hb
    convert (preTransparency := .instances) hb using 1 ; dsimp [J,k,A] ; ring
  have ht : ‖tail‖≤Ct*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := htail (1-a-6*e) ⟨by linarith,by linarith⟩ X Y Z hX hY hZ0 H hH0
    convert (preTransparency := .instances) hb using 1 ; dsimp [tail,k,E,A,height] ; rw [abs_of_nonneg hH0] ; ring
  have hdec := (rowIntegral_central_decomposition e a B H i he he' ha haTop hB hH0 hH S hS hmax hfirst
    P hP hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ0).2
  have heq : rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
      centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=n*(I*(J (-H)-J H)+tail) := by
    rw [hdec]
    dsimp [centralRowIntegral,n,J,tail,k,E]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(‖J (-H)‖+‖J H‖+‖tail‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg n)
      apply (norm_add_le (I*(J (-H)-J H)) tail).trans
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_sub_le (J (-H)) (J H)) (le_refl ‖tail‖)
    _ ≤ ‖n‖*(Cj*A+Cj*A+Ct*A) := by
      gcongr
      · exact hj (-H) (by rw [abs_neg,abs_of_nonneg hH0])
      · exact hj H (abs_of_nonneg hH0)
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.ProbeHighRowFamily.uniform_original_row_central_error_oai.{u_1} := @OAI.SevenEighths.ProbeHighRowFamily.uniform_original_row_central_error_oai.{u_1}
