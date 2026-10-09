-- Prove2me | solution 1 for OAI.SevenEighths.HeckeLogarithmic.disk_control_of_euler_log
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:48:54.351322+00:00
-- url     : https://prove2.me/submissions/417a1c29-4ebe-4a32-a374-19481b241013

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Continuation
namespace OAI

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation

theorem product_identity_on_halfPlane (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | a < s.re})
    (hM : AnalyticOnNhd ℂ M {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W {s : ℂ | a < s.re} := by
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by dsimp [z]; linarith [le_max_left a b]
  have hz' : max a b < z.re := by dsimp [z]; simp
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by
    filter_upwards [(Complex.isOpen_re_gt (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  exact (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
    (convex_halfSpace_re_gt a).isPreconnected hz hev

end SevenEighths.Continuation

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

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedCompleted_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

theorem regularizedLatticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring

end SevenEighths.HeckeTheta

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.FamilySeries
namespace OAI

noncomputable section
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem latticeL_eq_of_coefficients_right {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 1 < s.re) : latticeL w s = latticeL v s := by
  have hw := latticeL_hasSum w hs
  simp_rw [hcoeff] at hw
  exact hw.unique (latticeL_hasSum v hs)

theorem latticeL_eq_of_coefficients {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) : latticeL w s = latticeL v s := by
  have hwa : AnalyticOnNhd ℂ (regularizedLatticeL w) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (regularizedLatticeL_differentiableAt w
      (by intro h; simp [h] at hz)).differentiableWithinAt
  have hva : AnalyticOnNhd ℂ (regularizedLatticeL v) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (regularizedLatticeL_differentiableAt v
      (by intro h; simp [h] at hz)).differentiableWithinAt
  have hident := Continuation.product_identity_on_halfPlane 0 1
    (regularizedLatticeL w) (fun _ => 1) (regularizedLatticeL v)
    hwa analyticOnNhd_const hva (by
      intro z hz
      have hz' : 1 < z.re := by simpa using hz
      have hz₀ : z ≠ 0 := by intro h; norm_num [h] at hz'
      have hz₁ : z ≠ 1 := by intro h; norm_num [h] at hz'
      simp only [mul_one, regularizedLatticeL_eq w hz₀ hz₁,
        regularizedLatticeL_eq v hz₀ hz₁,
        latticeL_eq_of_coefficients_right w v hcoeff hz']) hs
  have hs₀ : s ≠ 0 := by intro h; simp [h] at hs
  simp only [mul_one, regularizedLatticeL_eq w hs₀ hs₁,
    regularizedLatticeL_eq v hs₀ hs₁] at hident
  exact mul_left_cancel₀ (sub_ne_zero.mpr hs₁) hident
end SevenEighths.HeckeTheta

namespace SevenEighths.HeckeFamily
open EisensteinTheta

theorem continuedLattice_eq_of_elementCoeff_eq (χ ψ : Character)
    (hχψ : ∀ z, elementCoeff χ z = elementCoeff ψ z)
    {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    continuedLattice χ s = continuedLattice ψ s := by
  apply HeckeTheta.latticeL_eq_of_coefficients (coefficients χ) (coefficients ψ) _ hs hs₁
  intro n
  simp only [periodicCoeff_eq_elementCoeff, hχψ]

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.MellinIdentity
namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace SevenEighths.HeckeMellinIdentity

theorem scaled_eq (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (A : ℝ) (hA : 0 < A)
    (hright : ∀ s : ℂ, 1 < s.re → P.Λ s = (A : ℂ)^(-s) * Q.Λ s)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    P.Λ s = (A : ℂ)^(-s) * Q.Λ s := by
  have hd : Differentiable ℂ (fun z : ℂ => (A : ℂ)^(-z) * regularized Q z) :=
    ((differentiable_id.neg).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hA.ne'))).mul (regularized_entire Q)
  have he : regularized P = fun z : ℂ => (A : ℂ)^(-z) * regularized Q z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularized_entire P)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have hz1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [regularized_eq P hP hz0 hz1, regularized_eq Q hQ hz0 hz1, hright z hz]
    ring
  have heq := congr_fun he s
  rw [regularized_eq P hP h0 h1, regularized_eq Q hQ h0 h1] at heq
  apply mul_left_cancel₀ (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  calc
    s * (s - 1) * P.Λ s = (A : ℂ)^(-s) * (s * (s-1) * Q.Λ s) := heq
    _ = s * (s-1) * ((A : ℂ)^(-s) * Q.Λ s) := by ring

theorem eq_of_f (P Q : WeakFEPair ℂ) (hP : P.k = 1) (hQ : Q.k = 1)
    (hf : ∀ t : ℝ, 0 < t → P.f t = Q.f t) (hf₀ : P.f₀ = Q.f₀)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : P.Λ s = Q.Λ s := by
  have h := scaled_eq P Q hP hQ 1 zero_lt_one (fun z hz => by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [← (P.hasMellin (by rwa [hP])).2, ← (Q.hasMellin (by rwa [hQ])).2]
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hf t ht, hf₀]) h0 h1
  simpa only [Complex.ofReal_one, Complex.one_cpow, one_mul] using h

end SevenEighths.HeckeMellinIdentity

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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

end

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

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

lemma rpow_between_endpoints (y a b σ : ℝ) (hy : 0<y) (ha : a≤σ) (hb : σ≤b) :
    y^σ≤y^a+y^b := by
  by_cases h1 : 1≤y
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hy.le a))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge h1) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le b))

theorem mellin_uniform_strip_bound (f : ℝ→ℂ) (a b : ℝ)
    (ha : MellinConvergent f (a:ℂ)) (hb : MellinConvergent f (b:ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,a≤ s.re→s.re≤b→‖mellin f s‖≤C := by
  let B : ℝ→ℝ := fun y=>‖(y:ℂ)^((a:ℂ)-1)*f y‖+‖(y:ℂ)^((b:ℂ)-1)*f y‖
  have hB : IntegrableOn B (Set.Ioi 0) := by
    exact ha.norm.add hb.norm
  refine ⟨∫y in Set.Ioi 0,B y,integral_nonneg (fun y=>add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro s hsa hsb
  unfold mellin
  apply norm_integral_le_of_norm_le hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 0<y at hy
  have hp := rpow_between_endpoints y (a-1) (b-1) (s.re-1) hy (by linarith) (by linarith)
  change ‖(y:ℂ)^(s-1)*f y‖≤B y
  dsimp only [B]
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (f y))

end VerticalContourShift

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

lemma norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖≤Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    _ ≤ ‖Complex.exp (-z*Complex.I)‖+‖Complex.exp (z*Complex.I)‖ := norm_sub_le _ _
    _ = Real.exp z.im+Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im|+Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _)) (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = _ := by ring

lemma Gamma_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im≠0) : Complex.Gamma z≠0 := by
  apply Complex.Gamma_ne_zero
  intro n he
  apply hz
  have h:=congrArg Complex.im he
  simpa using h

lemma inverse_Gamma_reflection (z : ℂ) (hz : z.im≠0) :
    (Complex.Gamma z)⁻¹=Complex.Gamma (1-z)*Complex.sin (Real.pi*z)/Real.pi := by
  have hg:=Gamma_ne_zero_of_im_ne_zero z hz
  have hh:=Gamma_ne_zero_of_im_ne_zero (1-z) (by simpa using hz)
  have hp : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : Complex.sin (Real.pi*z)≠0 := by
    intro hs
    have he:=Complex.Gamma_mul_Gamma_one_sub z
    rw [hs,div_zero] at he
    exact (mul_ne_zero hg hh) he
  apply mul_left_cancel₀ hg
  rw [mul_inv_cancel₀ hg]
  symm
  calc
    _ = (Complex.Gamma z*Complex.Gamma (1-z))*Complex.sin (Real.pi*z)/Real.pi := by ring
    _ = 1 := by
      rw [Complex.Gamma_mul_Gamma_one_sub,div_mul_cancel₀ _ hs,div_self hp]

lemma inverse_Gamma_norm_of_left (z : ℂ) (hz : z.re<1) (hi : z.im≠0) :
    ‖(Complex.Gamma z)⁻¹‖≤
      (Real.Gamma (1-z.re)/Real.pi)*Real.exp (Real.pi*|z.im|) := by
  rw [inverse_Gamma_reflection z hi,norm_div,norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hgamma:=norm_Gamma_le_real (1-z) (by simp;linarith)
  have hsin:=norm_sin_le_exp_abs_im (Real.pi*z)
  simp only [Complex.sub_re,Complex.one_re] at hgamma
  have him : |((Real.pi:ℂ)*z).im|=Real.pi*|z.im| := by
    simp [abs_mul, Real.pi_nonneg]
  rw [him] at hsin
  calc
    _ ≤ (Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|))/Real.pi :=
      div_le_div_of_nonneg_right
        (mul_le_mul hgamma hsin (norm_nonneg _) (Real.Gamma_pos_of_pos (by linarith)).le)
        Real.pi_pos.le
    _ = _ := by ring

lemma inverse_Gamma_norm_le_shift_left (z : ℂ) (n : ℕ) (hi : 1≤|z.im|) :
    ‖(Complex.Gamma z)⁻¹‖≤‖(Complex.Gamma (z-n))⁻¹‖ := by
  have he:=congrArg norm (CubicReflectionKernel.inverse_Gamma_shift (z-n) n)
  simp only [sub_add_cancel,norm_mul] at he
  have hprod : 1≤‖∏k∈Finset.range n,(z-(n:ℂ)+k)‖ := by
    rw [norm_prod]
    apply Finset.one_le_prod
    intro k hk
    calc
      1 ≤ |z.im| := hi
      _ = |(z-(n:ℂ)+k).im| := by simp
      _ ≤ _ := Complex.abs_im_le_norm _
  rw [he]
  exact le_mul_of_one_le_left (norm_nonneg _) hprod

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀x∈Set.Icc a b,Real.Gamma x≤C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx=>ha.trans_le hx.1)
  obtain ⟨C,hC⟩:=(isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

lemma inverse_Gamma_compact_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t∈Set.Icc (-1:ℝ) 1,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C := by
  have hc : Continuous (fun p : ℝ×ℝ=>
      ‖(Complex.Gamma ((p.1:ℂ)+p.2*Complex.I))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)).norm
  obtain ⟨C,hC⟩:=((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))).bddAbove_image hc.continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  intro σ hσ t ht
  exact (hC ⟨(σ,t),⟨hσ,ht⟩,rfl⟩).trans (by linarith [le_abs_self C])

theorem inverse_Gamma_strip_exp_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t : ℝ,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C*Real.exp (Real.pi*|t|) := by
  obtain ⟨n,hn⟩:=exists_nat_gt b
  obtain ⟨Cg,hCg,hg⟩:=real_Gamma_compact_bound ((n:ℝ)+1-b) ((n:ℝ)+1-a) (by linarith)
  obtain ⟨Cc,hCc,hc⟩:=inverse_Gamma_compact_strip_bound a b
  refine ⟨Cc+Cg/Real.pi,by positivity,?_⟩
  intro σ hσ t
  have hexp : 1≤Real.exp (Real.pi*|t|) := Real.one_le_exp (by positivity)
  by_cases ht:|t|≤1
  · have hsmall:=hc σ hσ t (abs_le.mp ht)
    calc
      _ ≤ Cc := hsmall
      _ ≤ Cc+Cg/Real.pi := le_add_of_nonneg_right (by positivity)
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        le_mul_of_one_le_right (by positivity) hexp
  · have ht1 : 1 < |t| :=lt_of_not_ge ht
    have ht0 : t≠0 := by intro ht0;subst t;norm_num at ht1
    let z : ℂ := (σ:ℂ)+t*Complex.I
    let w : ℂ := z-n
    have hw : w.re<1 := by
      dsimp [w,z]
      simp only [Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
        sub_zero,add_zero]
      linarith [hσ.2]
    have hwi : w.im≠0 := by simpa [w,z] using ht0
    have he : 1-w.re=(n:ℝ)+1-σ := by simp [w,z];ring
    have hi : w.im=t := by simp [w,z]
    have hbound:=inverse_Gamma_norm_of_left w hw hwi
    rw [he,hi] at hbound
    have hgbound:=hg ((n:ℝ)+1-σ) ⟨by linarith [hσ.2],by linarith [hσ.1]⟩
    calc
      _ ≤ ‖(Complex.Gamma w)⁻¹‖ :=
        inverse_Gamma_norm_le_shift_left z n (by simpa [z] using ht1.le)
      _ ≤ (Real.Gamma ((n:ℝ)+1-σ)/Real.pi)*Real.exp (Real.pi*|t|) := hbound
      _ ≤ (Cg/Real.pi)*Real.exp (Real.pi*|t|) := by gcongr
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCc.le) (Real.exp_pos _).le

theorem inverse_Gamma_strip_exp_bound_complex (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀z : ℂ,z.re∈Set.Icc a b →
      ‖(Complex.Gamma z)⁻¹‖≤C*Real.exp (Real.pi*|z.im|) := by
  obtain ⟨C,hC,hb⟩:=inverse_Gamma_strip_exp_bound a b
  refine ⟨C,hC,?_⟩
  intro z hz
  simpa only [Complex.re_add_im] using hb z.re hz z.im

end CubicGammaExponential

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open Filter MeasureTheory
open scoped Classical BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Primitive
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckePrimitive
open HeckeFamily

variable (c : O) [NeZero c]

theorem pair_completed_eq_right (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : 1 < s.re) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s := by
  let w := coefficients (character c χ hu)
  have h := (pair c χ hu hp).hasMellin hs
  calc
    (pair c χ hu hp).Λ s =
        mellin (fun t => HeckeTheta.theta w (scale c * t) - w (0,0)) s := h.2.symm
    _ = (scale c : ℂ) ^ (-s) * mellin (fun t => HeckeTheta.theta w t - w (0,0)) s :=
      by simpa only [smul_eq_mul] using
        mellin_comp_mul_left (fun t => HeckeTheta.theta w t - w (0,0)) s (scale_pos c)
    _ = (scale c : ℂ) ^ (-s) * HeckeTheta.completed w s := by
      congr 1
      rw [← (HeckeTheta.pair_hasMellin w hs).2]
      unfold mellin
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [HeckeTheta.theta_eq_pair w ht, HeckeTheta.pair_f₀]

theorem pair_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s :=
  HeckeMellinIdentity.scaled_eq (pair c χ hu hp)
    (HeckeTheta.pair (coefficients (character c χ hu))) rfl (HeckeTheta.pair_k _)
    (scale c) (scale_pos c) (fun _ hs => pair_completed_eq_right c χ hu hp hs) h0 h1

theorem symm_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).symm.Λ s =
      (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv).Λ s := by
  apply HeckeMellinIdentity.eq_of_f (pair c χ hu hp).symm
    (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv) rfl rfl _ rfl h0 h1
  intro t _
  change (pair c χ hu hp).g t = _
  rw [pair_g, pair_f]

theorem completedL_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedL c χ hu hp (1-s) = TraceCharacter.normalizedGauss c χ *
      completedL c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv s := by
  have h := (pair c χ hu hp).functional_equation s
  change (pair c χ hu hp).Λ (1-s) = TraceCharacter.normalizedGauss c χ *
    (pair c χ hu hp).symm.Λ s at h
  rw [symm_completed_eq c χ hu hp h0 h1] at h
  unfold completedL
  rw [h]
  ring

theorem completedL_eq_gamma_mul_LFunction (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s = (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) *
      Complex.Gamma s * LFunction (character c χ hu) s := by
  unfold completedL
  rw [pair_completed_eq c χ hu hp h0 h1]
  unfold LFunction continuedLattice HeckeTheta.latticeL
  simp only [Complex.cpow_neg]
  have hπ : (Real.pi : ℂ)^s ≠ 0 := by
    exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [Real.pi_ne_zero])
  field_simp

end SevenEighths.HeckePrimitive

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ReciprocalBound
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖CubicEisenstein.fullIdealWeight s I‖ ≤
      ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖ := by
  by_cases hI : I = 0
  · simp [hI, CubicEisenstein.fullIdealWeight]
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [CubicEisenstein.fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

end SevenEighths.HeckeReciprocalBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ThetaRegularity
namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

open ActualEisensteinCubic ConcreteTraceCRT GaussianTheta

theorem lattice_gap (z : O) (hz : z ≠ 0) : 1 ≤ ‖eisEmbedding z‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz)

variable (c : O) [NeZero c]

end SevenEighths.ThetaRegularity

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Strip
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter Asymptotics Set MeasureTheory

namespace SevenEighths.HeckeStrip

theorem gammaConstant_pos : 0 < gammaConstant :=
  div_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))

theorem gamma_ratio_left_bound (t : ℝ) :
    ‖Complex.Gamma (1 - ((-(1 / 10) : ℂ) + t * Complex.I)) /
      Complex.Gamma ((-(1 / 10) : ℂ) + t * Complex.I)‖ ≤
        gammaConstant * (3 + |t|) ^ 2 := by
  let s : ℂ := -(1 / 10) + t * Complex.I
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1 / 2) (3 / 5) (-t) 2 (by norm_num) (by norm_num)
  simp only [Complex.ofReal_neg] at hb
  have hnum : ((1 / 2 : ℝ) : ℂ) + ((3 / 5 : ℝ) + (-t) * Complex.I) = 1 - s := by
    dsimp [s]; push_cast; ring
  have hden : ((1 / 2 : ℝ) : ℂ) - ((3 / 5 : ℝ) + (-t) * Complex.I) + (2 : ℕ) = s + 2 := by
    dsimp [s]; push_cast; ring
  rw [hnum, hden] at hb
  norm_num only [show (1 / 2 : ℝ) + 3 / 5 = 11 / 10 by norm_num,
    show (1 / 2 : ℝ) - 3 / 5 + (2 : ℕ) = 19 / 10 by norm_num] at hb
  have heq : Complex.Gamma (1 - s) / Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s + k)) *
        (Complex.Gamma (1 - s) / Complex.Gamma (s + 2)) := by
    rw [div_eq_mul_inv, CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat, div_eq_mul_inv]
    ring
  have hs : ‖s‖ ≤ 1 / 10 + |t| := by
    simpa [s, norm_mul] using norm_add_le (-(1 / 10) : ℂ) ((t : ℂ) * Complex.I)
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  have hf' : ‖∏ k ∈ Finset.range 2, (s + k)‖ ≤ (3 + |t|) ^ 2 := by
    have hs2 : ‖s‖ + (2 : ℝ) ≤ 3 + |t| := by linarith
    exact hf.trans (pow_le_pow_left₀ (by positivity) hs2 2)
  change ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ ≤ _
  rw [heq, norm_mul]
  exact (mul_le_mul hf' hb (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem gamma_ratio_left_bound_of_re (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖Complex.Gamma (1 - z) / Complex.Gamma z‖ ≤ gammaConstant * (3 + |z.im|) ^ 2 := by
  have he : (-(1 / 10) : ℂ) + z.im * Complex.I = z := by
    simpa only [hz, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.re_add_im z
  simpa only [he] using gamma_ratio_left_bound z.im

theorem completionScale_pos (Q : ℝ) (hQ : 0 < Q) : 0 < completionScale Q := by
  unfold completionScale
  positivity

theorem completionScale_left_power (Q : ℝ) (hQ : 0 < Q) :
    completionScale Q ^ (6 / 5 : ℝ) =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
  have he : completionScale Q = (Real.sqrt 3 / (2 * Real.pi)) * Real.sqrt Q := by
    unfold completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [he, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
  congr 1
  rw [Real.sqrt_eq_rpow Q, ← Real.rpow_mul hQ.le]
  norm_num

theorem leftConstant_pos : 0 < leftConstant :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) gammaConstant_pos

theorem left_boundary_of_functional_equation (Q D : ℝ) (hQ : 0 < Q) (_hD : 0 ≤ D)
    (L Ldual : ℂ → ℂ) (ε : ℂ) (hε : ‖ε‖ = 1)
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖L z‖ ≤ leftConstant * D * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hscale : ‖(completionScale Q : ℂ) ^ (1 - 2 * z)‖ =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (completionScale_pos Q hQ)]
    have hre : (1 - 2 * z).re = 6 / 5 := by simp [hz]; norm_num
    rw [hre, completionScale_left_power Q hQ]
  have hd : ‖Ldual (1 - z)‖ ≤ D := hdual _ (by simp [hz]; norm_num)
  rw [hfe z hz, norm_mul, norm_mul, norm_mul, hε, one_mul, hscale]
  have hg := gamma_ratio_left_bound_of_re z hz
  have hc := gammaConstant_pos
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left hg (by positivity)) hd (norm_nonneg _)
    (by positivity : 0 ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
      (gammaConstant * (3 + |z.im|) ^ 2))
  calc
    _ ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
        (gammaConstant * (3 + |z.im|) ^ 2) * D := hm
    _ = _ := by unfold leftConstant; ring

theorem vertical_strip_of_exp_bound (F : ℂ → ℂ) (C : ℝ)
    (hF : DiffContOnCl ℂ F strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖F z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) → ‖F z‖ ≤ C)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖F z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) : ‖F z‖ ≤ C := by
  obtain ⟨A, B, hA, hB, hgrowth⟩ := hgrowth
  apply PhragmenLindelof.vertical_strip hF ?_ hleft hright hz.1 hz.2
  refine ⟨1, ?_, B, ?_⟩
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 11 / 10 - -(1 / 10))).mpr
    linarith [Real.two_le_pi]
  · apply isBigO_iff.mpr
    refine ⟨A, eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (hgrowth z hz).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hB

theorem closure_strip_subset : closure strip ⊆ closedStrip :=
  closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    (isClosed_Icc.preimage Complex.continuous_re)

theorem shift_norm_lower (z : ℂ) (hz : z ∈ closedStrip) : 1 ≤ ‖z + 2‖ := by
  have h := Complex.re_le_norm (z + 2)
  norm_num at h
  linarith [hz.1]

theorem shift_ne_zero (z : ℂ) (hz : z ∈ closedStrip) : z + 2 ≠ 0 := by
  have h := shift_norm_lower z hz
  intro hzero
  rw [hzero, norm_zero] at h
  norm_num at h

theorem height_le_shift_norm (z : ℂ) (hz : z ∈ closedStrip) :
    3 + |z.im| ≤ 3 * ‖z + 2‖ := by
  have hr := Complex.re_le_norm (z + 2)
  have hi := Complex.abs_im_le_norm (z + 2)
  norm_num at hr hi
  linarith [hz.1]

theorem shift_norm_le_height (z : ℂ) (hz : z ∈ closedStrip) :
    ‖z + 2‖ ≤ 2 * (3 + |z.im|) := by
  have hr : 0 ≤ z.re + 2 := by linarith [hz.1]
  have h := Complex.norm_le_abs_re_add_abs_im (z + 2)
  norm_num [abs_of_nonneg hr] at h
  linarith [hz.2, abs_nonneg z.im]

theorem norm_normalized (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ) (z : ℂ) :
    ‖normalized Q L z‖ = ‖L z‖ / (Q ^ (3 / 5 : ℝ) * ‖z + 2‖ ^ 2) := by
  simp [normalized, norm_pow,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hQ _)]

theorem normalized_diffContOnCl (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hL : DiffContOnCl ℂ L strip) : DiffContOnCl ℂ (normalized Q L) strip := by
  have hqn : ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)).ne'
  have hd : Differentiable ℂ (fun z : ℂ => ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2) := by
    fun_prop
  refine ⟨hL.differentiableOn.div hd.differentiableOn ?_, hL.continuousOn.div hd.continuous.continuousOn ?_⟩
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z ⟨hz.1.le, hz.2.le⟩))
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z (closure_strip_subset hz)))

theorem normalized_exp_bound (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖normalized Q L z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨A, B, hA, hB, hg⟩ := hgrowth
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  refine ⟨A / Q ^ (3 / 5 : ℝ), B, div_nonneg hA hq.le, hB, ?_⟩
  intro z hz
  have hn := shift_norm_lower z ⟨hz.1.le, hz.2.le⟩
  have hn2 : 1 ≤ ‖z + 2‖ ^ 2 := by nlinarith
  rw [norm_normalized Q hQ]
  calc
    _ ≤ ‖L z‖ / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hq (by nlinarith)
    _ ≤ (A * Real.exp (B * |z.im|)) / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_right (hg z hz) hq.le
    _ = _ := by ring

theorem normalized_boundary_bound (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (z : ℂ) (hz : z ∈ closedStrip)
    (hL : ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2) :
    ‖normalized Q L z‖ ≤ 9 * C := by
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hn : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  have hh := height_le_shift_norm z hz
  have hh2 : (3 + |z.im|) ^ 2 ≤ 9 * ‖z + 2‖ ^ 2 := by
    nlinarith [abs_nonneg z.im, norm_nonneg (z + 2)]
  rw [norm_normalized Q hQ]
  apply (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hn))).mpr
  apply hL.trans
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hC hq.le)
  nlinarith

theorem uniform_strip_bound_of_edges (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hn : ‖normalized Q L z‖ ≤ 9 * C := by
    apply vertical_strip_of_exp_bound _ _ (normalized_diffContOnCl Q hQ L hL)
      (normalized_exp_bound Q hQ L hgrowth) ?_ ?_ z hz
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw], by rw [hw]; norm_num⟩) (hleft w hw)
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw]; norm_num, by rw [hw]⟩) (hright w hw)
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hnz : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  rw [norm_normalized Q hQ] at hn
  have hb := (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hnz))).mp hn
  have hh := shift_norm_le_height z hz
  have hh2 : ‖z + 2‖ ^ 2 ≤ 4 * (3 + |z.im|) ^ 2 := by
    nlinarith [norm_nonneg (z + 2), abs_nonneg z.im]
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg (by positivity : 0 ≤ 9 * C) hq.le)
  nlinarith

theorem uniform_strip_bound (Q C : ℝ) (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  apply uniform_strip_bound_of_edges Q C (lt_of_lt_of_le zero_lt_one hQ) hC L hL
    hgrowth hleft ?_ z hz
  intro w hw
  apply (hright w hw).trans
  have hq : 1 ≤ Q ^ (3 / 5 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hh : 1 ≤ (3 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im]
  calc
    C ≤ C * Q ^ (3 / 5 : ℝ) := le_mul_of_one_le_right hC hq
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC (le_trans zero_le_one hq)) hh

theorem uniform_strip_bound_of_functional_equation
    (Q D : ℝ) (hQ : 1 ≤ Q) (hD : 0 ≤ D) (L Ldual : ℂ → ℂ)
    (ε : ℂ) (hε : ‖ε‖ = 1) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ D)
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * ((1 + leftConstant) * D) * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hQ0 := lt_of_lt_of_le zero_lt_one hQ
  have hc := leftConstant_pos
  apply uniform_strip_bound Q ((1 + leftConstant) * D) hQ (by positivity) L hL hgrowth ?_ ?_ z hz
  · intro w hw
    apply (left_boundary_of_functional_equation Q D hQ0 hD L Ldual ε hε hfe hdual w hw).trans
    have hbase : leftConstant * D ≤ (1 + leftConstant) * D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hQ0.le _)) (sq_nonneg _)
  · intro w hw
    apply (hright w hw).trans
    nlinarith

theorem uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (F : ℂ → ℂ)
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedStrip, ‖F z‖ ≤ C) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * F z‖ ≤
        A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨G, hG, hg⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (-(1 / 10)) (11 / 10)
  let S : ℝ := a ^ (-(11 / 10) : ℝ) + a ^ (1 / 10 : ℝ)
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  refine ⟨S * G * C, Real.pi, by positivity, Real.pi_pos.le, ?_⟩
  intro z hz
  have hzc : z ∈ closedStrip := ⟨hz.1.le, hz.2.le⟩
  have haBound : ‖(a : ℂ) ^ (-z)‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    exact VerticalContourShift.rpow_between_endpoints a (-(11 / 10)) (1 / 10) (-z.re)
      ha (by linarith [hz.2]) (by linarith [hz.1])
  rw [norm_mul, norm_mul]
  have hgamma := hg z hzc
  have hprod := mul_le_mul (mul_le_mul haBound hgamma (norm_nonneg _) hS)
    (hF z hzc) (norm_nonneg _) (mul_nonneg hS (mul_nonneg hG.le (Real.exp_nonneg _)))
  nlinarith

theorem mellin_uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ)
    (hleft : MellinConvergent f (-(1 / 10) : ℂ))
    (hright : MellinConvergent f (11 / 10 : ℂ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * mellin f z‖ ≤
        A * Real.exp (B * |z.im|) := by
  apply uncompleted_exp_bound a ha (mellin f)
  obtain ⟨C, hC, hb⟩ := VerticalContourShift.mellin_uniform_strip_bound f
    (-(1 / 10)) (11 / 10) (by simpa using hleft) (by simpa using hright)
  exact ⟨C, hC, fun z hz => hb z hz.1 hz.2⟩

end SevenEighths.HeckeStrip
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.StripActual
namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set MeasureTheory
namespace SevenEighths.HeckeStripActual
open HeckeFamily HeckePrimitive

variable (c : O) [NeZero c]

theorem conductor_ge_one : 1 ≤ conductor c := by
  unfold conductor
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {c}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact NeZero.ne c)

theorem completionScale_eq_inv :
    HeckeStrip.completionScale (conductor c) = (Real.pi * scale c)⁻¹ := by
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding c‖ := by
    have h := ThetaRegularity.lattice_gap c (NeZero.ne c)
    nlinarith [norm_nonneg (ConcreteTraceCRT.eisEmbedding c)]
  unfold HeckeStrip.completionScale conductor scale GaussianTheta.parameter
  rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (norm_nonneg _)]
  field_simp

theorem completionScale_cpow (s : ℂ) :
    (HeckeStrip.completionScale (conductor c) : ℂ)^s =
      (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) := by
  rw [completionScale_eq_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (mul_nonneg Real.pi_pos.le (scale_pos c).le),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (scale_pos c).le,
    mul_inv_rev]
  simp only [Complex.cpow_neg]

theorem completedL_eq_standard (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^s * Complex.Gamma s *
        LFunction (character c χ hu) s := by
  rw [completedL_eq_gamma_mul_LFunction c χ hu hp h0 h1 hΓ, completionScale_cpow]

theorem LFunction_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖LFunction η s‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series η hs1, IdealEuler.series]
  have hsum := IdealEuler.weighted_summable_norm (idealCoeff η) (idealCoeff_norm_le_one η) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖idealCoeff η I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I)).trans
    (HeckeReciprocalBound.normWeight_le_of_re_ge hs I)

theorem pair_strong (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    IsStrongFEPair (pair c χ hu hp) := by
  constructor
  · exact HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal (character c χ hu) hχ
  · apply HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal
      (character c χ⁻¹ (inverse_unit_trivial c χ hu))
    change χ⁻¹ ≠ 1
    simpa only [ne_eq, inv_eq_one] using hχ

theorem LFunction_eq_uncompleted (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) (s : ℂ) :
    LFunction (character c χ hu) s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-s) * (Complex.Gamma s)⁻¹ *
        completedL c χ hu hp s := by
  let a := HeckeStrip.completionScale (conductor c)
  have ha : 0 < a := HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))
  have hL := LFunction_entire_nonprincipal (character c χ hu) hχ
  have hΛ : Differentiable ℂ (completedL c χ hu hp) :=
    (pair_strong c χ hu hp hχ).differentiable_Λ.div_const 6
  have hR : Differentiable ℂ (fun z : ℂ => (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      completedL c χ hu hp z) :=
    (((differentiable_id.neg).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      Complex.differentiable_one_div_Gamma).mul hΛ
  have he : LFunction (character c χ hu) = fun z : ℂ => (a : ℂ)^(-z) *
      (Complex.Gamma z)⁻¹ * completedL c χ hu hp z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hL).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hR) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz
    have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    rw [completedL_eq_standard c χ hu hp h0 h1 hΓ]
    have haz : (a : ℂ)^z ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha.ne'])
    change LFunction (character c χ hu) z = (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      ((a : ℂ)^z * Complex.Gamma z * LFunction (character c χ hu) z)
    rw [Complex.cpow_neg]
    field_simp
  exact congr_fun he s

theorem functional_equation_left (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : s.re = -(1/10)) :
    LFunction (character c χ hu) s = TraceCharacter.normalizedGauss c χ *
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) *
      (Complex.Gamma (1-s) / Complex.Gamma s) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hs0 : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs1 : 1-s ≠ 1 := by intro h; apply h0; linear_combination -h
  have hΓdual : Complex.Gamma (1-s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
  have hΓ : Complex.Gamma s ≠ 0 := by
    have h := Complex.Gamma_ne_zero_of_re_pos (s := s+1) (by simp [hs]; norm_num)
    rw [Complex.Gamma_add_one s h0] at h
    exact (mul_ne_zero_iff.mp h).2
  have he := completedL_functional_equation c χ hu hp hs0 hs1
  rw [sub_sub_cancel] at he
  rw [completedL_eq_standard c χ hu hp h0 h1 hΓ,
    completedL_eq_standard c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv hs0 hs1 hΓdual] at he
  let a := HeckeStrip.completionScale (conductor c)
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))).ne'
  have haz : (a : ℂ)^s ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha])
  have hpow : (a : ℂ)^(1-s) = (a : ℂ)^s * (a : ℂ)^(1-2*s) := by
    rw [← Complex.cpow_add _ _ ha]
    congr 1
    ring
  apply mul_left_cancel₀ (mul_ne_zero haz hΓ)
  calc
    _ = TraceCharacter.normalizedGauss c χ * ((a : ℂ)^(1-s) * Complex.Gamma (1-s) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)) := he
    _ = _ := by
      change _ = ((a : ℂ)^s * Complex.Gamma s) *
        (TraceCharacter.normalizedGauss c χ * (a : ℂ)^(1-2*s) *
          (Complex.Gamma (1-s)/Complex.Gamma s) * _)
      rw [hpow]
      field_simp

theorem LFunction_exp_growth (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖LFunction (character c χ hu) z‖ ≤ A * Real.exp (B * |z.im|) := by
  let f : ℝ → ℂ := fun t => (pair c χ hu hp).f t / 6
  have hP := pair_strong c χ hu hp hχ
  have hconv (s : ℂ) : MellinConvergent f s := (hP.hasMellin s).1.div_const 6
  have h := HeckeStrip.mellin_uncompleted_exp_bound
    (HeckeStrip.completionScale (conductor c))
    (HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))) f
    (hconv _) (hconv _)
  have heq (z : ℂ) :
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-z) * (Complex.Gamma z)⁻¹ * mellin f z =
        LFunction (character c χ hu) z := by
    rw [LFunction_eq_uncompleted c χ hu hp hχ]
    congr 1
    change mellin (fun t => (pair c χ hu hp).f t / 6) z = (pair c χ hu hp).Λ z / 6
    rw [mellin_div_const, (hP.hasMellin z).2]
  simpa only [heq] using h

theorem uniform_strip_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖LFunction (character c χ hu) z‖ ≤
      36 * ((1 + HeckeStrip.leftConstant) * HeckeReciprocalBound.bound (11/10)) *
        conductor c ^ (3/5 : ℝ) * (3 + |z.im|)^2 := by
  apply HeckeStrip.uniform_strip_bound_of_functional_equation
    (conductor c) (HeckeReciprocalBound.bound (11/10)) (conductor_ge_one c)
    (tsum_nonneg (fun _ => norm_nonneg _))
    (LFunction (character c χ hu))
    (LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (TraceCharacter.normalizedGauss c χ) (TraceCharacter.normalizedGauss_norm c χ hp)
    (LFunction_entire_nonprincipal (character c χ hu) hχ).diffContOnCl
    (LFunction_exp_growth c χ hu hp hχ) (fun _ hs => functional_equation_left c χ hu hp hs)
    _ _ z hz
  · intro s hs
    exact LFunction_norm_le _ (by norm_num : (1 : ℝ) < 11/10) hs.ge
  · intro s hs
    exact LFunction_norm_le _ (by norm_num : (1 : ℝ) < 11/10) hs.ge

end SevenEighths.HeckeStripActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Presentation
namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckePresentation
open HeckeFamily

theorem principalResidue_primitive (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) :
    FiniteFourier.IsPrimitiveOnIdeals (principalResidue η) :=
  CharacterTransport.primitive_pullback (quotientEquiv η) η.residue hp

private theorem pullback_one {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    CharacterTransport.pullback e (1 : MulChar S ℂ) = 1 := by
  apply MulChar.ext'
  intro x
  rw [CharacterTransport.pullback_apply]
  by_cases hx : IsUnit x
  · have hxe : IsUnit (e x) := hx.map e.toMonoidHom
    rw [MulChar.one_apply hxe, MulChar.one_apply hx]
  · have he : ¬ IsUnit (e x) := by
      intro h
      apply hx
      simpa using h.map e.symm.toMonoidHom
    rw [MulChar.map_nonunit _ he, MulChar.map_nonunit _ hx]

theorem principalResidue_ne_one (η : Character) (hη : η.residue ≠ 1) :
    principalResidue η ≠ 1 := by
  intro h
  have he := congrArg (CharacterTransport.pullback (quotientEquiv η).symm) h
  rw [principalResidue, CharacterTransport.pullback_symm, pullback_one] at he
  exact hη he

theorem LFunction_principalCharacter (η : Character) (hη : η.residue ≠ 1) (s : ℂ) :
    LFunction (principalCharacter η) s = LFunction η s := by
  have hp : (principalCharacter η).residue ≠ 1 := principalResidue_ne_one η hη
  have ha := LFunction_entire_nonprincipal (principalCharacter η) hp
  have hb := LFunction_entire_nonprincipal η hη
  have he : LFunction (principalCharacter η) = LFunction η := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    unfold LFunction
    congr 1
    apply continuedLattice_eq_of_elementCoeff_eq _ _ (principalCharacter_elementCoeff η)
      (by linarith) (by intro h; norm_num [h] at hz)
  exact congr_fun he s

theorem uniform_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (hη : η.residue ≠ 1)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖LFunction η z‖ ≤
      36 * ((1 + HeckeStrip.leftConstant) * HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3 + |z.im|)^2 := by
  have h := HeckeStripActual.uniform_strip_bound (generator η) (principalResidue η)
    (principalResidue_unit η) (principalResidue_primitive η hp) (principalResidue_ne_one η hη) z hz
  change ‖LFunction (principalCharacter η) z‖ ≤ _ at h
  rw [LFunction_principalCharacter η hη z] at h
  simpa only [HeckeStripActual.conductor, span_generator] using h

end SevenEighths.HeckePresentation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrincipalStrip
namespace OAI

noncomputable section
open scoped Classical Topology
open Set MeasureTheory
namespace SevenEighths.HeckePrincipalStrip
open HeckeFamily HeckeTheta

theorem normalized_diffContOnCl (η : Character) :
    DiffContOnCl ℂ (normalized η) HeckeStrip.strip := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  exact ((HeckeOrigin.poleRemoved_entire η z).div (differentiableAt_id.add_const 2)
    (HeckeStrip.shift_ne_zero z (HeckeStrip.closure_strip_subset hz))).differentiableWithinAt

theorem norm_sub_one_le_shift (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z-1‖ ≤ ‖z+2‖ := by
  have h : ‖z+2‖^2 - ‖z-1‖^2 = 6*z.re+3 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  nlinarith [hz.1, norm_nonneg (z-1), norm_nonneg (z+2)]

theorem normalized_norm_le (η : Character) {z : ℂ} (hz : z ∈ HeckeStrip.closedStrip)
    (h0 : z ≠ 0) (h1 : z ≠ 1) : ‖normalized η z‖ ≤ ‖LFunction η z‖ := by
  unfold normalized
  rw [HeckeOrigin.poleRemoved_eq η h0 h1, norm_div, norm_mul]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (HeckeStrip.shift_norm_lower z hz))).mpr
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (norm_sub_one_le_shift z hz)
    (norm_nonneg (LFunction η z))

private theorem norm_z_le_height (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z‖ ≤ 3 + |z.im| := by
  apply (Complex.norm_le_abs_re_add_abs_im z).trans
  have hr : |z.re| ≤ 3 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  linarith

private theorem norm_sub_one_le_height (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z-1‖ ≤ 3 + |z.im| := by
  apply (Complex.norm_le_abs_re_add_abs_im (z-1)).trans
  have hr : |z.re-1| ≤ 3 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  linarith

theorem regularized_completion_bound (η : Character) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ HeckeStrip.closedStrip,
      ‖HeckeMellinIdentity.regularized (pair (coefficients η)) z‖ ≤ C * (3+|z.im|)^2 := by
  let P := pair (coefficients η)
  have hstrong := P.isStrongFEPair_toStrongFEPair
  obtain ⟨C, hC, hbound⟩ := VerticalContourShift.mellin_uniform_strip_bound P.f_modif
    (-(1/10)) (11/10) (hstrong.hasMellin _).1 (hstrong.hasMellin _).1
  let D := C + ‖P.f₀‖ + ‖P.ε‖ * ‖P.g₀‖
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro z hz
  have hΛ : ‖P.Λ₀ z‖ ≤ C := hbound z hz.1 hz.2
  have hT : 1 ≤ 3+|z.im| := by linarith [abs_nonneg z.im]
  have hz0 := norm_z_le_height z hz
  have hz1 := norm_sub_one_le_height z hz
  unfold HeckeMellinIdentity.regularized
  change ‖z*(z-1)*P.Λ₀ z - (z-1)*P.f₀ + z*P.ε*P.g₀‖ ≤ _
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (le_refl ‖z*P.ε*P.g₀‖)).trans
  simp only [norm_mul]
  calc
    _ ≤ ((3+|z.im|)*(3+|z.im|))*C + (3+|z.im|)*‖P.f₀‖ +
        (3+|z.im|)*‖P.ε‖*‖P.g₀‖ := by gcongr
    _ ≤ D*(3+|z.im|)^2 := by
      dsimp [D]
      have hf := norm_nonneg P.f₀
      have hg := mul_nonneg (norm_nonneg P.ε) (norm_nonneg P.g₀)
      have hsq : 3+|z.im| ≤ (3+|z.im|)^2 := by nlinarith
      nlinarith

theorem normalized_exp_growth (η : Character) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖normalized η z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hCbound⟩ := regularized_completion_bound η
  obtain ⟨G, hG, hGbound⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (9/10) (21/10)
  let S : ℝ := Real.pi ^ (-(1/10) : ℝ) + Real.pi ^ (11/10 : ℝ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨9*S*G*C, Real.pi+2, by positivity, by positivity, ?_⟩
  intro z hz
  have hzc : z ∈ HeckeStrip.closedStrip := ⟨hz.1.le, hz.2.le⟩
  have hp : ‖(Real.pi : ℂ)^z‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact VerticalContourShift.rpow_between_endpoints Real.pi (-(1/10)) (11/10) z.re
      Real.pi_pos hzc.1 hzc.2
  have hg : ‖(Complex.Gamma (z+1))⁻¹‖ ≤ G*Real.exp (Real.pi*|z.im|) := by
    simpa using hGbound (z+1) (by constructor <;> simp only [Complex.add_re, Complex.one_re] <;>
      linarith [hzc.1, hzc.2])
  have ht : (3+|z.im|)^2 ≤ 9*Real.exp (2*|z.im|) := by
    have he := Real.add_one_le_exp |z.im|
    have ht0 := abs_nonneg z.im
    have hle : 3+|z.im| ≤ 3*Real.exp |z.im| := by linarith
    have hs := sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|) (by positivity : 0 ≤ 3*Real.exp |z.im|)
    have hsq := hs.mpr hle
    rw [mul_pow, ← Real.exp_nat_mul] at hsq
    norm_num at hsq ⊢
    exact hsq
  unfold normalized HeckeOrigin.poleRemoved
  simp only [norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ ‖(Real.pi : ℂ)^z‖ * ‖(Complex.Gamma (z+1))⁻¹‖ *
        ‖HeckeMellinIdentity.regularized (pair (coefficients η)) z‖ := by
      apply (div_le_self (by positivity) (HeckeStrip.shift_norm_lower z hzc)).trans
      exact div_le_self (by positivity) (by norm_num)
    _ ≤ S * (G*Real.exp (Real.pi*|z.im|)) * (C*(3+|z.im|)^2) := by
      gcongr
      exact hCbound z hzc
    _ ≤ S * (G*Real.exp (Real.pi*|z.im|)) * (C*(9*Real.exp (2*|z.im|))) := by gcongr
    _ = _ := by
      rw [show (Real.pi+2)*|z.im| = Real.pi*|z.im| + 2*|z.im| by ring, Real.exp_add]
      ring

theorem primitive_normalized_bound (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖normalized (HeckePrimitive.character c χ hu) z‖ ≤
      36 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        HeckeStripActual.conductor c ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  let η := HeckePrimitive.character c χ hu
  let D := HeckeReciprocalBound.bound (11/10)
  have hD : 0 ≤ D := tsum_nonneg (fun _ => norm_nonneg _)
  have hc := HeckeStrip.leftConstant_pos
  have hQ := HeckeStripActual.conductor_ge_one c
  apply HeckeStrip.uniform_strip_bound (HeckeStripActual.conductor c)
    ((1+HeckeStrip.leftConstant)*D) hQ (by positivity) (normalized η)
    (normalized_diffContOnCl η) (normalized_exp_growth η) ?_ ?_ z hz
  · intro w hw
    have hwc : w ∈ HeckeStrip.closedStrip := ⟨by rw [hw], by rw [hw]; norm_num⟩
    apply (normalized_norm_le η hwc (by intro h; simp [h] at hw)
      (by intro h; norm_num [h] at hw)).trans
    have hb := HeckeStrip.left_boundary_of_functional_equation
      (HeckeStripActual.conductor c) D (lt_of_lt_of_le zero_lt_one hQ) hD
      (LFunction η) (LFunction (HeckePrimitive.character c χ⁻¹
        (HeckePrimitive.inverse_unit_trivial c χ hu))) (TraceCharacter.normalizedGauss c χ)
      (TraceCharacter.normalizedGauss_norm c χ hp)
      (fun _ hs => HeckeStripActual.functional_equation_left c χ hu hp hs)
      (fun _ hs => HeckeStripActual.LFunction_norm_le _ (by norm_num : (1 : ℝ)<11/10) hs.ge) w hw
    apply hb.trans
    have hbase : HeckeStrip.leftConstant*D ≤ (1+HeckeStrip.leftConstant)*D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _)
  · intro w hw
    have hwc : w ∈ HeckeStrip.closedStrip := ⟨by rw [hw]; norm_num, by rw [hw]⟩
    apply (normalized_norm_le η hwc (by intro h; norm_num [h] at hw)
      (by intro h; norm_num [h] at hw)).trans
    apply (HeckeStripActual.LFunction_norm_le η (by norm_num : (1 : ℝ)<11/10) hw.ge).trans
    change D ≤ (1+HeckeStrip.leftConstant)*D
    nlinarith

theorem poleRemoved_principalCharacter (η : Character) (s : ℂ) :
    HeckeOrigin.poleRemoved (HeckePresentation.principalCharacter η) s =
      HeckeOrigin.poleRemoved η s := by
  have he : HeckeOrigin.poleRemoved (HeckePresentation.principalCharacter η) =
      HeckeOrigin.poleRemoved η := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeOrigin.poleRemoved_entire _)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeOrigin.poleRemoved_entire _)) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1, HeckeOrigin.poleRemoved_eq _ h0 h1]
    congr 1
    unfold LFunction
    congr 1
    exact continuedLattice_eq_of_elementCoeff_eq _ _
      (HeckePresentation.principalCharacter_elementCoeff η) (by linarith) h1
  exact congr_fun he s

theorem uniform_normalized_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖normalized η z‖ ≤
      36 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  have h := primitive_normalized_bound (HeckePresentation.generator η)
    (HeckePresentation.principalResidue η) (HeckePresentation.principalResidue_unit η)
    (HeckePresentation.principalResidue_primitive η hp) z hz
  change ‖normalized (HeckePresentation.principalCharacter η) z‖ ≤ _ at h
  unfold normalized at h ⊢
  rw [poleRemoved_principalCharacter] at h
  simpa only [HeckeStripActual.conductor, HeckePresentation.span_generator] using h

theorem sourceNormalized_norm_le (η : Character) (z : ℂ)
    (hz : z ∈ HeckeStrip.closedStrip) :
    ‖sourceNormalized η z‖ ≤ 3 * ‖normalized η z‖ := by
  have hlow : (9/10 : ℝ) ≤ ‖z+1‖ := by
    have hre := Complex.re_le_norm (z+1)
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith [hz.1]
  have hn1 : z+1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn2 : z+2 ≠ 0 := HeckeStrip.shift_ne_zero z hz
  have hratio : ‖z+2‖ ≤ 3*‖z+1‖ := by
    have ht := norm_add_le (z+1) (1 : ℂ)
    rw [norm_one, show z+1+1=z+2 by ring] at ht
    linarith
  have heq : sourceNormalized η z = normalized η z * ((z+2)/(z+1)) := by
    unfold sourceNormalized normalized
    field_simp
  rw [heq, norm_mul, norm_div]
  have hd : ‖z+2‖ / ‖z+1‖ ≤ 3 := (div_le_iff₀ (norm_pos_iff.mpr hn1)).mpr hratio
  nlinarith [norm_nonneg (normalized η z)]

theorem uniform_source_normalized_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖sourceNormalized η z‖ ≤
      108 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  apply (sourceNormalized_norm_le η z hz).trans
  have h := mul_le_mul_of_nonneg_left (uniform_normalized_strip_bound η hp z hz) (by norm_num : (0 : ℝ) ≤ 3)
  convert (preTransparency := .instances) h using 1 ; ring

end SevenEighths.HeckePrincipalStrip

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
namespace OAI

noncomputable section
open scoped Classical Topology
open Set
namespace SevenEighths.HeckeLogarithmicInput
open HeckeFamily

theorem regular_eq_nonprincipal (η : Character) (hη : η.residue ≠ 1) :
    regular η = LFunction η := by funext s; simp [regular, hη]

theorem regular_differentiableAt (η : Character) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regular η) s := by
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · have he : regular η = HeckePrincipalStrip.sourceNormalized η := by
      funext z; simp [regular, hη]
    rw [he]
    exact (HeckeOrigin.poleRemoved_entire η s).div (differentiableAt_id.add_const 1) hplus
  · rw [regular_eq_nonprincipal η hη]
    exact LFunction_entire_nonprincipal η hη s

theorem principal_regular_factor_bound {s : ℂ} (hs : 0 ≤ s.re) :
    ‖s-1‖ ≤ ‖s+1‖ := by
  have he : ‖s+1‖^2 - ‖s-1‖^2 = 4*s.re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  nlinarith [norm_nonneg (s-1), norm_nonneg (s+1)]

theorem regular_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖regular η s‖ ≤ HeckeReciprocalBound.bound σ := by
  by_cases hη : η.residue = 1
  · have h0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
    have h1 : s ≠ 1 := by intro h; simp [h] at hs; linarith
    have hp : 0 < ‖s+1‖ := by
      have hr := Complex.re_le_norm (s+1)
      simp only [Complex.add_re, Complex.one_re] at hr
      linarith
    simp only [regular, if_pos hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, norm_div, norm_mul]
    apply le_trans _ (HeckeStripActual.LFunction_norm_le η hσ hs)
    apply (div_le_iff₀ hp).mpr
    nlinarith [principal_regular_factor_bound (s := s) (by linarith), norm_nonneg (LFunction η s)]
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeStripActual.LFunction_norm_le η hσ hs

theorem uniformConstant_nonneg : 0 ≤ uniformConstant := by
  have hc := HeckeStrip.leftConstant_pos
  have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
  unfold uniformConstant
  positivity

theorem modulus_norm_ge_one (η : Character) : 1 ≤ (η.modulus.absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

theorem regular_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (z : ℂ)
    (hz : z ∈ HeckeStrip.closedStrip) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hη : η.residue = 1
  · simpa only [regular, if_pos hη, uniformConstant] using
      HeckePrincipalStrip.uniform_source_normalized_strip_bound η hp z hz
  · rw [regular_eq_nonprincipal η hη]
    apply (HeckePresentation.uniform_strip_bound η hp hη z hz).trans
    have hc := HeckeStrip.leftConstant_pos
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    unfold uniformConstant
    gcongr ; norm_num

theorem regular_right_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) {z : ℂ}
    (hz : -(1/10 : ℝ) ≤ z.re) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hright : z.re ≤ 11/10
  · exact regular_strip_bound η hp z ⟨hz, hright⟩
  · apply (regular_norm_le η (by norm_num : (1 : ℝ)<11/10) (le_of_not_ge hright)).trans
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    have hc := HeckeStrip.leftConstant_pos
    have hC : HeckeReciprocalBound.bound (11/10) ≤ uniformConstant := by
      unfold uniformConstant; nlinarith
    have hQ : 1 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
      Real.one_le_rpow (modulus_norm_ge_one η) (by norm_num)
    have hT : 1 ≤ (3+|z.im|)^2 := by nlinarith [abs_nonneg z.im]
    exact hC.trans ((le_mul_of_one_le_right uniformConstant_nonneg hQ).trans
      (le_mul_of_one_le_right (mul_nonneg uniformConstant_nonneg (by linarith : 0 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ))) hT))

theorem regular_disk_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (a e t : ℝ)
    (ha : (1/2 : ℝ) ≤ a) (he : 0 ≤ e) {z : ℂ}
    (hz : z ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    ‖regular η z‖ ≤ (4*uniformConstant) * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|t|)^2 := by
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (z-((2 : ℂ)+t*Complex.I))
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.sub_im, Complex.add_im, Complex.mul_im] at hr hi
  have hzre : -(1/10 : ℝ) ≤ z.re := by
    have hh := neg_abs_le (z.re-2)
    linarith
  have hheight : 3+|z.im| ≤ 2*(3+|t|) := by
    have hab := abs_add_le (z.im-t) t
    rw [sub_add_cancel] at hab
    linarith [abs_nonneg t]
  apply (regular_right_growth η hp hzre).trans
  have hsq : (3+|z.im|)^2 ≤ 4*(3+|t|)^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|)
      (by positivity : 0 ≤ 2*(3+|t|))).mpr hheight
    nlinarith
  calc
    _ ≤ uniformConstant*(η.modulus.absNorm : ℝ)^(3/5 : ℝ)*(4*(3+|t|)^2) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg uniformConstant_nonneg (Real.rpow_nonneg (by positivity) _))
    _ = _ := by ring

end SevenEighths.HeckeLogarithmicInput

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.LogarithmicControl
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex

namespace SevenEighths.LogarithmicControl

theorem differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U)
    {L g : ℂ → ℂ} (hL : DifferentiableOn ℂ L U)
    (hg : ContinuousOn g U) (he : EqOn (Complex.exp ∘ g) L U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hLc : DifferentiableAt ℂ L z := (hL z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z)
    (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (L z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (L w)) =ᶠ[𝓝 z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hLc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

theorem exists_holomorphic_log {L : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) := by
  let : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨g, hg, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc
    isOpen_ball hL.continuousOn (by
      rintro ⟨z, hz, heq⟩
      exact h0 z hz heq)
  exact ⟨g, differentiableOn_of_exp_eq isOpen_ball hL hg he, he⟩

theorem exists_holomorphic_log_normalized {L : ℂ → ℂ} {c m : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) (hm : Complex.exp m = L c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) ∧ g c = m := by
  obtain ⟨g, hg, he⟩ := exists_holomorphic_log hR hL h0
  refine ⟨fun z ↦ g z + (m - g c), hg.add_const _, ?_, by simp⟩
  intro z hz
  change Complex.exp (g z + (m - g c)) = L z
  have hez : Complex.exp (g z) = L z := he hz
  have hec : Complex.exp (g c) = L c := he (mem_ball_self hR)
  rw [Complex.exp_add, Complex.exp_sub, hm, hez,
    hec, div_self (h0 c (mem_ball_self hR)), mul_one]

theorem log_eqOn_of_eq_center {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hh : DifferentiableOn ℂ h (ball c r))
    (he : EqOn (Complex.exp ∘ g) (Complex.exp ∘ h) (ball c r)) (hc : g c = h c) :
    EqOn g h (ball c r) := by
  have hcm : c ∈ ball c r := mem_ball_self hr
  have hgc := (hg.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hhc := (hh.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hs := Complex.hasStrictDerivAt_exp (g c)
  have hleft := hs.eventually_left_inverse (Complex.exp_ne_zero _)
  have hgleft := hgc.eventually hleft
  have hhc' : Tendsto h (𝓝 c) (𝓝 (g c)) := by
    rw [hc]
    exact hhc.tendsto
  have hhleft := hhc'.eventually hleft
  have heq : g =ᶠ[𝓝 c] h := by
    filter_upwards [hgleft, hhleft, isOpen_ball.mem_nhds hcm] with z hz1 hz2 hz
    rw [← hz1, ← hz2]
    exact congrArg _ (he hz)
  exact (hg.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hh.analyticOnNhd isOpen_ball) (convex_ball c r).isPreconnected hcm heq

theorem borel_caratheodory_closedBall {g : ℂ → ℂ} {c : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M) (hA : 0 ≤ A)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hRe : ∀ z ∈ ball c R, (g z).re ≤ M) (hc : ‖g c‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * M * r / (R - r) + A * (R + r) / (R - r) := by
  have hzn : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hzR : ‖z - c‖ < R := hzn.trans_lt hrR
  have hRp : 0 < R := hr.trans_lt hrR
  have hg' : DifferentiableOn ℂ (fun w ↦ g (c + w)) (ball 0 R) := by
    apply hg.comp ((differentiable_const c).add differentiable_id).differentiableOn
    intro w hw
    simpa [mem_ball, dist_eq_norm] using hw
  have hb := Complex.borelCaratheodory hM hg' (fun w hw ↦ hRe _ (by
    simpa [mem_ball, dist_eq_norm] using hw)) (hr.trans_lt hrR)
    (show z - c ∈ ball 0 R by simpa using hzR)
  simp only [add_sub_cancel, add_zero] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
  · gcongr

theorem three_circles {g : ℂ → ℂ} {c z : ℂ} {r R S A B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRS : R < S)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B)
    (hzr : r ≤ ‖z - c‖) (hzR : ‖z - c‖ ≤ R) :
    ‖g z‖ ≤ A ^ (1 - (Real.log ‖z - c‖ - Real.log r) /
      (Real.log R - Real.log r)) *
      B ^ ((Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) := by
  let F : ℂ → ℂ := fun w ↦ g (c + Complex.exp w)
  have hRp : 0 < R := hr.trans hrR
  have hlog : Real.log r < Real.log R := Real.log_lt_log hr hrR
  have hmap (w : ℂ) (hw : w.re ≤ Real.log R) : c + Complex.exp w ∈ closedBall c R := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw).trans_eq (Real.exp_log hRp)
  have hclosed : closure (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) ⊆
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    apply closure_minimal
    · intro w hw
      exact ⟨hw.1.le, hw.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hd : DiffContOnCl ℂ F
      (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    have hm := hmap w (hclosed hw).2
    have hm' : c + Complex.exp w ∈ ball c S :=
      closedBall_subset_ball hRS hm
    exact ((hg _ hm').differentiableAt (isOpen_ball.mem_nhds hm')).comp w
      ((differentiableAt_const c).add (Complex.differentiable_exp w)) |>.differentiableWithinAt
  have hbound : BddAbove ((norm ∘ F) ''
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hb _ (hmap w hw.2)
  have hzn : 0 < ‖z - c‖ := hr.trans_le hzr
  have hz0 : z - c ≠ 0 := norm_pos_iff.mp hzn
  have hw : Complex.log (z - c) ∈
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    change Real.log r ≤ (Complex.log (z - c)).re ∧
      (Complex.log (z - c)).re ≤ Real.log R
    simp only [Complex.log_re]
    exact ⟨Real.log_le_log hr hzr, Real.log_le_log hzn hzR⟩
  have h := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlog hw hd hbound (a := A) (b := B) ?_ ?_
  · simpa [F, Complex.exp_log hz0, Complex.log_re] using h
  · intro w hw
    apply ha
    simp only [mem_preimage, mem_singleton_iff] at hw
    simp [mem_closedBall, dist_eq_norm, hw, Complex.norm_exp, Real.exp_log hr]
  · intro w hw
    exact hb _ (hmap w (le_of_eq hw))

theorem three_circles_power_bound {g : ℂ → ℂ} {c z : ℂ} {r ρ R S A B T : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (hRS : R < S)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B * T)
    (hz : z ∈ closedBall c ρ) :
    ‖g z‖ ≤ A * B * T ^ ((Real.log ρ - Real.log r) /
      (Real.log R - Real.log r)) := by
  let θ := (Real.log ρ - Real.log r) / (Real.log R - Real.log r)
  have hlogR : 0 < Real.log R - Real.log r :=
    sub_pos.mpr (Real.log_lt_log hr (hrρ.trans hρR))
  have hθ0 : 0 ≤ θ := div_nonneg
    (sub_nonneg.mpr (Real.log_le_log hr hrρ.le)) hlogR.le
  have hθ1 : θ ≤ 1 := (div_le_one hlogR).mpr (by
    linarith [Real.log_le_log (hr.trans hrρ) hρR.le])
  have hzn : ‖z - c‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hBp : 0 ≤ B := zero_le_one.trans hB
  have hTp : 0 ≤ T := zero_le_one.trans hT
  have hp1 : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ0
  by_cases hzr : ‖z - c‖ ≤ r
  · have hgz := ha z (by simpa [mem_closedBall, dist_eq_norm] using hzr)
    exact hgz.trans (by nlinarith [mul_le_mul hB hp1 zero_le_one hBp])
  · have hzr' : r ≤ ‖z - c‖ := (lt_of_not_ge hzr).le
    have hzx : 0 < ‖z - c‖ := hr.trans_le hzr'
    let x := (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)
    have hx0 : 0 ≤ x := div_nonneg
      (sub_nonneg.mpr (Real.log_le_log hr hzr')) hlogR.le
    have hxθ : x ≤ θ := (div_le_div_iff_of_pos_right hlogR).mpr (by
      linarith [Real.log_le_log hzx hzn])
    have hx1 : x ≤ 1 := hxθ.trans hθ1
    have h := three_circles hr (hrρ.trans hρR) hRS hg ha hb hzr' (hzn.trans hρR.le)
    have hAa : A ^ (1 - x) ≤ A := by
      simpa using Real.rpow_le_rpow_of_exponent_le hA (show 1 - x ≤ 1 by linarith)
    have hBb : B ^ x ≤ B := by
      simpa using Real.rpow_le_rpow_of_exponent_le hB hx1
    have hTT : T ^ x ≤ T ^ θ := Real.rpow_le_rpow_of_exponent_le hT hxθ
    calc
      ‖g z‖ ≤ A ^ (1 - x) * (B * T) ^ x := h
      _ = A ^ (1 - x) * (B ^ x * T ^ x) := by rw [Real.mul_rpow hBp hTp]
      _ ≤ A * (B * T ^ θ) := mul_le_mul hAa
        (mul_le_mul hBb hTT (Real.rpow_nonneg hTp _) hBp)
        (by positivity) hAp
      _ = A * B * T ^ θ := by ring

theorem uniformTheta_mem {e : ℝ} (he : 0 < e) (he' : e < 1 / 1000) :
    0 < uniformTheta e ∧ uniformTheta e < 1 := by
  have hD : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hn : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  have hnD : Real.log (1 + e) < Real.log (200 / 49) :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold uniformTheta
  constructor
  · linarith [(div_lt_one hD).mpr hnD]
  · linarith [div_pos hn hD]

theorem three_circles_exponent_uniform {a e : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) :
    (Real.log (2 - a - 6 * e) - Real.log (49 / 100)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) ≤ uniformTheta e := by
  have hr : (0 : ℝ) < 49 / 100 := by norm_num
  have h6 : (49 / 100 : ℝ) < 2 - a - 6 * e := by linarith
  have h4 : (49 / 100 : ℝ) < 2 - a - 4 * e := by linarith
  have h6p : 0 < 2 - a - 6 * e := hr.trans h6
  have h4p : 0 < 2 - a - 4 * e := hr.trans h4
  have hep : 0 < 1 + e := by linarith
  have hD : 0 < Real.log (2 - a - 4 * e) - Real.log (49 / 100) :=
    sub_pos.mpr (Real.log_lt_log hr h4)
  have hU : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hDU : Real.log (2 - a - 4 * e) - Real.log (49 / 100) ≤
      Real.log (200 / 49) := by
    rw [← Real.log_div h4p.ne' hr.ne']
    apply Real.log_le_log (div_pos h4p hr)
    apply (div_le_iff₀ hr).mpr
    norm_num
    linarith
  have hprod : (2 - a - 6 * e) * (1 + e) ≤ 2 - a - 4 * e := by
    have : 2 - a - 6 * e ≤ 2 := by linarith
    nlinarith
  have hdiff : Real.log (1 + e) ≤ Real.log (2 - a - 4 * e) -
      Real.log (2 - a - 6 * e) := by
    have h := Real.log_le_log (mul_pos h6p hep) hprod
    rw [Real.log_mul h6p.ne' hep.ne'] at h
    linarith
  have hfrac : Real.log (1 + e) / Real.log (200 / 49) ≤
      (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
    gcongr
    exact (Real.log_pos (by linarith : 1 < 1 + e)).le.trans hdiff
  calc
    _ = 1 - (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
        (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
      apply eq_sub_iff_add_eq.mpr
      rw [← add_div]
      convert (preTransparency := .instances) div_self hD.ne' using 1
      ring
    _ ≤ uniformTheta e := sub_le_sub_left hfrac 1

theorem exp_sublinear_le {θ K ε : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      Real.exp (K * x ^ θ) ≤ D * Real.exp (ε * x) := by
  have ht : Tendsto (fun x : ℝ ↦ K * x ^ (-(1 - θ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).const_mul K
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let Y := max 1 X
  refine ⟨Real.exp (K * Y ^ θ), Real.exp_pos _, ?_⟩
  intro x hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hYp : 0 < Y := zero_lt_one.trans_le (le_max_left _ _)
  by_cases hxy : x ≤ Y
  · have h1 : Real.exp (K * x ^ θ) ≤ Real.exp (K * Y ^ θ) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxp.le hxy hθ) hK
    exact h1.trans (le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_exp (by positivity)))
  · have hlarge := hX x ((le_max_right 1 X).trans (lt_of_not_ge hxy).le)
    have heq : K * x ^ θ = (K * x ^ (-(1 - θ))) * x := by
      have hp := Real.rpow_add hxp (-(1 - θ)) 1
      rw [Real.rpow_one] at hp
      rw [mul_assoc, ← hp]
      congr 2
      ring
    have hlin : K * x ^ θ ≤ ε * x := by
      rw [heq]
      exact mul_le_mul_of_nonneg_right hlarge.le hxp.le
    exact (Real.exp_le_exp.mpr hlin).trans (le_mul_of_one_le_left
      (Real.exp_pos _).le (Real.one_le_exp (mul_nonneg hK (Real.rpow_nonneg hYp.le _))))

theorem outerConstant_ge_one {e A M : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) : 1 ≤ outerConstant e A M := by
  unfold outerConstant
  apply (le_div_iff₀ he).mpr
  nlinarith

theorem outer_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 4 * e)) :
    ‖g z‖ ≤ outerConstant e A M * T := by
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hb := borel_caratheodory_closedBall (by linarith : 0 ≤ 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 3 * e) (mul_pos hMp hTp) hAp
    (hg.mono (ball_subset_ball (by linarith))) hRe hc hz
  have hgap : 2 - a - 3 * e - (2 - a - 4 * e) = e := by ring
  rw [hgap] at hb
  have hfirst : 2 * (M * T) * (2 - a - 4 * e) ≤ 4 * M * T := by
    nlinarith [mul_le_mul_of_nonneg_left
      (show 2 - a - 4 * e ≤ 2 by linarith) (show 0 ≤ 2 * M * T by positivity)]
  have hsecond : A * (2 - a - 3 * e + (2 - a - 4 * e)) ≤ 4 * A * T := by
    have h1 := mul_le_mul_of_nonneg_left
      (show 2 - a - 3 * e + (2 - a - 4 * e) ≤ 4 by linarith) hAp
    nlinarith [mul_le_mul_of_nonneg_left hT (show 0 ≤ 4 * A by positivity)]
  refine hb.trans ?_
  rw [← add_div]
  unfold outerConstant
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right he).mpr (by nlinarith)

theorem inner_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hin : ∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c (2 - a - 6 * e)) :
    ‖g z‖ ≤ A * outerConstant e A M * T ^ uniformTheta e := by
  have hB := outerConstant_ge_one he he' hA hM
  have hb : ∀ w ∈ closedBall c (2 - a - 4 * e), ‖g w‖ ≤ outerConstant e A M * T :=
    fun w hw ↦ outer_log_bound ha ha' he he' hA hM hT hg hRe
      (hin c (mem_closedBall_self (by norm_num))) hw
  have h := three_circles_power_bound (by norm_num : (0 : ℝ) < 49 / 100)
    (by linarith : 49 / 100 < 2 - a - 6 * e)
    (by linarith : 2 - a - 6 * e < 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 2 * e)
    hA hB hT hg hin hb hz
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT (three_circles_exponent_uniform ha ha' he he'))
    (by positivity))

theorem logarithm_derivative_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 8 * e)) :
    ‖deriv g z‖ ≤ (outerConstant e A M / (2 * e)) * T := by
  have hzn : dist z c ≤ 2 - a - 8 * e := hz
  have hsub : closedBall z (2 * e) ⊆ ball c (2 - a - 2 * e) := by
    intro w hw
    have hw' : dist w z ≤ 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c < _
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < 2 * e)
    (hg.diffContOnCl_ball hsub) (C := outerConstant e A M * T) ?_
  · exact h.trans_eq (by ring)
  · intro w hw
    apply outer_log_bound ha ha' he he' hA hM hT hg hRe hc
    have hw' : dist w z = 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c ≤ _
    linarith

theorem zero_free_disk_logarithm {L E : ℂ → ℂ} {c : ℂ} {a e A M C : ℝ}
    (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) (hC : 0 < C)
    (hL : DifferentiableOn ℂ L (ball c (2 - a - 2 * e)))
    (h0 : ∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0)
    (hpoly : ∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M)
    (hE : DifferentiableOn ℂ E (ball c (1 / 2)))
    (hEL : EqOn (Complex.exp ∘ E) L (ball c (1 / 2)))
    (hEb : ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c (2 - a - 2 * e)) ∧
      EqOn (Complex.exp ∘ g) L (ball c (2 - a - 2 * e)) ∧
      (∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A) ∧
      (∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * Real.log C) := by
  have hR : (1 / 2 : ℝ) < 2 - a - 2 * e := by linarith
  obtain ⟨g, hg, hge, hgc⟩ := exists_holomorphic_log_normalized
    (by linarith : 0 < 2 - a - 2 * e) hL h0
    (hEL (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
  have hgE : EqOn g E (ball c (1 / 2)) := log_eqOn_of_eq_center (by norm_num)
    (hg.mono (ball_subset_ball hR.le)) hE
    (fun z hz ↦ (hge (ball_subset_ball hR.le hz)).trans (hEL hz).symm) hgc
  refine ⟨g, hg, hge, ?_, ?_⟩
  · intro z hz
    rw [hgE (closedBall_subset_ball (by norm_num : (49 / 100 : ℝ) < 1 / 2) hz)]
    exact hEb z hz
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) := ball_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hp := hpoly z hz
    rw [← hez, Complex.norm_exp, Real.rpow_def_of_pos hC] at hp
    simpa [mul_comm] using Real.exp_le_exp.mp hp

theorem logarithmic_derivative_eq {L g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (he : EqOn (Complex.exp ∘ g) L U)
    {z : ℂ} (hz : z ∈ U) : deriv L z / L z = deriv g z := by
  have hgz := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hd := hgz.hasDerivAt.cexp
  have heq : L =ᶠ[𝓝 z] (fun w ↦ Complex.exp (g w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (he hw).symm
  have hdl := hd.congr_of_eventuallyEq heq
  rw [hdl.deriv]
  have hez : Complex.exp (g z) = L z := he hz
  rw [← hez]
  field_simp

theorem logarithmic_control {e A M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C : ℝ) (L E : ℂ → ℂ) (c : ℂ),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      DifferentiableOn ℂ L (ball c (2 - a - 2 * e)) →
      (∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M) →
      DifferentiableOn ℂ E (ball c (1 / 2)) →
      EqOn (Complex.exp ∘ E) L (ball c (1 / 2)) →
      (∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall c (2 - a - 6 * e), ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall c (2 - a - 8 * e),
        ‖deriv L z / L z‖ ≤ (outerConstant e A M / (2 * e)) * Real.log C) := by
  have hθ := uniformTheta_mem he he'
  have hB := outerConstant_ge_one he he' hA hM
  have hK : 0 ≤ A * outerConstant e A M := by positivity
  obtain ⟨D, hD, hDb⟩ := exp_sublinear_le hθ.1.le hθ.2 hK hε
  refine ⟨2 * D, by positivity, ?_⟩
  intro a C L E c ha ha' hC hL h0 hpoly hE hEL hEb
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hT : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  obtain ⟨g, hg, hge, hgin, hgRe⟩ :=
    zero_free_disk_logarithm ha' he he' hCp hL h0 hpoly hE hEL hEb
  constructor
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) :=
      closedBall_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hb := inner_log_bound ha ha' he he' hA hM hT hg hgRe hgin hz
    have hp : Real.exp (A * outerConstant e A M * Real.log C ^ uniformTheta e) ≤
        D * C ^ ε := by
      convert (preTransparency := .instances) hDb (Real.log C) hT using 1
      rw [Real.rpow_def_of_pos hCp, mul_comm ε]
    have hu : ‖L z‖ ≤ D * C ^ ε := by
      rw [← hez, Complex.norm_exp]
      exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hb)).trans hp
    have hl : ‖(L z)⁻¹‖ ≤ D * C ^ ε := by
      rw [← hez, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
      have hre : -(g z).re ≤ ‖g z‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      exact (Real.exp_le_exp.mpr (hre.trans hb)).trans hp
    nlinarith
  · intro z hz
    rw [logarithmic_derivative_eq isOpen_ball hg hge
      (closedBall_subset_ball (by linarith) hz)]
    exact logarithm_derivative_bound ha ha' he he' hA hM hT hg hgRe
      (hgin c (mem_closedBall_self (by norm_num))) hz

theorem conductor_height_scale_ge_exp (Q t : ℝ) (hQ : 1 ≤ Q) :
    Real.exp 1 ≤ 2 * Q * (3 + |t|) ^ 2 := by
  have hs : 9 ≤ (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  have hq := mul_le_mul_of_nonneg_right hQ (sq_nonneg (3 + |t|))
  nlinarith [Real.exp_one_lt_three]

theorem absorb_polynomial_constant {K p : ℝ} (hp : 0 ≤ p) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ C : ℝ, Real.exp 1 ≤ C → K * C ^ p ≤ C ^ M := by
  let J := max 1 K
  have hJ : 1 ≤ J := le_max_left _ _
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hlogJ : 0 ≤ Real.log J := Real.log_nonneg hJ
  refine ⟨p + Real.log J + 1, by linarith, ?_⟩
  intro C hC
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hlogC : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  have hJC : J ≤ C ^ Real.log J := by
    rw [Real.rpow_def_of_pos hCp, ← Real.exp_log hJp]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    K * C ^ p ≤ J * C ^ p := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hCp.le _)
    _ ≤ C ^ Real.log J * C ^ p := mul_le_mul_of_nonneg_right hJC
      (Real.rpow_nonneg hCp.le _)
    _ = C ^ (p + Real.log J) := by rw [← Real.rpow_add hCp]; congr 1; ring
    _ ≤ C ^ (p + Real.log J + 1) := Real.rpow_le_rpow_of_exponent_le
      ((show (1 : ℝ) ≤ Real.exp 1 by exact Real.one_le_exp (by norm_num)).trans hC)
      (by linarith)

theorem disk_re_gt {a e t : ℝ} {z : ℂ}
    (hz : z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - a - 2 * e)) :
    a + 2 * e < z.re := by
  have hn : ‖z - (2 + (t : ℂ) * Complex.I)‖ < 2 - a - 2 * e := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z - (2 + (t : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, zero_mul, sub_zero, add_zero] at hr
  norm_num at hr
  linarith [neg_le_abs (z.re - 2)]

end SevenEighths.LogarithmicControl

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Logarithmic
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmic
open HeckeFamily HeckeLogarithmicInput

theorem complexity_ge_exp (η : Character) (t : ℝ) : Real.exp 1 ≤ complexity η t :=
  LogarithmicControl.conductor_height_scale_ge_exp _ t (modulus_norm_ge_one η)

theorem regular_disk_differentiable (η : Character) {a e t : ℝ}
    (ha : (1/2 : ℝ) ≤ a) (he : 0 < e) :
    DifferentiableOn ℂ (regular η) (ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) := by
  intro z hz
  exact (regular_differentiableAt η (by
    have hr := LogarithmicControl.disk_re_gt hz
    linarith)).differentiableWithinAt

theorem exists_uniform_polynomial_exponent :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (η : Character), FiniteFourier.IsPrimitiveOnIdeals η.residue →
      ∀ a e t : ℝ, 1/2 ≤ a → 0 < e → ∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-3*e),
        ‖regular η z‖ ≤ (complexity η t)^M := by
  obtain ⟨M, hM, hb⟩ := LogarithmicControl.absorb_polynomial_constant
    (K := 2*uniformConstant) (p := 1) (by norm_num)
  refine ⟨M, hM, ?_⟩
  intro η hp a e t ha he z hz
  have hz2 : z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hz
  have h := regular_disk_growth η hp a e t ha he.le hz2
  have hQ : (η.modulus.absNorm : ℝ)^(3/5 : ℝ) ≤ (η.modulus.absNorm : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (modulus_norm_ge_one η)
      (show (3/5 : ℝ)≤1 by norm_num)
  apply h.trans
  calc
    _ ≤ (4*uniformConstant)*(η.modulus.absNorm : ℝ)*(3+|t|)^2 := by
      gcongr
      exact mul_nonneg (by norm_num) uniformConstant_nonneg
    _ = (2*uniformConstant)*complexity η t := by unfold complexity; ring
    _ ≤ (complexity η t)^M := by simpa only [Real.rpow_one] using hb _ (complexity_ge_exp η t)

theorem disk_control_of_euler_log_oai (e A ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ D B : ℝ, 0 < D ∧ 0 ≤ B ∧ ∀ (η : Character),
      FiniteFourier.IsPrimitiveOnIdeals η.residue → ∀ (a t : ℝ) (E : ℂ → ℂ),
      1/2 ≤ a → a ≤ 1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular η z ≠ 0) →
      DifferentiableOn ℂ E (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      EqOn (Complex.exp ∘ E) (regular η) (ball ((2 : ℂ)+t*Complex.I) (1/2)) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (49/100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular η z‖ + ‖(regular η z)⁻¹‖ ≤ D*(complexity η t)^ε) ∧
      (∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖deriv (regular η) z / regular η z‖ ≤ B*Real.log (complexity η t)) := by
  obtain ⟨M,hM,hpoly⟩ := exists_uniform_polynomial_exponent
  obtain ⟨D,hD,hb⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, LogarithmicControl.outerConstant e A M/(2*e), hD, ?_, ?_⟩
  · have hB := LogarithmicControl.outerConstant_ge_one he he' hA hM
    positivity
  · intro η hp a t E ha ha' hzero hE hEL hEb
    exact hb a (complexity η t) (regular η) E ((2 : ℂ)+t*Complex.I) ha ha'
      (complexity_ge_exp η t) (regular_disk_differentiable η ha he) hzero
      (hpoly η hp a e t ha he) hE hEL hEb

end SevenEighths.HeckeLogarithmic

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckeLogarithmic.disk_control_of_euler_log_oai := @OAI.SevenEighths.HeckeLogarithmic.disk_control_of_euler_log_oai
