-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.HasCubicExponent.improve
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:04:58.318528+00:00
-- url     : https://prove2.me/submissions/8d59847c-4852-445b-b277-46e83efb1193

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B010
import Theorems.Thm_OAI_SevenEighths_CubicSieve_HasCubicExponent_frequencyCost_bound
import Theorems.Thm_OAI_SevenEighths_CubicSieve_cubic_smoothed_frequency_recurrence_all

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicDyadicDecay
namespace OAI

namespace SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

lemma decayConstant_pos (α : ℝ) (hα : 0 < α) (hα3 : α < 3) :
    0 < decayConstant α := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold decayConstant
  positivity

lemma descent_factor_le_one (e d u v : ℝ) (he : 1 ≤ e) (hed : e ≤ d)
    (hv : v ≤ 0) (huv : u+v ≤ 0) : e^u*d^v ≤ 1 := by
  have hd : 1 ≤ d := he.trans hed
  by_cases hu : 0 ≤ u
  · calc
      _ ≤ d^u*d^v := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by linarith) hed hu) (by positivity)
      _ = d^(u+v) := (Real.rpow_add (by linarith : 0 < d) u v).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd huv
  · exact (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos he (le_of_not_ge hu))
      (Real.rpow_le_one_of_one_le_of_nonpos hd hv) (by positivity) (by norm_num)).trans_eq
      (one_mul 1)

lemma monomial_descendant_le (M N e d u v : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hv : 0 ≤ v) (huv : 0 ≤ u+v) :
    (M/e)^u*(N/d)^v ≤ M^u*N^v := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  have hg := descent_factor_le_one e d (-u) (-v) he hed (by linarith) (by linarith)
  calc
    _ = (M^u*N^v)*(e^(-u)*d^(-v)) := by
      rw [Real.div_rpow hM.le he0.le, Real.div_rpow hN.le hd0.le,
        Real.rpow_neg he0.le, Real.rpow_neg hd0.le]
      ring
    _ ≤ (M^u*N^v)*1 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := mul_one _

lemma mixed_monomial_identity (M N δ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) =
      M^(2/3-δ)*N^(2/3+3*δ) := by
  rw [Real.mul_rpow hM.le hN.le]
  calc
    _ = (M^(-δ)*M^(2/3 : ℝ))*(N^(3*δ)*N^(2/3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring

lemma secondary_monomial_identity (M N δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) =
      M^(1-ξ-δ)*N^(2*ξ-1+3*δ) := by
  calc
    _ = (M^(-δ)*M^(1-ξ))*(N^(3*δ)*N^(2*ξ-1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring

lemma mixed_descendant_le (M N e d δ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*((M/e)*(N/d))^(2/3 : ℝ) ≤
      N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [mixed_monomial_identity (M/e) (N/d) δ (div_pos hM he0) (div_pos hN hd0),
    mixed_monomial_identity M N δ hM hN]
  exact monomial_descendant_le M N e d (2/3-δ) (2/3+3*δ) hM hN he hed
    (by linarith) (by linarith)

lemma secondary_descendant_le (M N e d δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1) ≤
      N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [secondary_monomial_identity (M/e) (N/d) δ ξ (div_pos hM he0) (div_pos hN hd0),
    secondary_monomial_identity M N δ ξ hM hN]
  exact monomial_descendant_le M N e d (1-ξ-δ) (2*ξ-1+3*δ) hM hN he hed
    (by linarith) (by linarith)

theorem poisson_envelope_descendant_le (M N e d δ ξ P Q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (N/d)^(3*δ)*(M/e)^(-δ) *
        (P*((M/e)*(N/d))^(2/3 : ℝ) + Q*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)) ≤
      N^(3*δ)*M^(-δ) * (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1)) := by
  have hm := mul_le_mul_of_nonneg_left (mixed_descendant_le M N e d δ hM hN he hed hδ) hP
  have hs := mul_le_mul_of_nonneg_left
    (secondary_descendant_le M N e d δ ξ hM hN he hed hδ hξ) hQ
  nlinarith [hm, hs]

end
end SevenEighths.CubicDyadicDecay

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Algebra
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [← pow_succ, one_mul] using hz
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  apply mul_right_cancel₀ h0
  rw [inv_mul_cancel₀ h0]
  simpa only [← pow_succ] using h3

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_ideal_moebius_le_one (I : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

end QuadraticInitialBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CrossFactorization
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

namespace CoprimeSieveOperator
open FiniteSieveOperator CoprimeMobiusExtension

theorem square_norm_sum {n : Type*} [Fintype n] (z : n → ℂ) :
    (↑(‖∑ j, z j‖ ^ 2) : ℂ) = ∑ j, ∑ k, star (z j) * z k := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, starRingEnd_apply]
  rw [Finset.sum_mul_sum]

end CoprimeSieveOperator

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RowMajorants
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

lemma rowMajorant_nonneg (s : ℝ) : 0 ≤ (rowMajorant s).re :=
  (Classical.choose_spec exists_rowMajorant).1 s

lemma rowMajorant_one (s : ℝ) (hs : |s| ≤ 1) : rowMajorant s = 1 :=
  (Classical.choose_spec exists_rowMajorant).2.1 s hs

lemma rowMajorant_zero (s : ℝ) (hs : 2 < s) : rowMajorant s = 0 :=
  (Classical.choose_spec exists_rowMajorant).2.2 s hs

lemma rowMajorant_zero_outside (Y : ℝ) (hY : 0 < Y) (z : O)
    (hz : z ∉ rowMajorantBall Y) : rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) = 0 := by
  have hn : Nat.ceil (2 * Y) < Ideal.absNorm (Ideal.span {z}) := by
    apply Nat.lt_of_not_ge
    intro hn
    exact hz (ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le _ z hn)
  have hn' : (Nat.ceil (2 * Y) : ℝ) < (Ideal.absNorm (Ideal.span {z}) : ℝ) := by exact_mod_cast hn
  apply rowMajorant_zero
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  apply (lt_div_iff₀ hY).2
  linarith [Nat.le_ceil (2 * Y)]

lemma rowMajorant_tsum_eq_sum (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) =
      ∑ z ∈ rowMajorantBall Y, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ) := by
  apply tsum_eq_sum
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]

lemma rowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]

theorem finite_row_energy_le_rowMajorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
  have hs := rowMajorant_summable P Y hY
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : |‖eisEmbedding z‖ ^ 2 / Y| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)]
        apply (div_le_one hY).2
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [rowMajorant_one _ hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

open MeasureTheory Set Module
open scoped BigOperators Classical ENNReal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.GcdReduction
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

theorem mem_gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) (j k : n) :
    gcd (cols j) (cols k) ∈ gcdPool cols :=
  Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩

theorem gcdPool_ne_zero {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀ j, cols j ≠ 0) (D : Ideal O) (hD : D ∈ gcdPool cols) : D ≠ 0 := by
  obtain ⟨⟨j, k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  intro h
  have hd := gcd_dvd_left (cols j) (cols k)
  rw [h, zero_dvd_iff] at hd
  exact hcols j hd

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
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
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

theorem mem_columnDivisorPool_of_dvd {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (j : n) (D : Ideal O)
    (hD : D ∣ left j) : D ∈ columnDivisorPool left := by
  apply Finset.mem_biUnion.mpr
  exact ⟨j,Finset.mem_univ j,(IdealMobiusDivisorSum.mem_idealDivisors (hleft j)).mpr hD⟩

theorem columnDivisorPool_norm_bounds {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (N : ℝ)
    (hN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N)
    (D : Ideal O) (hD : D ∈ columnDivisorPool left) :
    1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N := by
  obtain ⟨j,hj,hDj⟩ := Finset.mem_biUnion.mp hD
  have hd := (IdealMobiusDivisorSum.mem_idealDivisors (hleft j)).mp hDj
  have hDz : D ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hd
    exact hleft j hd
  have hDN : Ideal.absNorm D ≤ Ideal.absNorm (left j) :=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (fun h => hleft j (Ideal.absNorm_eq_zero_iff.mp h)))
      (map_dvd Ideal.absNorm hd)
  refine ⟨?_,(Nat.cast_le.mpr hDN).trans (hN j)⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hDz (Ideal.absNorm_eq_zero_iff.mp h))

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Ideal
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem idealSymbol_fourth (I : Ideal Eis) (x : Eis) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 4 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol I x) := by
  have hlocal (P : Ideal Eis) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 4 =
        eisEmbedding (CubicJacobiGlobal.primeValue P x) := by
    unfold CubicJacobiGlobal.primeValue
    split_ifs with h
    · let : P.IsMaximal := h.1
      let χ := actualSextic P h.2 ^ 2
      have hχ : χ ^ 3 = 1 := by
        dsimp [χ]
        rw [canonicalSextic_pow_two, MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
      simpa only [χ, canonicalSextic_pow_two, MulChar.ringHomComp_apply] using
        cubic_fourth_eq χ hχ (Ideal.Quotient.mk P x)
    · simp
  have hprod (S : Multiset (Ideal Eis)) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 4 =
        eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod) := by
    induction S using Multiset.induction_on with
    | empty => simp
    | @cons P S ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow, hlocal, ih]
  by_cases hI : I = 0
  · simp [hI]
  · simpa only [CubicJacobiGlobal.idealSymbol, if_neg hI] using
      hprod (UniqueFactorizationMonoid.normalizedFactors I)

theorem mem_idealRange {X : ℝ} {I : Ideal Eis} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.le_floor hN⟩, ha⟩
    intro hz
    exact (primaryGenerator_ne_zero_ideal I ha.2) (Ideal.absNorm_eq_zero_iff.mp hz)

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal Eis) (cols : n → Ideal Eis)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => idealKernel (cols j) (rows i)) ≤ sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (idealMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Norm
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primaryGenerator_inj_on_cubic_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J)
    (heq : primaryGenerator I = primaryGenerator J) : I = J := by
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I hI.2).1.symm
    _ = Ideal.span {primaryGenerator J} := by rw [heq]
    _ = J := (primaryGenerator_spec J hJ.2).1

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Extraction
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  apply family_squared_norm_le (fun I : idealRange M => I.val)
    (fun J : idealRange N => J.val) Subtype.val_injective Subtype.val_injective M' N'
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hM⟩
  · intro J
    exact ⟨(mem_idealRange.mp J.property).1, (mem_idealRange.mp J.property).2.trans hN⟩

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Elements
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem elementCharacter_norm_le_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O) :
    ‖elementCharacter I hI x‖ ≤ 1 := by
  change ‖eisEmbedding (CubicJacobiGlobal.idealSymbol I x)‖ ≤ 1
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm x I) 2).trans_eq (by norm_num)

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.IdealMasks
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

theorem ideal_coprime_mobius (K P : Ideal ActualEisensteinCubic.O) (hK : K ≠ 0) :
    (if IsCoprime K P then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors K, if R ∣ P then (moebius R : ℂ) else 0 := by
  let G := K ⊔ P
  have hG : G ≠ 0 := by
    intro hz
    apply hK
    exact le_antisymm (show K ≤ 0 from hz ▸ (le_sup_left : K ≤ G)) bot_le
  have hdiv : (idealDivisors K).filter (fun R => R ∣ P) = idealDivisors G := by
    ext R
    simp only [Finset.mem_filter, mem_idealDivisors hK, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G]

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Gcd
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicRow_mul (I J : Ideal O) (z : O) :
    cubicRow (I * J) z = cubicRow I z * cubicRow J z := by
  simp only [cubicRow, ← CanonicalRowCompletion.idealRowHom_square, map_mul, mul_pow]

lemma cubicRow_square_eq_star (I : Ideal O) (z : O) :
    cubicRow I z ^ 2 = star (cubicRow I z) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I z)

lemma cubicRow_common_mask (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
  rw [← cubicRow_square_eq_star]
  calc
    _ = cubicRow D z ^ 3 := by ring
    _ = _ := idealSymbol_cube_mask D z hD

lemma cubicRow_common_mobius (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        if E ∣ Ideal.span {z} then (UniqueFactorizationMonoid.moebius E : ℂ) else 0 := by
  rw [cubicRow_common_mask D hD z]
  exact SevenEighths.InverseMoment.ideal_coprime_mobius D _ (primaryGenerator_ne_zero_ideal D hD)

lemma cubic_admissible_of_dvd {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryGenerator_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

lemma cubic_admissible_quotient {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible (idealQuotient D I) :=
  cubic_admissible_of_dvd hI (CanonicalQuadraticSieve.idealQuotient_dvd hD)

lemma cubicRow_divisor_factor (D I : Ideal O) (hDI : D ∣ I) (z : O) :
    cubicRow I z = cubicRow D z * cubicRow (idealQuotient D I) z := by
  conv_lhs => rw [← CanonicalQuadraticSieve.idealQuotient_mul hDI]
  exact cubicRow_mul _ _ _

theorem cubicGcdTerm_eq_quotient {n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) :
    cubicGcdTerm D cols a z j k =
      (star (cubicRow D z) * cubicRow D z) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (cubicRow (totalQuotient D (cols j)) z * (if D ∣ cols j then a j else 0)) *
          (cubicRow (totalQuotient D (cols k)) z * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [cubicGcdTerm, totalQuotient, if_pos hj, if_pos hk]
      rw [← CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [if_pos hg, if_pos hg, cubicRow_divisor_factor D _ hj,
          cubicRow_divisor_factor D _ hk]
        simp only [star_mul]
        ring
      · simp only [if_neg hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [cubicGcdTerm, if_neg hg]
      simp [hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [cubicGcdTerm, if_neg hg]
    simp [hj]

theorem cubic_weighted_energy_eq_gcd_blocks {n : Type*} [Fintype n]
    (R : Finset O) (w : O → ℂ) (cols : n → Ideal O) (a : n → ℂ) :
    (∑ z ∈ R, w z * (‖∑ j, cubicRow (cols j) z * a j‖ ^ 2 : ℝ)) =
      ∑ D ∈ gcdPool cols, ∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k := by
  have hp (z : O) (j k : n) :
      (∑ D ∈ gcdPool cols, cubicGcdTerm D cols a z j k) =
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [cubicGcdTerm, ite_true]
    · intro D hD hne
      exact if_neg (Ne.symm hne)
    · exact fun h => (h (CanonicalQuadraticSieve.mem_gcdPool cols j k)).elim
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => arg 2; ext j; rw [Finset.sum_comm]
  simp_rw [hp]
  simpa only [Complex.ofReal_pow] using CoprimeSieveOperator.square_norm_sum
    (fun j => cubicRow (cols j) z * a j)

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Mobius
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma elementQuotient_mul (d z : O) (h : d ∣ z) : d * elementQuotient d z = z := by
  rw [elementQuotient, dif_pos h]
  exact h.choose_spec.symm

lemma elementQuotient_injective (d : O) : Set.InjOn (elementQuotient d) {z | d ∣ z} := by
  intro x hx y hy he
  rw [← elementQuotient_mul d x hx, ← elementQuotient_mul d y hy, he]

lemma sum_divisible_rows (R : Finset O) (d : O) (f : O → ℂ) :
    (∑ z ∈ R, if d ∣ z then f z else 0) =
      ∑ w ∈ dividedRows R d, f (d * w) := by
  rw [← Finset.sum_filter]
  unfold dividedRows
  have hinj : Set.InjOn (elementQuotient d) (↑(R.filter (fun z => d ∣ z)) : Set O) := by
    intro x hx y hy he
    exact elementQuotient_injective d (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro z hz
  rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]

lemma cubicRow_mul_argument (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x y : O) :
    cubicRow I (x * y) = cubicRow I x * cubicRow I y := by
  exact (elementCharacter I hI).map_mul x y

lemma totalQuotient_cubic_admissible (D I : Ideal O) (hI : Admissible I) :
    Admissible (totalQuotient D I) := by
  by_cases h : D ∣ I
  · rw [totalQuotient, if_pos h]
    exact cubic_admissible_quotient hI h
  · rw [totalQuotient, if_neg h]
    exact ⟨squarefree_one, by rw [primaryGenerator_one]; exact one_ne_zero⟩

lemma residualGram_rescale {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (d w : O) :
    residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * w) =
      residualGram D cols (descendedCoefficient D cols a d) w := by
  unfold residualGram
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · rw [cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols j)).2,
      cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols k)).2]
    simp only [descendedCoefficient, star_mul]
    ring
  · rfl

lemma ideal_dvd_span_iff_generator (E : Ideal O) (z : O) :
    E ∣ Ideal.span {z} ↔ idealGenerator E ∣ z := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have he : (z ∈ Ideal.span {idealGenerator E}) ↔ idealGenerator E ∣ z :=
    Ideal.mem_span_singleton
  rwa [span_idealGenerator] at he

lemma sum_dividedRows_residualGram_rescale {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) (d : O) :
    (∑ z ∈ dividedRows R d,
      w (d * z) * residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * z)) =
      ∑ z ∈ dividedRows R d,
        w (d * z) * residualGram D cols (descendedCoefficient D cols a d) z := by
  apply Finset.sum_congr rfl
  intro z _
  rw [residualGram_rescale D cols hcols a]

theorem cubic_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryGenerator D ≠ 0)
    (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) :
    (∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ dividedRows R (idealGenerator E),
            w (idealGenerator E * z) *
              residualGram D cols (descendedCoefficient D cols a (idealGenerator E)) z := by
  let b : n → ℂ := fun j => if D ∣ cols j then a j else 0
  have ht (z : O) : (∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      (star (cubicRow D z) * cubicRow D z) * residualGram D cols b z := by
    simp only [cubicGcdTerm_eq_quotient D (primaryGenerator_ne_zero_ideal D hD),
      residualGram, b, Finset.mul_sum]
  calc
    _ = ∑ z ∈ R, ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (if idealGenerator E ∣ z then w z * residualGram D cols b z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ht, cubicRow_common_mobius D hD, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [ideal_dvd_span_iff_generator]
      split_ifs <;> ring
    _ = ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ R, if idealGenerator E ∣ z then w z * residualGram D cols b z else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [sum_divisible_rows]
      exact congrArg ((UniqueFactorizationMonoid.moebius E : ℂ) * ·)
        (sum_dividedRows_residualGram_rescale D cols hcols a R w (idealGenerator E))

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.DescentEnergy
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum DivisorBlockCauchy
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma descendedCoefficient_norm_le {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (d : O) (j : n) :
    ‖descendedCoefficient D cols a d j‖ ≤ ‖if D ∣ cols j then a j else 0‖ := by
  unfold descendedCoefficient
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (elementCharacter_norm_le_one _ (totalQuotient_cubic_admissible D _ (hc j)).2 d)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem descended_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ) (hN0 : 0 ≤ N)
    (hN : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
      ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
        (divisorConstant ε hε * N^ε)^2 * ∑ j, ‖a j‖^2 := by
  have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
  let B := divisorConstant ε hε * N^ε
  have hB : 0 ≤ B := mul_nonneg (divisorConstant_pos ε hε).le (Real.rpow_nonneg hN0 _)
  have hcard (D : Ideal O) (hD : D ∈ columnDivisorPool cols) :
      ((idealDivisors D).card : ℝ) ≤ B := by
    have hd := columnDivisorPool_norm_bounds cols hc0 N hN D hD
    have hd0 : D ≠ 0 := by
      intro he
      have hh := hd.1
      norm_num [he] at hh
    exact ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 D hd0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hd.2 hε.le)
        (divisorConstant_pos ε hε).le)
  calc
    _ ≤ ∑ D ∈ columnDivisorPool cols, B * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ ∑ E ∈ idealDivisors D, ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          apply Finset.sum_le_sum
          intro E hE
          exact Finset.sum_le_sum (fun j hj => pow_le_pow_left₀ (norm_nonneg _)
            (descendedCoefficient_norm_le D cols hc a (idealGenerator E) j) 2)
        _ = ((idealDivisors D).card : ℝ) * ∑ j, ‖if D ∣ cols j then a j else 0‖^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD) (by positivity)
    _ = B * (∑ D ∈ columnDivisorPool cols, ∑ j, ‖if D ∣ cols j then a j else 0‖^2) := by
      rw [Finset.mul_sum]
    _ ≤ B * (B * ∑ j, ‖a j‖^2) := mul_le_mul_of_nonneg_left
      (divisor_mask_energy_small_power ε hε _ cols hc0 N hN a) hB
    _ = _ := by dsimp [B]; ring

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FullNorm
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem element_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => cubicRow (cols j) (rows i)) ≤ elementSieveNorm M N := by
  let r : m → elementRange M := fun i => ⟨rows i, (mem_elementRange M (rows i)).mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (elementMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma sieveNorm_le_elementSieveNorm (M N : ℝ) : sieveNorm M N ≤ elementSieveNorm M N := by
  apply element_family_squared_norm_le
    (fun I : idealRange M => primaryGenerator I.val) (fun J : idealRange N => J.val)
  · intro I J he
    exact Subtype.ext (primaryGenerator_inj_on_cubic_admissible
      (mem_idealRange.mp I.property).1 (mem_idealRange.mp J.property).1 he)
  · exact Subtype.val_injective
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1.2, by
      rw [(primaryGenerator_spec I.val (mem_idealRange.mp I.property).1.2).1]
      exact (mem_idealRange.mp I.property).2⟩
  · intro J
    exact mem_idealRange.mp J.property

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CompactDescent
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma majorant_radial_summable (P : O → ℂ) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖^2 / M) * P z) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall M) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside M hM z hz, zero_mul]

lemma majorant_rescale (d z : O) (_hd : d ≠ 0) (M : ℝ) :
    rowMajorant (‖eisEmbedding (d*z)‖^2 / M) =
      rowMajorant (‖eisEmbedding z‖^2 / (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) := by
  rw [map_mul, norm_mul, mul_pow, eisEmbedding_norm_sq_eq_absNorm_span d]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma dividedMajorant_tsum (P : O → ℂ) (d : O) (hd : d ≠ 0)
    (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ dividedRows (rowMajorantBall M) d,
      rowMajorant (‖eisEmbedding (d*z)‖^2 / M) * P z) =
      ∑' z : O, rowMajorant (‖eisEmbedding z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z := by
  symm
  rw [← show (fun z : O => rowMajorant (‖eisEmbedding (d*z)‖^2 / M) * P z) =
      (fun z : O => rowMajorant (‖eisEmbedding z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z) by
          funext z; rw [majorant_rescale d z hd M]]
  apply tsum_eq_sum
  intro z hz
  have hout : d*z ∉ rowMajorantBall M := by
    intro hin
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨d*z, Finset.mem_filter.mpr ⟨hin, dvd_mul_right d z⟩, ?_⟩
    apply mul_left_cancel₀ hd
    exact elementQuotient_mul d (d*z) (dvd_mul_right d z)
  rw [rowMajorant_zero_outside M hM (d*z) hout, zero_mul]

lemma majorant_coprime_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖^2 / M) *
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) =
      cubicSmoothedCoprime cols a rowMajorant M := by
  have hs (j k : n) := majorant_radial_summable
    (fun z => if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) M hM
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => hs j k))]
  unfold cubicSmoothedCoprime
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => hs j k)]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [if_pos hcop]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    simp only [star_mul]
    ring
  · simp only [if_neg hcop, mul_zero, tsum_zero]

lemma compact_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryGenerator D ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2 / M) *
      ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ idealDivisors D, (UniqueFactorizationMonoid.moebius E : ℂ) *
        cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ)) := by
  rw [cubic_gcd_mobius_descent D hD cols hc a]
  apply Finset.sum_congr rfl
  intro E hE
  have hE0 : E ≠ 0 := by
    intro he
    have hh := (mem_idealDivisors (primaryGenerator_ne_zero_ideal D hD)).mp hE
    rw [he, zero_dvd_iff] at hh
    exact primaryGenerator_ne_zero_ideal D hD hh
  have hgen := idealGenerator_ne_zero E hE0
  congr 1
  rw [dividedMajorant_tsum _ _ hgen M hM, span_idealGenerator]
  apply majorant_coprime_tsum
  have hNE : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  exact div_pos hM hNE

lemma gcdPool_cubic_admissible {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (D : Ideal O) (hD : D ∈ gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact cubic_admissible_of_dvd (hc j) (gcd_dvd_left _ _)

lemma gcdPool_subset_columnDivisorPool {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, cols j ≠ 0) :
    gcdPool cols ⊆ columnDivisorPool cols := by
  intro D hD
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact mem_columnDivisorPool_of_dvd cols hc j _ (gcd_dvd_left _ _)

theorem finite_energy_le_compact_descendants {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (R : Finset O) (M : ℝ) (hM : 0 < M)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ‖cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ))‖ := by
  have hs := finite_row_energy_le_rowMajorant
    (fun z => ∑ j, cubicRow (cols j) z * a j) R M hM hR
  apply hs.trans
  apply (Complex.re_le_norm _).trans
  rw [rowMajorant_tsum_eq_sum _ M hM,
    cubic_weighted_energy_eq_gcd_blocks (rowMajorantBall M) _ cols a]
  have he (D : Ideal O) (hD : D ∈ gcdPool cols) :=
    compact_gcd_mobius_descent D (gcdPool_cubic_admissible cols hc D hD).2 cols hc a M hM
  calc
    _ ≤ ∑ D ∈ gcdPool cols,
        ‖∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2 / M) *
          ∑ j, ∑ k, cubicGcdTerm D cols a z j k‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro D hD
      rw [he D hD]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (QuadraticInitialBound.norm_ideal_moebius_le_one E)
        (norm_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.QuotientColumns
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma finite_sum_restrict {n A : Type*} [Fintype n] [AddCommMonoid A]
    (p : n → Prop) (f : n → A) (hf : ∀ j, ¬p j → f j = 0) :
    (∑ j, f j) = ∑ j : {j // p j}, f j.val := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ j : {j // ¬p j}, f j.val) = 0 :=
    Finset.sum_eq_zero (fun j hj => hf j.val j.property)
  rw [hz, add_zero] at h
  exact h.symm

lemma cubicSmoothedCoprime_restrict {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (p : n → Prop)
    (ha : ∀ j, ¬p j → a j = 0) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime cols a W M =
      cubicSmoothedCoprime (fun j : {j // p j} => cols j.val) (fun j => a j.val) W M := by
  unfold cubicSmoothedCoprime
  rw [finite_sum_restrict p _ (by
    intro j hj
    simp [ha j hj])]
  apply Finset.sum_congr rfl
  intro j hj
  exact finite_sum_restrict p _ (by
    intro k hk
    simp [ha k hk])

lemma quotientColumn_injective {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : Function.Injective cols) : Function.Injective (quotientColumn D cols) := by
  intro j k he
  exact Subtype.ext (hc (idealQuotient_injective_on D j.property k.property he))

lemma quotientColumn_admissible {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (j : {j // D ∣ cols j}) :
    Admissible (quotientColumn D cols j) := cubic_admissible_quotient (hc j.val) j.property

lemma cubic_quotient_in_shell {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (hc : ∀ j, Admissible (cols j)) (N : ℝ)
    (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (j : {j // D ∣ cols j}) :
    (N / (Ideal.absNorm D : ℝ))/2 ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) ∧
      (Ideal.absNorm (quotientColumn D cols j) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryGenerator_ne_zero_ideal _ (hc j.val).2) j.property
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
  have he : (Ideal.absNorm (quotientColumn D cols j) : ℝ) * (Ideal.absNorm D : ℝ) =
      (Ideal.absNorm (cols j.val) : ℝ) := by
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, quotientColumn, idealQuotient_mul j.property]
  refine ⟨?_, idealQuotient_norm_le hD0 j.property N (hcols j.val).2⟩
  have hh : (N/2) / (Ideal.absNorm D : ℝ) ≤ (Ideal.absNorm (quotientColumn D cols j) : ℝ) := by
    apply (div_le_iff₀ hDN).mpr
    rw [he]
    exact (hcols j.val).1
  convert (preTransparency := .instances) hh using 1; ring

lemma compact_descendant_restrict {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
      (descendedCoefficient D cols a d) W M =
    cubicSmoothedCoprime (quotientColumn D cols) (quotientCoefficient D cols a d) W M := by
  rw [cubicSmoothedCoprime_restrict _ _ (fun j => D ∣ cols j) (by
    intro j hj
    simp only [descendedCoefficient, if_neg hj, mul_zero])]
  have hc : (fun j : {j // D ∣ cols j} => totalQuotient D (cols j.val)) = quotientColumn D cols := by
    funext j
    simp only [totalQuotient, if_pos j.property, quotientColumn]
  have ha : (fun j : {j // D ∣ cols j} => descendedCoefficient D cols a d j.val) =
      quotientCoefficient D cols a d := by
    funext j
    simp only [descendedCoefficient, totalQuotient, if_pos j.property, quotientCoefficient, quotientColumn]
  rw [hc, ha]

lemma quotientCoefficient_energy {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (d : O) :
    (∑ j : {j // D ∣ cols j}, ‖quotientCoefficient D cols a d j‖^2) =
      ∑ j, ‖descendedCoefficient D cols a d j‖^2 := by
  rw [finite_sum_restrict (fun j => D ∣ cols j) _ (by
    intro j hj
    simp only [descendedCoefficient, if_neg hj, mul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [quotientCoefficient, quotientColumn, descendedCoefficient, totalQuotient, if_pos j.property]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ColumnShells
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve FiniteSieveRestriction
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicColumnShell_bounds {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val/2 ≤ (Ideal.absNorm (cols j.val) : ℝ) ∧
      (Ideal.absNorm (cols j.val) : ℝ) ≤ (2 : ℝ)^l.val := by
  have hp : 1 ≤ (Ideal.absNorm (cols j.val) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (primaryGenerator_ne_zero_ideal _ (hc j.val).2))
  have hb := divisorDyadicLabel_bounds N (cols j.val) hp (hn j.val)
  have hj := j.property
  change divisorDyadicLabel N (cols j.val) = l at hj
  rw [hj] at hb
  exact ⟨hb.1.le,hb.2⟩

lemma cubicColumnShell_scale_le {n : Type*} (cols : n → Ideal O) (N : ℝ)
    (hc : ∀ j, Admissible (cols j)) (hn : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (l : Fin (columnDyadicLength N + 1)) (j : CubicColumnShell cols N l) :
    (2 : ℝ)^l.val ≤ 2*N := by
  have hh := (cubicColumnShell_bounds cols N hc hn l j).1
  linarith [hn j.val]

lemma cubicColumnShell_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) :
    (∑ l : Fin (columnDyadicLength N + 1), ∑ j : CubicColumnShell cols N l, ‖a j.val‖^2) =
      ∑ j, ‖a j‖^2 := Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => ‖a j‖^2)

theorem cubic_energy_column_shells {n : Type*} [Fintype n]
    (cols : n → Ideal O) (N : ℝ) (a : n → ℂ) (R : Finset O) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      (columnDyadicLength N + 1 : ℝ) *
        ∑ l : Fin (columnDyadicLength N + 1), ∑ z ∈ R,
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z * a j.val‖^2 := by
  have hp (z : O) : ‖∑ j, cubicRow (cols j) z*a j‖^2 ≤
      (columnDyadicLength N + 1 : ℝ)*∑ l : Fin (columnDyadicLength N + 1),
        ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 := by
    rw [← Fintype.sum_fiberwise (cubicColumnLabel cols N) (fun j => cubicRow (cols j) z*a j)]
    calc
      _ ≤ (∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
          Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
          (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ))
            (fun l : Fin (columnDyadicLength N + 1) =>
              ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖))
  calc
    _ ≤ ∑ z ∈ R, (columnDyadicLength N + 1 : ℝ)*
        ∑ l : Fin (columnDyadicLength N + 1),
          ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2 :=
      Finset.sum_le_sum (fun z hz => hp z)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CommonFactorBound
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum SecondPassArithmetic EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_common_factor_frequency_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M)
        (cols : n → Ideal O) (_hinj : Function.Injective cols)
        (_hc : ∀ j, Admissible (cols j))
        (_hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ) (R : Finset O)
        (_hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M),
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
          ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
            frequencyCost C ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ)) *
              ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 := by
  obtain ⟨C,hC,hrec⟩ := cubic_smoothed_frequency_recurrence_all rowMajorant
  refine ⟨C,hC,?_⟩
  intro n _ _ ε hε M N hM cols hinj hc hcols a R hR
  apply (finite_energy_le_compact_descendants cols hc a R M hM hR).trans
  apply Finset.sum_le_sum
  intro D hD
  have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
  have hDcol := gcdPool_subset_columnDivisorPool cols hc0 hD
  have hDN := columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D hDcol
  have hD0 := gcdPool_ne_zero cols hc0 D hD
  have hDN0 : 0 < (Ideal.absNorm D : ℝ) := by linarith [hDN.1]
  have hNshort : 1 ≤ N / (Ideal.absNorm D : ℝ) := (one_le_div hDN0).mpr hDN.2
  apply Finset.sum_le_sum
  intro E hE
  have hEdiv := (mem_idealDivisors hD0).mp hE
  have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hEdiv
  have hEN : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  rw [compact_descendant_restrict]
  have hh := hrec ε hε (M / (Ideal.absNorm E : ℝ)) (N / (Ideal.absNorm D : ℝ))
    (div_pos hM hEN) hNshort (quotientColumn D cols) (quotientColumn_injective D cols hinj)
    (fun j => ⟨quotientColumn_admissible D cols hc j, cubic_quotient_in_shell D cols hc N hcols j⟩)
    (quotientCoefficient D cols a (idealGenerator E))
  rw [quotientCoefficient_energy] at hh
  convert (preTransparency := .instances) hh using 1
  dsimp only [frequencyCost]
  ring

theorem common_factor_uniform_cost {n : Type*} [Fintype n]
    (C ε U M N : ℝ) (hε : 0 < ε) (hU : 0 ≤ U) (hN : 0 ≤ N)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hnorm : ∀ j, (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ)
    (hcost : ∀ D ∈ gcdPool cols, ∀ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U) :
    (∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
      frequencyCost C ε hε (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) *
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) ≤
      U*(DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2 := by
  have he := descended_energy_small_power ε hε cols hc N hN hnorm a
  have hsub := gcdPool_subset_columnDivisorPool cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hc j).2)
  calc
    _ ≤ ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        U * ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2 := by
      apply Finset.sum_le_sum
      intro D hD
      apply Finset.sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_right (hcost D hD E hE) (by positivity)
    _ = U*(∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by
      simp only [Finset.mul_sum]
    _ ≤ U*(∑ D ∈ columnDivisorPool cols, ∑ E ∈ idealDivisors D,
        ∑ j, ‖descendedCoefficient D cols a (idealGenerator E) j‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hU
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun D hD hnot => by positivity)
    _ ≤ U*((DivisorBlockCauchy.divisorConstant ε hε*N^ε)^2*∑ j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left he hU
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.DescendantBounds
namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma descendant_unit_scale_le (M N D E : ℝ) (hM : 0 ≤ M) (hN : 0 < N)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hDN : D ≤ N) :
    (M/E)*(2/(N/D)) ≤ 2*M := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hY : 1 ≤ N/D := (one_le_div hD0).mpr hDN
  have hr : 2/(N/D) ≤ 2 := div_le_self (by norm_num) hY
  calc
    _ ≤ M*2 := mul_le_mul (div_le_self hM hE) hr (by positivity) hM
    _ = _ := mul_comm _ _

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CostGrowth
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open SecondPassArithmetic EisensteinSchwartzPoisson SevenEighths.CubicDyadicDecay
noncomputable section

theorem frequencyCost_descendant_of_bound (C ε A δ ξ M N d e : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hα3 : 1/3+δ < 3) (hβ3 : ξ+δ < 3)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d) (hdN : d ≤ N)
    (hb : frequencyCost C ε hε (M/e) (N/d) ≤
      ((M/e)*(2/(N/d)))*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A)*(N/d)^ε*
        ((N/d)^(3*δ)*(M/e)^(-δ) *
          (decayConstant (1/3+δ)*((M/e)*(N/d))^(2/3 : ℝ) +
            decayConstant (ξ+δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)))) :
    frequencyCost C ε hε (M/e) (N/d) ≤
      2*M*‖paperRadialFourier rowMajorant 0‖ +
      (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A)*N^ε*
        (N^(3*δ)*M^(-δ) *
          (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
            decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1))) := by
  have hd : 1 ≤ d := he.trans hed
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hp := (decayConstant_pos (1/3+δ) (by linarith) hα3).le
  have hq := (decayConstant_pos (ξ+δ) (by linarith) hβ3).le
  have henv := poisson_envelope_descendant_le M N e d δ ξ
    (decayConstant (1/3+δ)) (decayConstant (ξ+δ)) hM hN he hed hδ hξ hp hq
  have hny : (N/d)^ε ≤ N^ε := Real.rpow_le_rpow (by positivity) (div_le_self hN.le hd) hε.le
  have hfac : 0 ≤ 2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A := by
    have hp := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    positivity
  apply hb.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (descendant_unit_scale_le M N d e hM.le hN hd he hdN) (norm_nonneg _)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hny hfac
    · exact henv
    · positivity
    · positivity

lemma poisson_envelope_absorb (M N δ ε ξ H Z P Q : ℝ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    2*M*Z + H*N^ε*(N^(3*δ)*M^(-δ)*
      (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1))) ≤
        (2*Z+H*(P+Q))*N^(3*δ+ε)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let X := (M*N)^(2/3 : ℝ)
  let Y := M^(1-ξ)*N^(2*ξ-1)
  let S := M+X+Y
  have hX : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hshape : P*X+Q*Y ≤ (P+Q)*S := by
    dsimp only [S]
    nlinarith [mul_nonneg hP hM0.le, mul_nonneg hQ hM0.le, mul_nonneg hP hY, mul_nonneg hQ hX]
  have hsmall : M^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM (by linarith)
  have hloss : 1 ≤ N^(3*δ+ε) := Real.one_le_rpow hN (by positivity)
  have hunit : 2*M*Z ≤ 2*Z*N^(3*δ+ε)*S := by
    have hmS : M ≤ S := by dsimp [S]; linarith
    calc
      _ = 2*Z*M := by ring
      _ ≤ 2*Z*S := mul_le_mul_of_nonneg_left hmS (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*Z) hS) (sub_nonneg.mpr hloss)]
  have htail : H*N^ε*(N^(3*δ)*M^(-δ)*(P*X+Q*Y)) ≤
      H*(P+Q)*N^(3*δ+ε)*S := by
    have hs : M^(-δ)*(P*X+Q*Y) ≤ (P+Q)*S :=
      (mul_le_of_le_one_left (by positivity) hsmall).trans hshape
    have hpow : N^ε*N^(3*δ) = N^(3*δ+ε) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      _ = H*(N^ε*N^(3*δ))*(M^(-δ)*(P*X+Q*Y)) := by ring
      _ ≤ H*(N^ε*N^(3*δ))*((P+Q)*S) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by rw [hpow]; ring
  have hh := add_le_add hunit htail
  convert (preTransparency := .instances) hh using 1 <;> dsimp only [S,X,Y] <;> ring

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.AnnularImprovement
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open IdealMobiusDivisorSum SecondPassArithmetic EisensteinSchwartzPoisson
open SevenEighths.CubicDyadicDecay
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem HasCubicExponent.annular_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (M N : ℝ), 1 ≤ M → 1 ≤ N → ∀ (cols : n → Ideal O), Function.Injective cols →
      (∀ j, Admissible (cols j)) →
      (∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      ∀ (a : n → ℂ) (R : Finset O),
        (∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) →
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z*a j‖^2) ≤
          K*N^(6*θ)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1))*∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hcf⟩ := cubic_common_factor_frequency_bound
  obtain ⟨A,hA,hfb⟩ := h.frequencyCost_bound hξ hξ2 θ hθ hθsmall
  let Z := ‖paperRadialFourier rowMajorant 0‖
  let P := decayConstant (1/3+θ)
  let Q := decayConstant (ξ+θ)
  let H := 2*C*IdealCoprimeSieveOperator.supportConstant θ hθ*A
  let V := 1+2*Z+H*(P+Q)
  let Dv := DivisorBlockCauchy.divisorConstant θ hθ
  have hZ : 0 ≤ Z := norm_nonneg _
  have hP : 0 ≤ P := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hQ : 0 ≤ Q := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hH : 0 ≤ H := by
    dsimp [H]
    have hs := (IdealCoprimeSieveOperator.supportConstant_pos θ hθ).le
    positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hDv : 0 < Dv := DivisorBlockCauchy.divisorConstant_pos θ hθ
  refine ⟨V*Dv^2, by positivity, ?_⟩
  intro n _ _ M N hM hN cols hinj hc hcols a R hR
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let U := V*N^(4*θ)*S
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcost (D : Ideal O) (hD : D ∈ gcdPool cols) (E : Ideal O) (hE : E ∈ idealDivisors D) :
      frequencyCost C θ hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U := by
    have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
    have hD0 := gcdPool_ne_zero cols hc0 D hD
    have hDE := (mem_idealDivisors hD0).mp hE
    have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hDE
    have he1 : 1 ≤ (Ideal.absNorm E : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
    have hed : (Ideal.absNorm E : ℝ) ≤ (Ideal.absNorm D : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
        (map_dvd Ideal.absNorm hDE)
    have hdN := (columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D
      (gcdPool_subset_columnDivisorPool cols hc0 hD)).2
    have hd0 : 0 < (Ideal.absNorm D : ℝ) := by linarith
    have he0 : 0 < (Ideal.absNorm E : ℝ) := by linarith
    have hh := hfb C θ hC hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ))
      (div_pos hM0 he0) ((one_le_div hd0).mpr hdN)
    have hd := frequencyCost_descendant_of_bound C θ A θ ξ M N
      (Ideal.absNorm D) (Ideal.absNorm E) hC hθ hA.le hθ.le (by linarith)
      (by linarith) (by linarith) hM0 hN0 he1 hed hdN hh
    have hb := poisson_envelope_absorb M N θ θ ξ H Z P Q hM hN hθ.le hθ.le hH hZ hP hQ
    have hx : 3*θ+θ = 4*θ := by ring
    rw [hx] at hb
    apply (hd.trans hb).trans
    change (2*Z+H*(P+Q))*N^(4*θ)*S ≤ V*N^(4*θ)*S
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [V]; linarith) (Real.rpow_nonneg hN0.le _)) hS
  have henergy := (hcf θ hθ M N hM0 cols hinj hc hcols a R hR).trans
    (common_factor_uniform_cost C θ U M N hθ hU hN0.le cols hc (fun j => (hcols j).2) a hcost)
  have hp : N^(4*θ)*(N^θ)^2 = N^(6*θ) := by
    rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  calc
    _ ≤ U*(Dv*N^θ)^2*∑ j, ‖a j‖^2 := henergy
    _ = (V*Dv^2)*(N^(4*θ)*(N^θ)^2)*S*∑ j, ‖a j‖^2 := by dsimp [U]; ring
    _ = _ := by rw [hp]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FullImprovement
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalQuadraticSieve (columnDyadicLength)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma improved_shape_shell (M N Y ξ : ℝ) (hM : 0 < M) (hN : 0 < N) (hY : 0 ≤ Y)
    (hYN : Y ≤ 2*N) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) :
    M+(M*Y)^(2/3 : ℝ)+M^(1-ξ)*Y^(2*ξ-1) ≤
      8*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  have hp : (2:ℝ)^(2/3 : ℝ) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (2/3 : ℝ)≤3)
    norm_num at hh ⊢
    exact hh
  have hq : (2:ℝ)^(2*ξ-1) ≤ 8 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 2*ξ-1 ≤ 3 by linarith)
    norm_num at hh
    exact hh
  have hcross := Real.rpow_le_rpow (mul_nonneg hM.le hY)
    (mul_le_mul_of_nonneg_left hYN hM.le) (by norm_num : (0:ℝ)≤2/3)
  have hsec := Real.rpow_le_rpow hY hYN (show 0 ≤ 2*ξ-1 by linarith)
  rw [show M*(2*N) = 2*(M*N) by ring, Real.mul_rpow (by norm_num) (mul_pos hM hN).le] at hcross
  rw [Real.mul_rpow (by norm_num) hN.le] at hsec
  have hx := (hcross.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (mul_pos hM hN).le _)))
  have hy := mul_le_mul_of_nonneg_left
    (hsec.trans (mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hN.le _)))
      (Real.rpow_nonneg hM.le (1-ξ))
  nlinarith

lemma improved_loss_shell (N Y θ : ℝ) (hN : 0 ≤ N) (hY : 0 ≤ Y) (hYN : Y ≤ 2*N)
    (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1/2) : Y^(6*θ) ≤ 8*N^(6*θ) := by
  have hh := Real.rpow_le_rpow hY hYN (show 0 ≤ 6*θ by positivity)
  rw [Real.mul_rpow (by norm_num) hN] at hh
  have hp : (2:ℝ)^(6*θ) ≤ 8 := by
    have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 6*θ ≤ 3 by linarith)
    norm_num at he
    exact he
  exact hh.trans (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN _))

theorem HasCubicExponent.full_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*N^(7*θ)*
        (M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)) := by
  obtain ⟨K,hK,hb⟩ := h.annular_improved hξ hξ2 θ hθ hθsmall
  let D : ℝ := 2+1/(θ*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    positivity
  refine ⟨64*K*D, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let cols : idealRange N → Ideal O := fun j => j.val
  have hc (j : idealRange N) : Admissible (cols j) := (mem_idealRange.mp j.property).1
  have hn (j : idealRange N) : (Ideal.absNorm (cols j) : ℝ) ≤ N := (mem_idealRange.mp j.property).2
  let R := elementRange M
  have hR (z : O) (hz : z ∈ R) : (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    ((mem_elementRange M z).mp hz).2
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  have hsector (l : Fin (columnDyadicLength N + 1)) :
      (∑ z ∈ R, ‖∑ j : CubicColumnShell cols N l, cubicRow (cols j.val) z*a j.val‖^2) ≤
        (64*K*N^(6*θ)*S)*∑ j : CubicColumnShell cols N l, ‖a j.val‖^2 := by
    by_cases hne : Nonempty (CubicColumnShell cols N l)
    · obtain ⟨j₀⟩ := hne
      have hYN := cubicColumnShell_scale_le cols N hc hn l j₀
      have hY1 : 1 ≤ (2:ℝ)^l.val := one_le_pow₀ (by norm_num)
      have hs := hb M ((2:ℝ)^l.val) hM hY1
        (fun j : CubicColumnShell cols N l => cols j.val)
        (fun j k he => Subtype.ext (Subtype.ext he)) (fun j => hc j.val)
        (fun j => cubicColumnShell_bounds cols N hc hn l j)
        (fun j => a j.val) R hR
      have hl := improved_loss_shell N ((2:ℝ)^l.val) θ hN0.le (by positivity) hYN hθ.le hθsmall.le
      have ht := improved_shape_shell M N ((2:ℝ)^l.val) ξ hM0 hN0 (by positivity) hYN
        (by linarith) hξ2
      apply hs.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hl hK.le) ht (by positivity) (by positivity)
      convert (preTransparency := .instances) hh using 1; dsimp only [S]; ring
    · let : IsEmpty (CubicColumnShell cols N l) := not_nonempty_iff.mp hne
      simp
  have hsum := cubic_energy_column_shells cols N a R
  have hle := Finset.sum_le_sum (s := Finset.univ) (fun l hl => hsector l)
  rw [← Finset.mul_sum, cubicColumnShell_energy cols N a] at hle
  have he := hsum.trans (mul_le_mul_of_nonneg_left hle (by positivity))
  have hlog := CanonicalQuadraticSieve.columnDyadicLength_small_power θ hθ N hN
  have he' := he.trans (mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ (64*K*N^(6*θ)*S)*∑ j, ‖a j‖^2 by positivity))
  have hp : N^θ*N^(6*θ) = N^(7*θ) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val*a j‖^2) ≤ _
  apply he'.trans_eq
  calc
    _ = (64*K*D)*(N^θ*N^(6*θ))*S*∑ j, ‖a j‖^2 := by dsimp [D]; ring
    _ = _ := by rw [hp]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ExponentImprovement
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

lemma enlargement_bounds (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    1 ≤ enlargementExponent ξ ∧ enlargementExponent ξ ≤ SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 0 < 3*ξ-1 := by linarith
  constructor
  · unfold enlargementExponent
    apply (one_le_div hd).mpr
    linarith
  · unfold enlargementExponent SevenEighths.HeathBrownIteration.step
    exact div_le_div_of_nonneg_right (by linarith) hd.le

lemma enlargement_cross_identity (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    (enlargementExponent ξ+1)*(2/3 : ℝ) = SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 3*ξ-1 ≠ 0 := by linarith
  unfold enlargementExponent SevenEighths.HeathBrownIteration.step
  apply (eq_div_iff hd).mpr
  have hc := div_mul_cancel₀ (6*ξ-5) hd
  nlinarith [hc]

lemma enlargement_secondary_identity (ξ : ℝ) (hξ : (4/3 : ℝ) ≤ ξ) :
    enlargementExponent ξ*(1-ξ)+(2*ξ-1) = SevenEighths.HeathBrownIteration.step ξ := by
  have hd : 3*ξ-1 ≠ 0 := by linarith
  unfold enlargementExponent SevenEighths.HeathBrownIteration.step
  apply (eq_div_iff hd).mpr
  have hc := div_mul_cancel₀ (6*ξ-5) hd
  nlinarith [hc]

theorem enlarged_improved_shape (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    let T := max M (N^(enlargementExponent ξ))
    T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤
      3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ)) := by
  let α := enlargementExponent ξ
  let β := SevenEighths.HeathBrownIteration.step ξ
  let T := max M (N^α)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hαβ : α ≤ β := (enlargement_bounds ξ hξ).2
  have hNb : 0 ≤ N^β := Real.rpow_nonneg hN0.le _
  have hcross : 0 ≤ (M*N)^(2/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have ht : T ≤ M+N^β := by
    apply max_le
    · exact le_add_of_nonneg_right hNb
    · exact (Real.rpow_le_rpow_of_exponent_le hN hαβ).trans (le_add_of_nonneg_left hM0.le)
  have hnx : (N^α*N)^(2/3 : ℝ) = N^β := by
    conv_lhs => arg 1; arg 2; rw [← Real.rpow_one N]
    rw [← Real.rpow_add hN0, ← Real.rpow_mul hN0.le, enlargement_cross_identity ξ hξ]
  have htc : (T*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ)+N^β := by
    by_cases hm : M ≤ N^α
    · dsimp only [T]
      rw [max_eq_right hm, hnx]
      exact le_add_of_nonneg_left hcross
    · dsimp only [T]
      rw [max_eq_left (le_of_not_ge hm)]
      exact le_add_of_nonneg_right hNb
  have hts : T^(1-ξ)*N^(2*ξ-1) ≤ N^β := by
    have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 α)
      (le_max_right M (N^α)) (show 1-ξ ≤ 0 by linarith)
    calc
      _ ≤ (N^α)^(1-ξ)*N^(2*ξ-1) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hN0.le _)
      _ = N^β := by
        rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, enlargement_secondary_identity ξ hξ]
  change T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1) ≤ 3*(M+N^β+(M*N)^(2/3 : ℝ))
  linarith

theorem HasCubicExponent.improve_oai {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) < ξ) (hξ2 : ξ ≤ 2) :
    HasCubicExponent (SevenEighths.HeathBrownIteration.step ξ) := by
  intro ε hε
  let θ := min (ε/14) (1/4 : ℝ)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθsmall : θ < 1/2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hθε : 7*θ ≤ ε := by
    have hh : θ ≤ ε/14 := min_le_left _ _
    linarith
  obtain ⟨C,hC,hb⟩ := h.full_improved hξ.le hξ2 θ hθ hθsmall
  refine ⟨3*C, by positivity, ?_⟩
  intro M N hM hN
  let T := max M (N^(enlargementExponent ξ))
  have hT : 1 ≤ T := hM.trans (le_max_left _ _)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hp : N^(7*θ) ≤ (M*N)^ε :=
    (Real.rpow_le_rpow_of_exponent_le hN hθε).trans
      (Real.rpow_le_rpow hN0.le (by nlinarith) hε.le)
  have ht := enlarged_improved_shape M N ξ hM hN hξ.le
  have hshape : 0 ≤ M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ) := by positivity
  calc
    _ ≤ sieveNorm T N := sieveNorm_mono (le_max_left _ _) le_rfl
    _ ≤ elementSieveNorm T N := sieveNorm_le_elementSieveNorm T N
    _ ≤ C*N^(7*θ)*(T+(T*N)^(2/3 : ℝ)+T^(1-ξ)*N^(2*ξ-1)) := hb T N hT hN
    _ ≤ C*N^(7*θ)*(3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ C*(M*N)^ε*(3*(M+N^(SevenEighths.HeathBrownIteration.step ξ)+(M*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (by positivity)
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CubicSieve.HasCubicExponent.improve_oai := @OAI.SevenEighths.CubicSieve.HasCubicExponent.improve_oai
