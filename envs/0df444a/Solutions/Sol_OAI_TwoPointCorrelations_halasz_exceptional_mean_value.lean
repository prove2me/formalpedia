-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_exceptional_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:36:22.69159+00:00
-- url     : https://prove2.me/submissions/645bdb02-3b21-42ab-b83b-c10908e5eb40

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_double_convolution_exception

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.AlignedPrimeCongruence
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped _root_.BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]



omit [DecidableEq α] [LinearOrder ι] in
@[simp] theorem mem_survivors {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α} :
    x ∈ survivors C P bad ↔ x ∈ C ∧ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [survivors]











instance decidableResidueBad (a : ℕ → ℕ) (p n : ℕ) : Decidable (residueBad a p n) :=
  inferInstanceAs (Decidable (n % p = a p % p))






end NumberTheoryLean.SievePartition

end

section

namespace NumberTheoryLean.SieveTree

open scoped _root_.BigOperators

variable {V : Type*} [DecidableEq V]








end NumberTheoryLean.SieveTree

end

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped _root_.BigOperators
open _root_.OAI.Erdos970.NumberTheoryLean.SievePartition

















end NumberTheoryLean.ResidueSieveTree

end

section

namespace ErdosInverseCounts
open _root_.OAI.Erdos970.NumberTheoryLean _root_.OAI.Erdos970.NumberTheoryLean.SievePartition









end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression






end ErdosAlignedProgression

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.LargePrimeDeletion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LargePrimeDeletion

open scoped _root_.BigOperators






@[simp] theorem mem_deletionCell {C : Finset ℕ} {a : ℤ} {q i : ℕ} :
    i ∈ deletionCell C a q ↔ i ∈ C ∧ (q : ℤ) ∣ a + i := by
  classical
  simp [deletionCell]







@[simp] theorem mem_cutoffSurvivors {Y z i : ℕ} {residue : ℕ → ℕ} :
    i ∈ cutoffSurvivors Y z residue ↔
      i < Y ∧ ∀ p, p.Prime → p ≤ z → i % p ≠ residue p % p := by
  classical
  simp only [cutoffSurvivors, SievePartition.mem_survivors, Finset.mem_range,
    mem_cutoffPrimes, SievePartition.residueBad]
  tauto





@[simp] theorem mem_coprimeOffsets {Y n i : ℕ} {a : ℤ} :
    i ∈ coprimeOffsets Y n a ↔ i < Y ∧ (a + i).natAbs.Coprime n := by
  classical
  simp [coprimeOffsets]









end NumberTheoryLean.LargePrimeDeletion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Sieve.IntervalBoundingSieve
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.IntervalBoundingSieve

open scoped _root_.BigOperators
















@[simp] theorem cutoffProduct_primeFactors (z : ℕ) :
    (cutoffProduct z).primeFactors = LargePrimeDeletion.cutoffPrimes z := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1


end NumberTheoryLean.IntervalBoundingSieve

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BonferroniDensity

open scoped _root_.BigOperators


@[simp] theorem elementarySum_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    elementarySum P g 0 = 1 := by simp [elementarySum]











@[simp] theorem densityPolynomial_zero (P : Finset ℕ) (g : ℕ → ℝ) :
    densityPolynomial 0 P g = 1 := by simp [densityPolynomial]









end NumberTheoryLean.BonferroniDensity

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.DisjointBlockExpansion
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DisjointBlockExpansion

open scoped _root_.BigOperators


@[simp] theorem mem_blockChoices {B : Finset ℕ} {blocks : ℕ → Finset ℕ}
    {choice : ∀ j ∈ B, Finset ℕ} :
    choice ∈ blockChoices B blocks ↔ ∀ j (hj : j ∈ B), choice j hj ⊆ blocks j := by
  classical
  simp only [blockChoices, Finset.mem_pi, Finset.mem_powerset]






















@[simp] theorem truncatedCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    truncatedCoefficient m T ≠ 0 ↔ T.card ≤ m := by
  unfold truncatedCoefficient
  split_ifs <;> simp_all

@[simp] theorem layerCoefficient_ne_zero_iff (m : ℕ) (T : Finset ℕ) :
    layerCoefficient m T ≠ 0 ↔ T.card = m := by
  unfold layerCoefficient
  split_ifs <;> simp_all


























end NumberTheoryLean.DisjointBlockExpansion

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Estimates.SquarefreeHarmonic
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SelbergOptimization

open scoped _root_.BigOperators _root_.ArithmeticFunction.Moebius




























end NumberTheoryLean.SelbergOptimization

end

section

namespace NumberTheoryLean.SquarefreeHarmonic

open scoped _root_.BigOperators


@[simp] theorem mem_squarefreeUpTo {R d : ℕ} :
    d ∈ squarefreeUpTo R ↔ 1 ≤ d ∧ d ≤ R ∧ Squarefree d := by
  classical
  simp only [squarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto
















end NumberTheoryLean.SquarefreeHarmonic

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.PrimeDensityBlocks
namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PrimeDensityBlocks

open scoped _root_.BigOperators


@[simp] theorem mem_dyadicPrimes {n p : ℕ} :
    p ∈ dyadicPrimes n ↔ n ≤ p ∧ p < 2 * n ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto






@[simp] theorem mem_geometricPrimes {j p : ℕ} :
    p ∈ geometricPrimes j ↔ 2 ^ (2 ^ j) ≤ p ∧ p < 2 ^ (2 ^ (j + 1)) ∧ p.Prime := by
  simp only [geometricPrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto





















end NumberTheoryLean.PrimeDensityBlocks

end

end Erdos970

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MertensScale
namespace OAI

/-! The exact classical reciprocal-prime input and its sole required scale.

Published source: J. B. Rosser and L. Schoenfeld, *Approximate formulas for
some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94,
Theorem 5, (3.17)–(3.18), bounded-error consequence of Mertens' second
theorem. DOI: https://doi.org/10.1215/ijm/1255631807.
The formal proof uses the bounded-error statement
`RS_prime.mertens_second_theorem'`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma sievePrimesUpTo_prime (y : ℝ) (p : ℕ) (hp : p ∈ sievePrimesUpTo y) :
    Nat.Prime p := (mem_filter.mp hp).2

lemma sievePrimesUpTo_le (y : ℝ) (hy : 0 ≤ y) (p : ℕ)
    (hp : p ∈ sievePrimesUpTo y) : (p : ℝ) ≤ y := by
  exact (Nat.le_floor_iff hy).mp (mem_Iic.mp (mem_filter.mp hp).1)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogConvolution
namespace OAI

/-! Exact logarithmic identities at the start of Halász's method. The
multiplicativity hypothesis here is complete multiplicativity on positive
arguments, as supplied by the corrected MRT reduction. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem halasz_logarithmic_convolution (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (n : ℕ) :
    f n * (Real.log (n : ℝ) : ℂ) =
      ∑ d ∈ n.divisors,
        (ArithmeticFunction.vonMangoldt d : ℂ) * f d * f (n / d) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hterm (d : ℕ) (hd : d ∈ n.divisors) :
      (ArithmeticFunction.vonMangoldt d : ℂ) * f d * f (n / d) =
        (ArithmeticFunction.vonMangoldt d : ℂ) * f n := by
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
    have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) hdpos
    rw [mul_assoc, ← hf d (n / d) hdpos hquot, Nat.mul_div_cancel' hdn]
  calc
    _ = (∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d : ℂ)) * f n := by
      rw [← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]
      ring
    _ = _ := by rw [sum_mul]; exact sum_congr rfl hterm |>.symm



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszHyperbola
namespace OAI

/-! The exact finite hyperbola decomposition underlying Halász's
logarithmic mean-value identity. All endpoints are positive integers. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem halasz_sum_divisorsAntidiagonal (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2) =
      ∑ p ∈ halaszHyperbola N, F p.1 p.2 := by
  rw [sum_sigma' (Icc 1 N) (fun n => n.divisorsAntidiagonal) (fun _ p => F p.1 p.2)]
  apply sum_bij (fun x _ => x.2)
  · intro x hx
    obtain ⟨hn, hp⟩ := mem_sigma.mp hx
    obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hpos : 0 < x.2.1 * x.2.2 := by rw [hmul]; exact (mem_Icc.mp hn).1
    have h₁ : 1 ≤ x.2.1 := Nat.pos_of_mul_pos_right hpos
    have h₂ : 1 ≤ x.2.2 := Nat.pos_of_mul_pos_left hpos
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨h₁, ?_⟩, mem_Icc.mpr ⟨h₂, ?_⟩⟩, ?_⟩
    · calc
        _ ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_right _ h₂
        _ = x.1 := hmul
        _ ≤ N := (mem_Icc.mp hn).2
    · calc
        _ ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_left _ h₁
        _ = x.1 := hmul
        _ ≤ N := (mem_Icc.mp hn).2
    · exact hmul ▸ (mem_Icc.mp hn).2
  · intro x hx y hy hxy
    obtain ⟨_, hpx⟩ := mem_sigma.mp hx
    obtain ⟨_, hpy⟩ := mem_sigma.mp hy
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp hpx).1
    have hyprod := (Nat.mem_divisorsAntidiagonal.mp hpy).1
    have hn : x.1 = y.1 := by rw [← hxprod, ← hyprod, hxy]
    cases x
    cases y
    simp_all
  · intro p hp
    obtain ⟨hp, hprod⟩ := mem_filter.mp hp
    obtain ⟨h₁, h₂⟩ := mem_product.mp hp
    have hpos : 0 < p.1 * p.2 := Nat.mul_pos (mem_Icc.mp h₁).1 (mem_Icc.mp h₂).1
    refine ⟨⟨p.1 * p.2, p⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨hpos, hprod⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt hpos⟩⟩, rfl⟩
  · intro x _
    rfl

theorem halasz_logarithmic_sum (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) =
      ∑ p ∈ halaszHyperbola N,
        (ArithmeticFunction.vonMangoldt p.1 : ℂ) * f p.1 * f p.2 := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.vonMangoldt p.1 : ℂ) * f p.1 * f p.2 := by
      apply sum_congr rfl
      intro n _
      rw [Nat.sum_divisorsAntidiagonal (fun a b =>
        (ArithmeticFunction.vonMangoldt a : ℂ) * f a * f b)]
      exact halasz_logarithmic_convolution f hf n
    _ = _ := halasz_sum_divisorsAntidiagonal
      (fun a b => (ArithmeticFunction.vonMangoldt a : ℂ) * f a * f b) N

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszHyperbolaRows
namespace OAI

/-! Row decomposition of the finite positive hyperbola. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem halasz_hyperbola_rows (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ p ∈ halaszHyperbola N, F p.1 p.2) =
      ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d m := by
  classical
  simp only [halaszHyperbola, sum_filter, Finset.product_eq_sprod]
  rw [sum_product (Icc 1 N) (Icc 1 N)
    (fun p : ℕ × ℕ => if p.1 * p.2 ≤ N then F p.1 p.2 else 0)]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter]
  apply sum_congr ?_ (fun _ _ => rfl)
  ext m
  have hdpos := (mem_Icc.mp hd).1
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hm, _⟩, hprod⟩
    refine ⟨hm, (Nat.le_div_iff_mul_le hdpos).mpr ?_⟩
    simpa only [Nat.mul_comm] using hprod
  · rintro ⟨hm, hquot⟩
    refine ⟨⟨hm, hquot.trans (Nat.div_le_self N d)⟩, ?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hquot

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogMean
namespace OAI

/-! Recover an ordinary mean from its logarithmically weighted sum.
The absolute error is at most N for a one-bounded sequence. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_sum_log_factorial (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log (n : ℝ)) = Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

lemma halasz_sum_log_gap (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (Real.log (N : ℝ) - Real.log (n : ℝ))) ≤ N := by
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc, halasz_sum_log_factorial]
  have hst := Stirling.le_log_factorial_stirling (Nat.ne_zero_of_lt hN)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.two_le_pi])
  simp only [Nat.add_sub_cancel] at *
  linarith

lemma halasz_logarithmic_sum_error (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Icc 1 N, f n) * (Real.log (N : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)‖ ≤ (N : ℝ) := by
  let S := ∑ n ∈ Icc 1 N, f n
  let W := ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)
  have he : S * (Real.log (N : ℝ) : ℂ) - W =
      ∑ n ∈ Icc 1 N, f n * ((Real.log (N : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ) := by
    dsimp [S, W]
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum ?_).trans (halasz_sum_log_gap N hN)
  intro n hn
  have hn' := mem_Icc.mp hn
  have hlog : 0 ≤ Real.log (N : ℝ) - Real.log (n : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast hn'.2))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact mul_le_of_le_one_left hlog (hf n hn'.1)

theorem halasz_logarithmic_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)‖ + N := by
  let S := ∑ n ∈ Icc 1 N, f n
  let W := ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)
  have hgap := halasz_logarithmic_sum_error f hf N hN
  have hh := norm_add_le W (S * (Real.log (N : ℝ) : ℂ) - W)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hnorm : ‖S * (Real.log (N : ℝ) : ℂ)‖ = Real.log (N : ℝ) * ‖S‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN, mul_comm]
  rw [add_sub_cancel, hnorm] at hh
  exact hh.trans (add_le_add le_rfl hgap)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowers
namespace OAI

/-! The total reciprocal contribution of higher prime powers is finite.
The modulus-one specialization of the prime-power series bounds
the finite hyperbola error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszPrimePowerWeight_nonneg (n : ℕ) : 0 ≤ halaszPrimePowerWeight n := by
  unfold halaszPrimePowerWeight
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma halaszPrimePowerWeight_summable :
    Summable (fun n : ℕ => halaszPrimePowerWeight n / (n : ℝ)) := by
  have hh := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
    (0 : ZMod 1)
  convert (preTransparency := .instances) hh using 1
  funext n
  simp only [halaszPrimePowerWeight, ArithmeticFunction.vonMangoldt.residueClass]
  have he : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [he]


lemma halaszPrimePowerConstant_nonneg : 0 ≤ halaszPrimePowerConstant :=
  tsum_nonneg (fun n => div_nonneg (halaszPrimePowerWeight_nonneg n) (Nat.cast_nonneg _))

lemma halasz_bounded_prefix_norm (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, f n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) :=
      sum_le_sum (fun n hn => hf n (mem_Icc.mp hn).1)
    _ = _ := by simp

/-- Discarding all higher prime powers in the logarithmic hyperbola incurs
at most an absolute constant times its outer cutoff. -/
theorem halasz_prime_power_error (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    ‖∑ d ∈ Icc 1 N, (halaszPrimePowerWeight d : ℂ) * f d *
      (∑ m ∈ Icc 1 (N / d), f m)‖ ≤ (N : ℝ) * halaszPrimePowerConstant := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (N : ℝ) * (halaszPrimePowerWeight d / (d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hdpos := (mem_Icc.mp hd).1
      have hdr : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hw := halaszPrimePowerWeight_nonneg d
      have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
        apply (le_div_iff₀ hdr).mpr
        exact_mod_cast Nat.div_mul_le_self N d
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      calc
        _ ≤ halaszPrimePowerWeight d * 1 * ((N / d : ℕ) : ℝ) := by
          gcongr
          · exact hf d hdpos
          · exact halasz_bounded_prefix_norm f hf (N / d)
        _ ≤ halaszPrimePowerWeight d * ((N : ℝ) / (d : ℝ)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hw
        _ = _ := by ring
    _ = (N : ℝ) * ∑ d ∈ Icc 1 N, halaszPrimePowerWeight d / (d : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact halaszPrimePowerWeight_summable.sum_le_tsum _
        (fun d _ => div_nonneg (halaszPrimePowerWeight_nonneg d) (Nat.cast_nonneg _))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeConvolution
namespace OAI

/-! Prime-only convolution and its explicit O(N) error. This is the first
step of the Granville--Harper--Soundararajan double-convolution argument. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_log_sum_rows (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) =
      ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d : ℂ) * f d *
        (∑ m ∈ Icc 1 (N / d), f m) := by
  rw [halasz_logarithmic_sum f hf N, halasz_hyperbola_rows
    (fun a b => (ArithmeticFunction.vonMangoldt a : ℂ) * f a * f b) N]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]

lemma halasz_prime_convolution_difference (f : ℕ → ℂ)
    (hf : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N =
      ∑ d ∈ Icc 1 N, (halaszPrimePowerWeight d : ℂ) * f d *
        (∑ m ∈ Icc 1 (N / d), f m) := by
  rw [halasz_log_sum_rows f hf N, halaszPrimeConvolution, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  by_cases hd : d.Prime
  · simp [hd, halaszPrimePowerWeight, ArithmeticFunction.vonMangoldt_apply_prime hd]
  · simp [hd, halaszPrimePowerWeight]

/-- The exact logarithmic sum differs from its prime-only convolution by
at most a constant times N, uniformly in the bounded multiplicative function. -/
theorem halasz_log_sum_prime_error (f : ℕ → ℂ) (hbound : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n) (N : ℕ) :
    ‖(∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N‖ ≤
      (N : ℝ) * halaszPrimePowerConstant := by
  rw [halasz_prime_convolution_difference f hmul N]
  exact halasz_prime_power_error f hbound N

/-- First Halasz reduction, with a uniform and completely proved error. -/
theorem halasz_prime_convolution_mean_bound (f : ℕ → ℂ) (hbound : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszPrimeConvolution f N‖ + (halaszPrimePowerConstant + 1) * (N : ℝ) := by
  have he := halasz_log_sum_prime_error f hbound hmul N
  have ht := norm_add_le (halaszPrimeConvolution f N)
    ((∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)) - halaszPrimeConvolution f N)
  rw [add_sub_cancel] at ht
  have hh := halasz_logarithmic_mean_bound f hbound N hN
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszInnerApproximation
namespace OAI

/-! A complex-valued approximation, not just a norm bound, permits a second
application of the prime convolution inside the first one. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_prime_log_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) :
    ‖(∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
      halaszPrimeConvolution f M‖ ≤ (halaszPrimePowerConstant + 1) * (M : ℝ) := by
  have he := halasz_logarithmic_sum_error f hf M hM
  have hp := halasz_log_sum_prime_error f hf hmul M
  have ht := norm_add_le
    ((∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 M, f n * (Real.log (n : ℝ) : ℂ))
    ((∑ n ∈ Icc 1 M, f n * (Real.log (n : ℝ) : ℂ)) -
      halaszPrimeConvolution f M)
  rw [sub_add_sub_cancel] at ht
  linarith



lemma halaszInnerErrorConstant_nonneg : 0 ≤ halaszInnerErrorConstant := by
  unfold halaszInnerErrorConstant
  have hC := halaszPrimePowerConstant_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- The logarithm may use the real cutoff, while the sum and convolution
retain the exact natural cutoff. Their rounding error is uniformly O(x). -/
lemma halasz_real_log_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) {x : ℝ} (hMx : (M : ℝ) ≤ x) (hxM : x ≤ 2 * M) :
    ‖(∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
      halaszPrimeConvolution f M‖ ≤ halaszInnerErrorConstant * x := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hx0 : 0 < x := hM0.trans_le hMx
  have hlog0 : 0 ≤ Real.log x - Real.log (M : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hM0 hMx)
  have hlog2 : Real.log x - Real.log (M : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_log hx0 hxM
    rw [Real.log_mul (by norm_num) hM0.ne'] at h
    linarith
  have he : (∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
      halaszPrimeConvolution f M =
      (∑ n ∈ Icc 1 M, f n) * ((Real.log x - Real.log (M : ℝ) : ℝ) : ℂ) +
      ((∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
        halaszPrimeConvolution f M) := by push_cast; ring
  rw [he]
  calc
    _ ≤ ‖(∑ n ∈ Icc 1 M, f n) * ((Real.log x - Real.log (M : ℝ) : ℝ) : ℂ)‖ +
        ‖(∑ n ∈ Icc 1 M, f n) * (Real.log (M : ℝ) : ℂ) -
          halaszPrimeConvolution f M‖ := norm_add_le _ _
    _ ≤ (M : ℝ) * Real.log 2 + (halaszPrimePowerConstant + 1) * M := by
      apply add_le_add _ (halasz_prime_log_approximation f hf hmul M hM)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
      exact mul_le_mul (halasz_bounded_prefix_norm f hf M) hlog2 hlog0 (Nat.cast_nonneg _)
    _ = halaszInnerErrorConstant * (M : ℝ) := by unfold halaszInnerErrorConstant; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMx halaszInnerErrorConstant_nonneg

lemma halasz_real_inner_approximation (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (M : ℕ) (hM : 1 ≤ M) {x : ℝ} (hx : 1 < x)
    (hMx : (M : ℝ) ≤ x) (hxM : x ≤ 2 * M) :
    ‖(∑ n ∈ Icc 1 M, f n) - halaszPrimeConvolution f M / (Real.log x : ℂ)‖ ≤
      halaszInnerErrorConstant * x / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hc : (Real.log x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlog
  have he : (∑ n ∈ Icc 1 M, f n) - halaszPrimeConvolution f M / (Real.log x : ℂ) =
      ((∑ n ∈ Icc 1 M, f n) * (Real.log x : ℂ) -
        halaszPrimeConvolution f M) / (Real.log x : ℂ) := by field_simp
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  exact div_le_div_of_nonneg_right (halasz_real_log_approximation f hf hmul M hM hMx hxM)
    hlog.le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
namespace OAI

/-! The finite Euler-product estimate needed in Halász's method.  The
pretentious-distance saving is obtained from the actual prime coefficients;
no mean-value theorem is assumed here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.ComplexConjugate

lemma mrt_local_euler_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 - z)⁻¹‖ ≤ Real.exp (z.re + ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hnz : 1 - z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one] at hz1
    exact lt_irrefl _ hz1
  have hi : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - ‖z‖)).mpr
    linarith
  have hrem : ‖Complex.log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hre : (Complex.log (1 - z)⁻¹).re ≤ z.re + ‖z‖ ^ 2 := by
    have h := (Complex.re_le_norm (Complex.log (1 - z)⁻¹ - z)).trans hrem
    rw [Complex.sub_re] at h
    linarith
  calc
    _ = Real.exp (Complex.log (1 - z)⁻¹).re := by
      rw [← Complex.norm_exp, Complex.exp_log (inv_ne_zero hnz)]
    _ ≤ _ := Real.exp_le_exp.mpr hre


lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _


lemma mrtPrimeEulerTerm_norm_le (b : ℕ → ℂ) (t : ℝ) {p : ℕ}
    (_hp : 0 < p) (hb : ‖b p‖ ≤ 1) :
    ‖mrtPrimeEulerTerm b t p‖ ≤ (1 : ℝ) / p := by
  rw [mrtPrimeEulerTerm, norm_div, norm_mul, norm_conj,
    mrtArchimedeanTwist_norm, mul_one, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg p)

lemma mrtPrimeEulerTerm_re (b : ℕ → ℂ) (t : ℝ) (p : ℕ) :
    (mrtPrimeEulerTerm b t p).re = (b p * conj (mrtArchimedeanTwist t p)).re / p := by
  change (b p * conj (mrtArchimedeanTwist t p) / ((p : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re]

/-- The finite Euler product retains the full pretentious-distance gain.
The remaining prime-square error is absolutely summable. -/
theorem mrt_finite_euler_distance_bound (b : ℕ → ℂ)
    (hb : ∀ n : ℕ, 0 < n → ‖b n‖ ≤ 1) (t : ℝ) (N : ℕ) :
    ‖∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm b t p)⁻¹‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance b (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  have hz (p : ℕ) (hp : p ∈ primesUpTo N) : ‖mrtPrimeEulerTerm b t p‖ ≤ 1 / 2 := by
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    exact (mrtPrimeEulerTerm_norm_le b t hprime.pos (hb p hprime.pos)).trans
      (one_div_le_one_div_of_le (by norm_num) hp2)
  have hs : (∑ p ∈ primesUpTo N,
      ((mrtPrimeEulerTerm b t p).re + (1 : ℝ) / (p : ℝ) ^ 2)) =
      (∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance b (mrtArchimedeanTwist t) N +
          ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2 := by
    rw [sum_add_distrib, squaredDistance, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro p _
    rw [mrtPrimeEulerTerm_re]
    ring
  rw [norm_prod, ← hs, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _
    exact norm_nonneg _
  · intro p hp
    apply (mrt_local_euler_bound (hz p hp)).trans
    apply Real.exp_le_exp.mpr
    apply add_le_add le_rfl
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ ≤ ((1 : ℝ) / p) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (mrtPrimeEulerTerm_norm_le b t hprime.pos
          (hb p hprime.pos)) 2
      _ = _ := by simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare
namespace OAI

/-! The normalized dyadic Dirichlet-polynomial mean-value estimate used in
corrected MRT Appendix A.  The coefficient bound is completely arbitrary. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open scoped _root_.BigOperators



lemma mrt_line_one_term (b : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term b (1 + (t : ℂ) * Complex.I) n =
      b n / (n : ℂ) * Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
    Complex.cpow_add _ _ hnC, Complex.cpow_neg_one,
    Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
  rw [div_eq_mul_inv, mul_assoc]
  congr 1
  congr 1
  push_cast
  ring_nf



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalRamare
namespace OAI

/-! Ramaré factorization on the actual typical-factorization set.  Removing
one selected prime band leaves exactly the remaining-band condition; the
prime-square correction and its bound are retained. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators






lemma mrt_LSeries_term_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  rw [LSeries.term_of_ne_zero (Nat.mul_pos hm hn).ne', LSeries.term_of_ne_zero hm.ne',
    LSeries.term_of_ne_zero hn.ne', hF m n hm hn, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, div_mul_div_comm]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothEuler
namespace OAI

/-! The finite-prime smooth Euler product on Re(s)=1.  Finite prime
support makes the series absolutely convergent even on this line; the
geometric local factors therefore give the actual analytic series to
which the pretentious-distance estimate applies. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.ComplexConjugate

lemma mrt_line_one_euler_term (F : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term F (1 + (t : ℂ) * Complex.I) n = mrtPrimeEulerTerm F t n := by
  have he : conj (mrtArchimedeanTwist t n) =
      Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
    rw [mrtArchimedeanTwist, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [mrt_line_one_term F hn t, mrtPrimeEulerTerm, he]
  ring

lemma mrt_LSeries_term_pow (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    LSeries.term F s (p ^ k) = (LSeries.term F s p) ^ k := by
  induction k with
  | zero => simp [LSeries.term, hF1]
  | succ k ih =>
    calc
      _ = LSeries.term F s (p ^ k * p) := by rw [pow_succ]
      _ = LSeries.term F s (p ^ k) * LSeries.term F s p :=
        mrt_LSeries_term_mul F hF s (pow_pos hp k) hp
      _ = _ := by rw [ih, pow_succ]

lemma mrt_LSeries_term_coprime_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (_h : m.Coprime n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  exact mrt_LSeries_term_mul F hF s (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

lemma mrt_prime_euler_norm_lt_one (F : ℕ → ℂ) (hF : OneBounded F)
    (t : ℝ) {p : ℕ} (hp : p.Prime) : ‖mrtPrimeEulerTerm F t p‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (1 : ℝ) / p := mrtPrimeEulerTerm_norm_le F t hp.pos (hF p hp.pos)
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    _ < 1 := by norm_num

/-- The actual smooth L-series is absolutely summable and equals its
finite Euler product on the boundary line `Re(s)=1`. -/
theorem mrt_smooth_euler_product (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) :
    Summable (fun n : Nat.smoothNumbers (N + 1) =>
      ‖LSeries.term F (1 + (t : ℂ) * Complex.I) n‖) ∧
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      LSeries.term F (1 + (t : ℂ) * Complex.I) n)
      (∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have h1 : LSeries.term F s 1 = 1 := by simp [LSeries.term, hF1]
  have hlocal (p : ℕ) (hp : p.Prime) (k : ℕ) :
      LSeries.term F s (p ^ k) = (mrtPrimeEulerTerm F t p) ^ k := by
    rw [mrt_LSeries_term_pow F hF1 hF s hp.pos k,
      mrt_line_one_euler_term F hp.ne_zero t]
  have hnorm : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖LSeries.term F s (p ^ k)‖) := by
    intro p hp
    simpa only [hlocal p hp, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg _)
        (mrt_prime_euler_norm_lt_one F hFb t hp))
  obtain ⟨hs, he⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 (fun {_ _} h => mrt_LSeries_term_coprime_mul F hF s h) hnorm (N + 1)
  have hprod : (∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, LSeries.term F s (p ^ k)) =
      ∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹ := by
    change (∏ p ∈ primesUpTo N, ∑' k : ℕ, LSeries.term F s (p ^ k)) = _
    apply prod_congr rfl
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ = ∑' k : ℕ, (mrtPrimeEulerTerm F t p) ^ k := tsum_congr (hlocal p hprime)
      _ = _ := (hasSum_geometric_of_norm_lt_one
        (mrt_prime_euler_norm_lt_one F hFb t hprime)).tsum_eq
  rw [hprod] at he
  exact ⟨hs, he⟩

/-- The distance saving applies to the analytic smooth series itself,
with the same finite prime-square error as its Euler product. -/
theorem mrt_smooth_euler_distance_bound (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) :
    ‖∑' n : Nat.smoothNumbers (N + 1), LSeries.term F (1 + (t : ℂ) * Complex.I) n‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [(mrt_smooth_euler_product F hF1 hF hFb N t).2.tsum_eq]
  exact mrt_finite_euler_distance_bound F hFb t N

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothSeries
namespace OAI

/-! The smooth Euler series used in the triple-convolution Perron formula.
The finite prime factors and the smooth factor are absolutely convergent
on the line Re(s)=1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike DeltaSpikeContinuous Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.Classical _root_.LSeries.notation



lemma halasz_smooth_term (f : ℕ → ℂ) (N : ℕ) (s : ℂ) (n : ℕ) :
    LSeries.term (halaszSmoothFunction f N) s n =
      (Nat.smoothNumbers (N + 1)).indicator (LSeries.term f s) n := by
  by_cases hn : n ∈ Nat.smoothNumbers (N + 1) <;>
    simp [LSeries.term, halaszSmoothFunction, hn]

lemma halasz_smooth_LSeries (f : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeries (halaszSmoothFunction f N) s =
      ∑' n : Nat.smoothNumbers (N + 1), LSeries.term f s n := by
  rw [LSeries, _root_.tsum_subtype (Nat.smoothNumbers (N + 1)) (LSeries.term f s)]
  exact tsum_congr (halasz_smooth_term f N s)







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]



theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring







theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]


lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩





lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top


private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp





section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end











theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply Real.log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind



theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply Real.log_pos; norm_num
        linarith [E₁.nonneg]




























end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
namespace OAI

/-! Mertens' second theorem in bounded-error form.

The formal proof uses `Erdos970.Mertens.sum_prime_div_eq_log_log`.
Only the convention for the finite prime set differs from
`PrimeReciprocalInput`; zero contributes no prime to either convention.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma sievePrimesUpTo_eq_Ioc (x : ℝ) :
    sievePrimesUpTo x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [sievePrimesUpTo, mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hp, hprime⟩

/-- Mertens' second theorem implies the reciprocal-prime estimate. -/
theorem primeReciprocalInput : PrimeReciprocalInput := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx => ?_⟩
  rw [sievePrimesUpTo_eq_Ioc]
  exact hC x hx

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands
namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The reciprocal-mass bounds follow from Mertens’ theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrt_sievePrimesUpTo_mono {P Q : ℝ} (hPQ : P ≤ Q) :
    sievePrimesUpTo P ⊆ sievePrimesUpTo Q := by
  intro p hp
  rcases mem_filter.mp hp with ⟨hp, hprime⟩
  exact mem_filter.mpr ⟨mem_Iic.mpr ((mem_Iic.mp hp).trans (Nat.floor_mono hPQ)), hprime⟩

lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1

lemma mrtPrimeBand_bounds {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : P < p ∧ (p : ℝ) ≤ Q := by
  have hpQ := (mem_sdiff.mp hp).1
  have hpP := (mem_sdiff.mp hp).2
  refine ⟨?_, sievePrimesUpTo_le Q hQ p hpQ⟩
  by_contra hnot
  have hple : (p : ℝ) ≤ P := le_of_not_gt hnot
  exact hpP (mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hP).mpr hple),
    mrtPrimeBand_prime hp⟩)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass
namespace OAI

/-! Mertens' first theorem, in the prime-band convention needed for the
small- and large-prime truncations in the Halasz convolution. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszMertensConstant_nonneg : 0 ≤ halaszMertensConstant := by
  unfold halaszMertensConstant
  positivity

lemma halasz_prime_prefix_mass {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) - Real.log x| ≤
      halaszMertensConstant := by
  rw [sievePrimesUpTo_eq_Ioc]
  exact Erdos970.Mertens.sum_log_prime_div_eq_log hx

lemma halasz_prime_band_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) =
      (∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) -
        ∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => Real.log (p : ℝ) / p)
    (mrt_sievePrimesUpTo_mono hPQ)

lemma halasz_prime_band_mertens {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    |(∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) -
        (Real.log Q - Real.log P)| ≤ 2 * halaszMertensConstant := by
  rw [halasz_prime_band_mass hPQ]
  have he : (∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) -
      (∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p) -
      (Real.log Q - Real.log P) =
      ((∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) - Real.log Q) -
      ((∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p) - Real.log P) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by
    linarith [halasz_prime_prefix_mass hP, halasz_prime_prefix_mass (hP.trans hPQ)])

lemma halasz_prime_prefix_mass_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) ≤
      Real.log x + halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_prefix_mass hx)).2]

lemma halasz_prime_band_mass_le {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) ≤
      Real.log Q - Real.log P + 2 * halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_band_mertens hP hPQ)).2]

lemma halasz_upper_half_prime_mass {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ mrtPrimeBand (x / 2) x, Real.log (p : ℝ) / p) ≤
      Real.log 2 + 2 * halaszMertensConstant := by
  have hx0 : 0 < x := by linarith
  have hm := halasz_prime_band_mass_le (P := x / 2) (Q := x)
    (by linarith) (by linarith)
  rw [Real.log_div (ne_of_gt hx0) (by norm_num)] at hm
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszParameters
namespace OAI

/-! The logarithmic truncation height and integer smoothing length used
in the grouped Perron estimate. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma halasz_eventually_numeric_scale (B : ℝ) :
    ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 1 ≤ Real.log (Real.log x) ∧
      2 ≤ Real.log x ^ 4 ∧ Real.log x ^ 16 ≤ x / 2 ∧ B ≤ Real.log x ^ 8 := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 16)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 B))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_ge_atTop (3 : ℝ), hlog, hloglog, hsmall] with x hx hl hll hs
  have hl2 : 2 ≤ Real.log x := (le_max_left _ _).trans hl
  have hl1 : 1 ≤ Real.log x := by linarith
  dsimp only [id] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log x) 16),
    Real.norm_eq_abs, abs_of_pos (by linarith : 0 < x)] at hs
  refine ⟨hx, hll, ?_, by linarith, ?_⟩
  · exact hl2.trans (le_self_pow₀ hl1 (by norm_num : (4 : ℕ) ≠ 0))
  · exact ((le_max_right _ _).trans hl).trans (le_self_pow₀ hl1 (by norm_num : (8 : ℕ) ≠ 0))

lemma halasz_smoothing_integer {N : ℕ} (hN : 2 ≤ N)
    (hlog : 2 ≤ Real.log (N : ℝ) ^ 4) (hsmall : Real.log (N : ℝ) ^ 4 ≤ N) :
    let m := ⌈(N : ℝ) / Real.log (N : ℝ) ^ 4⌉₊
    0 < m ∧ m ≤ N ∧ (N : ℝ) / Real.log (N : ℝ) ^ 4 ≤ m ∧
      (m : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ) ^ 4) ∧
      ((N : ℝ) + 1 / 2) / m ≤ 2 * Real.log (N : ℝ) ^ 4 := by
  let L := Real.log (N : ℝ) ^ 4
  let m := ⌈(N : ℝ) / L⌉₊
  have hL : 0 < L := by dsimp [L]; linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hratio : 1 ≤ (N : ℝ) / L := (le_div_iff₀ hL).mpr (by simpa [L] using hsmall)
  have hratioHigh : (N : ℝ) / L ≤ (N : ℝ) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
  have hmlo : (N : ℝ) / L ≤ m := Nat.le_ceil _
  have hmhi : (m : ℝ) < (N : ℝ) / L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmp : (0 : ℝ) < m := by linarith
  have hmNat : 0 < m := by exact_mod_cast hmp
  have hmN : m ≤ N := by exact_mod_cast (show (m : ℝ) ≤ N by linarith)
  refine ⟨hmNat, hmN, hmlo, by linarith, ?_⟩
  apply (div_le_iff₀ hmp).mpr
  have hmul : (N : ℝ) ≤ (m : ℝ) * L := (div_le_iff₀ hL).mp hmlo
  dsimp [L] at hmul ⊢
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNumericalErrors
namespace OAI

/-! The logarithmic height and integer smoothing length absorb the two
errors in the grouped Perron estimate. -/

namespace TwoPointCorrelations

lemma halasz_numerical_errors {N m : ℕ} {C H : ℝ}
    (hN : 3 ≤ N) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hm : 0 < m)
    (hml : (m : ℝ) ≤ 2 * ((N : ℝ) / Real.log (N : ℝ) ^ 4))
    (hmu : ((N : ℝ) + 1 / 2) / m ≤ 2 * Real.log (N : ℝ) ^ 4) :
    C * N * (H * Real.log N) * Real.log N /
        (((m : ℝ) / ((N : ℝ) + 1 / 2)) * Real.log N ^ 8) +
      C * m * Real.log (3 * N) ^ 2 ≤ (2 * C * H + 8 * C) * N := by
  let ℓ := Real.log (N : ℝ)
  have hℓ : 1 ≤ ℓ := hlog
  have hℓ0 : 0 < ℓ := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) ≤ 2 * ℓ ^ 8 := by
    calc
      _ ≤ ℓ ^ 2 * (2 * ℓ ^ 4) := mul_le_mul_of_nonneg_left hmu (sq_nonneg _)
      _ = 2 * ℓ ^ 6 := by ring
      _ ≤ 2 * ℓ ^ 8 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hℓ (by norm_num : (6 : ℕ) ≤ 8)) (by norm_num)
  have hfacdiv : ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) / ℓ ^ 8 ≤ 2 :=
    (div_le_iff₀ (pow_pos hℓ0 8)).mpr hfac
  have htail : C * N * (H * ℓ) * ℓ /
      (((m : ℝ) / ((N : ℝ) + 1 / 2)) * ℓ ^ 8) ≤ 2 * C * H * N := by
    calc
      _ = (C * N * H) * (ℓ ^ 2 * (((N : ℝ) + 1 / 2) / m) / ℓ ^ 8) := by
        field_simp
      _ ≤ (C * N * H) * 2 := mul_le_mul_of_nonneg_left hfacdiv (by positivity)
      _ = _ := by ring
  have hlog3 : 0 ≤ Real.log (3 * (N : ℝ)) := by
    apply Real.log_nonneg
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog3u : Real.log (3 * (N : ℝ)) ≤ 2 * ℓ := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have : Real.log 3 ≤ ℓ := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    linarith
  have hboundary : C * m * Real.log (3 * (N : ℝ)) ^ 2 ≤ 8 * C * N := by
    calc
      _ ≤ C * (2 * ((N : ℝ) / ℓ ^ 4)) * (2 * ℓ) ^ 2 := by gcongr
      _ = 8 * C * N / ℓ ^ 2 := by field_simp; ring
      _ ≤ 8 * C * N := div_le_self (by positivity) (one_le_pow₀ hℓ)
  change C * N * (H * ℓ) * ℓ /
      (((m : ℝ) / ((N : ℝ) + 1 / 2)) * ℓ ^ 8) +
      C * m * Real.log (3 * (N : ℝ)) ^ 2 ≤ _
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePartialSummation
namespace OAI

/-! Partial summation centered at Mertens' logarithmic main term. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma halasz_prime_weight_prefix (x : ℝ) :
    partialCoefficientSum halaszPrimeWeight x =
      ∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p := by
  have he : Icc 0 ⌊x⌋₊ = Iic ⌊x⌋₊ := by ext n; simp
  simp only [partialCoefficientSum, he, sievePrimesUpTo, halaszPrimeWeight, sum_filter]

lemma halasz_prime_weight_band (f : ℝ → ℝ) {a b : ℝ} :
    (∑ p ∈ mrtPrimeBand a b, f p * (Real.log (p : ℝ) / p)) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * halaszPrimeWeight n := by
  have he : mrtPrimeBand a b = (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    ext n
    simp only [mrtPrimeBand, sievePrimesUpTo, mem_sdiff, mem_filter, mem_Iic, mem_Ioc]
    by_cases hn : n.Prime <;> simp [hn, not_le, and_comm]
  rw [he, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : n.Prime <;> simp [halaszPrimeWeight, hn]

theorem halasz_prime_partial_summation (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ p ∈ mrtPrimeBand a b, f p * (Real.log (p : ℝ) / p)) -
        (∫ t in a..b, f t / t) =
      f b * (partialCoefficientSum halaszPrimeWeight b - Real.log b) -
      f a * (partialCoefficientSum halaszPrimeWeight a - Real.log a) -
      ∫ t in a..b, deriv f t *
        (partialCoefficientSum halaszPrimeWeight t - Real.log t) := by
  have hxn : ∀ x ∈ Set.Icc a b, x ≠ 0 := fun x hx => (ha.trans_le hx.1).ne'
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hdfi : IntervalIntegrable (deriv f) volume a b := hdf.intervalIntegrable_of_Icc hab
  have hlogi : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a b :=
    (continuousOn_id.inv₀ hxn).intervalIntegrable_of_Icc hab
  have hfi : IntervalIntegrable (fun x => f x / x) volume a b :=
    (hfc.div continuousOn_id hxn).intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun x => deriv f x * Real.log x) volume a b :=
    (hdf.mul hclog).intervalIntegrable_of_Icc hab
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum halaszPrimeWeight t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc halaszPrimeWeight ha.le hdf.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul halaszPrimeWeight ha.le hab hf
    hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab, ← halasz_prime_weight_band f] at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x hx => Real.hasDerivAt_log (hxn x (by simpa [Set.uIcc_of_le hab] using hx)))
    hdfi hlogi
  have hsplit : (∫ t in a..b, deriv f t * Real.log t + f t * t⁻¹) =
      (∫ t in a..b, deriv f t * Real.log t) + ∫ t in a..b, f t / t := by
    simp only [← div_eq_mul_inv]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t *
      (partialCoefficientSum halaszPrimeWeight t - Real.log t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum halaszPrimeWeight t) -
      ∫ t in a..b, deriv f t * Real.log t := by
    simp only [mul_sub]
    exact intervalIntegral.integral_sub hsum hdmain
  rw [herr, hAbel]
  dsimp [partialCoefficientSum] at *
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDenominatorCalculus
namespace OAI

/-! Calculus for the variable denominator in the second prime convolution. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory


lemma halasz_log_gap_pos {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    0 < Real.log X - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxX)

lemma halasz_denominator_hasDerivAt {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    HasDerivAt (halaszDenominatorWeight X)
      (x⁻¹ / (Real.log X - Real.log x) ^ 2) x := by
  have hg := (hasDerivAt_const x (Real.log X)).sub (Real.hasDerivAt_log hx.ne')
  have hd := hg.inv (ne_of_gt (halasz_log_gap_pos hx hxX))
  convert (preTransparency := .instances) hd using 1
  · rfl
  · simp only [Pi.sub_apply, zero_sub, neg_neg]

lemma halasz_denominator_primitive {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    HasDerivAt (fun y => -Real.log (Real.log X - Real.log y))
      (halaszDenominatorWeight X x / x) x := by
  have hg := (hasDerivAt_const x (Real.log X)).sub (Real.hasDerivAt_log hx.ne')
  have hd := ((Real.hasDerivAt_log (ne_of_gt (halasz_log_gap_pos hx hxX))).comp x hg).neg
  convert (preTransparency := .instances) hd using 1
  · rfl
  · simp only [zero_sub, halaszDenominatorWeight]
    ring

lemma halasz_denominator_deriv_continuous {X a b : ℝ} (ha : 0 < a)
    (hbX : b < X) : ContinuousOn (deriv (halaszDenominatorWeight X)) (Set.Icc a b) := by
  have hxn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hgap (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log X - Real.log x ≠ 0 :=
    (halasz_log_gap_pos (ha.trans_le hx.1) (hx.2.trans_lt hbX)).ne'
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  apply ContinuousOn.congr (f := fun x => x⁻¹ / (Real.log X - Real.log x) ^ 2)
  · exact (continuousOn_id.inv₀ hxn).div
      ((continuousOn_const.sub hlog).pow 2) (fun x hx => pow_ne_zero 2 (hgap x hx))
  · intro x hx
    exact (halasz_denominator_hasDerivAt (ha.trans_le hx.1) (hx.2.trans_lt hbX)).deriv

lemma halasz_denominator_integral {X a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbX : b < X) :
    (∫ t in a..b, halaszDenominatorWeight X t / t) =
      Real.log (Real.log X - Real.log a) - Real.log (Real.log X - Real.log b) := by
  have hf : ContinuousOn (fun t => halaszDenominatorWeight X t / t) (Set.Icc a b) := by
    have hxn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
    have hgap (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log X - Real.log x ≠ 0 :=
      (halasz_log_gap_pos (ha.trans_le hx.1) (hx.2.trans_lt hbX)).ne'
    have hlog : ContinuousOn Real.log (Set.Icc a b) :=
      fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
    exact ((continuousOn_const.sub hlog).inv₀ hgap).div continuousOn_id hxn
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => halasz_denominator_primitive
      (ha.trans_le (show x ∈ Set.Icc a b from by simpa [Set.uIcc_of_le hab] using hx).1)
      ((show x ∈ Set.Icc a b from by simpa [Set.uIcc_of_le hab] using hx).2.trans_lt hbX))
    (hf.intervalIntegrable_of_Icc hab)
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDenominatorMass
namespace OAI

/-! The weighted prime mass left by the second logarithmic convolution is
only of order log log X, with an absolute constant. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_denominator_prime_error {X a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hbX : b < X) :
    (∑ p ∈ mrtPrimeBand a b,
      halaszDenominatorWeight X p * (Real.log (p : ℝ) / p)) ≤
      Real.log (Real.log X - Real.log a) - Real.log (Real.log X - Real.log b) +
        2 * halaszMertensConstant * halaszDenominatorWeight X b := by
  let w := halaszDenominatorWeight X
  let E := fun x => partialCoefficientSum halaszPrimeWeight x - Real.log x
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hxpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < x := ha0.trans_le hx.1
  have hxX (x : ℝ) (hx : x ∈ Set.Icc a b) : x < X := hx.2.trans_lt hbX
  have hwpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 ≤ w x :=
    inv_nonneg.mpr (halasz_log_gap_pos (hxpos x hx) (hxX x hx)).le
  have hE (x : ℝ) (hx : x ∈ Set.Icc a b) : |E x| ≤ halaszMertensConstant := by
    dsimp [E]
    rw [halasz_prime_weight_prefix]
    exact halasz_prime_prefix_mass (ha.trans hx.1)
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt w (deriv w x) x :=
    (halasz_denominator_hasDerivAt (hxpos x hx) (hxX x hx)).differentiableAt.hasDerivAt
  have hdc : ContinuousOn (deriv w) (Set.Icc a b) :=
    halasz_denominator_deriv_continuous ha0 hbX
  have hdi : IntervalIntegrable (deriv w) volume a b := hdc.intervalIntegrable_of_Icc hab
  have hint : (∫ x in a..b, deriv w x) = w b - w a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x (by simpa [Set.uIcc_of_le hab] using hx)) hdi
  have hi : |∫ x in a..b, deriv w x * E x| ≤ halaszMertensConstant * (w b - w a) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun x => deriv w x * E x) (g := fun x => halaszMertensConstant * deriv w x) hab
      (Filter.Eventually.of_forall (fun x hx => by
        have hxi : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
        have hd0 : 0 ≤ deriv w x := by
          rw [(halasz_denominator_hasDerivAt (hxpos x hxi) (hxX x hxi)).deriv]
          exact div_nonneg (inv_nonneg.mpr (hxpos x hxi).le) (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd0]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hE x hxi) hd0))
      (hdi.const_mul halaszMertensConstant)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hint] at hb
    exact hb
  have hAbel := halasz_prime_partial_summation a b ha0 hab w
    (fun x hx => (hd x hx).differentiableAt) hdc
  rw [halasz_denominator_integral ha0 hab hbX] at hAbel
  change _ = w b * E b - w a * E a - _ at hAbel
  have heb := mul_le_mul_of_nonneg_left (abs_le.mp (hE b ⟨hab, le_rfl⟩)).2
    (hwpos b ⟨hab, le_rfl⟩)
  have hea := mul_le_mul_of_nonneg_left (abs_le.mp (hE a ⟨le_rfl, hab⟩)).1
    (hwpos a ⟨le_rfl, hab⟩)
  have hilow := (abs_le.mp hi).1
  dsimp [w] at *
  linarith

theorem halasz_denominator_prime_mass {X L : ℝ} (hL : 1 ≤ L) (hLX : L ≤ X / 2) :
    (∑ p ∈ mrtPrimeBand L (X / 2),
      Real.log (p : ℝ) / ((p : ℝ) * Real.log (X / p))) ≤
      Real.log (Real.log X) - Real.log (Real.log 2) +
        2 * halaszMertensConstant / Real.log 2 := by
  have hX : 2 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hhX : X / 2 < X := by linarith
  have he : Real.log X - Real.log (X / 2) = Real.log 2 := by
    rw [Real.log_div hX0.ne' (by norm_num)]
    ring
  have hgap := halasz_log_gap_pos hL0 (lt_of_le_of_lt hLX hhX)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hmain := Real.log_le_log hgap (show Real.log X - Real.log L ≤ Real.log X by linarith)
  have hb := halasz_denominator_prime_error hL hLX hhX
  have hsum : (∑ p ∈ mrtPrimeBand L (X / 2),
      Real.log (p : ℝ) / ((p : ℝ) * Real.log (X / p))) =
      ∑ p ∈ mrtPrimeBand L (X / 2),
        halaszDenominatorWeight X p * (Real.log (p : ℝ) / p) := by
    apply sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mrtPrimeBand_prime hp).pos
    rw [Real.log_div hX0.ne' hp0.ne', halaszDenominatorWeight]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsum]
  dsimp [halaszDenominatorWeight]
  simp only [halaszDenominatorWeight, he, ← div_eq_mul_inv] at hb
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeTruncation
namespace OAI

/-! The small- and large-prime deletion in the double-convolution argument.
All errors are uniform over one-bounded coefficients. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma halasz_prime_term_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N p : ℕ) (hp : p.Prime) :
    ‖halaszPrimeTerm f N p‖ ≤ (N : ℝ) * (Real.log (p : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hdiv : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
    apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  unfold halaszPrimeTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p : ℝ) * 1 * ((N / p : ℕ) : ℝ) := by
      gcongr
      · exact hf p hp.pos
      · exact halasz_bounded_prefix_norm f hf (N / p)
    _ ≤ Real.log (p : ℝ) * ((N : ℝ) / p) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hlog
    _ = _ := by ring

lemma halasz_prime_set_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ‖∑ p ∈ P, halaszPrimeTerm f N p‖ ≤
      (N : ℝ) * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  exact sum_le_sum (fun p hp => halasz_prime_term_bound f hf N p (hP p hp))

lemma halasz_prime_prefix_eq (f : ℕ → ℂ) (N : ℕ) :
    halaszPrimePrefix f N N = halaszPrimeConvolution f N := by
  have he : sievePrimesUpTo (N : ℝ) = (Icc 1 N).filter Nat.Prime := by
    ext p
    simp only [sievePrimesUpTo, Nat.floor_natCast, mem_filter, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  simp only [halaszPrimePrefix, he, halaszPrimeConvolution, halaszPrimeTerm]

lemma halasz_prime_band_eq (f : ℕ → ℂ) (N : ℕ) {L U : ℝ} (hLU : L ≤ U) :
    halaszPrimeBandConvolution f N L U =
      halaszPrimePrefix f N U - halaszPrimePrefix f N L := by
  exact sum_sdiff_eq_sub (f := halaszPrimeTerm f N) (mrt_sievePrimesUpTo_mono hLU)

lemma halasz_prime_prefix_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖halaszPrimePrefix f N x‖ ≤ (N : ℝ) * (Real.log x + halaszMertensConstant) := by
  exact (halasz_prime_set_bound f hf N _ (sievePrimesUpTo_prime x)).trans
    (mul_le_mul_of_nonneg_left (halasz_prime_prefix_mass_le hx) (Nat.cast_nonneg _))


/-- Delete all primes at most L and greater than N/2. -/
theorem halasz_prime_truncation_error (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    ‖halaszPrimeConvolution f N - halaszPrimeBandConvolution f N L ((N : ℝ) / 2)‖ ≤
      (N : ℝ) * (Real.log L + Real.log 2 + 3 * halaszMertensConstant) := by
  have hN : (2 : ℝ) ≤ N := by linarith
  have hhalf : (N : ℝ) / 2 ≤ N := by linarith
  have he : halaszPrimeConvolution f N -
      halaszPrimeBandConvolution f N L ((N : ℝ) / 2) =
      halaszPrimePrefix f N L +
        halaszPrimeBandConvolution f N ((N : ℝ) / 2) N := by
    rw [halasz_prime_band_eq f N hLN, halasz_prime_band_eq f N hhalf,
      halasz_prime_prefix_eq]
    ring
  rw [he]
  calc
    _ ≤ ‖halaszPrimePrefix f N L‖ +
        ‖halaszPrimeBandConvolution f N ((N : ℝ) / 2) N‖ := norm_add_le _ _
    _ ≤ (N : ℝ) * (Real.log L + halaszMertensConstant) +
        (N : ℝ) * (Real.log 2 + 2 * halaszMertensConstant) := by
      apply add_le_add (halasz_prime_prefix_bound f hf N hL)
      exact (halasz_prime_set_bound f hf N _ (fun _ hp => mrtPrimeBand_prime hp)).trans
        (mul_le_mul_of_nonneg_left (halasz_upper_half_prime_mass hN) (Nat.cast_nonneg _))
    _ = _ := by ring

theorem halasz_truncated_convolution_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2)‖ +
        (N : ℝ) * (Real.log L + Real.log 2 + 3 * halaszMertensConstant +
          halaszPrimePowerConstant + 1) := by
  have hN : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have ht := halasz_prime_truncation_error f hf N hL hLN
  have hm := halasz_prime_convolution_mean_bound f hf hmul N hN
  have hn := norm_add_le (halaszPrimeBandConvolution f N L ((N : ℝ) / 2))
    (halaszPrimeConvolution f N - halaszPrimeBandConvolution f N L ((N : ℝ) / 2))
  rw [add_sub_cancel] at hn
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleConvolution
namespace OAI

/-! Apply the prime convolution a second time, retaining the varying
denominator log(N/p). This is the adaptive triple sum in the short proof of
Halasz's theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_divisor_cutoff {N p : ℕ} (hp : 0 < p) (hpN : 2 * p ≤ N) :
    1 ≤ N / p ∧ ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p ∧
      (N : ℝ) / p ≤ 2 * ((N / p : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hM : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by omega)
  refine ⟨hM, ?_, ?_⟩
  · apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  · have hmod : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt N hp
    have hid : ((N % p : ℕ) : ℝ) + (p : ℝ) * ((N / p : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.mod_add_div N p
    have hM1 : (1 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hM
    apply (div_le_iff₀ hp0).mpr
    nlinarith

theorem halasz_double_convolution_error (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) :
    ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2) -
        halaszDoubleConvolution f N L‖ ≤
      halaszInnerErrorConstant * (N : ℝ) *
        ∑ p ∈ mrtPrimeBand L ((N : ℝ) / 2),
          Real.log (p : ℝ) / ((p : ℝ) * Real.log ((N : ℝ) / p)) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  unfold halaszPrimeBandConvolution halaszDoubleConvolution halaszPrimeTerm
  rw [← sum_sub_distrib, mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hprime := mrtPrimeBand_prime hp
  have hb := mrtPrimeBand_bounds hL0 (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2) hp
  have hpN : 2 * p ≤ N := by exact_mod_cast (show 2 * (p : ℝ) ≤ N by linarith)
  obtain ⟨hM, hMx, hxM⟩ := halasz_divisor_cutoff hprime.pos hpN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hx : 1 < (N : ℝ) / p := by
    have hh : (2 : ℝ) ≤ (N : ℝ) / p := (le_div_iff₀ hp0).mpr (by linarith)
    linarith
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  rw [← mul_sub, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p : ℝ) * 1 *
        (halaszInnerErrorConstant * ((N : ℝ) / p) / Real.log ((N : ℝ) / p)) := by
      gcongr
      · exact hf p hprime.pos
      · exact halasz_real_inner_approximation f hf hmul (N / p) hM hx hMx hxM
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleMean
namespace OAI

/-! The ordinary mean reduces to the adaptive double prime convolution,
with an explicit N log log N error. -/

namespace TwoPointCorrelations

open _root_.Finset


theorem halasz_double_mean_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszDoubleConvolution f N L‖ + (N : ℝ) *
        (Real.log L + Real.log 2 + 3 * halaszMertensConstant +
          halaszPrimePowerConstant + 1 + halaszInnerErrorConstant *
            (Real.log (Real.log N) + halaszDenominatorConstant)) := by
  have hmass := halasz_denominator_prime_mass hL hLN
  have hm := halasz_double_convolution_error f hf hmul N hL
  have hC : 0 ≤ halaszInnerErrorConstant * (N : ℝ) :=
    mul_nonneg halaszInnerErrorConstant_nonneg (Nat.cast_nonneg _)
  have herr : ‖halaszPrimeBandConvolution f N L ((N : ℝ) / 2) -
      halaszDoubleConvolution f N L‖ ≤
      halaszInnerErrorConstant * (N : ℝ) *
        (Real.log (Real.log N) + halaszDenominatorConstant) := by
    apply hm.trans
    apply mul_le_mul_of_nonneg_left _ hC
    simpa only [halaszDenominatorConstant, sub_eq_add_neg, add_assoc] using hmass
  have hn := norm_add_le (halaszDoubleConvolution f N L)
    (halaszPrimeBandConvolution f N L ((N : ℝ) / 2) - halaszDoubleConvolution f N L)
  rw [add_sub_cancel] at hn
  have ht := halasz_truncated_convolution_mean_bound f hf hmul N hL hLN
  nlinarith


lemma halaszDoubleErrorConstant_nonneg : 0 ≤ halaszDoubleErrorConstant := by
  have hm := halaszMertensConstant_nonneg
  have hp := halaszPrimePowerConstant_nonneg
  have hi := halaszInnerErrorConstant_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold halaszDoubleErrorConstant
  positivity


/-- The larger fixed logarithmic cutoff needed by the narrow-window
truncation. The deletion error still has order N log log N. -/
theorem halasz_double_mean_log_sixteenth (f : ℕ → ℂ) (hf : OneBounded f)
    (hmul : ∀ m n : ℕ, 0 < m → 0 < n → f (m * n) = f m * f n)
    (N : ℕ) (hlog : 1 ≤ Real.log (Real.log (N : ℝ)))
    (hL : 1 ≤ Real.log (N : ℝ) ^ 16)
    (hLN : Real.log (N : ℝ) ^ 16 ≤ (N : ℝ) / 2) :
    Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      ‖halaszDoubleConvolution f N (Real.log (N : ℝ) ^ 16)‖ +
        (halaszDoubleErrorConstant + 12) * (N : ℝ) * Real.log (Real.log N) := by
  have hb := halasz_double_mean_bound f hf hmul N hL hLN
  have hpow : Real.log (Real.log (N : ℝ) ^ 16) = 16 * Real.log (Real.log (N : ℝ)) := by
    rw [Real.log_pow]
    norm_num
  rw [hpow] at hb
  have hA : 0 ≤ Real.log 2 + 3 * halaszMertensConstant + halaszPrimePowerConstant + 1 := by
    have hm := halaszMertensConstant_nonneg
    have hp := halaszPrimePowerConstant_nonneg
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hi := halaszInnerErrorConstant_nonneg
  have hsmall := mul_le_mul_of_nonneg_left hlog hA
  have hD : halaszDenominatorConstant ≤ |halaszDenominatorConstant| *
      Real.log (Real.log (N : ℝ)) :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
  have hprod := mul_le_mul_of_nonneg_left hD hi
  have hscalar : 16 * Real.log (Real.log (N : ℝ)) + Real.log 2 +
      3 * halaszMertensConstant + halaszPrimePowerConstant + 1 +
      halaszInnerErrorConstant * (Real.log (Real.log N) + halaszDenominatorConstant) ≤
      (halaszDoubleErrorConstant + 12) * Real.log (Real.log N) := by
    unfold halaszDoubleErrorConstant
    nlinarith
  have hmulN := mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothDistance
namespace OAI

/-! Mertens turns the exact smooth Euler product into the usual
`log N * exp(-distance)` estimate, uniformly in the bounded coefficient. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_sievePrimesUpTo_nat (N : ℕ) : sievePrimesUpTo (N : ℝ) = primesUpTo N := by
  ext p
  simp only [sievePrimesUpTo, primesUpTo, mem_filter, mem_Iic, Nat.floor_natCast,
    mem_range, Nat.lt_succ_iff]

lemma mrt_prime_inverse_square_sum (N : ℕ) :
    (∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 := by
  have hs : primesUpTo N ⊆ Ioo 0 (N + 1) := by
    intro p hp
    exact mem_Ioo.mpr ⟨(mem_filter.mp hp).2.pos, mem_range.mp (mem_filter.mp hp).1⟩
  calc
    _ ≤ ∑ n ∈ Ioo 0 (N + 1), ((n : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ ≤ 2 := by simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

/-- The absolute Euler-product constant is independent of the
coefficient, height and smooth cutoff. -/
theorem mrt_smooth_distance_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (F : ℕ → ℂ), F 1 = 1 →
      (∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n) → OneBounded F →
      ∀ (N : ℕ), 2 ≤ N → ∀ t : ℝ,
      ‖∑' n : Nat.smoothNumbers (N + 1), LSeries.term F (1 + (t : ℂ) * Complex.I) n‖ ≤
        C * Real.log N * Real.exp (-squaredDistance F (mrtArchimedeanTwist t) N) := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  refine ⟨Real.exp (C + 2), Real.exp_pos _, ?_⟩
  intro F hF1 hF hFb N hN t
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hm := hC (N : ℝ) hN2
  rw [mrt_sievePrimesUpTo_nat] at hm
  have hmass := (abs_le.mp hm).2
  have hsq := mrt_prime_inverse_square_sum N
  calc
    _ ≤ Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) :=
      mrt_smooth_euler_distance_bound F hF1 hF hFb N t
    _ ≤ Real.exp (C + 2 + Real.log (Real.log N) +
        (-squaredDistance F (mrtArchimedeanTwist t) N)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log hlog]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothBounds
namespace OAI

/-! Continuity and uniform bounds for the actual smooth Euler series on
the Perron line. Only values at positive integers are bounded. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex

lemma halasz_distance_nonneg (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) (t : ℝ) :
    0 ≤ squaredDistance f (mrtArchimedeanTwist t) N := by
  unfold squaredDistance
  apply sum_nonneg
  intro p hp
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hprime : p.Prime := (mem_filter.mp hp).2
  have hn : ‖f p * star (mrtArchimedeanTwist t p)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, mrtArchimedeanTwist_norm, mul_one] using hf p hprime.pos
  exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hn)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszExceptionalMean
namespace OAI

/-! The ordinary mean estimate retaining the location of one exceptional
unit interval in the logarithmic-height Perron window. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

/-- Completely multiplicative means with one unit interval excluded from
the distance hypothesis. Its location supplies an additional decay term. -/
theorem halasz_exceptional_mean_value_oai : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (M τ : ℝ), 0 ≤ M →
      (∀ t ∈ Set.Ioc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8),
        t ∉ Set.Ioc (τ-1/2) (τ+1/2) → M ≤ squaredDistance f (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, f n‖ ≤ C * N *
        ((min M (Real.log (1+|τ|)) + 1) * Real.exp (-min M (Real.log (1+|τ|))) +
          Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C₁, B, hC₁, hB, hdouble⟩ := halasz_double_convolution_exception
  obtain ⟨H₀, hH₀, hEuler⟩ := mrt_smooth_distance_bound
  let H := max 1 H₀
  let D := 2 * C₁ * H + 8 * C₁ + (halaszDoubleErrorConstant + 12)
  let C := 1 + 2 * C₁ * H + D
  have hH : 1 ≤ H := le_max_left _ _
  have hH₀H : H₀ ≤ H := le_max_right _ _
  have hD : 0 ≤ D := by
    dsimp [D]
    have := halaszDoubleErrorConstant_nonneg
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (halasz_eventually_numeric_scale B)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨C, max X₀ X₁, hC, ?_⟩
  intro N hXN f hf1 hf hbound M τ hM hdist
  obtain ⟨hNr, hll, hl4, hl16, hBT⟩ := hX₀ N ((le_max_left _ _).trans hXN)
  have hN : 3 ≤ N := by exact_mod_cast hNr
  have hN2 : 2 ≤ N := by omega
  have hℓ2 : 2 ≤ Real.log (N : ℝ) := hX₁ N ((le_max_right _ _).trans hXN)
  have hℓ : 1 ≤ Real.log (N : ℝ) := by linarith
  have hℓ0 : 0 < Real.log (N : ℝ) := by linarith
  have hl4N : Real.log (N : ℝ) ^ 4 ≤ N :=
    (pow_le_pow_right₀ hℓ (by norm_num : (4 : ℕ) ≤ 16)).trans (by linarith)
  let m := ⌈(N : ℝ) / Real.log (N : ℝ) ^ 4⌉₊
  obtain ⟨hm, hmN, _, hml, hmu⟩ := halasz_smoothing_integer hN2 hl4 hl4N
  have hglobal (t : ℝ) :
      ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I)‖ ≤
        H * Real.log N := by
    rw [halasz_smooth_LSeries]
    have he := hEuler f hf1 hf hbound N hN2 t
    have hd := halasz_distance_nonneg f hbound N t
    have hx : Real.exp (-squaredDistance f (mrtArchimedeanTwist t) N) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    calc
      _ ≤ H₀ * Real.log N * Real.exp (-squaredDistance f (mrtArchimedeanTwist t) N) := he
      _ ≤ H₀ * Real.log N := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ H₀ * Real.log (N : ℝ))
      _ ≤ H * Real.log N := mul_le_mul_of_nonneg_right hH₀H hℓ0.le
  have hcentral (t : ℝ)
      (ht : t ∈ Set.Ioc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8))
      (hout : t ∉ Set.Ioc (τ-1/2) (τ+1/2)) :
      ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * Complex.I)‖ ≤
        (H * Real.log N) * Real.exp (-M) := by
    rw [halasz_smooth_LSeries]
    apply (hEuler f hf1 hf hbound N hN2 t).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hH₀H hℓ0.le
    · exact Real.exp_le_exp.mpr (neg_le_neg (hdist t ht hout))
    · positivity
    · positivity
  have hb := hdouble f hf1 hf hbound N m (Real.log N ^ 16) (Real.log N ^ 8)
    (H * Real.log N) (H * Real.log N) M τ hN2 hm hmN
    (one_le_pow₀ hℓ) (by rw [← pow_mul]) hBT
    (le_mul_of_one_le_left hℓ0.le hH) (by positivity) hM hcentral hglobal
  let M₁ := min M (Real.log (1+|τ|))
  have hM₁ : 0 ≤ M₁ := le_min hM (Real.log_nonneg (by linarith [abs_nonneg τ]))
  have herr := halasz_numerical_errors hN hC₁.le (by linarith : 0 ≤ H) hℓ hm hml hmu
  have hreduce := halasz_double_mean_log_sixteenth f hbound hf N hll (one_le_pow₀ hℓ) hl16
  have hsmall : (2 * C₁ * H + 8 * C₁) * N ≤
      (2 * C₁ * H + 8 * C₁) * N * Real.log (Real.log N) :=
    le_mul_of_one_le_right (by positivity) hll
  have hmain : Real.log (N : ℝ) * ‖∑ n ∈ Icc 1 N, f n‖ ≤
      2 * C₁ * N * (H * Real.log N) * (M₁ + 1) * Real.exp (-M₁) +
        D * N * Real.log (Real.log N) := by
    dsimp [D]
    linarith
  have hdiv := div_le_div_of_nonneg_right hmain hℓ0.le
  have heq : (2 * C₁ * N * (H * Real.log N) * (M₁ + 1) * Real.exp (-M₁) +
      D * N * Real.log (Real.log N)) / Real.log N =
      2 * C₁ * H * N * ((M₁ + 1) * Real.exp (-M₁)) +
        D * N * (Real.log (Real.log N) / Real.log N) := by
    field_simp
  rw [mul_div_cancel_left₀ _ hℓ0.ne', heq] at hdiv
  have hC₁H : 2 * C₁ * H ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith [show 0 ≤ C₁ * H by positivity]
  calc
    _ ≤ 2 * C₁ * H * N * ((M₁ + 1) * Real.exp (-M₁)) +
        D * N * (Real.log (Real.log N) / Real.log N) := hdiv
    _ ≤ C * N * ((M₁ + 1) * Real.exp (-M₁)) +
        C * N * (Real.log (Real.log N) / Real.log N) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_exceptional_mean_value_oai := @OAI.TwoPointCorrelations.halasz_exceptional_mean_value_oai
