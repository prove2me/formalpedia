-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_local_count_exception
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:40:07.698819+00:00
-- url     : https://prove2.me/submissions/bba8a53d-48f5-4978-bac6-3cb21a323a9f

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_exceptional_mean_value

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LocalFactors
namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations


@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]

/-- Coprime arguments have disjoint prime support, so arbitrary prime-power
values give an ordinary multiplicative function. -/
theorem fromPrimePowers_multiplicative (F : ℕ → ℕ → ℂ) :
    Multiplicative (fromPrimePowers F) := by
  intro m n hm hn hcop
  unfold fromPrimePowers
  rw [Nat.factorization_mul hm.ne' hn.ne']
  apply Finsupp.prod_add_index_of_disjoint
  simpa only [Nat.support_factorization] using hcop.disjoint_primeFactors

theorem fromPrimePowers_oneBounded (F : ℕ → ℕ → ℂ)
    (hF : ∀ p k, Nat.Prime p → 0 < k → ‖F p k‖ ≤ 1) :
    OneBounded (fromPrimePowers F) := by
  intro n hn
  unfold fromPrimePowers Finsupp.prod
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro p hp
    exact norm_nonneg _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    have hk : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact hF p _ hprime hk

@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowers
namespace OAI

/-! The total reciprocal contribution of higher prime powers is finite.
The modulus-one specialization of the prime-power series bounds
the finite hyperbola error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma halasz_bounded_prefix_norm (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, f n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) :=
      sum_le_sum (fun n hn => hf n (mem_Icc.mp hn).1)
    _ = _ := by simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FinitePrimePhases
namespace OAI

/-! The Fourier twists used in qualitative analytic centering count distinct
prime divisors, rather than their multiplicities. Their multiplicativity is
therefore asserted only for coprime arguments. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma finitePrimeDivisorCount_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (m n : ℕ) (hcop : m.Coprime n) :
    finitePrimeDivisorCount P (m * n) =
      finitePrimeDivisorCount P m + finitePrimeDivisorCount P n := by
  unfold finitePrimeDivisorCount
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hprime := hP p hp
  have hboth : ¬(p ∣ m ∧ p ∣ n) := by
    rintro ⟨hm, hn⟩
    exact hprime.ne_one (Nat.eq_one_of_dvd_coprimes hcop hm hn)
  simp only [hprime.dvd_mul]
  by_cases hm : p ∣ m <;> by_cases hn : p ∣ n <;> simp_all









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



lemma mrtArchimedeanTwist_norm (t : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _





/-- Multiplication by a real mask in `[0,1]` can reduce the squared
pretentious distance by at most a factor of two (MRT Lemma A.4(i)). -/
theorem mrt_masked_distance_lower (b twist : ℕ → ℂ) (mask : ℕ → ℝ) (N : ℕ)
    (hb : ∀ p ∈ primesUpTo N, ‖b p‖ ≤ 1)
    (htwist : ∀ p ∈ primesUpTo N, ‖twist p‖ ≤ 1)
    (hmask : ∀ p ∈ primesUpTo N, 0 ≤ mask p ∧ mask p ≤ 1) :
    squaredDistance b twist N ≤
      2 * squaredDistance (fun p => b p * (mask p : ℂ)) twist N := by
  unfold squaredDistance
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.pos
  have hz : ‖b p * conj (twist p)‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact (mul_le_mul (hb p hp) (htwist p hp) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have hx1 : (b p * conj (twist p)).re ≤ 1 := (Complex.re_le_norm _).trans hz
  have hx0 : -1 ≤ (b p * conj (twist p)).re := by
    have := (abs_le.mp (Complex.abs_re_le_norm (b p * conj (twist p)))).1
    linarith
  have he : (b p * (mask p : ℂ) * conj (twist p)).re =
      mask p * (b p * conj (twist p)).re := by
    rw [show b p * (mask p : ℂ) * conj (twist p) =
      (mask p : ℂ) * (b p * conj (twist p)) by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hp0.le
  rcases hmask p hp with ⟨hg0, hg1⟩
  by_cases hx : 0 ≤ (b p * conj (twist p)).re
  · have := mul_le_mul_of_nonneg_right hg1 hx
    nlinarith
  · have := mul_nonpos_of_nonneg_of_nonpos hg0 (le_of_lt (lt_of_not_ge hx))
    linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMultiplicativeReduction
namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma fromPrimePowers_prime_pow (F : ℕ → ℕ → ℂ)
    (hF : ∀ p, F p 0 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    fromPrimePowers F (p ^ k) = F p k := by
  unfold fromPrimePowers
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index (hF p)

lemma mrtCompletePart_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCompletePart f (p ^ k) = f p ^ k :=
  fromPrimePowers_prime_pow _ (fun _ => pow_zero _) hp k

lemma mrtCompletePart_mul (f : ℕ → ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    mrtCompletePart f (m * n) = mrtCompletePart f m * mrtCompletePart f n := by
  unfold mrtCompletePart fromPrimePowers
  rw [Nat.factorization_mul hm.ne' hn.ne']
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

lemma mrtCompletePart_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) :
    OneBounded (mrtCompletePart f) := by
  apply fromPrimePowers_oneBounded
  intro p k hp _
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hf p hp.pos)

@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]

lemma mrtCorrectionLocal_succ (f : ℕ → ℂ) (p k : ℕ) :
    mrtCorrectionLocal f p (k + 1) = f (p ^ (k + 1)) - f p * f (p ^ k) := by
  simp [mrtCorrectionLocal]

lemma mrtCorrection_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCorrection f (p ^ k) = mrtCorrectionLocal f p k :=
  fromPrimePowers_prime_pow _ (mrtCorrectionLocal_zero f) hp k

lemma mrtCorrectionLocal_norm_le (f : ℕ → ℂ) (hf : OneBounded f)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ‖mrtCorrectionLocal f p k‖ ≤ 2 := by
  rw [mrtCorrectionLocal, if_neg hk.ne']
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  have hpow := hf (p ^ k) (pow_pos hp.pos k)
  have hprev := hf (p ^ (k - 1)) (pow_pos hp.pos (k - 1))
  have hmul := mul_le_mul (hf p hp.pos) hprev (norm_nonneg _) zero_le_one
  nlinarith

/-- The local prime-power convolution telescopes exactly. -/
lemma mrt_local_convolution (f : ℕ → ℂ) (h1 : f 1 = 1) (p k : ℕ) :
    (∑ i ∈ range (k + 1), f p ^ i * mrtCorrectionLocal f p (k - i)) =
      f (p ^ k) := by
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [sum_range_succ']
    simp only [pow_zero, Nat.sub_zero, one_mul, mrtCorrectionLocal_succ,
      Nat.add_sub_add_right, pow_succ']
    simp only [mul_assoc]
    rw [← mul_sum, ih]
    ring


@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := if_neg hn.ne'

lemma mrtArithmetic_isMultiplicative (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) : (mrtArithmetic f).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [h1], ?_⟩
  intro m n hm hn hcop
  simp only [mrtArithmetic_apply_pos _ (Nat.pos_of_ne_zero hm),
    mrtArithmetic_apply_pos _ (Nat.pos_of_ne_zero hn),
    mrtArithmetic_apply_pos _ (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn))]
  exact hf m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop

/-- Every normalized multiplicative function factors as `g₁ * h`, where
`g₁` is completely multiplicative and `h(p)=0`. -/
theorem mrt_multiplicative_convolution (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) :
    mrtArithmetic (mrtCompletePart f) * mrtArithmetic (mrtCorrection f) =
      mrtArithmetic f := by
  have hc : (mrtArithmetic (mrtCompletePart f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  have hh : (mrtArithmetic (mrtCorrection f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hc.mul hh)
    _ (mrtArithmetic_isMultiplicative f hf h1)).mpr
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (fun a b => mrtArithmetic (mrtCompletePart f) a * mrtArithmetic (mrtCorrection f) b),
    Nat.sum_divisors_prime_pow hp]
  calc
    _ = ∑ i ∈ range (k + 1), f p ^ i * mrtCorrectionLocal f p (k - i) := by
      apply sum_congr rfl
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      rw [Nat.pow_div hik hp.pos, mrtArithmetic_apply_pos _ (pow_pos hp.pos i),
        mrtArithmetic_apply_pos _ (pow_pos hp.pos (k - i)),
        mrtCompletePart_prime_pow f hp, mrtCorrection_prime_pow f hp]
    _ = _ := by rw [mrt_local_convolution f h1, mrtArithmetic_apply_pos _ (pow_pos hp.pos k)]

/-- The convolution identity in the positive-integer notation used in MRT. -/
theorem mrt_multiplicative_divisor_sum (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    f n = ∑ d ∈ n.divisors, mrtCorrection f d * mrtCompletePart f (n / d) := by
  have he := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (mrt_multiplicative_convolution f hf h1)
  rw [mul_comm, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (mrtCorrection f) a * mrtArithmetic (mrtCompletePart f) b)] at he
  rw [mrtArithmetic_apply_pos _ hn] at he
  rw [← he]
  apply sum_congr rfl
  intro d hd
  rcases Nat.mem_divisors.mp hd with ⟨hdn, hn0⟩
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  rw [mrtArithmetic_apply_pos _ hd0, mrtArithmetic_apply_pos _ hquot]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionEuler
namespace OAI

/-! A finite-Euler-product criterion for the absolutely summable correction
in the general-multiplicative reduction.  The criterion is proved from local
prime-power sums, not used as a new analytic input. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators

theorem mrt_summable_of_local_euler_bound (a : ℕ → ℝ)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1) (ha : ∀ n, 0 ≤ a n)
    (hmul : ∀ {m n}, m.Coprime n → a (m * n) = a m * a n)
    (hloc : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => a (p ^ k)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p : ℕ, p.Prime →
      (∑' k : ℕ, a (p ^ k)) ≤ Real.exp (C * (p : ℝ) ^ (-(3 / 2 : ℝ)))) :
    Summable a ∧
      (∑' n : ℕ, a n) ≤ Real.exp (C * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hpseries : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    exact Real.summable_nat_rpow.mpr (by norm_num)
  have hprefix (N : ℕ) :
      (∑ n ∈ range N, a n) ≤ Real.exp (C * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have hlocnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖a (p ^ k)‖) := by
      intro p hp
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ha _)] using hloc p hp
    obtain ⟨_, hprod⟩ :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum ha1 hmul hlocnorm N
    have hi := hasSum_subtype_iff_indicator.mp hprod
    have hsum : (∑ n ∈ range N, a n) =
        ∑ n ∈ range N, (Nat.smoothNumbers N).indicator a n := by
      apply sum_congr rfl
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0, ha0, Set.indicator_apply]
      · exact (Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt
          (Nat.pos_of_ne_zero hn0) (mem_range.mp hn)) a).symm
    rw [hsum]
    calc
      _ ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, a (p ^ k) := by
        rw [← hi.tsum_eq]
        apply hi.summable.sum_le_tsum
        intro n _
        exact Set.indicator_nonneg (fun n _ => ha n) n
      _ ≤ ∏ p ∈ N.primesBelow, Real.exp (C * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        apply Finset.prod_le_prod
        · intro p _
          exact tsum_nonneg (fun _ => ha _)
        · intro p hp
          exact hbound p (Nat.prime_of_mem_primesBelow hp)
      _ = Real.exp (C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        rw [mul_sum, Real.exp_sum]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hC
        exact hpseries.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact ⟨summable_of_sum_range_le ha hprefix, Real.tsum_le_of_sum_range_le ha hprefix⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionSummability
namespace OAI

/-! Absolute summability of the prime-power correction in MRT's reduction
from multiplicative to completely multiplicative functions. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators




lemma mrtCorrectionWeight_nonneg (f : ℕ → ℂ) (n : ℕ) :
    0 ≤ mrtCorrectionWeight f n := by
  exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma mrtCorrectionWeight_zero (f : ℕ → ℂ) : mrtCorrectionWeight f 0 = 0 := by
  simp [mrtCorrectionWeight]

lemma mrtCorrectionWeight_one (f : ℕ → ℂ) : mrtCorrectionWeight f 1 = 1 := by
  simp [mrtCorrectionWeight, mrtCorrection, mrtArithmetic]

lemma mrtCorrectionWeight_mul (f : ℕ → ℂ) {m n : ℕ} (hcop : m.Coprime n) :
    mrtCorrectionWeight f (m * n) = mrtCorrectionWeight f m * mrtCorrectionWeight f n := by
  have hmult : (mrtArithmetic (mrtCorrection f)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  unfold mrtCorrectionWeight
  rw [hmult.map_mul_of_coprime hcop, norm_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

lemma mrtCorrectionWeight_prime_pow (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mrtCorrectionWeight f (p ^ k) =
      ‖mrtCorrectionLocal f p k‖ * ((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
  unfold mrtCorrectionWeight
  rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos k), mrtCorrection_prime_pow f hp,
    Nat.cast_pow, Real.rpow_pow_comm (Nat.cast_nonneg p)]

lemma mrtCorrectionEulerConstant_nonneg : 0 ≤ mrtCorrectionEulerConstant := by
  have hlt : (2 : ℝ) ^ (-(3 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  exact div_nonneg (by norm_num) (sub_nonneg.mpr hlt.le)

lemma mrt_correction_local_summable (f : ℕ → ℂ) (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => mrtCorrectionWeight f (p ^ k)) := by
  let r : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast hp.one_lt) (by norm_num)
  apply Summable.of_nonneg_of_le (fun k => mrtCorrectionWeight_nonneg f (p ^ k))
    (f := fun k => 2 * r ^ k)
  · intro k
    rw [mrtCorrectionWeight_prime_pow f hp]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 k)
    rcases k with _ | k
    · simp
    · exact mrtCorrectionLocal_norm_le f hf hp (Nat.succ_pos k)
  · exact (summable_geometric_of_lt_one hr0 hr1).mul_left 2

lemma mrt_correction_local_sum_bound (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1)
    {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, mrtCorrectionWeight f (p ^ k)) ≤
      Real.exp (mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let r : ℝ := (p : ℝ) ^ (-(3 / 4 : ℝ))
  let rho : ℝ := (2 : ℝ) ^ (-(3 / 4 : ℝ))
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hrho : rho < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hrle : r ≤ rho := Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by exact_mod_cast hp.two_le) (by norm_num)
  have hr1 : r < 1 := hrle.trans_lt hrho
  have hsum := mrt_correction_local_summable f hf hp
  have htail := (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * r ^ 2)
  have ht : (∑' k : ℕ, mrtCorrectionWeight f (p ^ (k + 2))) ≤
      (2 * r ^ 2) * (1 - r)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
    apply (hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum
      (fun k => ?_) htail
    change mrtCorrectionWeight f (p ^ (k + 2)) ≤ _
    rw [mrtCorrectionWeight_prime_pow f hp, pow_add]
    have hb := mrtCorrectionLocal_norm_le f hf hp (by omega : 0 < k + 2)
    calc
      _ ≤ 2 * (r ^ k * r ^ 2) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hs : (∑' k : ℕ, mrtCorrectionWeight f (p ^ k)) ≤
      1 + (2 * r ^ 2) * (1 - r)⁻¹ := by
    calc
      _ = 1 + ∑' k : ℕ, mrtCorrectionWeight f (p ^ (k + 2)) := by
        simpa [sum_range_succ, mrtCorrectionWeight_prime_pow f hp,
          mrtCorrectionLocal_one f h1] using (hsum.sum_add_tsum_nat_add 2).symm
      _ ≤ _ := add_le_add le_rfl ht
  have hinv : (1 - r)⁻¹ ≤ (1 - rho)⁻¹ :=
    inv_anti₀ (sub_pos.mpr hrho) (sub_le_sub_left hrle 1)
  have hsq : r ^ 2 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
    norm_num
  calc
    _ ≤ 1 + (2 * r ^ 2) * (1 - r)⁻¹ := hs
    _ ≤ 1 + (2 * r ^ 2) * (1 - rho)⁻¹ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ 2 * r ^ 2 by positivity))
    _ = 1 + mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [hsq]
      unfold mrtCorrectionEulerConstant
      dsimp [rho]
      ring
    _ ≤ _ := by
      simpa only [add_comm] using (Real.add_one_le_exp
        (mrtCorrectionEulerConstant * (p : ℝ) ^ (-(3 / 2 : ℝ))))

/-- Uniform absolute convergence at exponent `3/4`, exactly as required by
the general-multiplicative reduction in corrected MRT. -/
theorem mrt_correction_summable (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1) :
    Summable (mrtCorrectionWeight f) ∧
      (∑' n : ℕ, mrtCorrectionWeight f n) ≤ mrtCorrectionBound := by
  exact mrt_summable_of_local_euler_bound _ (mrtCorrectionWeight_zero f)
    (mrtCorrectionWeight_one f) (mrtCorrectionWeight_nonneg f)
    (mrtCorrectionWeight_mul f) (fun _ hp => mrt_correction_local_summable f hf hp)
    _ mrtCorrectionEulerConstant_nonneg
    (fun _ hp => mrt_correction_local_sum_bound f hf h1 hp)

/-- The large-divisor correction costs `O(W^(-1/4))`, with an absolute
constant independent of the multiplicative function and of the finite sum. -/
theorem mrt_correction_tail_bound (f : ℕ → ℂ) (hf : OneBounded f) (h1 : f 1 = 1)
    {W : ℕ} (hW : 0 < W) (S : Finset ℕ) (hS : ∀ n ∈ S, W ≤ n) :
    (∑ n ∈ S, ‖mrtCorrection f n‖ / (n : ℝ)) ≤
      mrtCorrectionBound * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hsum := mrt_correction_summable f hf h1
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  calc
    _ ≤ ∑ n ∈ S, mrtCorrectionWeight f n * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn0 : 0 < n := hW.trans_le (hS n hn)
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
      have hid : ‖mrtCorrection f n‖ / (n : ℝ) =
          mrtCorrectionWeight f n * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
        unfold mrtCorrectionWeight
        rw [mrtArithmetic_apply_pos _ hn0, mul_assoc, ← Real.rpow_add hnr]
        norm_num
        rw [Real.rpow_neg_one, div_eq_mul_inv]
      rw [hid]
      apply mul_le_mul_of_nonneg_left _ (mrtCorrectionWeight_nonneg f n)
      exact Real.rpow_le_rpow_of_nonpos hWr (by exact_mod_cast hS n hn) (by norm_num)
    _ = (∑ n ∈ S, mrtCorrectionWeight f n) * (W : ℝ) ^ (-(1 / 4 : ℝ)) :=
      (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      ((hsum.1.sum_le_tsum S (fun n _ => mrtCorrectionWeight_nonneg f n)).trans hsum.2)
      (Real.rpow_nonneg hWr.le _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCorrectionTransfer
namespace OAI

/-! Transfer an ordinary mean estimate through the exact prime-power
correction, retaining its uniform summable tail. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_correction_prefix (f : ℕ → ℂ) (hf : Multiplicative f) (hf1 : f 1 = 1)
    (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n) =
      ∑ d ∈ Icc 1 N, mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        mrtCorrection f p.1 * mrtCompletePart f p.2 := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.sum_divisorsAntidiagonal (fun d m => mrtCorrection f d * mrtCompletePart f m)]
      exact mrt_multiplicative_divisor_sum f hf hf1 (mem_Icc.mp hn).1
    _ = _ := by
      rw [halasz_sum_divisorsAntidiagonal (fun d n => mrtCorrection f d * mrtCompletePart f n),
        halasz_hyperbola_rows (fun d n => mrtCorrection f d * mrtCompletePart f n)]
      exact sum_congr rfl (fun d _ => (mul_sum _ _ _).symm)

theorem halasz_correction_mean_bound (f : ℕ → ℂ) (hf : Multiplicative f)
    (hbound : OneBounded f) (hf1 : f 1 = 1) (N W : ℕ) (hW : 0 < W)
    (A : ℝ) (hA : 0 ≤ A)
    (hmean : ∀ d ∈ Icc 1 N, d ≤ W →
      ‖∑ n ∈ Icc 1 (N / d), mrtCompletePart f n‖ ≤ A * ((N / d : ℕ) : ℝ)) :
    ‖∑ n ∈ Icc 1 N, f n‖ ≤
      mrtCorrectionBound * N * (A + (W : ℝ) ^ (-(1 / 4 : ℝ))) := by
  let S := (Icc 1 N).filter (fun d => d ≤ W)
  let U := (Icc 1 N).filter (fun d => ¬d ≤ W)
  let a := fun d : ℕ => mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n
  have hsplit : (∑ n ∈ Icc 1 N, f n) = (∑ d ∈ S, a d) + ∑ d ∈ U, a d := by
    rw [halasz_correction_prefix f hf hf1]
    exact (sum_filter_add_sum_filter_not (Icc 1 N) (fun d => d ≤ W) a).symm
  have hs : ‖∑ d ∈ S, a d‖ ≤ (A * N) * ∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ) := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hdN, hdW⟩ := mem_filter.mp hd
    rw [show a d = mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n from rfl, norm_mul]
    calc
      _ ≤ ‖mrtCorrection f d‖ * (A * ((N / d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmean d hdN hdW) (norm_nonneg _)
      _ ≤ ‖mrtCorrection f d‖ * (A * ((N : ℝ) / d)) := by
        gcongr
        exact Nat.cast_div_le
      _ = _ := by ring
  have hu : ‖∑ d ∈ U, a d‖ ≤ (N : ℝ) * ∑ d ∈ U, ‖mrtCorrection f d‖ / (d : ℝ) := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    rw [show a d = mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n from rfl, norm_mul]
    calc
      _ ≤ ‖mrtCorrection f d‖ * ((N / d : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (halasz_bounded_prefix_norm _ (mrtCompletePart_oneBounded f hbound) _) (norm_nonneg _)
      _ ≤ ‖mrtCorrection f d‖ * ((N : ℝ) / d) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le (norm_nonneg _)
      _ = _ := by ring
  have hsmass : (∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ)) ≤ mrtCorrectionBound := by
    simpa using mrt_correction_tail_bound f hbound hf1 (W := 1) (by norm_num) S
      (fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1)
  have humass := mrt_correction_tail_bound f hbound hf1 hW U
    (fun d hd => Nat.le_of_lt (Nat.lt_of_not_ge (mem_filter.mp hd).2))
  calc
    _ ≤ ‖∑ d ∈ S, a d‖ + ‖∑ d ∈ U, a d‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ (A * N) * (∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ)) +
        (N : ℝ) * (∑ d ∈ U, ‖mrtCorrection f d‖ / (d : ℝ)) := add_le_add hs hu
    _ ≤ (A * N) * mrtCorrectionBound +
        (N : ℝ) * (mrtCorrectionBound * (W : ℝ) ^ (-(1 / 4 : ℝ))) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalFactors
namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators




lemma mrtPrimeMask_bounds (P : Finset ℕ) (n : ℕ) :
    0 ≤ mrtPrimeMask P n ∧ mrtPrimeMask P n ≤ 1 := by
  unfold mrtPrimeMask
  split_ifs <;> norm_num



lemma mrtPrimeAvoids_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    mrtPrimeAvoids P (m * n) ↔ mrtPrimeAvoids P m ∧ mrtPrimeAvoids P n := by
  simp only [mrtPrimeAvoids]
  constructor
  · intro h
    exact ⟨fun p hp hpm => h p hp (dvd_mul_of_dvd_left hpm n),
      fun p hp hpn => h p hp (dvd_mul_of_dvd_right hpn m)⟩
  · rintro ⟨hm, hn⟩ p hp hdiv
    exact ((hP p hp).dvd_mul.mp hdiv).elim (hm p hp) (hn p hp)

lemma mrtPrimeMask_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m n : ℕ) :
    mrtPrimeMask P (m * n) = mrtPrimeMask P m * mrtPrimeMask P n := by
  simp only [mrtPrimeMask, mrtPrimeAvoids_mul P hP]
  by_cases hm : mrtPrimeAvoids P m <;> by_cases hn : mrtPrimeAvoids P n <;> simp [hm, hn]

lemma mrtPrimeMask_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    mrtPrimeMask P 1 = 1 := by
  unfold mrtPrimeMask
  apply if_pos
  intro p hp hdiv
  exact (hP p hp).ne_one (Nat.eq_one_of_dvd_one hdiv)









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCountMask
namespace OAI

/-! Reciprocal prime-count weights as an integral of multiplicative
soft masks.  This is the exact cofactor-weight reduction used in MRT
Appendix A, Lemma A.5. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma finitePrimeDivisorCount_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    finitePrimeDivisorCount P 1 = 0 := by
  unfold finitePrimeDivisorCount
  apply sum_eq_zero
  intro p hp
  apply if_neg
  intro hd
  exact (hP p hp).ne_one (Nat.eq_one_of_dvd_one hd)

lemma mrtCountMask_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    mrtCountMask P u 1 = 1 := by
  simp only [mrtCountMask, finitePrimeDivisorCount_one P hP, pow_zero]

lemma mrtCountMask_mul (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℝ) (m n : ℕ) (hcop : m.Coprime n) :
    mrtCountMask P u (m * n) = mrtCountMask P u m * mrtCountMask P u n := by
  simp only [mrtCountMask, finitePrimeDivisorCount_mul P hP m n hcop, pow_add]

lemma mrtCountMask_bounds (P : Finset ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    0 ≤ mrtCountMask P u n ∧ mrtCountMask P u n ≤ 1 :=
  ⟨pow_nonneg hu _, pow_le_one₀ hu hu1⟩



lemma Multiplicative.mrtCountMaskedCoefficient {F : ℕ → ℂ} (hF : Multiplicative F)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    Multiplicative (mrtCountMaskedCoefficient F P u) := by
  intro m n hm hn hcop
  simp only [TwoPointCorrelations.mrtCountMaskedCoefficient, hF m n hm hn hcop,
    mrtCountMask_mul P hP u m n hcop, Complex.ofReal_mul]
  ring

lemma OneBounded.mrtCountMaskedCoefficient {F : ℕ → ℂ} (hF : OneBounded F)
    (P : Finset ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    OneBounded (mrtCountMaskedCoefficient F P u) := by
  intro n hn
  rw [TwoPointCorrelations.mrtCountMaskedCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mrtCountMask_bounds P hu hu1 n).1]
  exact (mul_le_mul (hF n hn) (mrtCountMask_bounds P hu hu1 n).2
    (mrtCountMask_bounds P hu hu1 n).1 zero_le_one).trans_eq (mul_one 1)

lemma mrtCountMask_integral (P : Finset ℕ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, mrtCountMask P u n) =
      1 / ((finitePrimeDivisorCount P n : ℝ) + 1) := by
  simp [mrtCountMask, integral_pow]

lemma mrtCountMaskedCoefficient_integral (F : ℕ → ℂ) (P : Finset ℕ) (n : ℕ) :
    (∫ u in (0 : ℝ)..1, mrtCountMaskedCoefficient F P u n) =
      F n / ((finitePrimeDivisorCount P n : ℂ) + 1) := by
  simp only [mrtCountMaskedCoefficient, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, mrtCountMask_integral, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_add, Complex.ofReal_natCast]
  ring

/-- The literal reciprocal-count cofactor polynomial is the average of
the corresponding soft-mask polynomials. -/
theorem mrt_reciprocal_count_polynomial (S P : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ S, a n / ((finitePrimeDivisorCount P n : ℂ) + 1)) =
      ∫ u in (0 : ℝ)..1, ∑ n ∈ S, mrtCountMaskedCoefficient a P u n := by
  have hc (n : ℕ) : Continuous (fun u : ℝ => mrtCountMaskedCoefficient a P u n) := by
    unfold mrtCountMaskedCoefficient mrtCountMask
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun n _ => (hc n).intervalIntegrable _ _)]
  exact sum_congr rfl (fun n _ => (mrtCountMaskedCoefficient_integral a P n).symm)

theorem mrt_reciprocal_count_polynomial_bound (S P : Finset ℕ) (a : ℕ → ℂ)
    (B : ℝ) (hB : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ‖∑ n ∈ S, mrtCountMaskedCoefficient a P u n‖ ≤ B) :
    ‖∑ n ∈ S, a n / ((finitePrimeDivisorCount P n : ℂ) + 1)‖ ≤ B := by
  rw [mrt_reciprocal_count_polynomial]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun u => ∑ n ∈ S, mrtCountMaskedCoefficient a P u n) (fun u hu => by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact hB u hu.1.le hu.2)
  simpa using hb


/-- Missing-band and reciprocal-count masks are combined before applying
the distance inequality, so there is only one factor-two loss. -/
theorem mrt_missing_count_mask_distance (F twist : ℕ → ℂ) (Q P : Finset ℕ)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (N : ℕ)
    (hF : ∀ p ∈ primesUpTo N, ‖F p‖ ≤ 1)
    (htwist : ∀ p ∈ primesUpTo N, ‖twist p‖ ≤ 1) :
    squaredDistance F twist N ≤ 2 * squaredDistance
      (mrtCountMaskedCoefficient (fun n => F n * (mrtPrimeMask Q n : ℂ)) P u) twist N := by
  have hm (p : ℕ) : 0 ≤ mrtPrimeMask Q p * mrtCountMask P u p ∧
      mrtPrimeMask Q p * mrtCountMask P u p ≤ 1 := by
    have hq := mrtPrimeMask_bounds Q p
    have hp := mrtCountMask_bounds P hu hu1 p
    exact ⟨mul_nonneg hq.1 hp.1,
      (mul_le_mul hq.2 hp.2 hp.1 zero_le_one).trans_eq (mul_one 1)⟩
  have hb := mrt_masked_distance_lower F twist
    (fun n => mrtPrimeMask Q n * mrtCountMask P u n) N hF htwist (fun p _ => hm p)
  convert (preTransparency := .instances) hb using 1
  congr 2
  funext n
  simp only [mrtCountMaskedCoefficient, Complex.ofReal_mul, mul_assoc]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCorrectionScale
namespace OAI

/-! A logarithmic cutoff for the general multiplicative correction. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma halasz_eventually_correction_scale (X₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let W := ⌈Real.log x ^ 4⌉₊
      2 ≤ W ∧ X₀ ≤ (W : ℝ) ∧ (W : ℝ) ^ 2 ≤ x ∧
      (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / Real.log x ∧
      2 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 8)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 2 X₀))
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall, hlog, hll] with x hx hs hl hll
  let ℓ := Real.log x
  let W := ⌈ℓ ^ 4⌉₊
  have hℓ2 : 2 ≤ ℓ := (le_max_left _ _).trans hl
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hp : 1 ≤ ℓ ^ 4 := one_le_pow₀ hℓ1
  have hlow : ℓ ^ 4 ≤ (W : ℝ) := Nat.le_ceil _
  have hhigh : (W : ℝ) ≤ 2 * ℓ ^ 4 := by
    have hh : (W : ℝ) < ℓ ^ 4 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hℓle : ℓ ≤ ℓ ^ 4 := le_self_pow₀ hℓ1 (by norm_num : (4 : ℕ) ≠ 0)
  have hW2 : 2 ≤ W := by exact_mod_cast hℓ2.trans (hℓle.trans hlow)
  have hWX : X₀ ≤ (W : ℝ) := ((le_max_right _ _).trans hl).trans (hℓle.trans hlow)
  dsimp only [id] at hs
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hℓ0.le 8),
    Real.norm_eq_abs, abs_of_pos hx] at hs
  have hWs : (W : ℝ) ^ 2 ≤ x := by
    calc
      _ ≤ (2 * ℓ ^ 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg W) hhigh 2
      _ = 4 * ℓ ^ 8 := by ring
      _ ≤ x := by linarith
  have htail : (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / ℓ := by
    calc
      _ ≤ (ℓ ^ 4) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (pow_pos hℓ0 4) hlow (by norm_num)
      _ = 1 / ℓ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le]
        norm_num
        rw [Real.rpow_neg_one]
  exact ⟨hW2, hWX, hWs, htail, hℓ2, hll⟩

lemma halasz_correction_quotient {N W d : ℕ} (hW : 2 ≤ W) (hd : 0 < d)
    (hdW : d ≤ W) (hWN : W ^ 2 ≤ N) :
    W ≤ N / d ∧ N / d ≤ N ∧ N ≤ (N / d) ^ 3 := by
  have hWpos : 0 < W := by omega
  have hWd : W * d ≤ N := (Nat.mul_le_mul_left W hdW).trans (by simpa [pow_two] using hWN)
  have hWq : W ≤ N / d := (Nat.le_div_iff_mul_le hd).mpr hWd
  have hq : 2 ≤ N / d := hW.trans hWq
  have hdq : d ≤ N / d := hdW.trans hWq
  have hn := Nat.lt_mul_div_succ N hd
  refine ⟨hWq, Nat.div_le_self N d, ?_⟩
  have htwo : N / d + 1 ≤ (N / d) ^ 2 := by nlinarith
  calc
    N ≤ d * (N / d + 1) := hn.le
    _ ≤ (N / d) * ((N / d) ^ 2) := Nat.mul_le_mul hdq htwo
    _ = (N / d) ^ 3 := by ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDistanceCutoff
namespace OAI

/-! A fixed-power change of the prime cutoff changes the squared
pretentious distance by an absolute constant. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.ComplexConjugate

lemma halasz_prime_cutoff_subset {n N : ℕ} (hn : n ≤ N) : primesUpTo n ⊆ primesUpTo N := by
  intro p hp
  obtain ⟨hp, hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hp; omega), hprime⟩

theorem halasz_distance_cutoff_loss : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (n N : ℕ), 2 ≤ n → n ≤ N → N ≤ n ^ 3 →
    ∀ t : ℝ, squaredDistance f (mrtArchimedeanTwist t) N ≤
      squaredDistance f (mrtArchimedeanTwist t) n + K := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  let K := 2 * (Real.log 3 + 2 * |C|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro f hf n N hn hnN hNcube t
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlNn : Real.log (N : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have h := Real.log_le_log hN0 (show (N : ℝ) ≤ (n : ℝ) ^ 3 by exact_mod_cast hNcube)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hll : Real.log (Real.log (N : ℝ)) - Real.log (Real.log (n : ℝ)) ≤ Real.log 3 := by
    have h := Real.log_le_log hlN hlNn
    rw [Real.log_mul (by norm_num) hln.ne'] at h
    linarith
  have hmN := hC (N : ℝ) (by exact_mod_cast (show 2 ≤ N by omega))
  have hmn := hC (n : ℝ) (by exact_mod_cast hn)
  rw [mrt_sievePrimesUpTo_nat] at hmN hmn
  have hmass : (∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
      (∑ p ∈ primesUpTo n, (1 : ℝ) / p) ≤ Real.log 3 + 2 * |C| := by
    have ha := (abs_le.mp hmN).2
    have hb := (abs_le.mp hmn).1
    linarith [le_abs_self C]
  let P := primesUpTo N \ primesUpTo n
  have hsub := halasz_prime_cutoff_subset hnN
  have hterm (p : ℕ) (hp : p ∈ P) :
      (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ) ≤ 2 * (1 / (p : ℝ)) := by
    have hprime : p.Prime := (mem_filter.mp (mem_sdiff.mp hp).1).2
    have hnrm : ‖f p * conj (mrtArchimedeanTwist t p)‖ ≤ 1 := by
      simpa only [norm_mul, norm_conj, mrtArchimedeanTwist_norm, mul_one] using hf p hprime.pos
    have hre := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hnrm)
    have hnum : 1 - (f p * conj (mrtArchimedeanTwist t p)).re ≤ 2 := by linarith
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hnum (Nat.cast_nonneg p)
  have hs := sum_le_sum (fun p hp => hterm p hp)
  rw [← mul_sum] at hs
  have heDist := sum_sdiff hsub (f := fun p : ℕ =>
    (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ))
  have heMass := sum_sdiff hsub (f := fun p : ℕ => (1 : ℝ) / p)
  change (∑ p ∈ P, (1 - (f p * conj (mrtArchimedeanTwist t p)).re) / (p : ℝ)) +
    squaredDistance f (mrtArchimedeanTwist t) n = squaredDistance f (mrtArchimedeanTwist t) N at heDist
  change (∑ p ∈ P, (1 : ℝ) / p) + (∑ p ∈ primesUpTo n, (1 : ℝ) / p) =
    (∑ p ∈ primesUpTo N, (1 : ℝ) / p) at heMass
  dsimp [K]
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDistanceDecay
namespace OAI

/-! The elementary losses when changing the prime cutoff by a fixed power. -/

namespace TwoPointCorrelations

lemma halasz_decay_shift {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    (max 0 (M - K) + 1) * Real.exp (-max 0 (M - K)) ≤
      Real.exp K * ((M + 1) * Real.exp (-M)) := by
  by_cases hMK : M ≤ K
  · rw [max_eq_left (by linarith : M - K ≤ 0)]
    simp only [zero_add, neg_zero, Real.exp_zero, mul_one]
    have he : 1 ≤ Real.exp K * Real.exp (-M) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ M + 1 by linarith)
      (mul_nonneg (Real.exp_nonneg K) (Real.exp_nonneg (-M)))
    nlinarith
  · rw [max_eq_right (by linarith : 0 ≤ M - K)]
    have he : Real.exp (-(M - K)) = Real.exp K * Real.exp (-M) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right (show M - K + 1 ≤ M + 1 by linarith)
      (mul_nonneg (Real.exp_nonneg K) (Real.exp_nonneg (-M)))
    nlinarith

lemma halasz_log_error_cutoff {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    (hNc : N ≤ n ^ 3) (hllN : 0 ≤ Real.log (Real.log (N : ℝ))) :
    Real.log (Real.log (n : ℝ)) / Real.log n ≤
      3 * (Real.log (Real.log (N : ℝ)) / Real.log N) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlnN : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hln3 : Real.log (N : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have h := Real.log_le_log hN0 (show (N : ℝ) ≤ (n : ℝ) ^ 3 by exact_mod_cast hNc)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  calc
    _ ≤ Real.log (Real.log (N : ℝ)) / Real.log n :=
      div_le_div_of_nonneg_right (Real.log_le_log hln hlnN) hln.le
    _ ≤ 3 * (Real.log (Real.log (N : ℝ)) / Real.log N) := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hln hlN).mpr
      nlinarith [mul_le_mul_of_nonneg_left hln3 hllN]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszGeneralMean
namespace OAI

/-! The ordinary Halász estimate for general normalized multiplicative
functions. Only the values at primes enter the pretentious hypothesis. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

lemma halasz_complete_distance (f : ℕ → ℂ) (g : ℕ → ℂ) (N : ℕ) :
    squaredDistance (mrtCompletePart f) g N = squaredDistance f g N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p hp
  have hprime : p.Prime := (mem_filter.mp hp).2
  have he : mrtCompletePart f p = f p := by
    simpa using mrtCompletePart_prime_pow f hprime 1
  rw [he]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszGeneralException
namespace OAI

/-! The localized exceptional-window mean for ordinary multiplicative functions. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem halasz_general_exceptional_mean : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ (N : ℕ), X₀ ≤ N →
    ∀ (f : ℕ → ℂ), f 1 = 1 → Multiplicative f → OneBounded f →
    ∀ (M₀ τ : ℝ), 0 ≤ M₀ →
      (∀ t ∈ Set.Ioc (-(Real.log (N : ℝ) ^ 8)) (Real.log (N : ℝ) ^ 8),
        t ∉ Set.Ioc (τ-1/2) (τ+1/2) → M₀ ≤ squaredDistance f (mrtArchimedeanTwist t) N) →
      ‖∑ n ∈ Icc 1 N, f n‖ ≤ C * N *
        ((min M₀ (Real.log (1+|τ|)) + 1) * Real.exp (-min M₀ (Real.log (1+|τ|))) +
          Real.log (Real.log N) / Real.log N) := by
  obtain ⟨C₀, Y₀, hC₀, hmean⟩ := halasz_exceptional_mean_value
  obtain ⟨K, hK, hcut⟩ := halasz_distance_cutoff_loss
  let D := C₀ * Real.exp K + 3 * C₀ + 1
  let C := mrtCorrectionBound * D
  have hCorr : 0 < mrtCorrectionBound := Real.exp_pos _
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := mul_pos hCorr hD
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (halasz_eventually_correction_scale Y₀)
  refine ⟨C, X₀, hC, ?_⟩
  intro N hXN f hf1 hf hb M₀ τ hM₀ hd
  obtain ⟨hW, hWY, hWN, htail, hlog, hll⟩ := hX₀ N hXN
  let W := ⌈Real.log (N : ℝ) ^ 4⌉₊
  let M := min M₀ (Real.log (1+|τ|))
  have hM : 0 ≤ M := le_min hM₀ (Real.log_nonneg (by linarith [abs_nonneg τ]))
  have hMM₀ : M ≤ M₀ := min_le_left _ _
  let M' := max 0 (M - K)
  let E := (M + 1) * Real.exp (-M)
  let R := Real.log (Real.log (N : ℝ)) / Real.log N
  let A := C₀ * (Real.exp K * E + 3 * R)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hNlog : 0 < Real.log (N : ℝ) := by linarith
  have hprefix (d : ℕ) (hdN : d ∈ Icc 1 N) (hdW : d ≤ W) :
      ‖∑ n ∈ Icc 1 (N / d), mrtCompletePart f n‖ ≤ A * ((N / d : ℕ) : ℝ) := by
    have hd0 : 0 < d := (mem_Icc.mp hdN).1
    have hWNnat : W ^ 2 ≤ N := by exact_mod_cast hWN
    obtain ⟨hWq, hqN, hNq⟩ := halasz_correction_quotient hW hd0 hdW hWNnat
    have hq2 : 2 ≤ N / d := hW.trans hWq
    have hqY : Y₀ ≤ ((N / d : ℕ) : ℝ) :=
      hWY.trans (by exact_mod_cast hWq)
    have hlnq : 0 < Real.log ((N / d : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N / d by omega))
    have hlogqN : Real.log ((N / d : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < N / d by omega)) (by exact_mod_cast hqN)
    have hheight : Real.log ((N / d : ℕ) : ℝ) ^ 8 ≤ Real.log (N : ℝ) ^ 8 :=
      pow_le_pow_left₀ hlnq.le hlogqN 8
    have hdist (t : ℝ) (ht : t ∈ Set.Ioc
        (-(Real.log ((N / d : ℕ) : ℝ) ^ 8)) (Real.log ((N / d : ℕ) : ℝ) ^ 8))
        (hout : t ∉ Set.Ioc (τ-1/2) (τ+1/2)) :
        M' ≤ squaredDistance (mrtCompletePart f) (mrtArchimedeanTwist t) (N / d) := by
      rw [halasz_complete_distance]
      apply max_le
      · exact halasz_distance_nonneg f hb _ t
      · have hl := hcut f hb (N / d) N hq2 hqN hNq t
        have hu := hd t ⟨by linarith [ht.1], ht.2.trans hheight⟩ hout
        linarith
    have hm := hmean (N / d) hqY (mrtCompletePart f) (fromPrimePowers_one _)
      (fun a b ha hb => mrtCompletePart_mul f ha hb) (mrtCompletePart_oneBounded f hb)
      M' τ (le_max_left _ _) hdist
    have hMlog : M' ≤ Real.log (1+|τ|) := by
      have hm : M ≤ Real.log (1+|τ|) := min_le_right _ _
      exact max_le (Real.log_nonneg (by linarith [abs_nonneg τ])) (by linarith)
    rw [min_eq_left hMlog] at hm
    have hdec := halasz_decay_shift hM hK
    have herr := halasz_log_error_cutoff hq2 hqN hNq (by linarith)
    calc
      _ ≤ C₀ * ((N / d : ℕ) : ℝ) *
          ((M' + 1) * Real.exp (-M') +
            Real.log (Real.log ((N / d : ℕ) : ℝ)) / Real.log ((N / d : ℕ) : ℝ)) := hm
      _ ≤ C₀ * ((N / d : ℕ) : ℝ) * (Real.exp K * E + 3 * R) := by gcongr
      _ = _ := by ring
  have hc := halasz_correction_mean_bound f hf hb hf1 N W (by omega) A hA hprefix
  have hRtail : (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ R := by
    apply htail.trans
    exact div_le_div_of_nonneg_right hll hNlog.le
  have hsmall : A + (W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ D * (E + R) := by
    dsimp [A, D]
    have hCE : 0 ≤ C₀ * Real.exp K * R := by positivity
    have h3E : 0 ≤ 3 * C₀ * E := by positivity
    nlinarith
  calc
    _ ≤ mrtCorrectionBound * N * (A + (W : ℝ) ^ (-(1 / 4 : ℝ))) := hc
    _ ≤ mrtCorrectionBound * N * (D * (E + R)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by dsimp [C, E, R]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTwistedMean
namespace OAI

/-! Height translation for the ordinary mean estimate. This is the
form applied to Dirichlet polynomials on a vertical line. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.ComplexConjugate

lemma halasz_twist_add (t u : ℝ) (n : ℕ) :
    mrtArchimedeanTwist (t + u) n = mrtArchimedeanTwist t n * mrtArchimedeanTwist u n := by
  simp only [mrtArchimedeanTwist, add_mul, Complex.ofReal_add, Complex.exp_add]

lemma halasz_twist_mul (t : ℝ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    mrtArchimedeanTwist t (a * b) = mrtArchimedeanTwist t a * mrtArchimedeanTwist t b := by
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  simp only [mrtArchimedeanTwist, Nat.cast_mul, Real.log_mul har.ne' hbr.ne',
    mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]


lemma halasz_twisted_one (f : ℕ → ℂ) (hf : f 1 = 1) (t : ℝ) :
    halaszTwistedFunction f t 1 = 1 := by simp [halaszTwistedFunction, mrtArchimedeanTwist, hf]


lemma halasz_twisted_oneBounded (f : ℕ → ℂ) (hf : OneBounded f) (t : ℝ) :
    OneBounded (halaszTwistedFunction f t) := by
  intro n hn
  simpa only [halaszTwistedFunction, norm_mul, norm_conj, mrtArchimedeanTwist_norm, mul_one]
    using hf n hn

lemma halasz_twisted_distance (f : ℕ → ℂ) (t u : ℝ) (N : ℕ) :
    squaredDistance (halaszTwistedFunction f t) (mrtArchimedeanTwist u) N =
      squaredDistance f (mrtArchimedeanTwist (t + u)) N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p _
  simp only [halaszTwistedFunction, halasz_twist_add, map_mul, mul_assoc]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszGeneralTwist
namespace OAI

/-! General multiplicative ordinary means after a height translation. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.ComplexConjugate

lemma halasz_twisted_multiplicative (f : ℕ → ℂ) (hf : Multiplicative f) (t : ℝ) :
    Multiplicative (halaszTwistedFunction f t) := by
  intro a b ha hb hab
  simp only [halaszTwistedFunction, hf a b ha hb hab, halasz_twist_mul t ha hb, map_mul]
  ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCountMean
namespace OAI

/-! Ordinary mean cancellation with the literal reciprocal prime-count
weight. Integrating multiplicative soft masks gives the cofactor weight
exactly, while the missing-band and count masks lose only one factor two
in pretentious distance. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.ComplexConjugate _root_.Classical


lemma mrtMissingCoefficient_one (F : ℕ → ℂ) (hF : F 1 = 1)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    mrtMissingCoefficient F Q 1 = 1 := by
  simp only [mrtMissingCoefficient, hF, mrtPrimeMask_one Q hQ, Complex.ofReal_one, mul_one]

lemma mrtMissingCoefficient_multiplicative (F : ℕ → ℂ) (hF : Multiplicative F)
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    Multiplicative (mrtMissingCoefficient F Q) := by
  intro m n hm hn hcop
  simp only [mrtMissingCoefficient, hF m n hm hn hcop,
    mrtPrimeMask_mul Q hQ, Complex.ofReal_mul]
  ring

lemma mrtMissingCoefficient_oneBounded (F : ℕ → ℂ) (hF : OneBounded F)
    (Q : Finset ℕ) : OneBounded (mrtMissingCoefficient F Q) := by
  intro n hn
  rw [mrtMissingCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mrtPrimeMask_bounds Q n).1]
  exact (mul_le_mul (hF n hn) (mrtPrimeMask_bounds Q n).2
    (mrtPrimeMask_bounds Q n).1 zero_le_one).trans_eq (mul_one 1)

lemma mrt_missing_count_one (F : ℕ → ℂ) (hF : F 1 = 1)
    (Q P : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime) (u : ℝ) :
    mrtCountMaskedCoefficient (mrtMissingCoefficient F Q) P u 1 = 1 := by
  simp only [mrtCountMaskedCoefficient, mrtMissingCoefficient_one F hF Q hQ,
    mrtCountMask_one P hP, Complex.ofReal_one, mul_one]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszCountException
namespace OAI

/-! Localize the Halasz distance hypothesis to the frequency window
actually used by a reciprocal-count cofactor. This allows a distant
frequency to be treated even when the minimizing twist is close to zero. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

theorem halasz_local_count_exception_oai : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ N : ℕ, X₀ ≤ N →
    ∀ F : ℕ → ℂ, F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ t τ M : ℝ, 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (N:ℝ)^8 →
        1/2 ≤ |v-τ| → 2*M ≤ squaredDistance F (mrtArchimedeanTwist v) N) →
      ‖∑ n ∈ Icc 1 N, (mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n)) /
        ((finitePrimeDivisorCount P n : ℂ)+1)‖ ≤
      C*N*((min M (Real.log (1+|τ-t|))+1)*Real.exp (-min M (Real.log (1+|τ-t|)))+
          Real.log (Real.log N)/Real.log N) := by
  obtain ⟨C, X₀, hC, hmean⟩ := halasz_general_exceptional_mean
  refine ⟨C, X₀, hC, ?_⟩
  intro N hN F hF1 hFm hFb Q P hQ hP t τ M hM hd
  apply mrt_reciprocal_count_polynomial_bound (Icc 1 N) P
    (fun n => mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n))
  intro u hu hu1
  let G := mrtCountMaskedCoefficient (mrtMissingCoefficient F Q) P u
  have hG1 : G 1 = 1 := mrt_missing_count_one F hF1 Q P hQ hP u
  have hGm : Multiplicative G :=
    (mrtMissingCoefficient_multiplicative F hFm Q hQ).mrtCountMaskedCoefficient P hP u
  have hGb : OneBounded G :=
    (mrtMissingCoefficient_oneBounded F hFb Q).mrtCountMaskedCoefficient P hu hu1
  have hh := hmean N hN (halaszTwistedFunction G t)
    (halasz_twisted_one G hG1 t) (halasz_twisted_multiplicative G hGm t)
    (halasz_twisted_oneBounded G hGb t) M (τ-t) hM (by
      intro v hv hvout
      rw [halasz_twisted_distance]
      have hv' : |(t+v)-t| ≤ Real.log (N:ℝ)^8 := by
        simpa only [add_sub_cancel_left] using abs_le.mpr ⟨hv.1.le,hv.2⟩
      have haway : 1/2 ≤ |(t+v)-τ| := by
        by_contra! hh
        have he : |v-(τ-t)| = |(t+v)-τ| := by congr 1; ring
        rw [← he] at hh
        have hb := abs_lt.mp hh
        exact hvout ⟨by linarith [hb.1],by linarith [hb.2]⟩
      have hl := hd (t+v) hv' haway
      have hm := mrt_missing_count_mask_distance F (mrtArchimedeanTwist (t+v)) Q P hu hu1 N
        (fun p hp => hFb p ((mem_filter.mp hp).2.pos))
        (fun p _ => by rw [mrtArchimedeanTwist_norm])
      change squaredDistance F (mrtArchimedeanTwist (t+v)) N ≤
        2*squaredDistance G (mrtArchimedeanTwist (t+v)) N at hm
      linarith)
  convert (preTransparency := .instances) hh using 1
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [halaszTwistedFunction, G, mrtCountMaskedCoefficient]
  ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_local_count_exception_oai := @OAI.TwoPointCorrelations.halasz_local_count_exception_oai
