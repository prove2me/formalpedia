-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_near_renormalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:54:37.669992+00:00
-- url     : https://prove2.me/submissions/f92243e5-c2b5-4c12-a422-48969f8410bd

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_phase_mean_main_error

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


@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ThetaLogError
namespace OAI

/-! An integrable logarithmic error bound obtained from the stated exponential
prime-number error. It also pays exactly for finite exceptional prime sets. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma log_sq_le_two_mul (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 2 * x := by
  have hh := Real.pow_div_factorial_le_exp (Real.log x) (Real.log_nonneg hx) 2
  norm_num at hh
  rw [Real.exp_log (zero_lt_one.trans_le hx)] at hh
  linarith



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




@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]






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



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitCorrection
namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]


lemma halasz_unit_correction_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    halaszUnitCorrection F (p ^ k) = halaszUnitCorrectionLocal F p k :=
  fromPrimePowers_prime_pow _ (halaszUnitCorrectionLocal_zero F) hp k





lemma halasz_unit_correction_local_bound (F : ℕ → ℂ) (hF : OneBounded F)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ‖halaszUnitCorrectionLocal F p k‖ ≤ 2 := by
  rw [halaszUnitCorrectionLocal, if_neg hk.ne']
  exact (norm_sub_le _ _).trans (by
    linarith [hF (p ^ k) (pow_pos hp.pos k), hF (p ^ (k - 1)) (pow_pos hp.pos _)])


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPositiveLog
namespace OAI

/-! Logarithmic majorization of the absolute constant-one correction.
Only its bound by two on positive prime powers is used. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszPrimePowerLog_nonneg (n : ℕ) : 0 ≤ halaszPrimePowerLog n := by
  unfold halaszPrimePowerLog
  split_ifs with h
  · exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast h.one_lt.le))
  · exact le_rfl

lemma halasz_log_factorization (n : ℕ) (hn : n ≠ 0) :
    Real.log n = ∑ p ∈ n.factorization.support, Real.log ((p ^ n.factorization p : ℕ) : ℝ) := by
  have he := Nat.prod_factorization_pow_eq_self hn
  calc
    _ = Real.log ((n.factorization.prod (fun p k => p ^ k) : ℕ) : ℝ) := by rw [he]
    _ = Real.log (∏ p ∈ n.factorization.support, ((p ^ n.factorization p : ℕ) : ℝ)) := by
      simp only [Finsupp.prod, Nat.cast_prod]
    _ = _ := Real.log_prod (fun p hp => by
      exact_mod_cast pow_ne_zero (n.factorization p) (Nat.prime_of_mem_primeFactors
        (by simpa only [Nat.support_factorization] using hp)).ne_zero)

lemma halasz_unit_correction_log_bound (F : ℕ → ℂ) (hF : OneBounded F) (n : ℕ) :
    ‖halaszUnitCorrection F n‖ * Real.log n ≤
      ∑ d ∈ n.divisors, halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  let S := n.factorization.support
  let v := fun p => p ^ n.factorization p
  have hp (p : ℕ) (h : p ∈ S) : p.Prime :=
    Nat.prime_of_mem_primeFactors (by simpa only [S, Nat.support_factorization] using h)
  have hk (p : ℕ) (h : p ∈ S) : 0 < n.factorization p :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
  have hpower (p : ℕ) (h : p ∈ S) : IsPrimePow (v p) :=
    ⟨p, n.factorization p, (hp p h).prime, hk p h, rfl⟩
  have hvpos (p : ℕ) (h : p ∈ S) : 0 < v p := pow_pos (hp p h).pos _
  have hnorm (p : ℕ) (h : p ∈ S) :
      ‖halaszUnitCorrection F n‖ ≤ 2 * ‖halaszUnitCorrection F (n / v p)‖ := by
    have hquot : 0 < n / v p := Nat.ordCompl_pos p hn
    have hcop := (Nat.coprime_ordCompl (hp p h) hn).pow_left (n.factorization p)
    have he := fromPrimePowers_multiplicative (halaszUnitCorrectionLocal F)
      (v p) (n / v p) (hvpos p h) hquot hcop
    change halaszUnitCorrection F (v p * (n / v p)) =
      halaszUnitCorrection F (v p) * halaszUnitCorrection F (n / v p) at he
    rw [Nat.mul_div_cancel' (Nat.ordProj_dvd n p)] at he
    rw [he, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by rw [halasz_unit_correction_prime_pow F (hp p h)];
          exact halasz_unit_correction_local_bound F hF (hp p h) (hk p h)) (norm_nonneg _)
  have hinj : Set.InjOn v (S : Set ℕ) := by
    intro p hpS q hqS he
    exact ((hp p hpS).pow_inj' (hp q hqS) (hk p hpS).ne' (hk q hqS).ne' he).1
  have hsub : S.image v ⊆ n.divisors.filter IsPrimePow := by
    intro d hd
    obtain ⟨p, hpS, rfl⟩ := mem_image.mp hd
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.ordProj_dvd n p, hn⟩, hpower p hpS⟩
  calc
    _ = ∑ p ∈ S, ‖halaszUnitCorrection F n‖ * Real.log (v p) := by
      rw [halasz_log_factorization n hn, mul_sum]
    _ ≤ ∑ p ∈ S, halaszPrimePowerLog (v p) * ‖halaszUnitCorrection F (n / v p)‖ := by
      apply sum_le_sum
      intro p hpS
      rw [halaszPrimePowerLog, if_pos (hpower p hpS)]
      have hl : 0 ≤ Real.log (v p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (hpower p hpS).one_lt.le)
      nlinarith [mul_le_mul_of_nonneg_right (hnorm p hpS) hl]
    _ = ∑ d ∈ S.image v, halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      (sum_image (f := fun d : ℕ => halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖) hinj).symm
    _ ≤ ∑ d ∈ n.divisors.filter IsPrimePow,
        halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => mul_nonneg
        (halaszPrimePowerLog_nonneg d) (norm_nonneg _))
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro d _
      by_cases hd : IsPrimePow d <;> simp [halaszPrimePowerLog, hd]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerLogBound
namespace OAI

/-! A Chebyshev bound for the prime-power logarithmic kernel appearing in
the positive correction mean. Higher prime powers cost only an absolute
constant times the cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_log_sq_sqrt (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt x * Real.log x ^ 2 ≤ 8 * x := by
  have hs1 : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hx)
  have hh := log_sq_le_two_mul (Real.sqrt x) hs1
  rw [Real.log_sqrt (by linarith : 0 ≤ x)] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg x)
  nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x)]

lemma halasz_prime_power_log_term (N n : ℕ) (hN : 1 ≤ N)
    (hn : n ∈ Icc 1 N) :
    halaszPrimePowerLog n ≤ (2 * Real.log N / Real.log 2) * ArithmeticFunction.vonMangoldt n := by
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hnpp : IsPrimePow n
  · have hn1 : n ≠ 1 := (ne_of_gt hnpp.one_lt)
    have hmin : 2 ≤ n.minFac := (Nat.minFac_prime hn1).two_le
    have hΛ : Real.log 2 ≤ ArithmeticFunction.vonMangoldt n := by
      rw [ArithmeticFunction.vonMangoldt_apply, if_pos hnpp]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hmin)
    have hln : Real.log (n : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1) (by exact_mod_cast (mem_Icc.mp hn).2)
    rw [halaszPrimePowerLog, if_pos hnpp]
    have hh := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ 2 * Real.log N / Real.log 2 by positivity)
    have he : (2 * Real.log N / Real.log 2) * Real.log 2 = 2 * Real.log N := by field_simp
    rw [he] at hh
    linarith
  · rw [halaszPrimePowerLog, if_neg hnpp]
    exact mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg

lemma halasz_prime_power_log_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, halaszPrimePowerLog n) ≤ halaszPrimePowerLogConstant * N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNr
  have hset : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have hsplit : (∑ n ∈ Icc 1 N, halaszPrimePowerLog n) ≤
      2 * Chebyshev.theta N + (2 * Real.log N / Real.log 2) *
        (Chebyshev.psi N - Chebyshev.theta N) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Chebyshev.theta,
      Nat.floor_natCast, hset, mul_sum, mul_sum, sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro n hn
    by_cases hp : n.Prime
    · simp [hp, halaszPrimePowerLog, hp.prime.isPrimePow]
    · simpa only [hp, not_false_eq_true, ite_false, ite_true, zero_add] using
        halasz_prime_power_log_term N n hN hn
  have htheta := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  have htail := Chebyshev.psi_sub_theta_le hNr
  have hsq := halasz_log_sq_sqrt N hNr
  calc
    _ ≤ 2 * Chebyshev.theta N + (2 * Real.log N / Real.log 2) *
        (Chebyshev.psi N - Chebyshev.theta N) := hsplit
    _ ≤ 2 * (Real.log 4 * N) + (2 * Real.log N / Real.log 2) *
        (2 * Real.sqrt N * Real.log N) := by gcongr
    _ = 2 * (Real.log 4 * N) + (4 / Real.log 2) * (Real.sqrt N * Real.log N ^ 2) := by ring
    _ ≤ 2 * (Real.log 4 * N) + (4 / Real.log 2) * (8 * N) := by gcongr
    _ = _ := by unfold halaszPrimePowerLogConstant; ring

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

lemma mrtPrimeMask_prime (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hp : p.Prime) : mrtPrimeMask P p = if p ∈ P then 0 else 1 := by
  have he : mrtPrimeAvoids P p ↔ p ∉ P := by
    constructor
    · intro h hmem
      exact h p hmem (dvd_refl p)
    · intro h q hq hqp
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp
      exact h (heq ▸ hq)
  simp only [mrtPrimeMask, he]
  split_ifs <;> simp_all








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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseCells
namespace OAI

/-! Unit cells for the elementary power-sum approximation. Centering the
cells cancels the linear phase error, leaving a summable quadratic error. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset


@[simp] lemma halasz_power_phase_norm (t x : ℝ) : ‖halaszPowerPhase t x‖ = 1 := by
  simp [halaszPowerPhase, Complex.norm_exp, Complex.mul_re]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNearDiscrepancy
namespace OAI

/-! Prime discrepancy for the near-minimizing twist in MRT Appendix A.
The deleted-prime contribution is kept separate in Cauchy--Schwarz; this
retains the strict exponent needed by the renormalization error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.ComplexConjugate _root_.Classical


lemma halasz_one_sub_norm_sq {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - z‖ ^ 2 ≤ 2 * (1 - z.re) := by
  have hs : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im] at hs ⊢
  nlinarith

lemma halasz_prime_unit_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (t : ℝ) {N p : ℕ} (hp : p ∈ primesUpTo N) :
    ‖F p * conj (mrtArchimedeanTwist t p)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj, mrtArchimedeanTwist_norm, mul_one]
  exact hF p (mem_filter.mp hp).2.pos

lemma halasz_masked_discrepancy_split (F : ℕ → ℂ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (t : ℝ) (N : ℕ) :
    halaszPrimeDiscrepancy (mrtMissingCoefficient F Q) t N =
      (∑ p ∈ (primesUpTo N).filter (fun p => p ∈ Q), (1 : ℝ) / p) +
      ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
        ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p := by
  unfold halaszPrimeDiscrepancy
  rw [← sum_filter_add_sum_filter_not (primesUpTo N) (fun p => p ∈ Q)]
  congr 1 <;> apply sum_congr rfl
  · intro p hp
    obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
    rw [mrtMissingCoefficient, mrtPrimeMask_prime Q hQ (mem_filter.mp hpN).2,
      if_pos hpQ]
    simp
  · intro p hp
    obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
    rw [mrtMissingCoefficient, mrtPrimeMask_prime Q hQ (mem_filter.mp hpN).2,
      if_neg hpQ]
    simp

lemma halasz_undeleted_discrepancy_sq (F : ℕ → ℂ) (hF : OneBounded F)
    (Q : Finset ℕ) (t : ℝ) (N : ℕ) :
    (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
      ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p) ^ 2 ≤
      2 * (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p) *
        squaredDistance F (mrtArchimedeanTwist t) N := by
  let S := (primesUpTo N).filter (fun p => p ∉ Q)
  have hdef (p : ℕ) (hp : p ∈ primesUpTo N) :
      0 ≤ 1 - (F p * conj (mrtArchimedeanTwist t p)).re :=
    sub_nonneg.mpr ((Complex.re_le_norm _).trans (halasz_prime_unit_bound F hF t hp))
  have hh := sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := fun p => ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / (p : ℝ))
    (f := fun p => (1 : ℝ) / p)
    (g := fun p => 2 * (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p)
    (fun _ _ => by positivity)
    (fun p hp => div_nonneg (mul_nonneg (by norm_num) (hdef p (mem_filter.mp hp).1))
      (Nat.cast_nonneg p)) (fun p hp => ?_)
  · have hd : (∑ p ∈ S, (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p) ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp _
      exact div_nonneg (hdef p hp) (Nat.cast_nonneg p)
    have he : (∑ p ∈ S, 2 * (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p) =
        2 * ∑ p ∈ S, (1 - (F p * conj (mrtArchimedeanTwist t p)).re) / p := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    rw [he] at hh
    exact hh.trans (by
      have h := mul_le_mul_of_nonneg_left hd
        (show 0 ≤ 2 * ∑ p ∈ S, (1 : ℝ) / p by positivity)
      convert (preTransparency := .instances) h using 1
      ring)
  · have hsq := halasz_one_sub_norm_sq (halasz_prime_unit_bound F hF t (mem_filter.mp hp).1)
    rw [div_pow]
    apply (div_le_div_of_nonneg_right hsq (sq_nonneg (p : ℝ))).trans_eq
    ring

lemma halasz_near_discrepancy_numeric (L A B Z D : ℝ) (hL : 0 ≤ L)
    (hAB : A ≤ B)
    (hAhi : A ≤ 51 / 100 * L) (hBhi : B ≤ 101 / 100 * L)
    (hD : D ≤ L / 8) (hZsq : Z ^ 2 ≤ 2 * (B - A) * D) :
    A + Z ≤ 7 / 8 * L := by
  have hm := mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ 2 * (B - A))
  have hprod : 0 ≤ (A - 51 / 100 * L) * (A - 99 / 100 * L) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  by_contra hh
  have hz : 7 / 8 * L - A < Z := by linarith
  have hz0 : 0 ≤ 7 / 8 * L - A := by linarith
  have hs := mul_self_lt_mul_self hz0 hz
  nlinarith

/-- The `7/8` prime-discrepancy estimate used for near-twist renormalization.
Only primes below the actual Appendix-A cutoff may be deleted. -/
theorem halasz_near_masked_discrepancy :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      halaszPrimeDiscrepancy (mrtMissingCoefficient F Q) t N ≤
        7 / 8 * Real.log (Real.log N) := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := (Real.tendsto_log_atTop.comp hlog).eventually
    (eventually_ge_atTop (100 * |C|))
  filter_upwards [hlog.eventually (eventually_ge_atTop (4 : ℝ)), hll] with N hl hllN
  dsimp only [Function.comp_def] at hllN
  intro F hF Q hQ hcut t hD
  let L := Real.log (Real.log N)
  let A := ∑ p ∈ (primesUpTo N).filter (fun p => p ∈ Q), (1 : ℝ) / p
  let B := ∑ p ∈ primesUpTo N, (1 : ℝ) / p
  let Z := ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q),
    ‖1 - F p * conj (mrtArchimedeanTwist t p)‖ / p
  have hL : 0 ≤ L := by dsimp [L]; linarith [abs_nonneg C]
  have hCsmall : C ≤ L / 100 := by dsimp [L]; linarith [le_abs_self C]
  have hN1 : 1 < (N : ℝ) := (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ N := by exact_mod_cast hN1
    exact_mod_cast this
  have hB : B ≤ 101 / 100 * L := by
    have hh := (abs_le.mp (hC N hN2)).2
    rw [mrt_sievePrimesUpTo_nat] at hh
    dsimp [B, L]
    linarith
  have hsqrt : 2 ≤ Real.sqrt (Real.log N) := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ Real.log N)
    have hn := Real.sqrt_nonneg (Real.log N)
    nlinarith
  have hY2 : 2 ≤ Real.exp (Real.sqrt (Real.log N)) := by
    linarith [Real.add_one_le_exp (Real.sqrt (Real.log N))]
  have hA : A ≤ 51 / 100 * L := by
    have hsub : (primesUpTo N).filter (fun p => p ∈ Q) ⊆
        sievePrimesUpTo (Real.exp (Real.sqrt (Real.log N))) := by
      intro p hp
      obtain ⟨hpN, hpQ⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (by positivity)).mpr
        (hcut p hpQ)), (mem_filter.mp hpN).2⟩
    have ha := sum_le_sum_of_subset_of_nonneg hsub
      (f := fun p : ℕ => (1 : ℝ) / p) (by intros; positivity)
    have hb := (abs_le.mp (hC _ hY2)).2
    rw [Real.log_exp, Real.log_sqrt (by linarith : 0 ≤ Real.log N)] at hb
    dsimp [A, L] at *
    linarith
  have hmass : (∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p) = B - A := by
    have hh := sum_filter_add_sum_filter_not (primesUpTo N) (fun p => p ∈ Q)
      (fun p : ℕ => (1 : ℝ) / p)
    dsimp [A, B]
    linarith
  have hAB : A ≤ B := by
    have hh : 0 ≤ ∑ p ∈ (primesUpTo N).filter (fun p => p ∉ Q), (1 : ℝ) / p := by positivity
    rw [hmass] at hh
    linarith
  have hZ := halasz_undeleted_discrepancy_sq F hF Q t N
  rw [hmass] at hZ
  have hh := halasz_near_discrepancy_numeric L A B Z
    (squaredDistance F (mrtArchimedeanTwist t) N) hL hAB hA hB hD hZ
  simpa only [halasz_masked_discrepancy_split F Q hQ t N, A, Z] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitEuler
namespace OAI

/-! Absolute Euler control of the constant-one convolution correction.
The first-order exponent is the actual prime discrepancy. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_unit_reciprocal_nonneg (F : ℕ → ℂ) (n : ℕ) :
    0 ≤ halaszUnitReciprocal F n := by unfold halaszUnitReciprocal; positivity

lemma halasz_unit_reciprocal_one (F : ℕ → ℂ) : halaszUnitReciprocal F 1 = 1 := by
  simp [halaszUnitReciprocal, halaszUnitCorrection, mrtArithmetic]

lemma halasz_unit_reciprocal_mul (F : ℕ → ℂ) {m n : ℕ} (hcop : m.Coprime n) :
    halaszUnitReciprocal F (m * n) = halaszUnitReciprocal F m * halaszUnitReciprocal F n := by
  have hh := mrtArithmetic_isMultiplicative (halaszUnitCorrection F)
    (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  unfold halaszUnitReciprocal
  rw [hh.map_mul_of_coprime hcop, norm_mul, Nat.cast_mul, mul_div_mul_comm]

lemma halasz_unit_reciprocal_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    halaszUnitReciprocal F (p ^ k) =
      ‖halaszUnitCorrectionLocal F p k‖ * ((p : ℝ)⁻¹) ^ k := by
  unfold halaszUnitReciprocal
  rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos k), halasz_unit_correction_prime_pow F hp,
    Nat.cast_pow, div_eq_mul_inv, inv_pow]

lemma halasz_unit_reciprocal_local_summable (F : ℕ → ℂ) (hF : OneBounded F)
    {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => halaszUnitReciprocal F (p ^ k)) := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  apply Summable.of_nonneg_of_le (fun k => halasz_unit_reciprocal_nonneg F (p ^ k))
    (f := fun k => 2 * ((p : ℝ)⁻¹) ^ k)
  · intro k
    rw [halasz_unit_reciprocal_prime_pow F hp]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rcases k with _ | k
    · simp
    · exact halasz_unit_correction_local_bound F hF hp (Nat.succ_pos k)
  · exact (summable_geometric_of_lt_one (by positivity) hr).mul_left 2

lemma halasz_unit_reciprocal_local_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) ≤
      Real.exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2) := by
  let r : ℝ := (p : ℝ)⁻¹
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by simpa only [one_div] using inv_anti₀ (by norm_num) hp2
  have hr1 : r < 1 := by linarith
  have hs := halasz_unit_reciprocal_local_summable F hF hp
  have ht : (∑' k : ℕ, halaszUnitReciprocal F (p ^ (k + 2))) ≤
      2 * r ^ 2 * (1 - r)⁻¹ := by
    have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left (2 * r ^ 2)
    rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
    apply (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum _ hgeom
    intro k
    change halaszUnitReciprocal F (p ^ (k + 2)) ≤ _
    rw [halasz_unit_reciprocal_prime_pow F hp]
    have hh := halasz_unit_correction_local_bound F hF hp (by omega : 0 < k + 2)
    calc
      _ ≤ 2 * r ^ (k + 2) := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by rw [pow_add]; ring
  have he : (∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) =
      1 + ‖1 - F p‖ / p + ∑' k : ℕ, halaszUnitReciprocal F (p ^ (k + 2)) := by
    have hh := (hs.sum_add_tsum_nat_add 2).symm
    simpa [sum_range_succ, halasz_unit_reciprocal_prime_pow F hp,
      halaszUnitCorrectionLocal, hF1, norm_sub_rev, div_eq_mul_inv] using hh
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
    linarith
  have htail : 2 * r ^ 2 * (1 - r)⁻¹ ≤ 4 / (p : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * r ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by dsimp [r]; simp only [inv_pow, div_eq_mul_inv]; ring
  calc
    _ ≤ 1 + ‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2 := by rw [he]; linarith
    _ ≤ _ := by
      have hh := Real.add_one_le_exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2)
      linarith

lemma halasz_unit_reciprocal_prefix_le_prod (F : ℕ → ℂ) (hF : OneBounded F) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) ≤
      ∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k) := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖halaszUnitReciprocal F (p ^ k)‖) := by
    intro p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (halasz_unit_reciprocal_nonneg F _)] using
      halasz_unit_reciprocal_local_summable F hF hp
  obtain ⟨_, he⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := halaszUnitReciprocal F) (halasz_unit_reciprocal_one F) (fun {_ _} h => halasz_unit_reciprocal_mul F h)
    hlocal (N + 1)
  have hi : HasSum ((Nat.smoothNumbers (N + 1)).indicator (halaszUnitReciprocal F))
      (∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) :=
    (hasSum_subtype_iff_indicator (f := halaszUnitReciprocal F)
      (s := Nat.smoothNumbers (N + 1))).mp he
  have hsum : (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, (Nat.smoothNumbers (N + 1)).indicator (halaszUnitReciprocal F) n := by
    apply sum_congr rfl
    intro n hn
    have hn' := mem_Icc.mp hn
    rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hn'.1 (by omega))]
    unfold halaszUnitReciprocal
    rw [mrtArithmetic_apply_pos _ hn'.1]
  rw [hsum]
  have hfirst := hi.summable.sum_le_tsum (Icc 1 N)
    (fun n _ => Set.indicator_nonneg (fun n _ => halasz_unit_reciprocal_nonneg F n) n)
  rw [hi.tsum_eq] at hfirst
  exact hfirst

lemma halasz_unit_reciprocal_prod_bound (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) :
    (∏ p ∈ primesUpTo N, ∑' k : ℕ, halaszUnitReciprocal F (p ^ k)) ≤
      Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := by
  calc
    _ ≤ ∏ p ∈ primesUpTo N, Real.exp (‖1 - F p‖ / p + 4 / (p : ℝ) ^ 2) := by
      apply Finset.prod_le_prod
      · intro p _
        exact tsum_nonneg (fun _ => halasz_unit_reciprocal_nonneg F _)
      · intro p hp
        exact halasz_unit_reciprocal_local_bound F hF hF1 (mem_filter.mp hp).2
    _ = Real.exp ((∑ p ∈ primesUpTo N, ‖1 - F p‖ / p) +
        4 * ∑ p ∈ primesUpTo N, 1 / (p : ℝ) ^ 2) := by
      rw [← Real.exp_sum, sum_add_distrib, mul_sum]
      congr 2
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ Real.exp ((∑ p ∈ primesUpTo N, ‖1 - F p‖ / p) + 8) := by
      apply Real.exp_le_exp.mpr
      linarith [mrt_prime_inverse_square_sum N]
    _ = _ := by simp [halaszPrimeDiscrepancy, mrtArchimedeanTwist]

/-- Absolute reciprocal mass of the exact constant-one correction. -/
theorem halasz_unit_correction_reciprocal (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ)) ≤
      Real.exp (halaszPrimeDiscrepancy F 0 N + 8) :=
  (halasz_unit_reciprocal_prefix_le_prod F hF N).trans
    (halasz_unit_reciprocal_prod_bound F hF hF1 N)

lemma halasz_twisted_prime_discrepancy (F : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    halaszPrimeDiscrepancy (halaszTwistedFunction F t) 0 N =
      halaszPrimeDiscrepancy F t N := by
  simp [halaszPrimeDiscrepancy, halaszTwistedFunction, mrtArchimedeanTwist]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitMean
namespace OAI

/-! An ordinary absolute mean bound for the constant-one correction.
A positive logarithmic convolution and the finite Euler bound retain the
full prime-discrepancy exponent. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_real_hyperbola (G : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, G p.1 p.2) =
      ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G d m := by
  have hh := (halasz_sum_divisorsAntidiagonal (fun d m => (G d m : ℂ)) N).trans
    (halasz_hyperbola_rows (fun d m => (G d m : ℂ)) N)
  exact_mod_cast hh

lemma halasz_unit_logarithmic_sum (F : ℕ → ℂ) (hF : OneBounded F) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ * Real.log n) ≤
      halaszPrimePowerLogConstant * N *
        ∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ) := by
  have hC : 0 ≤ halaszPrimePowerLogConstant := by
    unfold halaszPrimePowerLogConstant
    positivity
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors,
        halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      sum_le_sum (fun n _ => halasz_unit_correction_log_bound F hF n)
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
        halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖ := by
      calc
        _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
            halaszPrimePowerLog p.2 * ‖halaszUnitCorrection F p.1‖ := by
          apply sum_congr rfl
          intro n _
          exact (Nat.sum_divisorsAntidiagonal' (fun d m =>
            halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖)).symm
        _ = _ := halasz_real_hyperbola (fun d m => halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖) N
    _ ≤ ∑ d ∈ Icc 1 N, (halaszPrimePowerLogConstant * N) *
        (‖halaszUnitCorrection F d‖ / (d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      have hq : 1 ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr (by simpa using (mem_Icc.mp hd).2)
      rw [← sum_mul]
      calc
        _ ≤ (halaszPrimePowerLogConstant * (N / d : ℕ)) * ‖halaszUnitCorrection F d‖ :=
          mul_le_mul_of_nonneg_right (halasz_prime_power_log_sum (N / d) hq) (norm_nonneg _)
        _ ≤ (halaszPrimePowerLogConstant * ((N : ℝ) / d)) * ‖halaszUnitCorrection F d‖ := by
          gcongr
          exact Nat.cast_div_le
        _ = _ := by ring
    _ = _ := (mul_sum _ _ _).symm

lemma halasz_positive_log_to_mean (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log N * (∑ n ∈ Icc 1 N, g n) ≤
      (∑ n ∈ Icc 1 N, g n * Real.log n) +
        (N : ℝ) * ∑ n ∈ Icc 1 N, g n / n := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh := Real.log_le_sub_one_of_pos (div_pos hN0 hn0)
  rw [Real.log_div hN0.ne' hn0.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left hh (hg n)
  have he : (N : ℝ) * (g n / n) = g n * ((N : ℝ) / n) := by ring
  rw [he]
  nlinarith [hg n]

theorem halasz_unit_correction_mean (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖) ≤
      (halaszPrimePowerLogConstant + 1) * N / Real.log N *
        Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := by
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ halaszPrimePowerLogConstant + 1 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have hh := halasz_positive_log_to_mean (fun n => ‖halaszUnitCorrection F n‖)
    (fun _ => norm_nonneg _) N (by omega)
  have hw := halasz_unit_logarithmic_sum F hF N
  have he := halasz_unit_correction_reciprocal F hF hF1 N
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hl).mpr
  have hmul := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (halaszPrimePowerLogConstant + 1) * (N : ℝ) by positivity)
  calc
    _ ≤ (halaszPrimePowerLogConstant + 1) * N *
        ∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ) := by nlinarith
    _ ≤ (halaszPrimePowerLogConstant + 1) * N *
        Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := hmul
    _ = _ := by ring

/-- Near the minimizing twist the absolute unit correction has a genuine
logarithmic saving, uniformly over all allowed missing-band masks. -/
theorem halasz_near_correction_mean :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      (∑ n ∈ Icc 1 N,
        ‖halaszUnitCorrection (halaszTwistedFunction (mrtMissingCoefficient F Q) t) n‖) ≤
          ((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
            (Real.log N) ^ (-1 / (8 : ℝ)) := by
  filter_upwards [halasz_near_masked_discrepancy, Filter.eventually_ge_atTop 2]
    with N hN hN2
  intro F hF1 hF Q hQ hcut t hD
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ halaszPrimePowerLogConstant + 1 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have hmean := halasz_unit_correction_mean (halaszTwistedFunction (mrtMissingCoefficient F Q) t)
    (halasz_twisted_oneBounded _ (mrtMissingCoefficient_oneBounded F hF Q) t)
    (halasz_twisted_one _ (mrtMissingCoefficient_one F hF1 Q hQ) t) N hN2
  rw [halasz_twisted_prime_discrepancy] at hmean
  apply hmean.trans
  have hdis := hN F hF Q hQ hcut t hD
  have he : Real.exp (7 / 8 * Real.log (Real.log N) + 8) =
      Real.exp 8 * (Real.log N) ^ (7 / (8 : ℝ)) := by
    rw [Real.rpow_def_of_pos hl, ← Real.exp_add]
    congr 1
    ring
  have hp : (Real.log N) ^ (7 / (8 : ℝ)) / Real.log N =
      (Real.log N) ^ (-1 / (8 : ℝ)) := by
    calc
      _ = (Real.log N) ^ (7 / (8 : ℝ)) / (Real.log N) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (Real.log N) ^ (7 / (8 : ℝ) - 1) := (Real.rpow_sub hl _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ (halaszPrimePowerLogConstant + 1) * N / Real.log N *
        Real.exp (7 / 8 * Real.log (Real.log N) + 8) := by gcongr
    _ = ((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        ((Real.log N) ^ (7 / (8 : ℝ)) / Real.log N) := by rw [he]; ring
    _ = _ := by rw [hp]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitRenormalization
namespace OAI

/-! Elementary near-twist renormalization using the absolute unit correction.
The power-sum error is uniform in the summation cutoff and linear in the twist. -/

namespace TwoPointCorrelations

open _root_.Finset




lemma halasz_phase_factor_norm (t x : ℝ) :
    ‖halaszPowerPhase t x / (1 + (-t : ℂ) * Complex.I)‖ ≤ 1 := by
  have hd : 1 ≤ ‖(1 : ℂ) + (-t : ℂ) * Complex.I‖ := by
    simpa [Complex.mul_re] using Complex.re_le_norm ((1 : ℂ) + (-t : ℂ) * Complex.I)
  rw [norm_div, halasz_power_phase_norm]
  exact (div_le_one (by linarith)).mpr hd




/-- A cutoff-uniform renormalization. Only the absolute correction mass is
needed; its near-center saving is supplied by `halasz_near_correction_mean`. -/
theorem halasz_unit_renormalization (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszPhaseMean F 0 N‖ ≤
      18 * (1 + |t|) * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
  have hzero : halaszPowerPhase 0 N / (1 + (-(0 : ℝ) : ℂ) * Complex.I) = 1 := by
    simp [halaszPowerPhase]
  have h0 := halasz_phase_mean_main_error F hF hF1 0 N
  rw [hzero, one_mul] at h0
  norm_num at h0
  have ht := halasz_phase_mean_main_error F hF hF1 t N
  have he : halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszPhaseMean F 0 N =
      (halaszPhaseMean F t N -
        (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N) +
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) *
        (halaszUnitMain F N - halaszPhaseMean F 0 N) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hh : ‖(halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) *
        (halaszUnitMain F N - halaszPhaseMean F 0 N)‖ ≤
      9 * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
    rw [norm_mul, norm_sub_rev]
    exact (mul_le_mul_of_nonneg_right (halasz_phase_factor_norm t N) (norm_nonneg _)).trans
      (by simpa using h0)
  have hmass : 0 ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [abs_nonneg t]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszNearRenormalization
namespace OAI

/-! Uniform renormalization on the small neighborhood of the minimizing twist.
This is the near-twist ingredient needed for the MRT Fourier energy estimate. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

/-- The elementary unit-correction argument loses only `log(N)^(-1/16)`
on the whole near-center frequency interval. -/
theorem halasz_near_renormalization :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      ∀ u : ℝ, |u| ≤ (Real.log N) ^ (1 / (16 : ℝ)) →
      let G := halaszTwistedFunction (mrtMissingCoefficient F Q) t
      ‖halaszPhaseMean G u N -
        (halaszPowerPhase u N / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean G 0 N‖ ≤
      (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        (Real.log N) ^ (-1 / (16 : ℝ)) := by
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [halasz_near_correction_mean, hlog] with N hmean hlogN
  intro F hF1 hFm hFb Q hQ hcut t hD u hu
  dsimp only
  let G := halaszTwistedFunction (mrtMissingCoefficient F Q) t
  have hGm : Multiplicative G := halasz_twisted_multiplicative _
    (mrtMissingCoefficient_multiplicative F hFm Q hQ) t
  have hG1 : G 1 = 1 := halasz_twisted_one _ (mrtMissingCoefficient_one F hF1 Q hQ) t
  have hh := halasz_unit_renormalization G hGm hG1 u N
  have hm := hmean F hF1 hFb Q hQ hcut t hD
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hp : 1 ≤ (Real.log N) ^ (1 / (16 : ℝ)) := Real.one_le_rpow hlogN (by norm_num)
  have hb : 18 * (1 + |u|) ≤ 36 * (Real.log N) ^ (1 / (16 : ℝ)) := by linarith
  have hc : 0 ≤ (halaszPrimePowerLogConstant + 1) * Real.exp 8 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have he : (Real.log N) ^ (1 / (16 : ℝ)) * (Real.log N) ^ (-1 / (8 : ℝ)) =
      (Real.log N) ^ (-1 / (16 : ℝ)) := by
    rw [← Real.rpow_add hl]
    norm_num
  apply hh.trans
  calc
    _ ≤ (36 * (Real.log N) ^ (1 / (16 : ℝ))) *
        (((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
          (Real.log N) ^ (-1 / (8 : ℝ))) := by
      exact mul_le_mul hb hm (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        ((Real.log N) ^ (1 / (16 : ℝ)) * (Real.log N) ^ (-1 / (8 : ℝ))) := by ring
    _ = _ := by rw [he]

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_near_renormalization := @OAI.TwoPointCorrelations.halasz_near_renormalization
