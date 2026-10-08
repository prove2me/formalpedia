-- Prove2me | solution 1 for OAI.TwoPointCorrelations.minor_arc_actual_working_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:18:26.726543+00:00
-- url     : https://prove2.me/submissions/8b6d6cef-91e7-4a5e-9eee-2b97e2115165

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_minor_arc_bilinear_parameter_saving

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds
namespace OAI
noncomputable section

open scoped _root_.BigOperators

namespace Problem337


instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩







end Problem337

end

end OAI

end

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



@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
namespace OAI

/-!
# Dirichlet character twists preserve uniform nonpretentiousness

Characters with different moduli are multiplied after changing both levels
to the product modulus. The resulting character equals the pointwise product
on every natural number, including the nonunit classes. This gives an exact
identity of pretentious distances and preserves the original height cutoff.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter



@[simp] lemma conjugateCharacter_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    conjugateCharacter χ n = conj (χ n) := rfl








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Dilation
namespace OAI

/-!
# Finite multiplicative expansion of a dilation

This is the arithmetic content of manuscript Lemma `lem:affine-dilation`.
The equality is asserted for positive arguments, the domain relevant to
ordinary multiplicative functions. No complete multiplicativity is used.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations










@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
namespace OAI

/-!
# Residue classes as finite multiplicative expansions

The character identity in manuscript Lemma `lem:affine-residue` includes
nonunit residue classes. Dividing by the gcd reduces to a unit class, so the
standard character orthogonality relation applies even when the reduced
modulus is one. Each resulting dilation has the finite expansion already
proved in `Dilation`.
-/

open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations




@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]














end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma shortExponentialSum_on_unit_cell (b : ℕ → ℂ) (D : ℕ) (α : ℝ)
    (v : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (v : ℝ) (v + 1)) :
    shortExponentialSum b D α y = shortExponentialSum b D α v := by
  have hy0 : 0 ≤ y := (Nat.cast_nonneg v).trans hy.1
  have hf := Nat.floor_eq_on_Ico v y hy
  unfold shortExponentialSum
  rw [Nat.floor_add_natCast hy0, hf, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D, Nat.floor_natCast]

lemma shortExponentialSum_unit_integrable (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    IntervalIntegrable (fun y => ‖shortExponentialSum b D α y‖)
      volume (v : ℝ) (v + 1) := by
  apply (intervalIntegrable_const : IntervalIntegrable
    (fun _ : ℝ => ‖shortExponentialSum b D α v‖) volume (v : ℝ) (v + 1)).congr_uIoo
  intro y hy
  rw [Set.uIoo_of_le (by linarith : (v : ℝ) ≤ v + 1)] at hy
  exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩).symm

lemma integral_shortExponentialSum_unit (b : ℕ → ℂ) (D : ℕ) (α : ℝ) (v : ℕ) :
    (∫ y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α y‖) =
      ‖shortExponentialSum b D α v‖ := by
  calc
    _ = ∫ _y in (v : ℝ)..(v + 1), ‖shortExponentialSum b D α v‖ := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
      intro y hy
      exact congrArg norm (shortExponentialSum_on_unit_cell b D α v ⟨hy.1.le, hy.2⟩)
    _ = _ := by simp

/-- Exact unit-cell decomposition, with no endpoint error. -/
theorem shortExponentialIntegral_eq_sum (b : ℕ → ℂ) (X D : ℕ) (α : ℝ) :
    shortExponentialIntegral b X D α =
      ∑ v ∈ range X, ‖shortExponentialSum b D α v‖ := by
  unfold shortExponentialIntegral
  symm
  calc
    _ = ∑ v ∈ range X, ∫ y in (v : ℝ)..((v + 1 : ℕ) : ℝ),
        ‖shortExponentialSum b D α y‖ := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (integral_shortExponentialSum_unit b D α v).symm
    _ = _ := by
      simpa only [Nat.cast_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => (n : ℝ)) (n := X)
          (fun v _ => by simpa only [Nat.cast_add, Nat.cast_one] using
            shortExponentialSum_unit_integrable b D α v))


lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl

lemma shortExponentialSum_at_nat (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v =
      ∑ n ∈ Icc (v + 1) (v + D), b n * additiveCharacter α n := by
  simp only [shortExponentialSum, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D]


lemma norm_additiveCharacter (α : ℝ) (n : ℕ) : ‖additiveCharacter α n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcDyadicSummation
namespace OAI

/-! Summing the reciprocal logarithmic saving over dyadic prime blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma minor_arc_dyadic_prime_bounds {p j : ℕ} (hp : 0 < p) (hj : Nat.log 2 p = j) :
    2 ^ j ≤ p ∧ p ≤ 2 * 2 ^ j := by
  have hl := Nat.pow_log_le_self 2 hp.ne'
  have hu := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rw [hj] at hl hu
  rw [pow_succ] at hu
  exact ⟨hl, by omega⟩

lemma minor_arc_dyadic_index_pos {p : ℕ} (hp : 2 ≤ p) : 1 ≤ Nat.log 2 p := by
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  simpa using hp



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcWindowInterval
namespace OAI

/-! Exact finite cofactor intervals for discrete short-sum origins. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma mem_minorArcWindowInterval (M A k H m : ℕ) (hA : 0 < A) :
    m ∈ minorArcWindowInterval M A k H ↔
      m < M ∧ k < A * m ∧ A * m ≤ k + H := by
  unfold minorArcWindowInterval
  rw [mem_Ico, lt_min_iff]
  have hlow : k / A < m ↔ k < A * m := by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hA : k / A < m ↔ k < m * A)
  have hhigh : m ≤ (k + H) / A ↔ A * m ≤ k + H := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hA : m ≤ (k + H) / A ↔ m * A ≤ k + H)
  omega





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








@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]






@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := if_neg hn.ne'




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









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix
namespace OAI

/-! Exact change of variables `x=u*z` for a divisibility indicator,
including the floor endpoint `floor(X/u)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_eq_Icc (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix F X = ∑ n ∈ Icc 1 X, F n := by
  simpa only [Nat.zero_add, positivePrefix] using (sum_Icc_shift F 0 X).symm

theorem divisibility_positivePrefix (F : ℕ → ℂ) (u X : ℕ) (hu : 0 < u) :
    positivePrefix (fun n => natDivisibilityIndicator u n * F n) X =
      positivePrefix (fun z => F (u * z)) (X / u) := by
  calc
    _ = ∑ n ∈ (Icc 1 X).filter (fun n => u ∣ n), F n := by
      rw [positivePrefix_eq_Icc, sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : u ∣ n <;> simp only [natDivisibilityIndicator, hn, ite_true, ite_false,
        one_mul, zero_mul]
    _ = ∑ z ∈ Icc 1 (X / u), F (u * z) := by
      symm
      apply sum_bij (fun z _ => u * z)
      · intro z hz
        obtain ⟨hz₁, hzX⟩ := mem_Icc.mp hz
        apply mem_filter.mpr
        refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hu hz₁, ?_⟩, dvd_mul_right u z⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu).mp hzX
      · intro z _ w _ heq
        exact Nat.eq_of_mul_eq_mul_left hu heq
      · intro n hn
        obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn₁, hnX⟩ := mem_Icc.mp hnI
        refine ⟨n / u, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnX⟩, Nat.mul_div_cancel' hdiv⟩
        exact Nat.div_pos (Nat.le_of_dvd hn₁ hdiv) hu
      · intro z _
        rfl
    _ = _ := (positivePrefix_eq_Icc (fun z => F (u * z)) (X / u)).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRamareIdentity
namespace OAI

/-! The corrected Ramaré identity from MRT v3, equation (3.2).
The denominator retains `1_{p ∤ m}`; repeated prime factors are allowed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma finitePrimeDivisorCount_eq_card (P : Finset ℕ) (n : ℕ) :
    finitePrimeDivisorCount P n = (P.filter (fun p => p ∣ n)).card := by
  simp [finitePrimeDivisorCount, sum_boole]

lemma finitePrimeDivisorCount_insert {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (n : ℕ) :
    finitePrimeDivisorCount (insert p P) n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount P n := by
  simp only [finitePrimeDivisorCount, sum_insert hp]

lemma finitePrimeDivisorCount_pos_of_mem {P : Finset ℕ} {p n : ℕ}
    (hp : p ∈ P) (hpn : p ∣ n) : 0 < finitePrimeDivisorCount P n := by
  rw [finitePrimeDivisorCount_eq_card, card_pos]
  exact ⟨p, mem_filter.mpr ⟨hp, hpn⟩⟩

/-- The correction term distinguishes a new prime from a repeated prime. -/
theorem mrt_prime_divisor_count_mul (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) (m : ℕ) :
    finitePrimeDivisorCount P (p * m) =
      (if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m := by
  have hc (n : ℕ) : finitePrimeDivisorCount P n =
      (if p ∣ n then 1 else 0) + finitePrimeDivisorCount (P.erase p) n := by
    conv_lhs => rw [← insert_erase hp]
    exact finitePrimeDivisorCount_insert (notMem_erase p P) n
  have he : finitePrimeDivisorCount (P.erase p) (p * m) =
      finitePrimeDivisorCount (P.erase p) m := by
    unfold finitePrimeDivisorCount
    apply sum_congr rfl
    intro q hq
    have hq' := mem_erase.mp hq
    have hqprime := hP q hq'.2
    have hqp : ¬q ∣ p := by
      intro hdiv
      exact hq'.1 ((Nat.prime_dvd_prime_iff_eq hqprime (hP p hp)).mp hdiv)
    simp only [hqprime.dvd_mul, hqp, false_or]
  rw [hc (p * m), hc m, he]
  simp only [dvd_mul_right, ite_true]
  split_ifs <;> omega

lemma mrt_ramare_common_denominator (P : Finset ℕ) (F : ℕ → ℂ) (n : ℕ) :
    (∑ p ∈ P, if p ∣ n then F n / (finitePrimeDivisorCount P n : ℂ) else 0) =
      if finitePrimeDivisorCount P n = 0 then 0 else F n := by
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, ← finitePrimeDivisorCount_eq_card]
  by_cases hn : finitePrimeDivisorCount P n = 0
  · simp [hn]
  · rw [if_neg hn]
    have hn' : (finitePrimeDivisorCount P n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp

/-- Corrected pointwise factorization, with no squarefree assumption. -/
theorem mrt_ramare_identity (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : ℕ → ℂ) (n : ℕ) :
    (if finitePrimeDivisorCount P n = 0 then 0 else F n) =
      ∑ p ∈ P, if p ∣ n then
        F (p * (n / p)) /
          (((if p ∣ n / p then 0 else 1) + finitePrimeDivisorCount P (n / p) : ℕ) : ℂ)
        else 0 := by
  rw [← mrt_ramare_common_denominator P F n]
  apply sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · simp only [hpn, ite_true]
    have he := Nat.mul_div_cancel' hpn
    have hc := mrt_prime_divisor_count_mul P hP hp (n / p)
    rw [he] at hc ⊢
    rw [hc]
  · simp only [hpn, ite_false]


lemma mrt_inverse_successor_difference {k : ℕ} (hk : 0 < k) :
    ‖(k : ℂ)⁻¹ - ((k + 1 : ℕ) : ℂ)⁻¹‖ ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1C : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have he : (k : ℂ)⁻¹ - ((k + 1 : ℕ) : ℂ)⁻¹ =
      ((1 / ((k : ℝ) * (k + 1)) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  apply (div_le_one (by positivity)).mpr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- Replacing the corrected denominator by `ω_P(m)+1` costs only the
prime-square terms.  This is the correction explicitly needed in MRT v3. -/
theorem mrt_ramare_denominator_error (P : Finset ℕ) {p m : ℕ}
    (hp : p ∈ P) (z : ℂ) :
    ‖z / (((if p ∣ m then 0 else 1) + finitePrimeDivisorCount P m : ℕ) : ℂ) -
      z / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)‖ ≤
        if p ∣ m then ‖z‖ else 0 := by
  by_cases hpm : p ∣ m
  · simp only [hpm, ite_true, zero_add]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, norm_mul]
    have hk := finitePrimeDivisorCount_pos_of_mem hp hpm
    exact (mul_le_mul_of_nonneg_left (mrt_inverse_successor_difference hk)
      (norm_nonneg z)).trans_eq (mul_one _)
  · simp only [hpm, ite_false, Nat.add_comm 1, sub_self, norm_zero, le_refl]


lemma mrt_count_multiples {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ m ∈ Icc 1 N, if p ∣ m then (1 : ℝ) else 0) = (N / p : ℕ) := by
  have he := divisibility_positivePrefix (fun _ => (1 : ℂ)) p N hp
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, mul_one,
    sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum, apply_ite, Complex.one_re, Complex.zero_re,
    Complex.natCast_re] using hr


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeSquareMean
namespace OAI

/-! The prime-square error in the corrected Ramaré decomposition has a
small mean square.  The count is evaluated by pairing prime-square
divisibility tests; distinct primes give the product modulus exactly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrtPrimeSquareCount_nonneg (P : Finset ℕ) (n : ℕ) :
    0 ≤ mrtPrimeSquareCount P n := by
  unfold mrtPrimeSquareCount
  exact sum_nonneg fun _ _ => by split_ifs <;> norm_num





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRamareMeanError
namespace OAI

/-! The actual coefficient error made by replacing the corrected Ramaré
denominator with `ω_P(m)+1`.  The pointwise error is supported on prime
squares, so the preceding second-moment count applies directly. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem mrt_ramare_correction_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (n : ℕ) :
    ‖mrtRamareCorrection P F n‖ ≤ ‖F n‖ * mrtPrimeSquareCount P n := by
  unfold mrtRamareCorrection
  rw [mrt_ramare_identity P hP F n, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, if p ^ 2 ∣ n then ‖F n‖ else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hpn : p ∣ n
      · simp only [hpn, ite_true, Nat.mul_div_cancel' hpn]
        have he : p ∣ n / p ↔ p ^ 2 ∣ n := by
          simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hpn : p ∣ n / p ↔ p * p ∣ n)
        simpa only [he] using mrt_ramare_denominator_error P hp (F n) (m := n / p)
      · have hs : ¬p ^ 2 ∣ n := by
          intro hn
          apply hpn
          exact dvd_trans (by simpa only [pow_two] using (dvd_mul_right p p)) hn
        simp only [hpn, hs, ite_false, sub_self, norm_zero, le_refl]
    _ = _ := by
      unfold mrtPrimeSquareCount
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs <;> simp

theorem mrt_ramare_correction_oneBounded (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (F : ℕ → ℂ) (hF : OneBounded F)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtRamareCorrection P F n‖ ≤ mrtPrimeSquareCount P n := by
  apply (mrt_ramare_correction_bound P hP F n).trans
  exact (mul_le_mul_of_nonneg_right (hF n hn) (mrtPrimeSquareCount_nonneg P n)).trans_eq
    (one_mul _)


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















/-- Dividing out a number smaller than all the selected primes does not
change membership in the typical-factorization set. -/
theorem mrtTypical_mul_of_avoids {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime) {d : ℕ}
    (hd : mrtPrimeAvoids (J.biUnion P) d) (n : ℕ) :
    mrtTypical J P (d * n) ↔ mrtTypical J P n := by
  constructor
  · intro h j hj
    obtain ⟨p, hp, hpdn⟩ := h j hj
    refine ⟨p, hp, ?_⟩
    exact ((hP j hj p hp).dvd_mul.mp hpdn).resolve_left
      (hd p (mem_biUnion.mpr ⟨j, hj, hp⟩))
  · intro h j hj
    obtain ⟨p, hp, hpn⟩ := h j hj
    exact ⟨p, hp, dvd_mul_of_dvd_right hpn d⟩



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

lemma mrtTypical_count_pos {ι : Type*} {J : Finset ι} {P : ι → Finset ℕ}
    {j : ι} (hj : j ∈ J) {n : ℕ} (hn : mrtTypical J P n) :
    0 < finitePrimeDivisorCount (P j) n := by
  obtain ⟨p, hp, hpn⟩ := hn j hj
  exact finitePrimeDivisorCount_pos_of_mem hp hpn

lemma mrtTypical_prime_mul {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    {p : ℕ} (hp : p ∈ P j) (m : ℕ) :
    mrtTypical J P (p * m) ↔ mrtTypical (J.erase j) P m := by
  have hnot (i : ι) (hi : i ∈ J.erase j) : p ∉ P i := by
    intro hpi
    exact Finset.disjoint_left.mp (hdis (mem_erase.mp hi).2 hj (mem_erase.mp hi).1)
      hpi hp
  have hd : mrtPrimeAvoids ((J.erase j).biUnion P) p := by
    intro q hq hqp
    obtain ⟨i, hi, hqi⟩ := mem_biUnion.mp hq
    have he : q = p := (Nat.prime_dvd_prime_iff_eq
      (hP i (mem_erase.mp hi).2 q hqi) (hP j hj p hp)).mp hqp
    exact hnot i hi (he ▸ hqi)
  have hmul := mrtTypical_mul_of_avoids (J.erase j) P
    (fun i hi => hP i (mem_erase.mp hi).2) hd m
  constructor
  · intro h
    apply hmul.mp
    exact fun i hi => h i (mem_erase.mp hi).2
  · intro h i hi
    by_cases hij : i = j
    · subst i
      exact ⟨p, hp, dvd_mul_right p m⟩
    · exact hmul.mpr h i (mem_erase.mpr ⟨hij, hi⟩)

lemma mrtTypical_ramare_supported {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    {j : ι} (hj : j ∈ J) (F : ℕ → ℂ) (n : ℕ) :
    (if finitePrimeDivisorCount (P j) n = 0 then 0 else
      if mrtTypical J P n then F n else 0) =
      if mrtTypical J P n then F n else 0 := by
  by_cases ht : mrtTypical J P n
  · have hpos := mrtTypical_count_pos hj ht
    simp only [ht, ite_true, ne_of_gt hpos, ite_false]
  · simp only [ht, ite_false, ite_self]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma mrtTypicalCoefficient_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) :
    OneBounded (mrtTypicalCoefficient J P F) := by
  intro n hn
  unfold mrtTypicalCoefficient
  split_ifs
  · exact hF n hn
  · simp





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcPublishedRate
namespace OAI

/-! The common major/minor-arc parameter and its quantitative rates.
The fifth-root working length retains the published logarithmic error. -/
namespace TwoPointCorrelations

open _root_.Filter


lemma major_arc_parameter_bounds {L H M : ℝ} (hL : 1 ≤ L)
    (hH : 1 ≤ Real.log H) (hM : 0 ≤ M) :
    1 ≤ majorArcParameter L H M ∧
      majorArcParameter L H M ≤ (Real.log H)^5 ∧
      majorArcParameter L H M ≤ L^(1/125:ℝ) ∧
      majorArcParameter L H M ≤ Real.exp (M/3) := by
  exact ⟨le_min (one_le_pow₀ hH) (le_min
    (Real.one_le_rpow hL (by norm_num)) (Real.one_le_exp (by positivity))),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩


lemma major_arc_working_short {H : ℝ} (hH : 1 ≤ Real.log H)
    (hHH : 1 ≤ Real.log (Real.log H)) :
    majorArcWorkingError ((Real.log H)^5) ≤ 6*Real.log (Real.log H)/Real.log H := by
  have hL : 0 < Real.log H := by linarith
  have hp : ((Real.log H)^5)^(-1/5:ℝ) = (Real.log H)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    norm_num [Real.rpow_neg_one]
  unfold majorArcWorkingError
  rw [hp,Real.log_pow]
  rw [mul_inv_le_iff₀ hL]
  field_simp
  norm_num
  linarith

lemma major_arc_working_exponential {M : ℝ} (hM : 0 ≤ M) :
    majorArcWorkingError (Real.exp (M/3)) ≤ 21*Real.exp (-M/20) := by
  have hh := Real.add_one_le_exp (M/60)
  have hcoef : 1+M/3 ≤ 21*Real.exp (M/60) := by
    have he : 1 ≤ Real.exp (M/60) := Real.one_le_exp (by positivity)
    linarith
  unfold majorArcWorkingError
  rw [Real.log_exp,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  calc
    _ ≤ (21*Real.exp (M/60))*Real.exp (M/3*(-1/5)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring

lemma major_arc_working_outer :
    ∀ᶠ L : ℝ in atTop,
      majorArcWorkingError (L^(1/125:ℝ)) ≤ L^(-1/700:ℝ) := by
  have hh := (isLittleO_log_rpow_atTop (show (0:ℝ)<3/17500 by norm_num)).bound
    (show (0:ℝ)<1/2 by norm_num)
  have hg := (tendsto_rpow_atTop (show (0:ℝ)<3/17500 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hh,hg,eventually_ge_atTop (1:ℝ)] with L hh hg hL
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hh
  have hp : (L^(1/125:ℝ))^(-1/5:ℝ)=L^(-1/625:ℝ) := by
    rw [← Real.rpow_mul hL0.le]
    norm_num
  unfold majorArcWorkingError
  rw [Real.log_rpow hL0,hp]
  calc
    _ ≤ L^(3/17500:ℝ)*L^(-1/625:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL0.le _)
      nlinarith [Real.log_nonneg hL]
    _ = _ := by rw [← Real.rpow_add hL0]; norm_num

lemma major_arc_working_min {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    majorArcWorkingError (min a b) ≤ majorArcWorkingError a+majorArcWorkingError b := by
  have hfa : 0 ≤ majorArcWorkingError a :=
    mul_nonneg (by linarith [Real.log_nonneg ha]) (Real.rpow_nonneg (by linarith) _)
  have hfb : 0 ≤ majorArcWorkingError b :=
    mul_nonneg (by linarith [Real.log_nonneg hb]) (Real.rpow_nonneg (by linarith) _)
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact le_add_of_nonneg_right hfb
  · rw [min_eq_right hba]
    exact le_add_of_nonneg_left hfa

lemma major_arc_parameter_rate :
    ∀ᶠ L : ℝ in atTop, ∀ H M : ℝ, 1 ≤ Real.log H →
      1 ≤ Real.log (Real.log H) → 0 ≤ M →
      majorArcWorkingError (majorArcParameter L H M) ≤
        6*Real.log (Real.log H)/Real.log H + L^(-1/700:ℝ)+21*Real.exp (-M/20) := by
  filter_upwards [major_arc_working_outer,eventually_ge_atTop (1:ℝ)] with L houter hL
  intro H M hH hHH hM
  have ha : 1 ≤ (Real.log H)^5 := one_le_pow₀ hH
  have hb : 1 ≤ L^(1/125:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hc : 1 ≤ Real.exp (M/3) := Real.one_le_exp (by positivity)
  have hi := major_arc_working_min hb hc
  have hj := major_arc_working_min ha (le_min hb hc)
  change majorArcWorkingError (majorArcParameter L H M) ≤ _ at hj
  linarith [major_arc_working_short hH hHH,major_arc_working_exponential hM]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralPrimeError
namespace OAI

/-! The general-multiplicative discrepancy in extracting a prime factor.
It vanishes unless that prime divides the cofactor, and hence has the
same prime-square support as the corrected Ramaré denominator error. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma mrtTypicalCoefficient_prime_mul_coprime {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : Multiplicative F)
    {p : ℕ} (hp : p ∈ P j) {m : ℕ} (hm : 0 < m) (hpm : ¬p ∣ m) :
    mrtTypicalCoefficient J P F (p * m) =
      F p * mrtTypicalCoefficient (J.erase j) P F m := by
  unfold mrtTypicalCoefficient
  rw [mrtTypical_prime_mul J P hP hdis hj hp]
  split_ifs
  · exact hF p m (hP j hj p hp).pos hm ((hP j hj p hp).coprime_iff_not_dvd.mpr hpm)
  · simp


theorem mrt_prime_product_error_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (active : ℕ → ℕ → Prop) (C A B : ℕ → ℂ)
    (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtPrimeProductError P active C A B n‖ ≤ 2 * mrtPrimeSquareCount P n := by
  unfold mrtPrimeProductError
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, if p ^ 2 ∣ n then (2 : ℝ) else 0 := by
      apply sum_le_sum
      intro p hp
      by_cases hgate : p ∣ n ∧ active p n
      · rw [if_pos hgate]
        have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hgate.1) (hP p hp).pos
        by_cases hsquare : p ^ 2 ∣ n
        · rw [if_pos hsquare, norm_div, Complex.norm_natCast]
          have hc : ‖C n - A p * B (n / p)‖ ≤ 2 := by
            apply (norm_sub_le _ _).trans
            rw [norm_mul]
            have hab := mul_le_mul (hA p (hP p hp).pos) (hB (n / p) hm)
              (norm_nonneg _) zero_le_one
            nlinarith [hC n hn]
          calc
            _ ≤ 2 / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℝ) :=
              div_le_div_of_nonneg_right hc (by positivity)
            _ ≤ 2 := div_le_self (by norm_num) (by norm_num)
        · have hnot : ¬p ∣ n / p := by
            intro hd
            apply hsquare
            simpa only [pow_two] using (Nat.dvd_div_iff_mul_dvd hgate.1).mp hd
          have he : C n = A p * B (n / p) := by
            calc
              C n = C (p * (n / p)) := congrArg C (Nat.mul_div_cancel' hgate.1).symm
              _ = _ := hproduct p hp (n / p) hm hnot
          rw [he, sub_self, zero_div, norm_zero, if_neg hsquare]
      · rw [if_neg hgate, norm_zero]
        split_ifs <;> norm_num
    _ = _ := by
      unfold mrtPrimeSquareCount
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      split_ifs <;> norm_num

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcRamareError
namespace OAI

/-! The combined denominator and prime-extraction error for the additive
short-window argument. Both errors are supported on prime squares. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma minor_arc_ramare_pointwise (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (C A B : ℕ → ℂ) (hC : OneBounded C) (hA : OneBounded A) (hB : OneBounded B)
    (hproduct : ∀ p ∈ P, ∀ m, 0 < m → ¬p ∣ m → C (p * m) = A p * B m)
    {n : ℕ} (hn : 0 < n) :
    ‖(if finitePrimeDivisorCount P n = 0 then 0 else C n) -
      minorArcRamareApprox P A B n‖ ≤ 3 * mrtPrimeSquareCount P n := by
  have he : (if finitePrimeDivisorCount P n = 0 then 0 else C n) -
      minorArcRamareApprox P A B n =
      mrtRamareCorrection P C n + mrtPrimeProductError P (fun _ _ => True) C A B n := by
    have hterm (p : ℕ) :
        (if p ∣ n ∧ True then
          (C n - A p * B (n / p)) / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ)
        else 0) =
        (if p ∣ n then C n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) -
        (if p ∣ n then A p * B (n / p) /
          ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) := by
      by_cases hp : p ∣ n <;> simp [hp, sub_div]
    have hsum : mrtPrimeProductError P (fun _ _ => True) C A B n =
        ∑ p ∈ P,
          ((if p ∣ n then C n / ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) -
          (if p ∣ n then A p * B (n / p) /
            ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0)) := by
      unfold mrtPrimeProductError
      apply sum_congr rfl
      intro p _
      simpa only [and_true] using hterm p
    rw [hsum, sum_sub_distrib]
    unfold minorArcRamareApprox mrtRamareCorrection
    ring
  rw [he]
  have hden := mrt_ramare_correction_oneBounded P hP C hC hn
  have hprod := mrt_prime_product_error_bound P hP (fun _ _ => True) C A B hC hA hB hproduct hn
  exact (norm_add_le _ _).trans (by linarith)

lemma minor_arc_typical_ramare_pointwise {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {n : ℕ} (hn : 0 < n) :
    ‖mrtTypicalCoefficient J P F n -
      minorArcRamareApprox (P j) F (mrtTypicalCoefficient (J.erase j) P F) n‖ ≤
      3 * mrtPrimeSquareCount (P j) n := by
  have hh := minor_arc_ramare_pointwise (P j) (hP j hj)
    (mrtTypicalCoefficient J P F) F (mrtTypicalCoefficient (J.erase j) P F)
    (mrtTypicalCoefficient_oneBounded J P F hFb) hFb
    (mrtTypicalCoefficient_oneBounded (J.erase j) P F hFb)
    (fun p hp m hm hpm => mrtTypicalCoefficient_prime_mul_coprime J P hP hdis hj F hF hp hm hpm)
    hn
  simpa only [mrtTypicalCoefficient, mrtTypical_ramare_supported J P hj F] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcRamareWindow
namespace OAI

/-! Exact change of variables from the Ramaré coefficient to the finite
bilinear short-window sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma minor_arc_ramare_cofactor_bound (P : Finset ℕ) (B : ℕ → ℂ)
    (hB : OneBounded B) (m : ℕ) : ‖minorArcRamareCofactor P B m‖ ≤ 1 := by
  unfold minorArcRamareCofactor
  split_ifs with hm
  · simp
  · rw [norm_div, Complex.norm_natCast]
    apply (div_le_self (norm_nonneg _) (by norm_num)).trans
    exact hB m (Nat.pos_of_ne_zero hm)

lemma minor_arc_bilinear_zero_cofactor (P : Finset ℕ) (M H d : ℕ)
    (a c : ℕ → ℂ) (α : ℝ) (k : ℕ) :
    minorArcBilinearWindow P M H d (fun m => if m = 0 then 0 else a m) c α k =
      minorArcBilinearWindow P M H d a c α k := by
  unfold minorArcBilinearWindow
  apply sum_congr rfl
  intro m _
  by_cases hm : m = 0
  · subst m
    simp [minorArcWindowTerm, minorArcWindowInterval]
  · simp only [if_neg hm]

lemma minor_arc_divisibility_window (p M k H : ℕ) (hp : 0 < p)
    (hM : (k + H) / p < M) (F : ℕ → ℂ) :
    (∑ n ∈ Icc (k + 1) (k + H), if p ∣ n then F n else 0) =
      ∑ m ∈ minorArcWindowInterval M p k H, F (p * m) := by
  rw [← sum_filter]
  symm
  apply sum_bij (fun m _ => p * m)
  · intro m hm
    have hh := (mem_minorArcWindowInterval M p k H m hp).mp hm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hh.2.2⟩, dvd_mul_right p m⟩
  · intro m _ n _ hmn
    exact Nat.eq_of_mul_eq_mul_left hp hmn
  · intro n hn
    obtain ⟨hnI, hpn⟩ := mem_filter.mp hn
    have hnI' := mem_Icc.mp hnI
    refine ⟨n / p, (mem_minorArcWindowInterval M p k H (n / p) hp).mpr ?_,
      Nat.mul_div_cancel' hpn⟩
    have hdiv : n / p ≤ (k + H) / p := Nat.div_le_div_right hnI'.2
    refine ⟨hdiv.trans_lt hM, ?_, ?_⟩
    · rw [Nat.mul_div_cancel' hpn]
      omega
    · simpa only [Nat.mul_div_cancel' hpn] using hnI'.2
  · intro m _
    rfl

lemma minor_arc_window_weighted_sum (M p k H : ℕ) (a : ℕ → ℂ) (c : ℂ) (β : ℝ) :
    (∑ m ∈ range M, a m * minorArcWindowTerm M p k H c β m) =
      ∑ m ∈ minorArcWindowInterval M p k H, a m * (c * additiveCharacter β m) := by
  let W := minorArcWindowInterval M p k H
  have hsub : W ⊆ range M := by
    intro m hm
    exact mem_range.mpr ((mem_Ico.mp hm).2.trans_le (min_le_left _ _))
  have hf : (range M).filter (fun m => m ∈ W) = W := by
    ext m
    simp only [mem_filter]
    exact ⟨And.right, fun hm => ⟨hsub hm, hm⟩⟩
  change (∑ m ∈ range M, a m * minorArcWindowTerm M p k H c β m) =
    ∑ m ∈ W, a m * (c * additiveCharacter β m)
  rw [← hf, sum_filter]
  apply sum_congr rfl
  intro m _
  change a m * (if m ∈ W then c * additiveCharacter β m else 0) =
    if m ∈ W then a m * (c * additiveCharacter β m) else 0
  split_ifs <;> simp



lemma minor_arc_ramare_short_eq (P : Finset ℕ) (M H k : ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hM : ∀ p ∈ P, (k + H) / p < M)
    (A B : ℕ → ℂ) (α : ℝ) :
    shortExponentialSum (minorArcRamareApprox P A B) H α k =
      minorArcBilinearWindow P M H 1
        (fun m => B m / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)) A α k := by
  rw [shortExponentialSum_at_nat]
  unfold minorArcRamareApprox minorArcBilinearWindow
  simp only [sum_mul, mul_sum, one_mul]
  rw [sum_comm, sum_comm (s := range M) (t := P)]
  apply sum_congr rfl
  intro p hp
  have he : (∑ n ∈ Icc (k + 1) (k + H),
      (if p ∣ n then A p * B (n / p) /
        ((finitePrimeDivisorCount P (n / p) + 1 : ℕ) : ℂ) else 0) * additiveCharacter α n) =
      ∑ m ∈ minorArcWindowInterval M p k H,
        (A p * B m / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)) *
          additiveCharacter α (p * m) := by
    simp only [ite_mul, zero_mul]
    rw [minor_arc_divisibility_window p M k H (hP p hp) (hM p hp)]
    simp only [Nat.mul_div_cancel_left _ (hP p hp)]
  rw [he, minor_arc_window_weighted_sum]
  apply sum_congr rfl
  intro m _
  have hphase : additiveCharacter α (p * m) = additiveCharacter (α * p) m := by
    unfold additiveCharacter
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

lemma minor_arc_ramare_short_eq_bounded (P : Finset ℕ) (M H k : ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hM : ∀ p ∈ P, (k + H) / p < M)
    (A B : ℕ → ℂ) (α : ℝ) :
    shortExponentialSum (minorArcRamareApprox P A B) H α k =
      minorArcBilinearWindow P M H 1 (minorArcRamareCofactor P B) A α k := by
  rw [minor_arc_ramare_short_eq P M H k hP hM]
  exact (minor_arc_bilinear_zero_cofactor P M H 1
    (fun m => B m / ((finitePrimeDivisorCount P m + 1 : ℕ) : ℂ)) A α k).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcShortError
namespace OAI

/-! Averaging the prime-square correction over literal short windows. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_square_reciprocal_sum (P : Finset ℕ) (R N : ℕ) (hR : 0 < R)
    (hP : ∀ p ∈ P, R ≤ p ∧ p ≤ N) :
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 2 / (R : ℝ) := by
  have hsub : P ⊆ Ioo (R - 1) (N + 1) := by
    intro p hp
    have hh := hP p hp
    exact mem_Ioo.mpr ⟨by omega, by omega⟩
  calc
    _ ≤ ∑ p ∈ Ioo (R - 1) (N + 1), ((p : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / ((R - 1 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le (R - 1) (N + 1)
    _ = _ := by rw [Nat.cast_sub (by omega : 1 ≤ R)]; push_cast; ring

lemma minor_arc_origin_weight_count (X H n : ℕ) :
    ((range X).filter (fun k => k < n ∧ n ≤ k + H)).card ≤ H := by
  have hs : (range X).filter (fun k => k < n ∧ n ≤ k + H) ⊆ Ico (n - H) n := by
    intro k hk
    have h := (mem_filter.mp hk).2
    exact mem_Ico.mpr ⟨by omega, h.1⟩
  apply (card_le_card hs).trans
  rw [Nat.card_Ico]
  omega

lemma minor_arc_window_mass (X H : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑ k ∈ range X, ∑ n ∈ Icc (k + 1) (k + H), w n) ≤
      (H : ℝ) * ∑ n ∈ Icc 1 (X + H), w n := by
  have he (k : ℕ) (hk : k ∈ range X) :
      (∑ n ∈ Icc (k + 1) (k + H), w n) =
        ∑ n ∈ Icc 1 (X + H), if k < n ∧ n ≤ k + H then w n else 0 := by
    have hf : (Icc 1 (X + H)).filter (fun n => k < n ∧ n ≤ k + H) =
        Icc (k + 1) (k + H) := by
      ext n
      have hkX := mem_range.mp hk
      simp only [mem_filter, mem_Icc]
      omega
    rw [← sum_filter, hf]
  calc
    _ = ∑ k ∈ range X, ∑ n ∈ Icc 1 (X + H),
        if k < n ∧ n ≤ k + H then w n else 0 := sum_congr rfl he
    _ = ∑ n ∈ Icc 1 (X + H), ∑ k ∈ range X,
        if k < n ∧ n ≤ k + H then w n else 0 := sum_comm
    _ = ∑ n ∈ Icc 1 (X + H),
        (((range X).filter (fun k => k < n ∧ n ≤ k + H)).card : ℝ) * w n := by
      simp only [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Icc 1 (X + H), (H : ℝ) * w n := by
      apply sum_le_sum
      intro n _
      exact mul_le_mul_of_nonneg_right
        ((Nat.cast_le (α := ℝ)).mpr (minor_arc_origin_weight_count X H n)) (hw n)
    _ = _ := (mul_sum _ _ _).symm

lemma minor_arc_prime_square_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N, mrtPrimeSquareCount P n) ≤
      (N : ℝ) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
  unfold mrtPrimeSquareCount
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro p hp
  rw [mrt_count_multiples (pow_pos (hP p hp).pos 2)]
  convert (preTransparency := .instances) (Nat.cast_div_le (m := N) (n := p ^ 2) :
    ((N / p ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / (p ^ 2 : ℕ)) using 1
  push_cast
  ring

lemma minor_arc_short_square_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E : ℕ → ℂ) (X H : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hE : ∀ n, 0 < n → n ≤ X + H → ‖E n‖ ≤ A * mrtPrimeSquareCount P n)
    (α : ℝ) :
    (∑ k ∈ range X, ‖shortExponentialSum E H α k‖) ≤
      A * (H : ℝ) * (X + H) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
  have hpoint (k : ℕ) (hk : k ∈ range X) :
      ‖shortExponentialSum E H α k‖ ≤ A * ∑ n ∈ Icc (k + 1) (k + H),
        mrtPrimeSquareCount P n := by
    rw [shortExponentialSum_at_nat]
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    rw [norm_mul, norm_additiveCharacter, mul_one]
    have hnI := mem_Icc.mp hn
    have hkX := mem_range.mp hk
    exact hE n (by omega) (by omega)
  calc
    _ ≤ ∑ k ∈ range X, A * ∑ n ∈ Icc (k + 1) (k + H), mrtPrimeSquareCount P n :=
      sum_le_sum hpoint
    _ = A * ∑ k ∈ range X, ∑ n ∈ Icc (k + 1) (k + H), mrtPrimeSquareCount P n :=
      (mul_sum _ _ _).symm
    _ ≤ A * ((H : ℝ) * ∑ n ∈ Icc 1 (X + H), mrtPrimeSquareCount P n) :=
      mul_le_mul_of_nonneg_left (minor_arc_window_mass X H _ (mrtPrimeSquareCount_nonneg P)) hA
    _ ≤ A * ((H : ℝ) * ((X + H : ℕ) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact mul_le_mul_of_nonneg_left (minor_arc_prime_square_mass P hP (X + H)) (Nat.cast_nonneg H)
    _ = _ := by push_cast; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcTypicalIntegral
namespace OAI

/-! The actual typical-set short-sum integral, reduced to the bounded
bilinear window plus its single prime-square error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem minor_arc_typical_integral_le {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    (X H M : ℕ) (hM : ∀ p ∈ P j, ∀ k ∈ range X, (k + H) / p < M) (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      (∑ k ∈ range X, ‖minorArcBilinearWindow (P j) M H 1
        (minorArcRamareCofactor (P j) (mrtTypicalCoefficient (J.erase j) P F)) F α k‖) +
        3 * (H : ℝ) * (X + H) * ∑ p ∈ P j, 1 / (p : ℝ) ^ 2 := by
  let C := mrtTypicalCoefficient J P F
  let B := mrtTypicalCoefficient (J.erase j) P F
  let A := minorArcRamareApprox (P j) F B
  let E := fun n => C n - A n
  have herr : (∑ k ∈ range X, ‖shortExponentialSum E H α k‖) ≤
      3 * (H : ℝ) * (X + H) * ∑ p ∈ P j, 1 / (p : ℝ) ^ 2 := by
    apply minor_arc_short_square_error (P j) (hP j hj) E X H 3 (by norm_num)
    intro n hn _
    exact minor_arc_typical_ramare_pointwise J P hP hdis hj F hF hFb hn
  have hlin (k : ℕ) : shortExponentialSum C H α k =
      shortExponentialSum A H α k + shortExponentialSum E H α k := by
    simp only [shortExponentialSum_at_nat]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    dsimp [E]
    ring
  rw [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ k ∈ range X, (‖shortExponentialSum A H α k‖ +
        ‖shortExponentialSum E H α k‖) := by
      apply sum_le_sum
      intro k _
      rw [show mrtTypicalCoefficient J P F = C from rfl, hlin]
      exact norm_add_le _ _
    _ = (∑ k ∈ range X, ‖minorArcBilinearWindow (P j) M H 1
          (minorArcRamareCofactor (P j) B) F α k‖) +
        ∑ k ∈ range X, ‖shortExponentialSum E H α k‖ := by
      rw [sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro k hk
      exact congrArg norm (minor_arc_ramare_short_eq_bounded (P j) M H k
        (fun p hp => (hP j hj p hp).pos) (fun p hp => hM p hp k hk) F B α)
    _ ≤ _ := add_le_add le_rfl herr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingLength
namespace OAI

/-! Cap the original short length before choosing its prime bands. The
uncapped branch is kept exactly; on the capped branch the omitted final
block is negligible compared with W^(-1/4). -/

namespace TwoPointCorrelations

open _root_.Filter



lemma mrt_working_cap_upper (W : ℝ) :
    (mrtWorkingCap W : ℝ) ≤ Real.exp (Real.sqrt W / 2) :=
  Nat.floor_le (Real.exp_pos _).le

/-- The fixed cap eventually exceeds every prescribed power of W. -/
theorem mrt_working_cap_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, W ^ a ≤ (mrtWorkingCap W : ℝ) := by
  have hsmall := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hlarge := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually
    (eventually_ge_atTop (8 * ((a : ℝ) + 1)))
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with W hs ht hW
  have hW0 : 0 < W := by linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  have ht0 : 0 ≤ W ^ (1 / 4 : ℝ) := Real.rpow_nonneg hW0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_nonneg ht0, one_mul] at hs
  have ht2 : (W ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt W := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, Real.sqrt_eq_rpow]
    norm_num
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have ham := mul_le_mul_of_nonneg_left hs ha
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hmul := mul_nonneg ht0 (sub_nonneg.mpr ht)
  have he : Real.log 2 + (a : ℝ) * Real.log W ≤ Real.sqrt W / 2 := by
    nlinarith
  have hpow : 2 * W ^ a ≤ Real.exp (Real.sqrt W / 2) := by
    calc
      _ = Real.exp (Real.log 2 + (a : ℝ) * Real.log W) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          Real.exp_nat_mul, Real.exp_log hW0]
      _ ≤ _ := Real.exp_le_exp.mpr he
  have hp : 1 ≤ W ^ a := one_le_pow₀ hW
  have hf := Nat.lt_floor_add_one (Real.exp (Real.sqrt W / 2))
  change Real.exp (Real.sqrt W / 2) < (mrtWorkingCap W : ℝ) + 1 at hf
  linarith


lemma mrt_working_length_exp_upper (H : ℕ) (W : ℝ) :
    (mrtWorkingLength H W : ℝ) ≤ Real.exp (Real.sqrt W) := by
  unfold mrtWorkingLength
  split_ifs with h
  · exact h
  · exact (mrt_working_cap_upper W).trans
      (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg W]))




lemma mrt_working_length_loglog {H : ℕ} {W : ℝ}
    (hW : 0 < W) (hH : (1 : ℝ) < mrtWorkingLength H W) :
    Real.log (Real.log (mrtWorkingLength H W : ℝ)) ≤ (1 / 2 : ℝ) * Real.log W := by
  have hpos : (0 : ℝ) < mrtWorkingLength H W := by linarith
  have hlpos := Real.log_pos hH
  have hlog := Real.log_le_log hpos (mrt_working_length_exp_upper H W)
  rw [Real.log_exp] at hlog
  have hh := Real.log_le_log hlpos hlog
  rw [Real.log_sqrt hW.le] at hh
  linarith


/-- The bound W ≤ log(H)^5 forces H above any fixed power of W. -/
theorem mrt_working_original_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℝ, 0 < H → 1 ≤ Real.log H →
      W ≤ (Real.log H) ^ (5 : ℕ) → W ^ a ≤ H := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have ht := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually
    (eventually_ge_atTop (a : ℝ))
  filter_upwards [hs, ht, eventually_ge_atTop (1 : ℝ)] with W hs ht hW
  have hW0 : 0 < W := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hW), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hW0.le _), one_mul] at hs
  intro H hH0 hlog hWH
  have hp : W ^ (1 / 5 : ℝ) ≤ Real.log H := by
    calc
      _ ≤ ((Real.log H) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow hW0.le hWH (by norm_num)
      _ = Real.log H := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log H)]
        norm_num
  have ha : (a : ℝ) * Real.log W ≤ W ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ W ^ (1 / 10 : ℝ) * W ^ (1 / 10 : ℝ) :=
        mul_le_mul ht hs (Real.log_nonneg hW) (Real.rpow_nonneg hW0.le _)
      _ = _ := by rw [← Real.rpow_add hW0]; norm_num
  calc
    W ^ a = Real.exp ((a : ℝ) * Real.log W) := by
      rw [Real.exp_nat_mul, Real.exp_log hW0]
    _ ≤ Real.exp (Real.log H) := Real.exp_le_exp.mpr (ha.trans hp)
    _ = H := Real.exp_log hH0

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingLength
namespace OAI

/-! A fifth-root logarithmic cap, obtained from the general square-root
cap by substitution. Its size suits the common Diophantine parameter. -/
namespace TwoPointCorrelations

open _root_.Filter


lemma major_arc_working_root {W : ℝ} (hW : 0 ≤ W) :
    Real.sqrt (W^(2/5:ℝ))=W^(1/5:ℝ) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hW]
  norm_num


lemma major_arc_working_length_loglog {H : ℕ} {W : ℝ}
    (hW : 0 < W) (hH : (1:ℝ) < majorArcWorkingLength H W) :
    Real.log (Real.log (majorArcWorkingLength H W:ℝ)) ≤ (1/5:ℝ)*Real.log W := by
  have hh := mrt_working_length_loglog (Real.rpow_pos_of_pos hW (2/5)) hH
  rw [Real.log_rpow hW] at hh
  dsimp only [majorArcWorkingLength]
  linarith

lemma major_arc_working_length_exp_upper (H : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (majorArcWorkingLength H W:ℝ) ≤ Real.exp (W^(1/5:ℝ)) := by
  simpa only [majorArcWorkingLength,major_arc_working_root hW] using
    mrt_working_length_exp_upper H (W^(2/5:ℝ))

theorem major_arc_working_length_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) →
      W ≤ Real.log (H:ℝ)^5 → W^a ≤ (majorArcWorkingLength H W:ℝ) := by
  have ht : Tendsto (fun W:ℝ => W^(2/5:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [ht.eventually (mrt_working_cap_power (5*a)),
    mrt_working_original_power a,eventually_ge_atTop (1:ℝ)] with W hcap horiginal hW
  intro H hH hlog hWH
  have hW0 : 0 < W := by linarith
  have hc : W^a ≤ (mrtWorkingCap (W^(2/5:ℝ)):ℝ) := by
    apply le_trans _ hcap
    rw [← Real.rpow_mul_natCast hW0.le (2/5:ℝ) (5*a)]
    rw [show (2/5:ℝ)*(5*a:ℕ)=(2:ℝ)*a by push_cast; ring]
    rw [Real.rpow_mul_natCast hW0.le,Real.rpow_two]
    exact pow_le_pow_left₀ hW0.le (by nlinarith) a
  unfold majorArcWorkingLength mrtWorkingLength
  split_ifs
  · exact horiginal H (by exact_mod_cast hH) hlog hWH
  · exact hc



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













































attribute [fun_prop] measurable_from_top












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












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands
namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The reciprocal-mass bounds follow from Mertens’ theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcParameterTypical
namespace OAI

/-! The minor-arc short-integral estimate for the actual MRT typical set. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem minor_arc_typical_parameter_saving :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ),
      (∀ i ∈ I, ∀ p ∈ P i, p.Prime) → Set.PairwiseDisjoint (I : Set ι) P →
      ∀ i ∈ I, ∀ (J : Finset ℕ) (X H N : ℕ), 1 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → J ⊆ Icc 1 N →
      (∀ p ∈ P i, Nat.log 2 p ∈ J) → (∀ p ∈ P i, p ≠ 2) →
      (∀ j ∈ J, R₀ ≤ 2 ^ j ∧ 2 ^ j ≤ X) →
      ∀ W : ℝ, 1 ≤ W →
      (∀ j ∈ J, W ≤ (2 : ℝ) ^ j ∧
        (2 : ℝ) ^ j ≤ (H : ℝ) / W) →
      ∀ (F : ℕ → ℂ), Multiplicative F → OneBounded F →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      W ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      shortExponentialIntegral (mrtTypicalCoefficient I P F) X H α ≤
        C * (X : ℝ) * H * (1 + Real.log (N : ℝ)) * (Real.log (H : ℝ)/W)^(1/4:ℝ) +
          3 * (H : ℝ) * (X + H) * ∑ p ∈ P i, 1 / (p : ℝ) ^ 2 := by
  obtain ⟨C, hC, R₀, hbound⟩ := minor_arc_bilinear_parameter_saving
  refine ⟨C, hC, R₀, ?_⟩
  intro ι I P hP hdis i hi J X H N hH hHX hlogH hJN hPJ hodd hR W hW hgeom
    F hF hFb r q hq hWq hqH α hcop happ
  let B := mrtTypicalCoefficient (I.erase i) P F
  let a := minorArcRamareCofactor (P i) B
  have ha : ∀ m, ‖a m‖ ≤ 1 :=
    minor_arc_ramare_cofactor_bound (P i) B
      (mrtTypicalCoefficient_oneBounded (I.erase i) P F hFb)
  have hc : ∀ p ∈ P i, ‖F p‖ ≤ 1 := fun p hp => hFb p (hP i hi p hp).pos
  have hbil := hbound (P i) J X H N hH hHX hlogH hJN hPJ
    (fun p hp => ⟨hP i hi p hp, hodd p hp⟩) hR W hW hgeom a F ha hc
    r q hq hWq hqH α hcop happ
  have hcut : ∀ p ∈ P i, ∀ k ∈ range X, (k + H) / p < X + H + 1 := by
    intro p _ k hk
    have hkX := mem_range.mp hk
    have hd := Nat.div_le_self (k + H) p
    omega
  have htyp := minor_arc_typical_integral_le I P hP hdis hi F hF hFb
    X H (X + H + 1) hcut α
  exact htyp.trans (add_le_add hbil le_rfl)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcLogLog
namespace OAI

/-! The dyadic index count contributes only a logarithm of a logarithm. -/

namespace TwoPointCorrelations

lemma minor_arc_log_index_bound (H : ℕ) (hH : 1 ≤ H) :
    (Nat.log 2 H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
  have hH0 : H ≠ 0 := by omega
  have hp : (2 : ℝ) ^ Nat.log 2 H ≤ H := by
    exact_mod_cast Nat.pow_log_le_self 2 hH0
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 H) hp
  rw [Real.log_pow] at hl
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (Nat.log 2 H) :
    (0 : ℝ) ≤ Nat.log 2 H)
  nlinarith

lemma minor_arc_dyadic_log_log_bound (H : ℕ) (hH : 2 ≤ H)
    (hlogH : 1 ≤ Real.log (H : ℝ)) (hloglogH : 1 ≤ Real.log (Real.log (H : ℝ))) :
    1 + Real.log (Nat.log 2 H : ℝ) ≤ 3 * Real.log (Real.log (H : ℝ)) := by
  have hindex : 0 < Nat.log 2 H := lt_of_lt_of_le (by norm_num)
    (minor_arc_dyadic_index_pos hH)
  have hindex0 : (0 : ℝ) < Nat.log 2 H := by exact_mod_cast hindex
  have hlog0 : 0 < Real.log (H : ℝ) := by linarith
  have hh := Real.log_le_log hindex0 (minor_arc_log_index_bound H (by omega))
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlog0.ne'] at hh
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcParameterRanges
namespace OAI

/-! Verifying every dyadic hypothesis from the actual prime range. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_parameter_range_dyadics (P : Finset ℕ) (H R₀ : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (W : ℝ) (hW : 1 ≤ W)
    (hrange : ∀ p ∈ P, 2 * R₀ ≤ p ∧
      2 * W ≤ (p : ℝ) ∧
      (p : ℝ) ≤ (H : ℝ) / W) :
    let J := P.image (Nat.log 2)
    J ⊆ Icc 1 (Nat.log 2 H) ∧
      (∀ p ∈ P, Nat.log 2 p ∈ J) ∧
      (∀ j ∈ J, R₀ ≤ 2 ^ j ∧ 2 ^ j ≤ H) ∧
      (∀ j ∈ J, W ≤ (2 : ℝ) ^ j ∧
        (2 : ℝ) ^ j ≤ (H : ℝ) / W) := by
  dsimp only
  have hpH (p : ℕ) (hp : p ∈ P) : p ≤ H := by
    have hh := (hrange p hp).2.2
    have hb : (p : ℝ) ≤ H := hh.trans (div_le_self (Nat.cast_nonneg H) hW)
    exact_mod_cast hb
  refine ⟨?_, fun p hp => mem_image.mpr ⟨p, hp, rfl⟩, ?_, ?_⟩
  · intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    exact mem_Icc.mpr ⟨minor_arc_dyadic_index_pos (hP p hp).two_le,
      Nat.log_mono_right (hpH p hp)⟩
  · intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have hd := minor_arc_dyadic_prime_bounds (hP p hp).pos rfl
    constructor
    · nlinarith [(hrange p hp).1, hd.2]
    · exact hd.1.trans (hpH p hp)
  · intro j hj
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hj
    have hd := minor_arc_dyadic_prime_bounds (hP p hp).pos rfl
    have hlo : (2 : ℝ) * (2 : ℝ) ^ Nat.log 2 p ≥ p := by exact_mod_cast hd.2
    have hhi : (2 : ℝ) ^ Nat.log 2 p ≤ p := by exact_mod_cast hd.1
    exact ⟨by linarith [(hrange p hp).2.1], hhi.trans (hrange p hp).2.2⟩

theorem minor_arc_typical_parameter_range_saving :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ),
      (∀ i ∈ I, ∀ p ∈ P i, p.Prime) → Set.PairwiseDisjoint (I : Set ι) P →
      ∀ i ∈ I, ∀ (X H : ℕ), 2 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → 1 ≤ Real.log (Real.log (H : ℝ)) →
      ∀ W : ℝ, 1 ≤ W →
      (∀ p ∈ P i, p ≠ 2 ∧ 2 * R₀ ≤ p ∧
        2 * W ≤ (p : ℝ) ∧
        (p : ℝ) ≤ (H : ℝ) / W) →
      ∀ (F : ℕ → ℂ), Multiplicative F → OneBounded F →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      W ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      shortExponentialIntegral (mrtTypicalCoefficient I P F) X H α ≤
        C * (X : ℝ) * H * Real.log (Real.log (H : ℝ)) * (Real.log (H : ℝ)/W)^(1/4:ℝ) +
          3 * (H : ℝ) * (X + H) * ∑ p ∈ P i, 1 / (p : ℝ) ^ 2 := by
  obtain ⟨C, hC, R₀, hbound⟩ := minor_arc_typical_parameter_saving
  refine ⟨3 * C, by positivity, R₀, ?_⟩
  intro ι I P hP hdis i hi X H hH hHX hlogH hloglog W hW hrange F hF hFb
    r q hq hWq hqH α hcop happ
  obtain ⟨hJ, hPJ, hR, hgeom⟩ := minor_arc_parameter_range_dyadics (P i) H R₀ (hP i hi)
    W hW (fun p hp => (hrange p hp).2)
  have hbound' := hbound I P hP hdis i hi ((P i).image (Nat.log 2)) X H (Nat.log 2 H)
    (by omega) hHX hlogH hJ hPJ (fun p hp => (hrange p hp).1)
    (fun j hj => ⟨(hR j hj).1, (hR j hj).2.trans hHX⟩) W hW hgeom
    F hF hFb r q hq hWq hqH α hcop happ
  apply hbound'.trans
  apply add_le_add _ le_rfl
  have hh := mul_le_mul_of_nonneg_left (minor_arc_dyadic_log_log_bound H hH hlogH hloglog)
    (by positivity : 0 ≤ C * (X : ℝ) * H)
  have hh' := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (show 0 ≤ Real.log (H:ℝ)/W by positivity) (1/4:ℝ))
  convert (preTransparency := .instances) hh' using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma mrtBandLower_one (P Q : ℝ) (hP : 0 < P) : mrtBandLower P Q 1 = P := by
  simp [mrtBandLower, Real.exp_log hP]

lemma mrtBandUpper_one (Q : ℝ) (hQ : 0 < Q) : mrtBandUpper Q 1 = Q := by
  simp [mrtBandUpper, Real.exp_log hQ]


lemma mrt_band_endpoints (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogQ : 1 ≤ Real.log Q) :
    2 ≤ mrtBandLower P Q j ∧ mrtBandLower P Q j ≤ mrtBandUpper Q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp0 : 0 < P := by linarith
  have hq0 : 0 < Q := hp0.trans_le hPQ
  have hlp : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hlpq : Real.log P ≤ Real.log Q := Real.log_le_log hp0 hPQ
  have hc : 1 ≤ (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) (one_le_pow₀ hlogQ)
  constructor
  · calc
      2 ≤ P := hP
      _ = Real.exp (Real.log P) := (Real.exp_log hp0).symm
      _ ≤ mrtBandLower P Q j := by
        apply Real.exp_le_exp.mpr
        nlinarith
  · apply Real.exp_le_exp.mpr
    have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log P ≤
          (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlpq (by positivity)
      _ = (j : ℝ) ^ (4 * j) * Real.log Q ^ j := by rw [hpow]; ring
      _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj1 (by omega)) (by positivity)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandSeparation
namespace OAI

/-! The actual MRT bands are disjoint, as required by the corrected
Ramaré decomposition; no disjointness hypothesis on those bands remains. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_adjacent_band_gap (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q j < mrtBandLower P Q (j + 1) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hpow : (j : ℝ) ^ (4 * j + 2) ≤ ((j : ℝ) + 1) ^ (4 * (j + 1)) := by
    calc
      _ ≤ ((j : ℝ) + 1) ^ (4 * j + 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  apply Real.exp_lt_exp.mpr
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hlogQ.le j)
  have hp : 0 < (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by positivity
  nlinarith

lemma mrt_band_lower_monotone (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandLower P Q i ≤ mrtBandLower P Q j := by
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  refine Nat.le_induction le_rfl (fun k hk ih => ?_) j hij
  exact ih.trans (((mrt_band_endpoints P Q k (hi.trans hk) hP hPQ hlogQ).2).trans
    (mrt_adjacent_band_gap P Q k (hi.trans hk) hP hPQ hlogP).le)

lemma mrt_band_gap (P Q : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i < j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    mrtBandUpper Q i < mrtBandLower P Q j :=
  (mrt_adjacent_band_gap P Q i hi hP hPQ hlogP).trans_le
    (mrt_band_lower_monotone P Q (i + 1) j (by omega) (by omega) hP hPQ hlogP)

theorem mrt_actual_bands_pairwise_disjoint (P Q : ℝ) (J : ℕ)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Set.univ : Set {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)})
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  intro i _ j _ hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := mem_Icc.mp i.property
  have hj := mem_Icc.mp j.property
  have hn : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hlogQ : 1 ≤ Real.log Q :=
    hlogP.le.trans (Real.log_le_log (by linarith) hPQ)
  have hip := mrtPrimeBand_bounds
    ((mrt_band_endpoints P Q i hi.1 hP hPQ hlogQ).1.trans' (by norm_num))
    (Real.exp_pos _).le hpi
  have hjp := mrtPrimeBand_bounds
    ((mrt_band_endpoints P Q j hj.1 hP hPQ hlogQ).1.trans' (by norm_num))
    (Real.exp_pos _).le hpj
  change mrtBandLower P Q i < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q i at hip
  change mrtBandLower P Q j < (p : ℝ) ∧ (p : ℝ) ≤ mrtBandUpper Q j at hjp
  rcases lt_or_gt_of_ne hn with hij' | hji'
  · have hgap := mrt_band_gap P Q i j hi.1 hij' hP hPQ hlogP
    linarith
  · have hgap := mrt_band_gap P Q j i hj.1 hji' hP hPQ hlogP
    linarith

end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrincipalPsi
namespace OAI

/-! The principal character only removes powers of five.  For the required
error bound it is enough to charge the prime 5 once, and all remaining
terms to the already proved elementary prime-power error. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
namespace OAI

/-! The fixed modulus-five prime number theorem follows from the three
nonprincipal contour estimates, the zeta prime number theorem, and finite
character orthogonality. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩







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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcBandAvoidance
namespace OAI

/-! The chosen bands avoid every small correction or gcd divisor, and
passing to the completely multiplicative part preserves the exact distance. -/
namespace TwoPointCorrelations

open _root_.Finset



lemma major_arc_actual_bands_disjoint {P Q : ℝ} {J : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hLP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Icc 1 J : Set ℕ)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  intro i hi j hj hij
  have hdis := mrt_actual_bands_pairwise_disjoint P Q J hP hPQ hLP
  exact hdis (x := ⟨i,hi⟩) (y := ⟨j,hj⟩) (by trivial) (by trivial)
    (fun h => hij (congrArg Subtype.val h))

lemma major_arc_first_prime_range {P Q W : ℝ} {H R₀ p : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hPW : 2*W ≤ P) (hPR : (2*R₀:ℕ) ≤ P)
    (hQH : Q ≤ (H:ℝ)/W)
    (hp : p ∈ mrtPrimeBand (mrtBandLower P Q 1) (mrtBandUpper Q 1)) :
    p ≠ 2 ∧ 2*R₀ ≤ p ∧ 2*W ≤ (p:ℝ) ∧ (p:ℝ) ≤ (H:ℝ)/W := by
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := hP0.trans_le hPQ
  have hp' : p ∈ mrtPrimeBand P Q := by
    simpa only [mrtBandLower_one P Q hP0,mrtBandUpper_one Q hQ0] using hp
  have hb := mrtPrimeBand_bounds hP0.le hQ0.le hp'
  refine ⟨?_,?_,hPW.trans hb.1.le,hb.2.trans hQH⟩
  · intro he
    norm_num [he] at hb
    linarith [hb.1]
  · exact_mod_cast hPR.trans hb.1.le


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingBand
namespace OAI

/-! Prime-band costs for the fifth-root working length. Both density
and the minor-arc fourth root have the same elementary rate. -/
namespace TwoPointCorrelations

open _root_.Filter




lemma major_arc_minor_working_rate {W h : ℝ} (hW : 1 ≤ W)
    (hh : 1 ≤ Real.log h) (hupper : Real.log h ≤ W^(1/5:ℝ)) :
    Real.log (Real.log h)*(Real.log h/W)^(1/4:ℝ) ≤ majorArcWorkingError W := by
  have hW0 : 0 < W := by linarith
  have hlog0 : 0 < Real.log h := by linarith
  have hlog := Real.log_le_log hlog0 hupper
  rw [Real.log_rpow hW0] at hlog
  have hp : (Real.log h/W)^(1/4:ℝ) ≤ W^(-1/5:ℝ) := by
    calc
      _ ≤ (W^(1/5:ℝ)/W)^(1/4:ℝ) := Real.rpow_le_rpow
        (div_nonneg hlog0.le hW0.le) (div_le_div_of_nonneg_right hupper hW0.le) (by norm_num)
      _ = _ := by
        rw [div_eq_mul_inv,← Real.rpow_neg_one W,← Real.rpow_add hW0,← Real.rpow_mul hW0.le]
        norm_num
  unfold majorArcWorkingError
  apply mul_le_mul _ hp (Real.rpow_nonneg (div_nonneg hlog0.le hW0.le) _) (by linarith [Real.log_nonneg hW])
  nlinarith [Real.log_nonneg hW]

lemma major_arc_working_band_budget (A : ℕ) (hA : 500000 ≤ A)
    {H : ℕ} {W Q : ℝ} (hW : 10 ≤ Real.log W) (hW0 : 0 < W)
    (hQ : 1 < Q) (hQH : Q ≤ majorArcWorkingLength H W) :
    8192 * (Real.log (Real.log Q) + 1) ≤ (1 / 100 : ℝ) * Real.log (W ^ A) := by
  have hh : (1 : ℝ) < majorArcWorkingLength H W := hQ.trans_le hQH
  have hlog := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have hb := hlog.trans (major_arc_working_length_loglog hW0 hh)
  have hAr : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAr (show 0 ≤ Real.log W by linarith)
  rw [Real.log_pow]
  nlinarith

lemma major_arc_working_band_resolution (A : ℕ) (hA : 500000 ≤ A)
    {H : ℕ} {W Q : ℝ} (hW : 1 ≤ W) (hQ : 1 < Q)
    (hQH : Q ≤ majorArcWorkingLength H W) :
    W ^ (100 : ℕ) ≤ mrtBaseResolution (W ^ A) Q (1 / 100) := by
  have hW0 : 0 < W := by linarith
  have hh : (1 : ℝ) < majorArcWorkingLength H W := hQ.trans_le hQH
  have hlog := Real.log_le_log (Real.log_pos hQ)
    (Real.log_le_log (by linarith : 0 < Q) hQH)
  have hb := hlog.trans (major_arc_working_length_loglog hW0 hh)
  have hAr : (500000 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAr (Real.log_nonneg hW)
  rw [show W ^ (100 : ℕ) = Real.exp ((100 : ℝ) * Real.log W) by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hW0]
    congr 1
    ring, mrtBaseResolution, Real.log_pow]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_nonneg hW]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcWorkingBound
namespace OAI

/-! The typical minor-arc estimate at the common working length. Both
the fourth-root saving and the prime-square remainder fit one rate. -/
namespace TwoPointCorrelations

open _root_.Finset

theorem minor_arc_typical_working_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ),
      (∀ i ∈ I, ∀ p ∈ P i, p.Prime) → Set.PairwiseDisjoint (I:Set ι) P →
      ∀ i ∈ I, ∀ X H : ℕ, 2 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
      ∀ W : ℝ, 1 ≤ W → Real.log (H:ℝ) ≤ W^(1/5:ℝ) →
      (∀ p ∈ P i, p ≠ 2 ∧ 2*R₀ ≤ p ∧ 2*W ≤ (p:ℝ) ∧ (p:ℝ) ≤ (H:ℝ)/W) →
      ∀ F : ℕ → ℂ, Multiplicative F → OneBounded F →
      ∀ r : ℤ, ∀ q : ℕ, 2 ≤ q → W ≤ (q:ℝ) → (q:ℝ) ≤ (H:ℝ)/W →
      ∀ α : ℝ, IsCoprime (q:ℤ) r → |α-(r:ℝ)/q| ≤ 1/(q:ℝ)^2 →
      shortExponentialIntegral (mrtTypicalCoefficient I P F) X H α ≤
        C*(X:ℝ)*H*majorArcWorkingError W := by
  obtain ⟨C,hC,R₀,hbound⟩ := minor_arc_typical_parameter_range_saving
  refine ⟨C+12,by positivity,R₀,?_⟩
  intro ι I P hP hdis i hi X H hH hHX hLH hLL W hW hcap hrange F hFm hFb r q hq hWq hqH α hcop happ
  have hW0 : 0 < W := by linarith
  have hR : 0 < ⌈W⌉₊ := Nat.ceil_pos.mpr hW0
  have hpr : ∀ p ∈ P i, ⌈W⌉₊ ≤ p ∧ p ≤ H := by
    intro p hp
    have hr := hrange p hp
    refine ⟨Nat.ceil_le.mpr (by linarith [hr.2.2.1]),?_⟩
    exact_mod_cast hr.2.2.2.trans (div_le_self (Nat.cast_nonneg H) hW)
  have htail : (∑ p ∈ P i, 1/(p:ℝ)^2) ≤ 2/W := by
    apply (minor_arc_square_reciprocal_sum (P i) ⌈W⌉₊ H hR hpr).trans
    exact div_le_div_of_nonneg_left (by norm_num) hW0 (Nat.le_ceil W)
  have hworking := major_arc_minor_working_rate hW hLH hcap
  have hinv : W⁻¹ ≤ majorArcWorkingError W := by
    calc
      _ = W^(-1:ℝ) := (Real.rpow_neg_one W).symm
      _ ≤ W^(-1/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hW (by norm_num)
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _)
        (by linarith [Real.log_nonneg hW])
  have hx : (X:ℝ)+(H:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show X+H ≤ 2*X by omega)
  have hmain := mul_le_mul_of_nonneg_left hworking (show 0 ≤ C*(X:ℝ)*H by positivity)
  have he : 3*(H:ℝ)*(X+H)*(∑ p ∈ P i, 1/(p:ℝ)^2) ≤
      12*(X:ℝ)*H*majorArcWorkingError W := by
    calc
      _ ≤ 3*(H:ℝ)*(X+H)*(2/W) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ 3*(H:ℝ)*(2*X)*(2/W) := by gcongr
      _ = 12*(X:ℝ)*H*W⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
  apply (hbound I P hP hdis i hi X H hH hHX hLH hLL W hW hrange
    F hFm hFb r q hq hWq hqH α hcop happ).trans
  have hh := add_le_add hmain he
  convert (preTransparency := .instances) hh using 1 <;> ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingParameters
namespace OAI

/-! The literal first prime band, working length and common final band.
The W and X thresholds are independent of the original short length. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem mrt_working_prime_parameters :
    ∀ᶠ W : ℝ in atTop, 2 ≤ W ∧ ∀ H : ℕ, 0 < H →
      1 ≤ Real.log (H:ℝ) → W ≤ Real.log (H:ℝ)^5 →
      let P := W^(500000:ℕ)
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      2 ≤ P ∧ P ≤ Q ∧ 2 ≤ Real.log P ∧ 1 ≤ Real.log Q ∧
        8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P ∧
        W^100 ≤ mrtBaseResolution P Q (1/100) ∧
        2 ≤ mrtBaseResolution P Q (1/100) := by
  filter_upwards [major_arc_working_length_power 500003,eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10:ℝ))]
    with W hpower hW hlog
  refine ⟨hW,?_⟩
  intro H hH hLH hWH
  let P := W^(500000:ℕ)
  let Q := (majorArcWorkingLength H W:ℝ)/W^3
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hlarge := hpower H hH hLH hWH
  have hP : 2 ≤ P := hW.trans (le_self_pow₀ hW1 (by decide))
  have hPQ : P ≤ Q := by
    apply (le_div_iff₀ (pow_pos hW0 3)).mpr
    change W^500000*W^3 ≤ (majorArcWorkingLength H W:ℝ)
    simpa only [← pow_add] using hlarge
  have hLP : 2 ≤ Real.log P := by
    change 2 ≤ Real.log (W^(500000:ℕ))
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hLQ : 1 ≤ Real.log Q :=
    (show (1:ℝ)≤2 by norm_num).trans (hLP.trans
      (Real.log_le_log (by linarith : 0< P) hPQ))
  have hQ : 1 < Q := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (hP.trans hPQ)
  have hQH : Q ≤ (majorArcWorkingLength H W:ℝ) :=
    div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hW1)
  have hbudget := major_arc_working_band_budget 500000 le_rfl hlog hW0 hQ hQH
  have hres := major_arc_working_band_resolution 500000 le_rfl hW1 hQ hQH
  exact ⟨hP,hPQ,hLP,hLQ,hbudget,hres,
    (hW.trans (le_self_pow₀ hW1 (by decide))).trans hres⟩



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcWorkingParameters
namespace OAI

/-! The literal first band satisfies all minor-arc support conditions
once the common parameter exceeds a fixed threshold. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem minor_arc_actual_working_parameters (R₀ : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) →
      W ≤ Real.log (H:ℝ)^5 →
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      2 ≤ h ∧ 1 ≤ W ∧ W ≤ h ∧ 1 ≤ Real.log (h:ℝ) ∧
        1 ≤ Real.log (Real.log (h:ℝ)) ∧ Real.log (h:ℝ) ≤ W^(1/5:ℝ) ∧
        (∀ p ∈ mrtPrimeBand (mrtBandLower P Q 1) (mrtBandUpper Q 1),
          p ≠ 2 ∧ 2*R₀ ≤ p ∧ 2*W ≤ (p:ℝ) ∧ (p:ℝ) ≤ (h:ℝ)/W) := by
  have hlog : Tendsto (fun W:ℝ => Real.log W) atTop atTop := Real.tendsto_log_atTop
  filter_upwards [mrt_working_prime_parameters,major_arc_working_length_power 2,
    (hlog.comp hlog).eventually (eventually_ge_atTop (1:ℝ)),
    hlog.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop ((2*R₀:ℕ):ℝ)] with W hp hpower hLL hL hR
  intro H hH hLH hWH
  dsimp only
  obtain ⟨hW,hpar⟩ := hp
  obtain ⟨hP,hPQ,_,_,_,_,_⟩ := hpar H hH hLH hWH
  let h := majorArcWorkingLength H W
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hhpow : W^2 ≤ (h:ℝ) := hpower H hH hLH hWH
  have hWh : W ≤ (h:ℝ) := (le_self_pow₀ hW1 (by decide : (2:ℕ)≠0)).trans hhpow
  have hh : 2 ≤ h := by exact_mod_cast hW.trans hWh
  have hLh : 1 ≤ Real.log (h:ℝ) := hL.trans (Real.log_le_log hW0 hWh)
  have hLLh : 1 ≤ Real.log (Real.log (h:ℝ)) :=
    hLL.trans (Real.log_le_log (by linarith : 0 < Real.log W)
      (Real.log_le_log hW0 hWh))
  have hcap : Real.log (h:ℝ) ≤ W^(1/5:ℝ) := by
    have hl := Real.log_le_log (by exact_mod_cast (show 0< h by omega))
      (major_arc_working_length_exp_upper H hW0.le)
    simpa only [Real.log_exp] using hl
  refine ⟨hh,hW1,hWh,hLh,hLLh,hcap,?_⟩
  intro p hp
  have hPW : 2*W ≤ P :=
    (show 2*W ≤ W^2 by nlinarith only [hW]).trans
      (pow_le_pow_right₀ hW1 (by norm_num : (2:ℕ)≤500000))
  have hPR : ((2*R₀:ℕ):ℝ) ≤ P :=
    hR.trans (le_self_pow₀ hW1 (by decide : (500000:ℕ)≠0))
  have hQH : Q ≤ (h:ℝ)/W := div_le_div_of_nonneg_left (Nat.cast_nonneg h) hW0
    (le_self_pow₀ hW1 (by decide : (3:ℕ)≠0))
  exact major_arc_first_prime_range hP hPQ hPW hPR hQH hp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcWorkingMean
namespace OAI

/-! Minor arcs at the same parameter and prime bands as the major arcs.
The original outer logarithm remains fixed while the origin range varies. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem minor_arc_actual_working_mean_oai :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter L H M
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      W₀ ≤ W → ∀ Y J : ℕ, h ≤ Y → 1 ≤ J →
    ∀ F : ℕ → ℂ, Multiplicative F → OneBounded F →
    ∀ r : ℤ, ∀ q : ℕ, W ≤ (q:ℝ) → (q:ℝ) ≤ (h:ℝ)/W →
    ∀ α : ℝ, IsCoprime (q:ℤ) r → |α-(r:ℝ)/q| ≤ 1/(q:ℝ)^2 →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α ≤
      C*(Y:ℝ)*h*(Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)) := by
  obtain ⟨C,hC,R₀,hminor⟩ := minor_arc_typical_working_bound
  obtain ⟨W₀,hW₀⟩ := eventually_atTop.mp
    ((minor_arc_actual_working_parameters R₀).and mrt_working_prime_parameters)
  refine ⟨21*C,by positivity,W₀,?_⟩
  filter_upwards [major_arc_parameter_rate,eventually_ge_atTop (1:ℝ)] with L hrate hL
  intro H hH hLH hLL M hM
  dsimp only
  intro hWlarge Y J hhY hJ F hFm hFb r q hWq hqh α hcop happ
  let W := majorArcParameter L H M
  let h := majorArcWorkingLength H W
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  obtain ⟨_,hWH,_,_⟩ := major_arc_parameter_bounds hL hLH hM
  obtain ⟨hwindow,hprime⟩ := hW₀ W hWlarge
  obtain ⟨hh,hW,hWh,hLh,hLLh,hcap,hprimes⟩ := hwindow H hH hLH hWH
  obtain ⟨hP,hPQ,hLP,_,_,_,_⟩ := hprime.2 H hH hLH hWH
  have hq : 2 ≤ q := by exact_mod_cast hprime.1.trans hWq
  have hm := hminor (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
    (fun _ _ _ hp => mrtPrimeBand_prime hp)
    (major_arc_actual_bands_disjoint hP hPQ (by linarith)) 1
    (mem_Icc.mpr ⟨le_rfl,hJ⟩) Y h hh hhY hLh hLLh W hW hcap hprimes
    F hFm hFb r q hq hWq hqh α hcop happ
  have hs := hrate (H:ℝ) M hLH hLL hM
  rw [mul_div_assoc] at hs
  have he : majorArcWorkingError W ≤
      21*(Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)) := by
    have hshort : 0 ≤ Real.log (Real.log (H:ℝ))/Real.log H := by positivity
    have herr : 0 ≤ L^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    linarith only [hs,hshort,herr]
  apply hm.trans
  have hp := mul_le_mul_of_nonneg_left he (show 0≤ C*(Y:ℝ)*h by positivity)
  convert (preTransparency := .instances) hp using 1
  ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.minor_arc_actual_working_mean_oai := @OAI.TwoPointCorrelations.minor_arc_actual_working_mean_oai
