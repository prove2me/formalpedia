-- Prove2me | solution 1 for OAI.TwoPointCorrelations.major_arc_corrected_typical_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:26:59.064984+00:00
-- url     : https://prove2.me/submissions/c4f24ce1-96de-417c-8aab-79a985125f5f

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_major_arc_typical_rational_global

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial




namespace Finset

/-- Backport (Mathlib d13f23b): summation by parts, differencing the module factor. -/
theorem sum_range_by_parts' {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (f : ℕ → R) (g : ℕ → M) (n : ℕ) :
    ∑ i ∈ range n, f i • g i =
      (∑ i ∈ range n, f i) • g (n - 1) -
        ∑ i ∈ range (n - 1), (∑ j ∈ range (i + 1), f j) • (g (i + 1) - g i) := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ (f := fun i ↦ f i • g i), ih]
      simp only [sum_range_succ, smul_sub, add_smul]
      abel

/-- Backport (Mathlib d13f23b), additive form of `prod_le_prod_of_injOn`. -/
theorem sum_le_sum_of_injOn {ι α N : Type*} [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  refine le_trans ?_ <| sum_le_sum_of_subset_of_nonneg ht hg
  rw [sum_image he]
  exact sum_le_sum h

end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst

end

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn


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

open _root_.Filter
open _root_.Finset hiding sum_le_sum_of_injOn
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

open _root_.Complex _root_.HurwitzZeta
open _root_.Finset hiding sum_le_sum_of_injOn
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

open _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open _root_.Finset hiding sum_le_sum_of_injOn
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProgressionFourier
namespace OAI

/-!
# Additive Fourier resolution of every progression class

The coefficient mass is exactly one. There is no invertibility assumption
on the class, and no frequency supremum is put inside an integral.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators

theorem additiveCharacter_add (α β : ℝ) (n : ℕ) :
    additiveCharacter (α + β) n = additiveCharacter α n * additiveCharacter β n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring





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

open _root_.MeasureTheory
open _root_.Finset hiding sum_le_sum_of_injOn
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

lemma additiveCharacter_nat_add (α : ℝ) (m n : ℕ) :
    additiveCharacter α (m + n) = additiveCharacter α m * additiveCharacter α n := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_additiveCharacter (α : ℝ) (n : ℕ) : ‖additiveCharacter α n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _


lemma shortExponentialSum_eq_window (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v = additiveCharacter α v * shortWindowSum b D α v := by
  rw [shortExponentialSum_at_nat, sum_Icc_shift]
  unfold shortWindowSum
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  rw [show v + m + 1 = v + (m + 1) by omega, additiveCharacter_nat_add]
  ring

lemma norm_shortExponentialSum_eq_window (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    ‖shortExponentialSum b D α v‖ = ‖shortWindowSum b D α v‖ := by
  rw [shortExponentialSum_eq_window, norm_mul, norm_additiveCharacter, one_mul]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcPerturbation
namespace OAI

/-! A finite partial-summation form of the major-arc frequency perturbation.
The error uses the actual shorter windows before averaging the origin;
no frequency supremum is moved inside an integral. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma major_arc_abel_bound (a w : ℕ → ℂ) (N : ℕ) (L : ℝ)
    (hw : ∀ n, ‖w n‖ ≤ 1)
    (hstep : ∀ n, ‖w (n + 1) - w n‖ ≤ L) :
    ‖∑ n ∈ range N, a n * w n‖ ≤ ‖∑ n ∈ range N, a n‖ +
      L * ∑ n ∈ range (N - 1), ‖∑ j ∈ range (n + 1), a j‖ := by
  have he := sum_range_by_parts' a w N
  simp only [smul_eq_mul] at he
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hw _)
  · calc
      _ ≤ ∑ n ∈ range (N - 1),
          ‖(∑ j ∈ range (n + 1), a j) * (w (n + 1) - w n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range (N - 1), L * ‖∑ j ∈ range (n + 1), a j‖ := by
        apply sum_le_sum
        intro n _
        rw [norm_mul, mul_comm L]
        exact mul_le_mul_of_nonneg_left (hstep n) (norm_nonneg _)
      _ = _ := (mul_sum _ _ _).symm

lemma major_arc_character_step (β : ℝ) (n : ℕ) :
    ‖additiveCharacter β (n + 1) - additiveCharacter β n‖ ≤
      2 * Real.pi * |β| := by
  have he : additiveCharacter β (n + 1) - additiveCharacter β n =
      additiveCharacter β n * (additiveCharacter β 1 - 1) := by
    rw [additiveCharacter_nat_add]
    ring
  rw [he, norm_mul, norm_additiveCharacter, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * β)
  have harg : additiveCharacter β 1 = Complex.exp (Complex.I * (2 * Real.pi * β : ℝ)) := by
    unfold additiveCharacter
    congr 1
    push_cast
    ring
  rw [harg]
  convert (preTransparency := .instances) h using 1
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

lemma major_arc_frequency_perturbation (a : ℕ → ℂ) (H v : ℕ) (α β : ℝ) :
    ‖shortExponentialSum a H (α + β) v‖ ≤
      ‖shortExponentialSum a H α v‖ + 2 * Real.pi * |β| *
        ∑ h ∈ range (H - 1), ‖shortExponentialSum a (h + 1) α v‖ := by
  have hb := major_arc_abel_bound
    (fun n => a (v + n + 1) * additiveCharacter α (v + n + 1))
    (fun n => additiveCharacter β (v + n + 1)) H (2 * Real.pi * |β|)
    (fun n => (norm_additiveCharacter β _).le)
    (fun n => by
      simpa only [Nat.add_assoc] using major_arc_character_step β (v + n + 1))
  simp only [shortExponentialSum_at_nat, sum_Icc_shift]
  convert (preTransparency := .instances) hb using 1
  apply congrArg norm
  apply sum_congr rfl
  intro n _
  rw [additiveCharacter_add]
  ring

theorem major_arc_integral_perturbation (a : ℕ → ℂ) (X H : ℕ) (α β : ℝ) :
    shortExponentialIntegral a X H (α + β) ≤
      shortExponentialIntegral a X H α + 2 * Real.pi * |β| *
        ∑ h ∈ range (H - 1), shortExponentialIntegral a X (h + 1) α := by
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X, (‖shortExponentialSum a H α v‖ + 2 * Real.pi * |β| *
        ∑ h ∈ range (H - 1), ‖shortExponentialSum a (h + 1) α v‖) :=
      sum_le_sum (fun v _ => major_arc_frequency_perturbation a H v α β)
    _ = _ := by rw [sum_add_distrib, ← mul_sum, sum_comm]

lemma major_arc_integral_perturbation_uniform (a : ℕ → ℂ) (X H : ℕ)
    (hH : 0 < H) (α β K : ℝ) (hK : 0 ≤ K)
    (hprefix : ∀ h : ℕ, 1 ≤ h → h ≤ H → shortExponentialIntegral a X h α ≤ K) :
    shortExponentialIntegral a X H (α + β) ≤
      (1 + 2 * Real.pi * |β| * H) * K := by
  apply (major_arc_integral_perturbation a X H α β).trans
  have hs : (∑ h ∈ range (H - 1), shortExponentialIntegral a X (h + 1) α) ≤
      (H : ℝ) * K := by
    calc
      _ ≤ ∑ _h ∈ range (H - 1), K := by
        apply sum_le_sum
        intro h hh
        exact hprefix (h + 1) (by omega) (by have := mem_range.mp hh; omega)
      _ = ((H - 1 : ℕ) : ℝ) * K := by simp
      _ ≤ (H : ℝ) * K := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.sub_le H 1) hK
  calc
    _ ≤ K + 2 * Real.pi * |β| * ((H : ℝ) * K) :=
      add_le_add (hprefix H hH le_rfl) (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcTrivial
namespace OAI

/-! The exact trivial bound used for bounded ranges of the short length. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

lemma minor_arc_short_sum_trivial (F : ℕ → ℂ) (hF : OneBounded F)
    (H k : ℕ) (α : ℝ) : ‖shortExponentialSum F H α k‖ ≤ H := by
  rw [shortExponentialSum_at_nat]
  calc
    _ ≤ ∑ n ∈ Icc (k + 1) (k + H), ‖F n * additiveCharacter α n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc (k + 1) (k + H), (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul, norm_additiveCharacter, mul_one]
      exact hF n (by have hh := (mem_Icc.mp hn).1; omega)
    _ = H := by
      simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
      congr 1
      omega

lemma minor_arc_short_integral_trivial (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) (α : ℝ) : shortExponentialIntegral F X H α ≤ (X : ℝ) * H := by
  rw [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ _k ∈ range X, (H : ℝ) :=
      sum_le_sum (fun k _ => minor_arc_short_sum_trivial F hF H k α)
    _ = _ := by simp

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

open _root_.Finset hiding sum_le_sum_of_injOn
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitCorrection
namespace OAI

/-! The exact convolution with the constant-one function used for the
near-twist renormalization. Its prime coefficients are the actual deviation
from one, including missing-prime masks. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical



@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]









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

open _root_.Finset hiding sum_le_sum_of_injOn
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

open _root_.Finset hiding sum_le_sum_of_injOn
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DilatedWindows
namespace OAI

/-! Exact short-window reindexing for a sequence supported on multiples
of a fixed integer. Only one endpoint term is lost to a fixed window length. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma additiveCharacter_nat_mul (α : ℝ) (a m : ℕ) :
    additiveCharacter α (a * m) = additiveCharacter (a * α) m := by
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma shortExponentialSum_dilation (f : ℕ → ℂ) (a D v : ℕ)
    (ha : 0 < a) (α : ℝ) :
    shortExponentialSum (dilationSequence a f) D α v =
      shortExponentialSum f ((v + D) / a - v / a) (a * α) ((v / a : ℕ) : ℝ) := by
  have hle : v / a ≤ (v + D) / a := Nat.div_le_div_right (Nat.le_add_right _ _)
  rw [shortExponentialSum_at_nat, shortExponentialSum_at_nat,
    Nat.add_sub_of_le hle]
  have hleft : (∑ n ∈ Icc (v + 1) (v + D),
      dilationSequence a f n * additiveCharacter α n) =
      ∑ n ∈ (Icc (v + 1) (v + D)).filter (fun n => a ∣ n),
        f (n / a) * additiveCharacter α n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    unfold dilationSequence
    split_ifs <;> simp
  rw [hleft]
  symm
  apply sum_bij (fun m _ => a * m)
  · intro m hm
    obtain ⟨hm0, hm1⟩ := mem_Icc.mp hm
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right a m⟩
    · have ht : v < a * m := by
        have hh := (Nat.div_lt_iff_lt_mul ha).mp (show v / a < m by omega)
        simpa only [Nat.mul_comm] using hh
      omega
    · have hh := (Nat.le_div_iff_mul_le ha).mp hm1
      simpa only [Nat.mul_comm] using hh
  · intro m _ n _ he
    exact Nat.eq_of_mul_eq_mul_left ha he
  · intro n hn
    obtain ⟨hnI, hd⟩ := mem_filter.mp hn
    obtain ⟨hn0, hn1⟩ := mem_Icc.mp hnI
    refine ⟨n / a, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hn1⟩,
      Nat.mul_div_cancel' hd⟩
    have he : v < a * (n / a) := by rw [Nat.mul_div_cancel' hd]; omega
    have hh : v / a < n / a := (Nat.div_lt_iff_lt_mul ha).mpr (by
      simpa only [Nat.mul_comm] using he)
    omega
  · intro m _
    rw [Nat.mul_div_cancel_left _ ha, additiveCharacter_nat_mul]

lemma quotient_window_length (a D v : ℕ) (_ha : 0 < a) :
    (v + D) / a - v / a = D / a ∨ (v + D) / a - v / a = D / a + 1 := by
  have hlo : v / a + D / a ≤ (v + D) / a := Nat.div_add_div_le_add_div
  have hhi := Nat.add_div_le_div_add_div_add_one v D a
  generalize (v + D) / a = t at *
  generalize v / a = u at *
  generalize D / a = w at *
  omega

lemma norm_shortWindowSum_le_succ (f : ℕ → ℂ) (hf : OneBounded f)
    (D v : ℕ) (α : ℝ) :
    ‖shortWindowSum f D α v‖ ≤ ‖shortWindowSum f (D + 1) α v‖ + 1 := by
  have he : shortWindowSum f (D + 1) α v = shortWindowSum f D α v +
      f (v + D + 1) * additiveCharacter α (D + 1) := by
    simp only [shortWindowSum, sum_range_succ]
  have hn : ‖f (v + D + 1) * additiveCharacter α (D + 1)‖ ≤ 1 := by
    rw [norm_mul, norm_additiveCharacter, mul_one]
    exact hf _ (by omega)
  have ht := norm_sub_le (shortWindowSum f (D + 1) α v)
    (f (v + D + 1) * additiveCharacter α (D + 1))
  have ht' : ‖shortWindowSum f D α v‖ ≤
      ‖shortWindowSum f (D + 1) α v‖ +
        ‖f (v + D + 1) * additiveCharacter α (D + 1)‖ := by
    simpa only [he, add_sub_cancel_right] using ht
  linarith

lemma norm_shortExponentialSum_dilation_le (f : ℕ → ℂ) (hf : OneBounded f)
    (a D v : ℕ) (ha : 0 < a) (α : ℝ) :
    ‖shortExponentialSum (dilationSequence a f) D α v‖ ≤
      ‖shortWindowSum f (D / a + 1) (a * α) (v / a)‖ + 1 := by
  rw [shortExponentialSum_dilation f a D v ha α,
    norm_shortExponentialSum_eq_window]
  rcases quotient_window_length a D v ha with he | he
  · rw [he]
    exact norm_shortWindowSum_le_succ f hf _ _ _
  · rw [he]
    exact le_add_of_nonneg_right zero_le_one

lemma quotient_sample_sum_le (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (a Y : ℕ) (ha : 0 < a) :
    (∑ v ∈ range Y, F (v / a)) ≤
      (a : ℝ) * ∑ m ∈ range (Y / a + 1), F m := by
  have hb : (∑ v ∈ range Y, F (v / a)) ≤
      ∑ x ∈ range (Y / a + 1) ×ˢ range a, F x.1 := by
    apply sum_le_sum_of_injOn (fun v => (v / a, v % a))
    · intro v _ w _ he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      nlinarith [Nat.div_add_mod v a, Nat.div_add_mod w a]
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact mem_product.mpr ⟨mem_range.mpr (by
        have hh : v / a ≤ Y / a := Nat.div_le_div_right (Nat.le_of_lt (mem_range.mp hv))
        exact Nat.lt_succ_of_le hh),
        mem_range.mpr (Nat.mod_lt _ ha)⟩
    · intro v _
      exact le_rfl
    · intro x _ _
      exact hF x.1
  apply hb.trans_eq
  rw [sum_product]
  simp only [sum_const, card_range, nsmul_eq_mul, ← mul_sum]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowSum
namespace OAI

/-! The exact smooth-divisor decomposition inside a short Fourier window,
with the discarded tail bounded before any cancellation is used. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma shortWindowSum_sub (f g : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortWindowSum (fun n => f n - g n) D α v =
      shortWindowSum f D α v - shortWindowSum g D α v := by
  simp only [shortWindowSum, sub_mul, sum_sub_distrib]

lemma norm_shortWindowSum_le (f : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    ‖shortWindowSum f D α v‖ ≤ ∑ m ∈ range D, ‖f (v + m + 1)‖ := by
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, norm_additiveCharacter, mul_one, le_refl]

lemma window_error_from_density (f g : ℕ → ℂ) (e : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hfg : ∀ n, 0 < n → ‖f n - g n‖ ≤ e n)
    (D Y : ℕ) (α : ℝ) :
    (∑ v ∈ range Y, ‖shortWindowSum f D α v - shortWindowSum g D α v‖) ≤
      (D : ℝ) * ∑ n ∈ range (Y + D), e (n + 1) := by
  calc
    _ ≤ ∑ v ∈ range Y, ∑ m ∈ range D, e (v + m + 1) := by
      apply sum_le_sum
      intro v _
      rw [← shortWindowSum_sub]
      exact (norm_shortWindowSum_le _ _ _ _).trans
        (sum_le_sum (fun m _ => hfg _ (by omega)))
    _ = ∑ m ∈ range D, ∑ v ∈ range Y, e (v + m + 1) := sum_comm
    _ ≤ ∑ _m ∈ range D, ∑ n ∈ range (Y + D), e (n + 1) := by
      apply sum_le_sum
      intro m hm
      apply sum_le_sum_of_injOn (fun v => v + m)
      · intro v _ w _ h
        change v + m = w + m at h
        omega
      · intro x hx
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
        simp only [mem_range] at hm hv ⊢
        omega
      · intro v _
        exact le_rfl
      · intro n _ _
        exact he _
    _ = _ := by simp





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionShortWindow
namespace OAI

/-! Exact short-window convolution and the uniform large-divisor tail
in the reduction to completely multiplicative functions. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_correction_finite_sum (F : ℕ → ℂ) (hF : Multiplicative F) (hF1 : F 1=1)
    {n B : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    F n = ∑ d ∈ Icc 1 B,
      mrtCorrection F d*dilationSequence d (mrtCompletePart F) n := by
  rw [mrt_multiplicative_divisor_sum F hF hF1 hn]
  have hsub : n.divisors ⊆ Icc 1 B := by
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdvd hn,(Nat.le_of_dvd hn hdvd).trans hnB⟩
  calc
    _ = ∑ d ∈ n.divisors, mrtCorrection F d*dilationSequence d (mrtCompletePart F) n := by
      apply sum_congr rfl
      intro d hd
      simp only [dilationSequence,(Nat.mem_divisors.mp hd).1,ite_true]
    _ = _ := sum_subset hsub (by
      intro d _ hd
      have hnot : ¬d ∣ n := fun h => hd (Nat.mem_divisors.mpr ⟨h,hn.ne'⟩)
      simp only [dilationSequence,hnot,ite_false,mul_zero])



lemma mrt_dilation_prefix_count (d B : ℕ) (hd : 0 < d) :
    (∑ n ∈ range B, if d ∣ n+1 then (1:ℝ) else 0) = (B/d:ℕ) := by
  have he : (∑ n ∈ range B, if d ∣ n+1 then (1:ℝ) else 0) =
      ∑ n ∈ Icc 1 B, if d ∣ n then (1:ℝ) else 0 := by
    apply sum_bij (fun n _ => n+1)
    · intro n hn
      exact mem_Icc.mpr ⟨by omega,by have hh := mem_range.mp hn; omega⟩
    · intro n _ m _ hnm
      omega
    · intro n hn
      obtain ⟨hn1,hnB⟩ := mem_Icc.mp hn
      exact ⟨n-1,mem_range.mpr (by omega),by omega⟩
    · intro n _
      rfl
  rw [he,← sum_filter]
  calc
    _ = ∑ _m ∈ Icc 1 (B/d), (1:ℝ) := by
      symm
      apply sum_bij (fun m _ => d*m)
      · intro m hm
        obtain ⟨hm1,hmB⟩ := mem_Icc.mp hm
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd hm1,
          by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmB⟩,
          dvd_mul_right d m⟩
      · intro m _ n _ hmn
        exact Nat.eq_of_mul_eq_mul_left hd hmn
      · intro n hn
        obtain ⟨hnI,hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn1,hnB⟩ := mem_Icc.mp hnI
        exact ⟨n/d,mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdiv) hd,
          Nat.div_le_div_right hnB⟩,Nat.mul_div_cancel' hdiv⟩
      · intro _ _
        rfl
    _ = _ := by simp

lemma mrt_dilation_short_integral (G : ℕ → ℂ) (hG : OneBounded G)
    (d X H : ℕ) (hd : 0 < d) (α : ℝ) :
    shortExponentialIntegral (dilationSequence d G) X H α ≤ (H:ℝ)*( (X+H)/d:ℕ) := by
  have hpoint (n : ℕ) (hn : 0 < n) :
      ‖dilationSequence d G n-(0:ℂ)‖ ≤ if d ∣ n then (1:ℝ) else 0 := by
    by_cases hdn : d ∣ n
    · simpa only [dilationSequence,hdn,ite_true,sub_zero] using
        hG (n/d) (Nat.div_pos (Nat.le_of_dvd hn hdn) hd)
    · simp only [dilationSequence,hdn,ite_false,sub_self,norm_zero,le_refl]
  have hz (v : ℕ) : shortWindowSum (fun _ => (0:ℂ)) H α v = 0 := by
    simp only [shortWindowSum,zero_mul,sum_const_zero]
  have he := window_error_from_density (dilationSequence d G) (fun _ => (0:ℂ))
    (fun n => if d ∣ n then (1:ℝ) else 0) (fun _ => by split_ifs <;> positivity)
    hpoint H X α
  rw [mrt_dilation_prefix_count d (X+H) hd] at he
  simpa only [shortExponentialIntegral_eq_sum,norm_shortExponentialSum_eq_window,hz,sub_zero] using he



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalFactors
namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical _root_.BigOperators














lemma mrtPrimeAvoids_of_lt (P : Finset ℕ) {d : ℕ} (hd : 0 < d)
    (hP : ∀ p ∈ P, d < p) : mrtPrimeAvoids P d := by
  intro p hp hpd
  exact (not_le_of_gt (hP p hp)) (Nat.le_of_dvd hd hpd)

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
namespace OAI

/-! Coarse Ramaré factorization on the actual typical-factorization set.
Removing a prime from the selected band leaves precisely the other-band
mask; the square and endpoint errors retain their uniform finite bounds. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory
open _root_.Finset hiding sum_le_sum_of_injOn
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcPrefixCutoff
namespace OAI

/-! Very short prefixes use boundedness; character estimates are only
needed above the cutoff where all divided windows remain long. -/
namespace TwoPointCorrelations

lemma major_arc_prefix_cutoff (B : ℕ → ℂ) (hB : OneBounded B)
    (X H : ℕ) (α U K : ℝ) (hsmall : (X:ℝ)*U ≤ K)
    (hlong : ∀ h : ℕ, 1 ≤ h → h ≤ H → U ≤ (h:ℝ) →
      shortExponentialIntegral B X h α ≤ K) :
    ∀ h : ℕ, 1 ≤ h → h ≤ H → shortExponentialIntegral B X h α ≤ K := by
  intro h hh hhH
  by_cases hu : U ≤ (h:ℝ)
  · exact hlong h hh hhH hu
  · exact (minor_arc_short_integral_trivial B hB X h α).trans
      ((mul_le_mul_of_nonneg_left (le_of_not_ge hu) (Nat.cast_nonneg X)).trans hsmall)


theorem major_arc_perturbation_cutoff_two (B : ℕ → ℂ) (hB : OneBounded B)
    (X H : ℕ) (hH : 0 < H) (α β U K : ℝ) (hK : 0 ≤ K)
    (hsmall : (X:ℝ)*U ≤ K) (hphase : |β| *(H:ℝ) ≤ 2)
    (hlong : ∀ h : ℕ, 1 ≤ h → h ≤ H → U ≤ (h:ℝ) →
      shortExponentialIntegral B X h α ≤ K) :
    shortExponentialIntegral B X H (α+β) ≤ (1+4*Real.pi)*K := by
  apply (major_arc_integral_perturbation_uniform B X H hH α β K hK
    (major_arc_prefix_cutoff B hB X H α U K hsmall hlong)).trans
  apply mul_le_mul_of_nonneg_right _ hK
  nlinarith [Real.pi_pos]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionTypical
namespace OAI

/-! The prime-power correction preserves the literal typical mask on
small divisors avoiding the selected bands. The remaining divisors are
paid by their absolute reciprocal mass, without removing that mask. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrt_correction_masked_dilation {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (d n : ℕ) :
    dilationSequence d (mrtCorrectionMaskedCofactor J P F d) n =
      if mrtTypical J P n then dilationSequence d (mrtCompletePart F) n else 0 := by
  unfold dilationSequence mrtCorrectionMaskedCofactor
  by_cases hd : d ∣ n
  · simp only [hd,ite_true,Nat.mul_div_cancel' hd]
  · simp only [hd,ite_false,ite_self]

lemma mrt_correction_masked_oneBounded {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F) (d : ℕ) :
    OneBounded (mrtCorrectionMaskedCofactor J P F d) := by
  intro n hn
  unfold mrtCorrectionMaskedCofactor
  split_ifs
  · exact mrtCompletePart_oneBounded F hF n hn
  · simp

lemma mrt_correction_masked_of_avoids {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) {d : ℕ} (hd : mrtPrimeAvoids (J.biUnion P) d) :
    mrtCorrectionMaskedCofactor J P F d = mrtTypicalCoefficient J P (mrtCompletePart F) := by
  funext n
  unfold mrtCorrectionMaskedCofactor mrtTypicalCoefficient
  rw [mrtTypical_mul_of_avoids J P hP hd n]

lemma mrt_correction_typical_finite {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : Multiplicative F) (hF1 : F 1=1)
    {n B : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    mrtTypicalCoefficient J P F n = ∑ d ∈ Icc 1 B, mrtCorrection F d*
      dilationSequence d (mrtCorrectionMaskedCofactor J P F d) n := by
  simp only [mrt_correction_masked_dilation]
  unfold mrtTypicalCoefficient
  by_cases ht : mrtTypical J P n
  · simpa only [ht,ite_true] using mrt_correction_finite_sum F hF hF1 hn hnB
  · simp only [ht,ite_false,mul_zero,sum_const_zero]

theorem mrt_correction_typical_short_sum {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : Multiplicative F) (hF1 : F 1=1)
    (H v B : ℕ) (hv : v+H ≤ B) (α : ℝ) :
    shortExponentialSum (mrtTypicalCoefficient J P F) H α (v:ℕ) =
      ∑ d ∈ Icc 1 B, mrtCorrection F d*
        shortExponentialSum (dilationSequence d (mrtCorrectionMaskedCofactor J P F d))
          H α (v:ℕ) := by
  simp only [shortExponentialSum_at_nat]
  calc
    _ = ∑ n ∈ Icc (v+1) (v+H),
        (∑ d ∈ Icc 1 B, mrtCorrection F d*
          dilationSequence d (mrtCorrectionMaskedCofactor J P F d) n)*additiveCharacter α n := by
      apply sum_congr rfl
      intro n hn
      rw [mrt_correction_typical_finite J P F hF hF1
        (by have hh := (mem_Icc.mp hn).1; omega) ((mem_Icc.mp hn).2.trans hv)]
    _ = _ := by
      simp only [sum_mul,mul_sum,mul_assoc]
      rw [sum_comm]

lemma mrt_correction_typical_integral_sum {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : Multiplicative F) (hF1 : F 1=1)
    (X H : ℕ) (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        shortExponentialIntegral
          (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α := by
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X, ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        ‖shortExponentialSum (dilationSequence d (mrtCorrectionMaskedCofactor J P F d))
          H α (v:ℕ)‖ := by
      apply sum_le_sum
      intro v hv
      rw [mrt_correction_typical_short_sum J P F hF hF1 H v (X+H)
        (by have hh := mem_range.mp hv; omega) α]
      simpa only [norm_mul] using norm_sum_le (Icc 1 (X+H))
        (fun d => mrtCorrection F d*shortExponentialSum
          (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) H α (v:ℕ))
    _ = _ := by rw [sum_comm]; simp only [mul_sum]

theorem mrt_correction_typical_tail {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F) (hF1 : F 1=1)
    (X H W : ℕ) (hW : 0 < W) (hHX : H ≤ X)
    (havoid : ∀ d : ℕ, 0 < d → d ≤ W → mrtPrimeAvoids (J.biUnion P) d)
    (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      (∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
        shortExponentialIntegral
          (dilationSequence d (mrtTypicalCoefficient J P (mrtCompletePart F))) X H α) +
      2*mrtCorrectionBound*X*H*(W:ℝ)^(-(1/4:ℝ)) := by
  let U := (Icc 1 (X+H)).filter (fun d => ¬d ≤ W)
  have htail : (∑ d ∈ U, ‖mrtCorrection F d‖*
      shortExponentialIntegral (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α) ≤
      2*mrtCorrectionBound*X*H*(W:ℝ)^(-(1/4:ℝ)) := by
    have hm := mrt_correction_tail_bound F hFb hF1 hW U
      (fun d hd => by have hh := (mem_filter.mp hd).2; omega)
    calc
      _ ≤ (H:ℝ)*(X+H)*(∑ d ∈ U, ‖mrtCorrection F d‖/(d:ℝ)) := by
        rw [mul_sum]
        apply sum_le_sum
        intro d hd
        have hd0 : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
        have hi := mrt_dilation_short_integral (mrtCorrectionMaskedCofactor J P F d)
          (mrt_correction_masked_oneBounded J P F hFb d) d X H hd0 α
        calc
          _ ≤ ‖mrtCorrection F d‖*((H:ℝ)*((X+H)/d:ℕ)) :=
            mul_le_mul_of_nonneg_left hi (norm_nonneg _)
          _ ≤ ‖mrtCorrection F d‖*((H:ℝ)*((X+H:ℕ):ℝ)/(d:ℝ)) := by
            have hh₀ : (((X+H)/d:ℕ):ℝ) ≤ ((X+H:ℕ):ℝ)/(d:ℝ) := Nat.cast_div_le
            have hh : (H:ℝ)*((X+H)/d:ℕ) ≤ (H:ℝ)*(((X+H:ℕ):ℝ)/(d:ℝ)) :=
              mul_le_mul_of_nonneg_left hh₀ (Nat.cast_nonneg H)
            simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hh (norm_nonneg (mrtCorrection F d))
          _ = _ := by push_cast; ring
      _ ≤ (H:ℝ)*(X+H)*(mrtCorrectionBound*(W:ℝ)^(-(1/4:ℝ))) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ _ := by
        have hHXr : (H:ℝ) ≤ X := by exact_mod_cast hHX
        have hC : 0 ≤ mrtCorrectionBound*(W:ℝ)^(-(1/4:ℝ)) := by
          unfold mrtCorrectionBound
          positivity
        have hh := mul_le_mul_of_nonneg_right hHXr (mul_nonneg (Nat.cast_nonneg H) hC)
        nlinarith
  have hsmall : (∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
      shortExponentialIntegral (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α) =
      ∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
        shortExponentialIntegral
          (dilationSequence d (mrtTypicalCoefficient J P (mrtCompletePart F))) X H α := by
    apply sum_congr rfl
    intro d hd
    obtain ⟨hdI,hdW⟩ := mem_filter.mp hd
    rw [mrt_correction_masked_of_avoids J P hP F (havoid d (mem_Icc.mp hdI).1 hdW)]
  calc
    _ ≤ ∑ d ∈ Icc 1 (X+H), ‖mrtCorrection F d‖*
        shortExponentialIntegral (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α :=
      mrt_correction_typical_integral_sum J P F hF hF1 X H α
    _ = _ + ∑ d ∈ U, ‖mrtCorrection F d‖*
        shortExponentialIntegral (dilationSequence d (mrtCorrectionMaskedCofactor J P F d)) X H α :=
      (sum_filter_add_sum_filter_not _ (fun d => d ≤ W) _).symm
    _ ≤ _ := by rw [hsmall]; exact add_le_add le_rfl htail

theorem mrt_correction_typical_tail_below_primes {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F) (hF1 : F 1=1)
    (X H W : ℕ) (hW : 0 < W) (hHX : H ≤ X)
    (hlarge : ∀ j ∈ J, ∀ p ∈ P j, W < p) (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      (∑ d ∈ (Icc 1 (X+H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖*
        shortExponentialIntegral
          (dilationSequence d (mrtTypicalCoefficient J P (mrtCompletePart F))) X H α) +
      2*mrtCorrectionBound*X*H*(W:ℝ)^(-(1/4:ℝ)) := by
  apply mrt_correction_typical_tail J P hP F hF hFb hF1 X H W hW hHX _ α
  intro d hd hdW
  apply mrtPrimeAvoids_of_lt _ hd
  intro p hp
  obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
  exact hdW.trans_lt (hlarge j hj p hp)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionQuotient
namespace OAI

/-! The small-divisor terms in the general-multiplicative correction use
literal divided origin ranges, divided window lengths, and dilated additive
frequencies. The rounding cost is one term per original origin. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem mrt_dilation_integral_quotient (G : ℕ → ℂ) (hG : OneBounded G)
    (d X H : ℕ) (hd : 0 < d) (α : ℝ) :
    shortExponentialIntegral (dilationSequence d G) X H α ≤
      (d : ℝ) * shortExponentialIntegral G (X / d + 1) (H / d + 1) (d * α) + X := by
  rw [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X, (‖shortWindowSum G (H / d + 1) (d * α) (v / d)‖ + 1) := by
      apply sum_le_sum
      intro v _
      exact norm_shortExponentialSum_dilation_le G hG d H v hd α
    _ = (∑ v ∈ range X, ‖shortWindowSum G (H / d + 1) (d * α) (v / d)‖) + X := by
      rw [sum_add_distrib]
      simp
    _ ≤ (d : ℝ) * (∑ m ∈ range (X / d + 1),
        ‖shortWindowSum G (H / d + 1) (d * α) m‖) + X :=
      add_le_add (quotient_sample_sum_le _ (fun _ => norm_nonneg _) d X hd) le_rfl
    _ = _ := by
      rw [shortExponentialIntegral_eq_sum]
      simp_rw [norm_shortExponentialSum_eq_window]


theorem mrt_correction_typical_quotient_tail {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F) (hF1 : F 1 = 1)
    (X H W : ℕ) (hW : 0 < W) (hHX : H ≤ X)
    (hlarge : ∀ j ∈ J, ∀ p ∈ P j, W < p) (α : ℝ) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      (∑ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖ *
        ((d : ℝ) * shortExponentialIntegral (mrtTypicalCoefficient J P (mrtCompletePart F))
          (X / d + 1) (H / d + 1) (d * α) + X)) +
      2 * mrtCorrectionBound * X * H * (W : ℝ) ^ (-(1 / 4 : ℝ)) := by
  apply (mrt_correction_typical_tail_below_primes J P hP F hF hFb hF1
    X H W hW hHX hlarge α).trans
  apply add_le_add _ le_rfl
  apply sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (mrt_dilation_integral_quotient (mrtTypicalCoefficient J P (mrtCompletePart F))
      (mrtTypicalCoefficient_oneBounded J P _ (mrtCompletePart_oneBounded F hFb))
      d X H (mem_Icc.mp (mem_filter.mp hd).1).1 α) (norm_nonneg _)

lemma mrt_quotient_length_le_two {d A : ℕ} (hd : 0 < d) (hdA : d ≤ A) :
    ((A / d + 1 : ℕ) : ℝ) ≤ 2 * ((A : ℝ) / d) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (A : ℝ) / d :=
    (le_div_iff₀ hdr).mpr (by simpa only [one_mul] using (show (d : ℝ) ≤ A by exact_mod_cast hdA))
  have hdiv : ((A / d : ℕ) : ℝ) ≤ (A : ℝ) / d := Nat.cast_div_le
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

lemma mrt_small_correction_quotient_bound (F G : ℕ → ℂ)
    (hFb : OneBounded F) (hF1 : F 1 = 1) (X H W : ℕ)
    (hWH : W ≤ H) (hHX : H ≤ X) (α ε : ℝ) (hε : 0 ≤ ε)
    (hmean : ∀ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W),
      shortExponentialIntegral G (X / d + 1) (H / d + 1) (d * α) ≤
        ε * (X / d + 1 : ℕ) * (H / d + 1 : ℕ)) :
    (∑ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W), ‖mrtCorrection F d‖ *
      ((d : ℝ) * shortExponentialIntegral G (X / d + 1) (H / d + 1) (d * α) + X)) ≤
      mrtCorrectionBound * ((4 * ε * X * H) + (W : ℝ) * X) := by
  let S := (Icc 1 (X + H)).filter (fun d => d ≤ W)
  have hmass : (∑ d ∈ S, ‖mrtCorrection F d‖ / (d : ℝ)) ≤ mrtCorrectionBound := by
    simpa only [Nat.cast_one, Real.one_rpow, mul_one] using
      mrt_correction_tail_bound F hFb hF1 (W := 1) (by omega) S
        (fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1)
  have hsum : (∑ d ∈ S, ‖mrtCorrection F d‖ *
      ((d : ℝ) * shortExponentialIntegral G (X / d + 1) (H / d + 1) (d * α) + X)) ≤
      ((4 * ε * X * H) + (W : ℝ) * X) *
        (∑ d ∈ S, ‖mrtCorrection F d‖ / (d : ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hdI, hdW⟩ := mem_filter.mp hd
    have hd0 : 0 < d := (mem_Icc.mp hdI).1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have hdH : d ≤ H := hdW.trans hWH
    have hdX : d ≤ X := hdH.trans hHX
    have hx := mrt_quotient_length_le_two hd0 hdX
    have hh := mrt_quotient_length_le_two hd0 hdH
    have hprod : ε * (X / d + 1 : ℕ) * (H / d + 1 : ℕ) ≤
        ε * (2 * ((X : ℝ) / d)) * (2 * ((H : ℝ) / d)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hx hε
      · exact hh
      · positivity
      · positivity
    have hi : (d : ℝ) * shortExponentialIntegral G
        (X / d + 1) (H / d + 1) (d * α) ≤ (4 * ε * X * H) / d := by
      calc
        _ ≤ (d : ℝ) * (ε * (2 * ((X : ℝ) / d)) * (2 * ((H : ℝ) / d))) :=
          mul_le_mul_of_nonneg_left ((hmean d hd).trans hprod) hdr.le
        _ = _ := by field_simp; ring
    have he : (X : ℝ) ≤ ((W : ℝ) * X) / d := by
      apply (le_div_iff₀ hdr).mpr
      have hdWr : (d : ℝ) ≤ W := by exact_mod_cast hdW
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hdWr (Nat.cast_nonneg X)
    calc
      _ ≤ ‖mrtCorrection F d‖ * ((4 * ε * X * H) / d + ((W : ℝ) * X) / d) :=
        mul_le_mul_of_nonneg_left (add_le_add hi he) (norm_nonneg _)
      _ = _ := by ring
  apply hsum.trans
  calc
    _ ≤ ((4 * ε * X * H) + (W : ℝ) * X) * mrtCorrectionBound :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := mul_comm _ _

/-- A uniform divided-window estimate transfers to the original typical
coefficient with an absolute correction constant and explicit rounding loss. -/
theorem mrt_correction_typical_quotient_mean {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F) (hF1 : F 1 = 1)
    (X H W : ℕ) (hW : 0 < W) (hWH : W ≤ H) (hHX : H ≤ X)
    (hlarge : ∀ j ∈ J, ∀ p ∈ P j, W < p) (α ε : ℝ) (hε : 0 ≤ ε)
    (hmean : ∀ d ∈ (Icc 1 (X + H)).filter (fun d => d ≤ W),
      shortExponentialIntegral (mrtTypicalCoefficient J P (mrtCompletePart F))
        (X / d + 1) (H / d + 1) (d * α) ≤ ε * (X / d + 1 : ℕ) * (H / d + 1 : ℕ)) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α ≤
      mrtCorrectionBound * X * H *
        (4 * ε + (W : ℝ) / H + 2 * (W : ℝ) ^ (-(1 / 4 : ℝ))) := by
  have hs := mrt_small_correction_quotient_bound F
    (mrtTypicalCoefficient J P (mrtCompletePart F)) hFb hF1
    X H W hWH hHX α ε hε hmean
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast (hW.trans_le hWH).ne'
  calc
    _ ≤ _ := mrt_correction_typical_quotient_tail J P hP F hF hFb hF1
      X H W hW hHX hlarge α
    _ ≤ mrtCorrectionBound * ((4 * ε * X * H) + (W : ℝ) * X) +
        2 * mrtCorrectionBound * X * H * (W : ℝ) ^ (-(1 / 4 : ℝ)) :=
      add_le_add hs le_rfl
    _ = _ := by field_simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionParameters
namespace OAI

/-! Scalar budgets for the prime-power correction. The real parameter W
allows the published logarithmic cutoff, while the actual divisor cutoff
is the natural floor of W^5. -/

namespace TwoPointCorrelations

open scoped _root_.Classical


lemma mrt_correction_fifth_tail {W : ℝ} (hW : 0 ≤ W) :
    (W ^ (5 : ℕ)) ^ (-(1 / 4 : ℝ)) = W ^ (-(5 / 4 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
  norm_num

lemma mrt_correction_endpoint {W H : ℝ} (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H) :
    W ^ (5 : ℕ) / H ≤ W ^ (-(5 / 4 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 < H := (pow_pos hW0 250).trans_le hH
  apply (div_le_iff₀ hH0).mpr
  calc
    W ^ (5 : ℕ) = W ^ (-(5 / 4 : ℝ)) * W ^ (25 / 4 : ℝ) := by
      rw [← Real.rpow_add hW0]
      norm_num
    _ ≤ W ^ (-(5 / 4 : ℝ)) * W ^ (250 : ℕ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hW0.le _)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hW (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg hW0.le _)

lemma mrt_correction_cutoff_bounds {W : ℝ} (hW : 2 ≤ W) :
    1 ≤ mrtCorrectionCutoff W ∧
      W ^ (5 : ℕ) / 2 ≤ (mrtCorrectionCutoff W : ℝ) ∧
      (mrtCorrectionCutoff W : ℝ) ≤ W ^ (5 : ℕ) := by
  have hW1 : 1 ≤ W := by linarith
  have hpow : 2 ≤ W ^ (5 : ℕ) :=
    hW.trans (le_self_pow₀ hW1 (by norm_num : (5 : ℕ) ≠ 0))
  have hlt := Nat.lt_floor_add_one (W ^ (5 : ℕ))
  refine ⟨?_, ?_, Nat.floor_le (pow_nonneg (by linarith) _)⟩
  · exact (Nat.one_le_floor_iff _).mpr (by linarith)
  · change W ^ (5 : ℕ) / 2 ≤ (⌊W ^ (5 : ℕ)⌋₊ : ℝ)
    linarith

lemma mrt_correction_cutoff_tail {W : ℝ} (hW : 2 ≤ W) :
    (mrtCorrectionCutoff W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2 * W ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨_, hlo, _⟩ := mrt_correction_cutoff_bounds hW
  have hW0 : 0 < W := by linarith
  have hhalf : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have htwo : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  calc
    _ ≤ (W ^ (5 : ℕ) / 2) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by norm_num)
    _ = W ^ (-(5 / 4 : ℝ)) / (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.div_rpow (pow_nonneg hW0.le _) (by norm_num), mrt_correction_fifth_tail hW0.le]
    _ ≤ _ := by
      apply (div_le_iff₀ htwo).mpr
      nlinarith [Real.rpow_nonneg hW0.le (-(5 / 4 : ℝ))]

lemma mrt_correction_cutoff_scale {W : ℝ} {H : ℕ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) :
    0 < mrtCorrectionCutoff W ∧ mrtCorrectionCutoff W ≤ H ∧
      (mrtCorrectionCutoff W : ℝ) / H ≤ W ^ (-(5 / 4 : ℝ)) ∧
      (mrtCorrectionCutoff W : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 2 * W ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨hpos, _, hupper⟩ := mrt_correction_cutoff_bounds hW
  have hW1 : 1 ≤ W := by linarith
  have hpow : W ^ (5 : ℕ) ≤ W ^ (250 : ℕ) :=
    pow_le_pow_right₀ hW1 (by norm_num)
  have hH0 : (0 : ℝ) < H := (pow_pos (by linarith : 0 < W) 250).trans_le hH
  refine ⟨by omega, ?_, ?_, mrt_correction_cutoff_tail hW⟩
  · exact_mod_cast hupper.trans (hpow.trans hH)
  · exact (div_le_div_of_nonneg_right hupper hH0.le).trans (mrt_correction_endpoint hW1 hH)

lemma mrt_correction_quotient_length {W H : ℝ} {h d : ℕ}
    (hW : 0 < W) (hd : 0 < d) (hdW : (d : ℝ) ≤ W ^ (5 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    H / W ^ (7 : ℕ) ≤ (h / d + 1 : ℕ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hquot : (h : ℝ) / d < (h / d + 1 : ℕ) := by
    apply (div_lt_iff₀ hdr).mpr
    have ht : (h : ℝ) < (d : ℝ) * (h / d + 1 : ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ h hd
    simpa only [mul_comm] using ht
  calc
    H / W ^ (7 : ℕ) = (H / W ^ (2 : ℕ)) / W ^ (5 : ℕ) := by
      rw [div_div, ← pow_add]
    _ ≤ (h : ℝ) / W ^ (5 : ℕ) := div_le_div_of_nonneg_right hh (pow_nonneg hW.le _)
    _ ≤ (h : ℝ) / d := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdr hdW
    _ ≤ _ := hquot.le

lemma mrt_correction_quotient_power {W H : ℝ} {h d : ℕ}
    (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H)
    (hd : 0 < d) (hdW : (d : ℝ) ≤ W ^ (5 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    W ^ (243 : ℕ) ≤ (h / d + 1 : ℕ) := by
  have hW0 : 0 < W := by linarith
  calc
    W ^ (243 : ℕ) = W ^ (250 : ℕ) / W ^ (7 : ℕ) := by
      rw [show (250 : ℕ) = 243 + 7 by decide, pow_add]
      exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hW0.ne')).symm
    _ ≤ H / W ^ (7 : ℕ) := div_le_div_of_nonneg_right hH (pow_nonneg hW0.le _)
    _ ≤ _ := mrt_correction_quotient_length hW0 hd hdW hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcGlobalRate
namespace OAI

/-! Absorb the initial dyadic block and quotient rounding after the
square-root character estimate, retaining the published energy rate. -/
namespace TwoPointCorrelations

lemma major_arc_boundary_rate {W q V H K : ℝ}
    (hW : 1 ≤ W) (hq : 1 ≤ q) (hqW : q ≤ W)
    (hK : (2*K+1)/V ≤ (W^4)⁻¹) (hH : W^3 ≤ H) :
    2*Real.sqrt q*(1+Real.log q)*q*((2*K+1)/V)+Real.sqrt q*q/H ≤ 3/W := by
  have hW0 : 0 < W := by linarith
  have hq0 : 0 < q := by linarith
  have hH0 : 0 < H := (pow_pos hW0 3).trans_le hH
  have hroot : Real.sqrt q ≤ W :=
    (Real.sqrt_le_self_iff.mpr (Or.inr hq)).trans hqW
  have hlog : 1+Real.log q ≤ W := by
    linarith [Real.log_le_sub_one_of_pos hq0]
  have hlog0 : 0 ≤ 1+Real.log q := by linarith [Real.log_nonneg hq]
  have hfirst : 2*Real.sqrt q*(1+Real.log q)*q*((2*K+1)/V) ≤ 2/W := by
    calc
      _ ≤ 2*Real.sqrt q*(1+Real.log q)*q*(W^4)⁻¹ :=
        mul_le_mul_of_nonneg_left hK (by positivity)
      _ ≤ 2*W*W*W*(W^4)⁻¹ := by gcongr
      _ = _ := by field_simp
  have hsecond : Real.sqrt q*q/H ≤ 1/W := by
    apply (div_le_iff₀ hH0).mpr
    calc
      _ ≤ W*W := mul_le_mul hroot hqW hq0.le hW0.le
      _ ≤ (1/W)*H := by
        rw [div_mul_eq_mul_div,one_mul]
        apply (le_div_iff₀ hW0).mpr
        simpa only [pow_succ,pow_two,pow_zero,one_mul] using hH
  calc
    _ ≤ 2/W+1/W := add_le_add hfirst hsecond
    _ = _ := by ring

lemma major_arc_global_normalized {I C R W q V H K : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hW : 1 ≤ W) (hq : 1 ≤ q) (hqW : q ≤ W)
    (hV : 0 < V) (hK : (2*K+1)/V ≤ (W^4)⁻¹) (hH : W^3 ≤ H)
    (hi : I ≤ Real.sqrt q*((1+Real.log q)*
      (4*C*V*H*R+2*q*(2*K+1)*H)+q*V)) :
    I ≤ V*H*(4*C*(Real.sqrt W*(1+Real.log W))*R+3/W) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 < H := (pow_pos hW0 3).trans_le hH
  have hq0 : 0 < q := by linarith
  have hweight : Real.sqrt q*(1+Real.log q) ≤ Real.sqrt W*(1+Real.log W) := by
    apply mul_le_mul (Real.sqrt_le_sqrt hqW)
      (by linarith [Real.log_le_log hq0 hqW])
      (by linarith [Real.log_nonneg hq]) (Real.sqrt_nonneg W)
  have hmain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hweight (show 0 ≤ 4*C by positivity)) hR
  have herr := major_arc_boundary_rate hW hq hqW hK hH
  calc
    I ≤ Real.sqrt q*((1+Real.log q)*(4*C*V*H*R+2*q*(2*K+1)*H)+q*V) := hi
    _ = V*H*(4*C*(Real.sqrt q*(1+Real.log q))*R+
        (2*Real.sqrt q*(1+Real.log q)*q*((2*K+1)/V)+Real.sqrt q*q/H)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hmain herr) (mul_nonneg hV.le hH0.le)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Interval _root_.MeasureTheory
open _root_.Finset hiding sum_le_sum_of_injOn

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

open _root_.Real _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.Finset hiding sum_le_sum_of_injOn
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

open _root_.Finset hiding sum_le_sum_of_injOn
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandParameters
namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open _root_.Filter
open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical



lemma mrtBandLower_one (P Q : ℝ) (hP : 0 < P) : mrtBandLower P Q 1 = P := by
  simp [mrtBandLower, Real.exp_log hP]



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

open _root_.Finset hiding sum_le_sum_of_injOn
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

open _root_.Complex _root_.ArithmeticFunction
open _root_.Finset hiding sum_le_sum_of_injOn
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

open _root_.Filter
open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩







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

lemma major_arc_actual_prime_lower {P Q : ℝ} {J j p : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hLP : 1 < Real.log P)
    (hj : j ∈ Icc 1 J)
    (hp : p ∈ mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) : P < (p:ℝ) := by
  have hlo := mrt_band_lower_monotone P Q 1 j (by decide) (mem_Icc.mp hj).1 hP hPQ hLP
  rw [mrtBandLower_one P Q (by linarith)] at hlo
  have hb := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp
  exact hlo.trans_lt hb.1

lemma major_arc_actual_bands_avoid {P Q : ℝ} {J d : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hLP : 1 < Real.log P)
    (hd : 0 < d) (hdP : (d:ℝ) ≤ P) :
    mrtPrimeAvoids ((Icc 1 J).biUnion
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) d := by
  apply mrtPrimeAvoids_of_lt _ hd
  intro p hp
  obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
  exact_mod_cast hdP.trans_lt (major_arc_actual_prime_lower hP hPQ hLP hj hp)



lemma major_arc_complete_distance {F : ℕ → ℂ} {X H : ℕ} {M : ℝ}
    (hd : MRTDistanceLowerBound F X H M) :
    MRTDistanceLowerBound (mrtCompletePart F) X H M := by
  intro q hq hqmax χ t ht
  rw [halasz_complete_distance]
  exact hd q hq hqmax χ t ht

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcPerturbedGlobal
namespace OAI

/-! Major-arc perturbation for the literal typical coefficient. Very short
prefixes use boundedness; every longer prefix uses the proved character mean. -/
namespace TwoPointCorrelations

open _root_.Finset

theorem major_arc_typical_perturbed_global
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X V H K H₀ : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → V ≤ 2*X → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
      ∀ W : ℝ, 1 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) → W^2 ≤ P →
      W^5 ≤ (H:ℝ) → (2*(K:ℝ)+1)/(V:ℝ) ≤ (W^4)⁻¹ →
      ∀ q : ℕ, 0 < q → q ≤ V → (q:ℝ) ≤ W → (q:ℝ) ≤ mrtModulusCutoff X H₀ →
      (∀ d ∈ q.divisors, mrtPrimeAvoids ((Icc 1 J).biUnion
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) d) →
      (∀ h : ℕ, 1 ≤ h → h ≤ H → (H:ℝ)/W^2 ≤ h →
        ∀ d ∈ q.divisors, 4 ≤ h/d+1 ∧ h/d+1 ≤ K ∧
          W ≤ (h/d+1:ℕ) ∧ Q/(h/d+1:ℕ) ≤ W^7) →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M → MRTDistanceLowerBound F X H₀ M → ∀ r : ℤ, ∀ β : ℝ,
      |β| *(H:ℝ) ≤ 2 →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) V H ((r:ℝ)/q+β) ≤
      (1+4*Real.pi)*(V:ℝ)*H*
        (4*C*(Real.sqrt W*(1+Real.log W))*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+3/W) := by
  obtain ⟨C,hC,N₀,hrational⟩ := major_arc_typical_rational_global hprime hhigh
  refine ⟨C,hC,N₀,?_⟩
  intro X V H K H₀ hX hLX hV hKN hK hKX P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP hH hboundary q hq hqV hqW hqmax havoid hwindow
    F hF1 hFc hFb M hM hd r β hβ
  let R := Real.exp (-2*M/5)+
    Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  let ε := 4*C*(Real.sqrt W*(1+Real.log W))*R+3/W
  have hW0 : 0 < W := by linarith
  have hH0 : (0:ℝ) < H := (pow_pos hW0 5).trans_le hH
  have hV0 : (0:ℝ) < V := by exact_mod_cast hq.trans_le hqV
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlog : 0 ≤ 1+Real.log W := by linarith [Real.log_nonneg hW]
  have hmain : 0 ≤ 4*C*(Real.sqrt W*(1+Real.log W))*R := by positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hsmall : (V:ℝ)*((H:ℝ)/W^2) ≤ (V:ℝ)*H*ε := by
    have hsq : W ≤ W^2 := le_self_pow₀ hW (by decide)
    have hi : (W^2)⁻¹ ≤ W⁻¹ := inv_le_inv₀ (pow_pos hW0 2) hW0 |>.mpr hsq
    have he : W⁻¹ ≤ ε := by dsimp [ε]; rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr hW0]
    have hh := mul_le_mul_of_nonneg_left (hi.trans he) (Nat.cast_nonneg H)
    simpa only [div_eq_mul_inv,mul_assoc] using mul_le_mul_of_nonneg_left hh hV0.le
  have hp := major_arc_perturbation_cutoff_two _
    (mrtTypicalCoefficient_oneBounded (Icc 1 J)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F hFb)
    V H (by exact_mod_cast hH0) ((r:ℝ)/q) β ((H:ℝ)/W^2) ((V:ℝ)*H*ε)
    (by positivity) hsmall hβ ?_
  · convert (preTransparency := .instances) hp using 1
    dsimp [ε,R]
    ring
  intro h hh hhH hu
  have hp3 : W^3 ≤ (h:ℝ) := by
    apply le_trans _ hu
    apply (le_div_iff₀ (pow_pos hW0 2)).mpr
    simpa only [←pow_add] using hH
  have hqh : q ≤ h := by
    have ht : (q:ℝ) ≤ h := hqW.trans ((le_self_pow₀ hW (by decide : 3≠0)).trans hp3)
    exact_mod_cast ht
  have hr := hrational X V h K H₀ hX hLX hV hKN hK hKX P Q hP hPQ hLP hLQ
    hbudget hres hQK J hJ hbands W hW hWK hWR hWP q hq hqV hqh hqmax havoid
    (hwindow h hh hhH hu) F hF1 hFc hFb M hM hd r
  have hn := major_arc_global_normalized hC.le hR hW hq1 hqW hV0 hboundary hp3 hr
  have hhreal : (h:ℝ) ≤ H := by exact_mod_cast hhH
  calc
    _ ≤ (V:ℝ)*h*ε := hn
    _ ≤ _ := by gcongr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcCorrectedMean
namespace OAI

/-! Apply the character estimate to the completely multiplicative part
inside each small correction divisor. The original coefficient and original
pretentious distance return in the conclusion. -/
namespace TwoPointCorrelations

open _root_.Finset

theorem major_arc_corrected_typical_mean_oai
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X V H K H₀ : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → H ≤ V → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
      ∀ W : ℝ, 2 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) → W^5 ≤ P →
      W^250 ≤ (H:ℝ) →
      (∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
        V/d+1 ≤ 2*X ∧ (2*(K:ℝ)+1)/(V/d+1:ℕ) ≤ (W^4)⁻¹) →
      ∀ q : ℕ, 0 < q → (q:ℝ) ≤ W → (q:ℝ) ≤ mrtModulusCutoff X H₀ →
      (∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W → q ≤ V/d+1 ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ H/d+1 → ((H/d+1:ℕ):ℝ)/W^2 ≤ k →
          ∀ b ∈ q.divisors, 4 ≤ k/b+1 ∧ k/b+1 ≤ K ∧
            W ≤ (k/b+1:ℕ) ∧ Q/(k/b+1:ℕ) ≤ W^7) →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      ∀ M : ℝ, 0 ≤ M → MRTDistanceLowerBound F X H₀ M → ∀ r : ℤ, ∀ β : ℝ,
      |β| *(H:ℝ) ≤ 1 →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) V H ((r:ℝ)/q+β) ≤
      mrtCorrectionBound*(V:ℝ)*H*
        (4*(1+4*Real.pi)*(4*C*(Real.sqrt W*(1+Real.log W))*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+3/W)+
          5*W^(-5/4:ℝ)) := by
  obtain ⟨C,hC,N₀,hmajor⟩ := major_arc_typical_perturbed_global hprime hhigh
  refine ⟨C,hC,N₀,?_⟩
  intro X V H K H₀ hX hLX hHV hKN hK hKX P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP hH houter q hq hqW hqmax hwindow
    F hF1 hFm hFb M hM hd r β hβ
  have hCB : 0 < mrtCorrectionBound := Real.exp_pos _
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  obtain ⟨hD,hDH,hDover,hDtail⟩ := mrt_correction_cutoff_scale hW hH
  have hWP2 : W^2 ≤ P := (pow_le_pow_right₀ hW1 (by norm_num : (2:ℕ)≤5)).trans hWP
  let R := Real.exp (-2*M/5)+Real.sqrt
    (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  let ε := (1+4*Real.pi)*(4*C*(Real.sqrt W*(1+Real.log W))*R+3/W)
  have hlog : 0 ≤ 1+Real.log W := by linarith [Real.log_nonneg hW1]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hp : ∀ j ∈ Icc 1 J, ∀ p ∈ mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j),
      mrtCorrectionCutoff W < p := by
    intro j hj p hp
    have hlow := major_arc_actual_prime_lower hP hPQ (by linarith) hj hp
    exact_mod_cast (mrt_correction_cutoff_bounds hW).2.2.trans_lt (hWP.trans_lt hlow)
  have hav : ∀ b ∈ q.divisors, mrtPrimeAvoids ((Icc 1 J).biUnion
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) b := by
    intro b hb
    have hb0 : 0 < b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 hq
    have hbq : b ≤ q := Nat.le_of_dvd hq (Nat.mem_divisors.mp hb).1
    apply major_arc_actual_bands_avoid hP hPQ (by linarith) hb0
    exact (show (b:ℝ) ≤ q by exact_mod_cast hbq).trans (hqW.trans
      ((le_self_pow₀ hW1 (by decide : (5:ℕ)≠0)).trans hWP))
  have hm := mrt_correction_typical_quotient_mean (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
    (fun _ _ _ hp => mrtPrimeBand_prime hp) F hFm hFb hF1 V H (mrtCorrectionCutoff W)
    hD hDH hHV hp ((r:ℝ)/q+β) ε hε ?_
  · have ht : (mrtCorrectionCutoff W:ℝ)/H+
        2*(mrtCorrectionCutoff W:ℝ)^(-(1/4:ℝ)) ≤ 5*W^(-5/4:ℝ) := by linarith
    calc
      _ ≤ mrtCorrectionBound*(V:ℝ)*H*(4*ε+
          (mrtCorrectionCutoff W:ℝ)/H+2*(mrtCorrectionCutoff W:ℝ)^(-(1/4:ℝ))) := hm
      _ ≤ mrtCorrectionBound*(V:ℝ)*H*(4*ε+5*W^(-5/4:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [ht]
      _ = _ := by dsimp [ε,R]; ring
  intro d hdD
  obtain ⟨hdI,hdD⟩ := mem_filter.mp hdD
  have hd0 : 0 < d := (mem_Icc.mp hdI).1
  have hdW : (d:ℝ) ≤ W^5 :=
    (show (d:ℝ) ≤ mrtCorrectionCutoff W by exact_mod_cast hdD).trans
      (mrt_correction_cutoff_bounds hW).2.2
  have hdH : d ≤ H := hdD.trans hDH
  have hHp : W^5 ≤ ((H/d+1:ℕ):ℝ) := by
    have hb := mrt_correction_quotient_power hW1 hH hd0 hdW
      (show (H:ℝ)/W^2 ≤ H from div_le_self (Nat.cast_nonneg H) (one_le_pow₀ hW1))
    exact (pow_le_pow_right₀ hW1 (by norm_num : (5:ℕ)≤243)).trans hb
  have hβd : |(d:ℝ)*β| *((H/d+1:ℕ):ℝ) ≤ 2 := by
    have hlen := mrt_quotient_length_le_two hd0 hdH
    have hdr : (0:ℝ) < d := by exact_mod_cast hd0
    rw [abs_mul,abs_of_pos hdr]
    calc
      _ = |β| *((d:ℝ)*(H/d+1:ℕ)) := by ring
      _ ≤ |β| *(2*(H:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
        calc
          (d:ℝ)*(H/d+1:ℕ) ≤ (d:ℝ)*(2*((H:ℝ)/d)) :=
            mul_le_mul_of_nonneg_left hlen hdr.le
          _ = _ := by field_simp
      _ ≤ _ := by nlinarith
  have hFcomp1 : mrtCompletePart F 1=1 := fromPrimePowers_one _
  have hi := hmajor X (V/d+1) (H/d+1) K H₀ hX hLX (houter d hd0 hdD).1
    hKN hK hKX P Q hP hPQ hLP hLQ hbudget hres hQK J hJ hbands W hW1 hWK hWR hWP2
    hHp (houter d hd0 hdD).2 q hq (hwindow d hd0 hdD).1 hqW hqmax hav
    (hwindow d hd0 hdD).2 (mrtCompletePart F) hFcomp1
    (fun a b ha hb => mrtCompletePart_mul F ha hb) (mrtCompletePart_oneBounded F hFb)
    M hM (major_arc_complete_distance hd) (d*(r:ℤ)) ((d:ℝ)*β) hβd
  have hphase : (d:ℝ)*((r:ℝ)/q+β) = ((d*(r:ℤ):ℤ):ℝ)/q+(d:ℝ)*β := by
    push_cast
    ring
  rw [hphase]
  simpa only [ε,R,mul_assoc,mul_left_comm,mul_comm] using hi

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.major_arc_corrected_typical_mean_oai := @OAI.TwoPointCorrelations.major_arc_corrected_typical_mean_oai
