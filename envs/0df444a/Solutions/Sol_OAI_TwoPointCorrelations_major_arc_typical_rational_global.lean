-- Prove2me | solution 1 for OAI.TwoPointCorrelations.major_arc_typical_rational_global
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:24:06.947394+00:00
-- url     : https://prove2.me/submissions/bb6d70a4-84d7-472a-8af2-3f6ddf8a861d

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_short_mean_sharp

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial




namespace Finset


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






lemma OneBounded.twistByCharacter {q : ℕ} {f : ℕ → ℂ}
    (hf : OneBounded f) (χ : DirichletCharacter ℂ q) : OneBounded (TwoPointCorrelations.twistByCharacter f χ) := by
  intro n hn
  unfold TwoPointCorrelations.twistByCharacter
  rw [norm_mul]
  exact (mul_le_mul (hf n hn) (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
    (by norm_num)


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

/-- The inverse-value form of conjugation on a unit residue. -/
lemma character_conj_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) : conj (χ a) = χ a⁻¹ := by
  rw [show conj (χ a) = χ⁻¹ a from MulChar.star_apply' χ a, MulChar.inv_apply]
  obtain ⟨u, rfl⟩ := ha
  rw [Ring.inverse_unit, ZMod.inv_coe_unit]













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


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShortEndpoint
namespace OAI

/-! The finite endpoint cost when a divided outer cutoff exceeds the
range supported by the original distance hypothesis. -/
namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

lemma halasz_short_outer_endpoint (B : ℕ → ℂ) (hB : OneBounded B)
    (Y Z D H : ℕ) (hYZ : Y ≤ Z+D) (α : ℝ) :
    shortExponentialIntegral B Y H α ≤
      shortExponentialIntegral B Z H α+(D:ℝ)*H := by
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ n ∈ range (Z+D), ‖shortExponentialSum B H α n‖ :=
      sum_le_sum_of_subset_of_nonneg (range_mono hYZ) (fun _ _ _ => norm_nonneg _)
    _ = (∑ n ∈ range Z, ‖shortExponentialSum B H α n‖)+
        ∑ n ∈ range D, ‖shortExponentialSum B H α ((Z+n : ℕ) : ℝ)‖ :=
      sum_range_add _ _ _
    _ ≤ (∑ n ∈ range Z, ‖shortExponentialSum B H α n‖)+
        ∑ _n ∈ range D, (H:ℝ) :=
      add_le_add le_rfl (sum_le_sum (fun n _ => minor_arc_short_sum_trivial B hB H (Z+n) α))
    _ = _ := by simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterFourier
namespace OAI

/-! Finite multiplicative Fourier inversion on the unit residues. The
L1 coefficient bound follows from Parseval and Cauchy--Schwarz and requires
no primitive-character or Gauss-sum estimate. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical _root_.ComplexConjugate


lemma mrt_character_fourier_kernel {q : ℕ} [NeZero q] (b z : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, conj (χ b) * χ z) =
      if b = z then if IsUnit z then (q.totient : ℂ) else 0 else 0 := by
  by_cases hb : IsUnit b
  · simp_rw [character_conj_unit _ hb]
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb z]
    by_cases he : b = z
    · subst z
      simp [hb]
    · simp [he]
  · have hz (χ : DirichletCharacter ℂ q) : χ b = 0 := χ.map_nonunit hb
    simp only [hz, map_zero, zero_mul, sum_const_zero]
    by_cases he : b = z
    · subst z
      simp [hb]
    · simp [he]

theorem mrt_character_fourier_inversion {q : ℕ} [NeZero q]
    (A : ZMod q → ℂ) (z : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, mrtCharacterFourierCoefficient A χ * χ z) =
      if IsUnit z then A z else 0 := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have he (χ : DirichletCharacter ℂ q) : mrtCharacterFourierCoefficient A χ * χ z =
      (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, A b * (conj (χ b) * χ z) := by
    unfold mrtCharacterFourierCoefficient
    rw [mul_assoc, sum_mul]
    congr 1
    apply sum_congr rfl
    intro b _
    ring
  calc
    _ = (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, A b *
        ∑ χ : DirichletCharacter ℂ q, conj (χ b) * χ z := by
      simp_rw [he]
      rw [← mul_sum, sum_comm]
      simp only [mul_sum]
    _ = (q.totient : ℂ)⁻¹ *
        (A z * (if IsUnit z then (q.totient : ℂ) else 0)) := by
      simp only [mrt_character_fourier_kernel, mul_ite, mul_zero]
      rw [sum_eq_single z]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    _ = _ := by
      by_cases hz : IsUnit z <;> simp [hz, hφ, mul_comm]

lemma mrt_character_coefficient_conj {q : ℕ} [NeZero q]
    (A : ZMod q → ℂ) (χ : DirichletCharacter ℂ q) :
    conj (mrtCharacterFourierCoefficient A χ) =
      (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, conj (A b) * χ b := by
  simp only [mrtCharacterFourierCoefficient, map_mul, map_inv₀, map_sum,
    map_natCast, Complex.conj_conj]

theorem mrt_character_fourier_parseval {q : ℕ} [NeZero q] (A : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖mrtCharacterFourierCoefficient A χ‖ ^ 2) =
      (q.totient : ℝ)⁻¹ * ∑ b : ZMod q, if IsUnit b then ‖A b‖ ^ 2 else 0 := by
  have he (χ : DirichletCharacter ℂ q) :
      mrtCharacterFourierCoefficient A χ * conj (mrtCharacterFourierCoefficient A χ) =
      (q.totient : ℂ)⁻¹ * ∑ b : ZMod q,
        conj (A b) * (mrtCharacterFourierCoefficient A χ * χ b) := by
    rw [mrt_character_coefficient_conj]
    calc
      _ = (q.totient : ℂ)⁻¹ *
          (mrtCharacterFourierCoefficient A χ * ∑ b : ZMod q, conj (A b) * χ b) := by ring
      _ = _ := by
        rw [mul_sum]
        congr 1
        apply sum_congr rfl
        intro b _
        ring
  apply Complex.ofReal_injective
  push_cast
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
        mrtCharacterFourierCoefficient A χ * conj (mrtCharacterFourierCoefficient A χ) := by
      apply sum_congr rfl
      intro χ _
      exact (Complex.mul_conj' _).symm
    _ = (q.totient : ℂ)⁻¹ * ∑ b : ZMod q, conj (A b) *
        ∑ χ : DirichletCharacter ℂ q, mrtCharacterFourierCoefficient A χ * χ b := by
      simp_rw [he]
      rw [← mul_sum, sum_comm]
      simp only [mul_sum]
    _ = (q.totient : ℂ)⁻¹ * ∑ b : ZMod q,
        conj (A b) * (if IsUnit b then A b else 0) := by
      simp only [mrt_character_fourier_inversion]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro b _
      by_cases hb : IsUnit b
      · simpa only [hb, ite_true, Complex.ofReal_pow] using Complex.conj_mul' (A b)
      · simp [hb]

theorem mrt_character_fourier_l1 {q : ℕ} [NeZero q] (A : ZMod q → ℂ)
    (hA : ∀ b, ‖A b‖ ≤ 1) :
    (∑ χ : DirichletCharacter ℂ q, ‖mrtCharacterFourierCoefficient A χ‖) ≤
      Real.sqrt (q : ℝ) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset (DirichletCharacter ℂ q))
    (fun _ => (1 : ℝ)) (fun χ => ‖mrtCharacterFourierCoefficient A χ‖)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, hcard] at hc
  rw [mrt_character_fourier_parseval, ← mul_assoc, mul_inv_cancel₀ hφ.ne', one_mul] at hc
  have hm : (∑ b : ZMod q, if IsUnit b then ‖A b‖ ^ 2 else 0) ≤ (q : ℝ) := by
    calc
      _ ≤ ∑ _b : ZMod q, (1 : ℝ) := by
        apply sum_le_sum
        intro b _
        by_cases hb : IsUnit b
        · simp only [hb, ite_true]
          nlinarith [norm_nonneg (A b), hA b]
        · simp [hb]
      _ = _ := by simp [ZMod.card]
  have hs := hc.trans hm
  have hn : 0 ≤ ∑ χ : DirichletCharacter ℂ q, ‖mrtCharacterFourierCoefficient A χ‖ :=
    sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q), Real.sqrt_nonneg (q : ℝ)]


theorem mrt_additive_character_inversion (q : ℕ) [NeZero q] (r : ℤ) (z : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, mrtAdditiveCharacterCoefficient q r χ * χ z) =
      if IsUnit z then additiveCharacter ((r : ℝ) / q) z.val else 0 :=
  mrt_character_fourier_inversion _ z

theorem mrt_additive_character_l1 (q : ℕ) [NeZero q] (r : ℤ) :
    (∑ χ : DirichletCharacter ℂ q, ‖mrtAdditiveCharacterCoefficient q r χ‖) ≤
      Real.sqrt (q : ℝ) := by
  apply mrt_character_fourier_l1
  intro b
  exact (norm_additiveCharacter _ _).le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicPrefix
namespace OAI

/-! Finite halving of a prefix. The at most one omitted integer at each
halving step is absorbed in the dyadic allowance, without counting the
number of steps. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

theorem mrt_dyadic_prefix_bound (f : ℕ → ℝ) (X W : ℕ) (H ε : ℝ)
    (hW : 1 ≤ W) (hH : 0 ≤ H) (hε : 0 ≤ ε) (hbudget : 1 ≤ ε*W)
    (hpos : ∀ n, 0 ≤ f n) (hbound : ∀ n, f n ≤ H)
    (hdyadic : ∀ n : ℕ, W ≤ n → 2*n ≤ X →
      (∑ k ∈ Ico n (2*n), f k) ≤ ε*n*H) :
    (∑ n ∈ range X, f n) ≤ 2*ε*X*H+2*W*H := by
  have hprefix : ∀ m : ℕ, m ≤ X →
      (∑ n ∈ range m, f n) ≤ 2*ε*m*H+2*W*H := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmX
      by_cases hm : m < 2*W
      · have hmR : (m:ℝ) ≤ 2*W := by exact_mod_cast (show m ≤ 2*W by omega)
        calc
          _ ≤ ∑ _n ∈ range m, H := sum_le_sum (fun n _ => hbound n)
          _ = (m:ℝ)*H := by simp
          _ ≤ 2*W*H := mul_le_mul_of_nonneg_right hmR hH
          _ ≤ 2*ε*m*H+2*W*H := le_add_of_nonneg_left (by positivity)
      · let n := m/2
        have hnW : W ≤ n := by dsimp [n]; omega
        have hnlt : n < m := by dsimp [n]; omega
        have hnX : n ≤ X := (Nat.le_of_lt hnlt).trans hmX
        have hnm : 2*n ≤ m := by dsimp [n]; omega
        have hmn : m ≤ 2*n+1 := by dsimp [n]; omega
        have hi := ih n hnlt hnX
        have hd := hdyadic n hnW (hnm.trans hmX)
        have hs : (∑ k ∈ range m, f k) ≤
            (∑ k ∈ range n, f k)+(∑ k ∈ Ico n (2*n), f k)+H := by
          calc
            _ ≤ ∑ k ∈ range (2*n+1), f k :=
              sum_le_sum_of_subset_of_nonneg (range_mono hmn) (fun k _ _ => hpos k)
            _ = (∑ k ∈ range (2*n), f k)+f (2*n) := sum_range_succ _ _
            _ ≤ (∑ k ∈ range (2*n), f k)+H := add_le_add le_rfl (hbound _)
            _ = _ := by rw [sum_range_add_sum_Ico _ (by omega : n ≤ 2*n)]
        have hnWR : (W:ℝ) ≤ n := by exact_mod_cast hnW
        have hen : 1 ≤ ε*n := hbudget.trans (mul_le_mul_of_nonneg_left hnWR hε)
        have hmR : 2*(n:ℝ) ≤ m := by exact_mod_cast hnm
        have hgap : H ≤ ε*n*H := by simpa using mul_le_mul_of_nonneg_right hen hH
        calc
          _ ≤ (2*ε*n*H+2*W*H)+(ε*n*H)+H := hs.trans (by linarith)
          _ ≤ 4*ε*n*H+2*W*H := by linarith
          _ ≤ 2*ε*m*H+2*W*H := by
            have hh := mul_le_mul_of_nonneg_left hmR (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hε) hH)
            nlinarith
  exact hprefix X le_rfl

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

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical



@[simp] lemma halaszUnitCorrectionLocal_zero (F : ℕ → ℂ) (p : ℕ) :
    halaszUnitCorrectionLocal F p 0 = 1 := by simp [halaszUnitCorrectionLocal]









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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalFactors
namespace OAI

/-! Exact finite typical-factorization masks used by MRT.  The prime bands
are kept arbitrary here; scale and sieve bounds are separate analytic steps. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcResidues
namespace OAI

/-! Gcd reduction of a typical-set progression, including nonunit classes.
The removed gcd avoids the prime bands, so the typical mask is unchanged.
The resulting windows are literal character twists at the divided scale. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.ComplexConjugate

lemma major_arc_typical_dilation {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a * b) = F a * F b)
    {d : ℕ} (hd : 0 < d) (havoid : mrtPrimeAvoids (J.biUnion P) d)
    {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 0 < n) :
    mrtTypicalCoefficient J P F n * dilate d (naturalCharacter χ) n =
      F d * dilationSequence d (mrtTypicalCoefficient J P (twistByCharacter F χ)) n := by
  by_cases hdn : d ∣ n
  · have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
    have he : n = d * (n / d) := (Nat.mul_div_cancel' hdn).symm
    have ht := mrtTypical_mul_of_avoids J P hP havoid (n / d)
    simp only [dilate, dilationSequence, if_pos hdn, naturalCharacter]
    unfold mrtTypicalCoefficient twistByCharacter
    rw [he] at ⊢
    rw [Nat.mul_div_cancel_left _ hd, ht, hF d (n / d) hd hm]
    split_ifs <;> simp [mul_assoc]
  · simp [dilate, dilationSequence, hdn]




lemma major_arc_dilation_average (F : ℕ → ℂ) (hF : OneBounded F)
    (d X H : ℕ) (hd : 0 < d) :
    (∑ v ∈ range X, ‖shortExponentialSum (dilationSequence d F) H 0 v‖) ≤
      (d : ℝ) * shortExponentialIntegral F (X / d + 1) (H / d + 1) 0 + X := by
  calc
    _ ≤ ∑ v ∈ range X, (‖shortWindowSum F (H / d + 1) 0 (v / d)‖ + 1) := by
      apply sum_le_sum
      intro v _
      simpa using norm_shortExponentialSum_dilation_le F hF d H v hd 0
    _ = (∑ v ∈ range X, ‖shortWindowSum F (H / d + 1) 0 (v / d)‖) + X := by
      rw [sum_add_distrib]
      simp
    _ ≤ (d : ℝ) * (∑ m ∈ range (X / d + 1),
        ‖shortWindowSum F (H / d + 1) 0 m‖) + X :=
      add_le_add (quotient_sample_sum_le _ (fun _ => norm_nonneg _) d X hd) le_rfl
    _ = _ := by
      rw [shortExponentialIntegral_eq_sum]
      simp_rw [norm_shortExponentialSum_eq_window]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcGCD
namespace OAI

/-! Gcd strata of a rational additive phase. The unit character expansion
on the quotient is supported on exactly one divisor of the modulus. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma major_arc_reduced_unit_iff (q d n : ℕ) (hq : 0 < q)
    (hdq : d∣q) (hdn : d∣n) :
    IsUnit ((n/d:ℕ) : ZMod (q/d)) ↔ n.gcd q=d := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hquot : 0 < q/d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd
  let : NeZero (q/d) := ⟨hquot.ne'⟩
  rw [ZMod.isUnit_iff_coprime]
  constructor
  · intro hc
    have he : n.gcd q=d*((n/d).gcd (q/d)) := by
      conv_lhs => rw [←Nat.mul_div_cancel' hdn,←Nat.mul_div_cancel' hdq]
      exact Nat.gcd_mul_left d (n/d) (q/d)
    simpa only [hc.gcd_eq_one,mul_one] using he
  · intro he
    have hc := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right n hq)
    rwa [he] at hc

lemma major_arc_gcd_phase (q n : ℕ) (hq : 0 < q) (r : ℤ) :
    additiveCharacter ((r:ℝ)/((q/n.gcd q:ℕ):ℝ)) (n/n.gcd q) =
      additiveCharacter ((r:ℝ)/q) n := by
  have hd : 0 < n.gcd q := Nat.gcd_pos_of_pos_right n hq
  have hd0 : (n.gcd q:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hq0 : (q:ℝ)≠0 := by exact_mod_cast hq.ne'
  have hncast : ((n/n.gcd q:ℕ):ℝ)=(n:ℝ)/(n.gcd q:ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_left n q) hd0
  have hqcast : ((q/n.gcd q:ℕ):ℝ)=(q:ℝ)/(n.gcd q:ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_right n q) hd0
  unfold additiveCharacter
  rw [hncast,hqcast]
  congr 2
  field_simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcDivisorBounds
namespace OAI

/-! The divided-scale volume pays for the gcd sum. The main term costs
only sqrt(q)(1+log q), while endpoint rounding has an explicit q factor. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma major_arc_divisor_reciprocal (q : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, (d:ℝ)⁻¹) ≤ 1+Real.log q := by
  have hs : q.divisors ⊆ Icc 1 q := by
    intro d hd
    have hdq := (Nat.mem_divisors.mp hd).1
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hdq hq,Nat.le_of_dvd hq hdq⟩
  calc
    _  ≤  ∑ d ∈ Icc 1 q, (d:ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ = (harmonic q:ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    _  ≤  _ := harmonic_le_one_add_log q

lemma major_arc_divisor_weighted (q : ℕ) (hq : 0 < q) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∑ d ∈ q.divisors, Real.sqrt ((q/d:ℕ):ℝ)*(A/(d:ℝ)+B))  ≤
      Real.sqrt (q:ℝ)*((1+Real.log q)*A+(q:ℝ)*B) := by
  calc
    _  ≤  ∑ d ∈ q.divisors, Real.sqrt (q:ℝ)*(A/(d:ℝ)+B) := by
      apply sum_le_sum
      intro d _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.div_le_self q d
    _ = Real.sqrt (q:ℝ)*(A*(∑ d ∈ q.divisors,(d:ℝ)⁻¹)+(q.divisors.card:ℝ)*B) := by
      rw [mul_sum]
      simp only [div_eq_mul_inv,sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    _  ≤  _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply add_le_add
      · simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (major_arc_divisor_reciprocal q hq) hA
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self q) hB


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcRational
namespace OAI

/-! Resolving a rational additive phase into its residue classes before
the multiplicative character expansion. Only a factor equal to the modulus
is lost; no Gauss-sum estimate is needed for the application. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma major_arc_rational_character (q : ℕ) [NeZero q] (r : ℤ) (n : ℕ) :
    additiveCharacter ((r : ℝ) / q) n =
      ZMod.stdAddChar ((r : ZMod q) * (n : ZMod q)) := by
  rw [← Int.cast_natCast n, ← Int.cast_mul, ZMod.stdAddChar_coe]
  unfold additiveCharacter
  congr 1
  push_cast
  ring




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcDivisors
namespace OAI

/-! Resolving a rational phase on each gcd stratum. The coefficients are
finite unit-group Fourier coefficients, so their total mass is controlled
by the square root of the reduced modulus. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma major_arc_rational_val (q : ℕ) [NeZero q] (r : ℤ) (n : ℕ) :
    additiveCharacter ((r:ℝ)/q) (n:ZMod q).val = additiveCharacter ((r:ℝ)/q) n := by
  rw [major_arc_rational_character,major_arc_rational_character]
  simp

lemma major_arc_character_inversion_nat (q : ℕ) [NeZero q] (r : ℤ) (n : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, mrtAdditiveCharacterCoefficient q r χ*naturalCharacter χ n) =
      if IsUnit (n:ZMod q) then additiveCharacter ((r:ℝ)/q) n else 0 := by
  rw [show (∑ χ : DirichletCharacter ℂ q,
      mrtAdditiveCharacterCoefficient q r χ*naturalCharacter χ n) =
    ∑ χ : DirichletCharacter ℂ q, mrtAdditiveCharacterCoefficient q r χ*χ (n:ZMod q) by rfl]
  rw [mrt_additive_character_inversion,major_arc_rational_val]



lemma major_arc_divisor_term {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b)
    (q : ℕ) (hq : 0 < q) (r : ℤ) (d : {d : ℕ // d ∈ q.divisors})
    (havoid : mrtPrimeAvoids (J.biUnion P) d.val) (n : ℕ) (hn : 0 < n) :
    majorArcDivisorTerm J P F q hq r d n =
      if n.gcd q=d.val then
        mrtTypicalCoefficient J P F n*additiveCharacter ((r:ℝ)/q) n else 0 := by
  let : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  have hdq := (Nat.mem_divisors.mp d.property).1
  have hd : 0 < d.val := Nat.pos_of_dvd_of_pos hdq hq
  have he : majorArcDivisorTerm J P F q hq r d n =
      mrtTypicalCoefficient J P F n *
        ∑ χ : DirichletCharacter ℂ (q/d.val),
          mrtAdditiveCharacterCoefficient (q/d.val) r χ*dilate d.val (naturalCharacter χ) n := by
    unfold majorArcDivisorTerm
    rw [mul_sum,mul_sum]
    apply sum_congr rfl
    intro χ _
    have hh := major_arc_typical_dilation J P hP F hF hd havoid χ hn
    calc
      _ = mrtAdditiveCharacterCoefficient (q/d.val) r χ *
          (F d.val*dilationSequence d.val (mrtTypicalCoefficient J P (twistByCharacter F χ)) n) := by ring
      _ = _ := by rw [←hh]; ring
  rw [he]
  by_cases hdn : d.val∣n
  · simp only [dilate,hdn,ite_true]
    rw [major_arc_character_inversion_nat]
    by_cases hu : IsUnit ((n/d.val:ℕ):ZMod (q/d.val))
    · have hg := (major_arc_reduced_unit_iff q d.val n hq hdq hdn).mp hu
      rw [if_pos hu,if_pos hg]
      have hp := major_arc_gcd_phase q n hq r
      rw [hg] at hp
      rw [hp]
    · have hg : n.gcd q≠d.val := fun h => hu
        ((major_arc_reduced_unit_iff q d.val n hq hdq hdn).mpr h)
      rw [if_neg hu,if_neg hg,mul_zero]
  · simp only [dilate,hdn,ite_false,mul_zero,sum_const_zero]
    have hg : n.gcd q≠d.val := by
      intro hg
      exact hdn (hg ▸ Nat.gcd_dvd_left n q)
    rw [if_neg hg]

theorem major_arc_divisor_expansion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b)
    (q : ℕ) (hq : 0 < q) (r : ℤ)
    (havoid : ∀ d ∈ q.divisors, mrtPrimeAvoids (J.biUnion P) d)
    (n : ℕ) (hn : 0 < n) :
    mrtTypicalCoefficient J P F n*additiveCharacter ((r:ℝ)/q) n =
      ∑ d : {d : ℕ // d ∈ q.divisors}, majorArcDivisorTerm J P F q hq r d n := by
  simp_rw [major_arc_divisor_term J P hP F hF q hq r _ (havoid _ (Subtype.property _)) n hn]
  let dg : {d : ℕ // d ∈ q.divisors} := ⟨n.gcd q,Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n q,hq.ne'⟩⟩
  rw [sum_eq_single dg]
  · simp [dg]
  · intro d _ hd
    have hg : n.gcd q≠d.val := by
      intro hg
      apply hd
      exact Subtype.ext hg.symm
    rw [if_neg hg]
  · simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcRationalSharp
namespace OAI

/-! Rational short sums with the square-root character loss. The
reciprocal gcd volume is retained before summing the strata. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma major_arc_divisor_window {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (q : ℕ) (hq : 0 < q) (r : ℤ)
    (d : {d : ℕ // d ∈ q.divisors}) (v H : ℕ) :
    (∑ n ∈ Icc (v+1) (v+H), majorArcDivisorTerm J P F q hq r d n) =
      majorArcDivisorWindow J P F q hq r d v H := by
  let : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  unfold majorArcDivisorTerm majorArcDivisorWindow
  rw [←mul_sum,sum_comm]
  congr 1
  apply sum_congr rfl
  intro χ _
  rw [shortExponentialSum_at_nat]
  simp [additiveCharacter,mul_sum]

lemma major_arc_divisor_window_average {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    (q : ℕ) (hq : 0 < q) (r : ℤ) (d : {d : ℕ // d ∈ q.divisors}) (X H : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hshort : ∀ χ : DirichletCharacter ℂ (q/d.val),
      (d.val:ℝ)*shortExponentialIntegral (mrtTypicalCoefficient J P (twistByCharacter F χ))
        (X/d.val+1) (H/d.val+1) 0  ≤  A/(d.val:ℝ)) :
    (∑ v ∈ range X, ‖majorArcDivisorWindow J P F q hq r d v H‖)  ≤
      Real.sqrt ((q/d.val:ℕ):ℝ)*(A/(d.val:ℝ)+X) := by
  let : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  have hd : 0 < d.val := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 hq
  have hb : ∀ v : ℕ, ‖majorArcDivisorWindow J P F q hq r d v H‖  ≤
      ∑ χ : DirichletCharacter ℂ (q/d.val), ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖*
        ‖shortExponentialSum (dilationSequence d.val
          (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖ := by
    intro v
    unfold majorArcDivisorWindow
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hF d.val hd)).trans
    exact (norm_sum_le _ _).trans_eq (sum_congr rfl (fun χ _ => norm_mul _ _))
  calc
    _  ≤  ∑ v ∈ range X, ∑ χ : DirichletCharacter ℂ (q/d.val),
        ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖*
          ‖shortExponentialSum (dilationSequence d.val
            (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖ := sum_le_sum (fun v _ => hb v)
    _ = ∑ χ : DirichletCharacter ℂ (q/d.val), ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖*
        (∑ v ∈ range X, ‖shortExponentialSum (dilationSequence d.val
          (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖) := by
      rw [sum_comm]
      simp only [mul_sum]
    _  ≤  ∑ χ : DirichletCharacter ℂ (q/d.val),
        ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖*(A/(d.val:ℝ)+X) := by
      apply sum_le_sum
      intro χ _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (major_arc_dilation_average _
        (mrtTypicalCoefficient_oneBounded J P _ (hF.twistByCharacter χ)) d.val X H hd).trans
          (add_le_add (hshort χ) le_rfl)
    _ = (∑ χ : DirichletCharacter ℂ (q/d.val),
        ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖)*(A/(d.val:ℝ)+X) := (sum_mul _ _ _).symm
    _  ≤  _ := mul_le_mul_of_nonneg_right (mrt_additive_character_l1 (q/d.val) r) (by positivity)

theorem major_arc_typical_rational_sharp {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hFm : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) (hF : OneBounded F)
    (q : ℕ) (hq : 0 < q) (r : ℤ) (X H : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (havoid : ∀ d ∈ q.divisors, mrtPrimeAvoids (J.biUnion P) d)
    (hshort : ∀ d : {d : ℕ // d ∈ q.divisors}, ∀ χ : DirichletCharacter ℂ (q/d.val),
      (d.val:ℝ)*shortExponentialIntegral (mrtTypicalCoefficient J P (twistByCharacter F χ))
        (X/d.val+1) (H/d.val+1) 0  ≤  A/(d.val:ℝ)) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H ((r:ℝ)/q)  ≤
      Real.sqrt (q:ℝ)*((1+Real.log q)*A+(q:ℝ)*X) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hw (v : ℕ) : shortExponentialSum (mrtTypicalCoefficient J P F) H ((r:ℝ)/q) v =
      ∑ d : {d : ℕ // d ∈ q.divisors}, majorArcDivisorWindow J P F q hq r d v H := by
    rw [shortExponentialSum_at_nat]
    have he (n : ℕ) (hn : n ∈ Icc (v+1) (v+H)) :=
      major_arc_divisor_expansion J P hP F hFm q hq r havoid n
        (show 0 < n by have := (mem_Icc.mp hn).1; omega)
    calc
      _ = ∑ n∈Icc (v+1) (v+H), ∑ d : {d : ℕ // d∈q.divisors},
          majorArcDivisorTerm J P F q hq r d n := sum_congr rfl he
      _ = ∑ d : {d : ℕ // d∈q.divisors}, ∑ n∈Icc (v+1) (v+H),
          majorArcDivisorTerm J P F q hq r d n := sum_comm
      _ = _ := sum_congr rfl (fun d _ => major_arc_divisor_window J P F q hq r d v H)
  rw [shortExponentialIntegral_eq_sum]
  calc
    _  ≤  ∑ v ∈ range X, ∑ d : {d : ℕ // d ∈ q.divisors}, ‖majorArcDivisorWindow J P F q hq r d v H‖ := by
      apply sum_le_sum
      intro v _
      rw [hw]
      exact norm_sum_le _ _
    _ = ∑ d : {d : ℕ // d ∈ q.divisors}, ∑ v ∈ range X, ‖majorArcDivisorWindow J P F q hq r d v H‖ := sum_comm
    _  ≤  ∑ d : {d : ℕ // d ∈ q.divisors}, Real.sqrt ((q/d.val:ℕ):ℝ)*(A/(d.val:ℝ)+X) :=
      sum_le_sum (fun d _ => major_arc_divisor_window_average J P F hF q hq r d X H A hA (hshort d))
    _ = ∑ d ∈ q.divisors, Real.sqrt ((q/d:ℕ):ℝ)*(A/(d:ℝ)+X) := by
      exact Finset.sum_coe_sort q.divisors (fun d : ℕ => Real.sqrt ((q/d:ℕ):ℝ)*(A/(d:ℝ)+(X:ℝ)))
    _  ≤  _ := major_arc_divisor_weighted q hq A X hA (Nat.cast_nonneg X)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcReduction
namespace OAI

/-! The full major-arc reduction to the short means supplied by MRT's
Dirichlet-polynomial argument. All residues, divided scales, shorter lengths,
and rounding errors remain explicit. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma major_arc_character_distance (F : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    squaredDistance (twistByCharacter F χ) (mrtArchimedeanTwist t) N =
      squaredDistance F (characterTwist (conjugateCharacter χ) t) N := by
  unfold squaredDistance
  apply sum_congr rfl
  intro p _
  simp only [twistByCharacter, mrtArchimedeanTwist, characterTwist,
    conjugateCharacter_apply, map_mul, Complex.conj_conj, mul_assoc]

lemma MRTDistanceLowerBound.major_arc_character {F : ℕ → ℂ} {X H : ℕ} {M : ℝ}
    (hd : MRTDistanceLowerBound F X H M) (q : ℕ) (hq : 0 < q)
    (hqmax : (q : ℝ) ≤ mrtModulusCutoff X H)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : |t| ≤ (X : ℝ)) :
    M ≤ squaredDistance (twistByCharacter F χ) (mrtArchimedeanTwist t) X := by
  rw [major_arc_character_distance]
  exact hd q hq hqmax (conjugateCharacter χ) t ht


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcPerturbedSharp
namespace OAI

/-! Preserve the square-root modulus loss through partial summation.
The estimates for shorter intervals remain explicit. -/
namespace TwoPointCorrelations

open _root_.Finset


lemma major_arc_twist_complete {q : ℕ} (F : ℕ → ℂ)
    (hF : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b)
    (χ : DirichletCharacter ℂ q) :
    ∀ a b, 0 < a → 0 < b → twistByCharacter F χ (a*b)=twistByCharacter F χ a*twistByCharacter F χ b := by
  intro a b ha hb
  simp only [twistByCharacter,hF a b ha hb,Nat.cast_mul,map_mul]
  ring

lemma major_arc_divisor_distance {F : ℕ → ℂ} {X H : ℕ} {M : ℝ}
    (hd : MRTDistanceLowerBound F X H M) (q : ℕ) (hq : 0 < q)
    (hqmax : (q:ℝ) ≤ mrtModulusCutoff X H)
    (d : {d : ℕ // d ∈ q.divisors}) (χ : DirichletCharacter ℂ (q/d.val))
    (t : ℝ) (ht : |t| ≤ X) :
    M ≤ squaredDistance (twistByCharacter F χ) (mrtArchimedeanTwist t) X := by
  apply hd.major_arc_character (q/d.val) (major_arc_divisor_quotient_pos hq d) _ χ t ht
  exact (show ((q/d.val:ℕ):ℝ) ≤ q by exact_mod_cast Nat.div_le_self q d.val).trans hqmax

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




lemma mrt_quotient_length_le_two {d A : ℕ} (hd : 0 < d) (hdA : d ≤ A) :
    ((A / d + 1 : ℕ) : ℝ) ≤ 2 * ((A : ℝ) / d) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (A : ℝ) / d :=
    (le_div_iff₀ hdr).mpr (by simpa only [one_mul] using (show (d : ℝ) ≤ A by exact_mod_cast hdA))
  have hdiv : ((A / d : ℕ) : ℝ) ≤ (A : ℝ) / d := Nat.cast_div_le
  simp only [Nat.cast_add, Nat.cast_one]
  linarith



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShortL1
namespace OAI

/-! The typical-set error is linear in its density in the published L1
norm. No square root of the discarded density is introduced. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_short_integral_cells (F : ℕ → ℂ) (A N H : ℕ) (α : ℝ) :
    (∫ x in (A:ℝ)..(A+N:ℕ), ‖shortExponentialSum F H α x‖) =
      ∑ v ∈ range N, ‖shortExponentialSum F H α (A+v:ℕ)‖ := by
  symm
  calc
    _ = ∑ v ∈ range N, ∫ x in (A+v:ℕ)..(A+v+1:ℕ),
        ‖shortExponentialSum F H α x‖ := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (integral_shortExponentialSum_unit F H α (A+v)).symm
    _ = _ := by
      simpa only [Nat.add_zero, Nat.add_assoc] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => ((A+n:ℕ):ℝ)) (n := N)
          (fun v _ => by simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, add_assoc] using
            shortExponentialSum_unit_integrable F H α (A+v)))




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalGlobal
namespace OAI

/-! Sum the literal typical energy over dyadic origins. Keeping the
coefficient fixed is essential when it is later resolved into characters. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory

lemma halasz_short_dyadic_cells (B : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    (∑ k ∈ Ico n (2*n), ‖shortExponentialSum B H α k‖) =
      ∫ x in (n:ℝ)..(2*n), ‖shortExponentialSum B H α x‖ := by
  have he := halasz_short_integral_cells B n n H α
  rw [show n+n=2*n by omega] at he
  rw [show 2*(n:ℝ)=((2*n:ℕ):ℝ) by push_cast; ring,he]
  symm
  apply sum_bij (fun v : ℕ => fun _ => n+v)
  · intro v hv
    exact mem_Ico.mpr ⟨by omega,by have := mem_range.mp hv; omega⟩
  · intro v _ w _ h
    omega
  · intro k hk
    have := mem_Ico.mp hk
    exact ⟨k-n,mem_range.mpr (by omega),by omega⟩
  · intro _ _
    rfl



lemma halasz_sharp_log_error_comparison {L l : ℝ} (hL : 1 ≤ L)
    (hlo : L/2 ≤ l) (hhi : l ≤ L) :
    Real.log l/l^(1/80:ℝ) ≤ 2*(Real.log L/L^(1/80:ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hl0 : 0 < l := by linarith
  have hlog := Real.log_le_log hl0 hhi
  have hpow := Real.rpow_le_rpow_of_nonpos (show 0 < L/2 by positivity) hlo
    (show (-1/80:ℝ) ≤ 0 by norm_num)
  have htwo : (2:ℝ)^(1/80:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ 2 by norm_num) (show (1/80:ℝ) ≤ 1 by norm_num)
  have he : (2:ℝ)^(-1/80:ℝ)=((2:ℝ)^(1/80:ℝ))⁻¹ := by
    rw [show (-1/80:ℝ)=-(1/80:ℝ) by ring,Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  rw [Real.div_rpow hL0.le (by norm_num : (0:ℝ)≤2),he,div_inv_eq_mul] at hpow
  have hp : l^(-1/80:ℝ) ≤ 2*L^(-1/80:ℝ) := by
    exact hpow.trans (by nlinarith only
      [mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hL0.le (-1/80))])
  have hll : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlp : 0 ≤ l^(-1/80:ℝ) := Real.rpow_nonneg hl0.le _
  have hh := mul_le_mul hlog hp hlp hll
  have hinv (x : ℝ) (hx : 0 ≤ x) : x^(-1/80:ℝ)=(x^(1/80:ℝ))⁻¹ := by
    rw [show (-1/80:ℝ)=-(1/80:ℝ) by ring,Real.rpow_neg hx]
  rw [hinv l hl0.le,hinv L hL0.le] at hh
  convert (preTransparency := .instances) hh using 1 <;> ring

lemma halasz_sharp_root_error_comparison {L l : ℝ} (hL : 1 ≤ L)
    (hlo : L/2 ≤ l) (hhi : l ≤ L) :
    Real.sqrt (Real.log l/l^(1/80:ℝ)) ≤ 2*Real.sqrt (Real.log L/L^(1/80:ℝ)) := by
  have hδ : 0 ≤ Real.log L/L^(1/80:ℝ) := div_nonneg (Real.log_nonneg hL) (by positivity)
  apply (Real.sqrt_le_sqrt (halasz_sharp_log_error_comparison hL hlo hhi)).trans
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity,by nlinarith [Real.sq_sqrt hδ]⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDyadicScale
namespace OAI

/-! The dyadic blocks above the square-root cutoff stay inside the
original pretentious scale, with uniform logarithmic errors. -/

namespace TwoPointCorrelations

lemma halasz_dyadic_original_scale {X N : ℕ} (hX : 2 ≤ X)
    (hN : Real.sqrt (X:ℝ) ≤ N) :
    X ≤ N^3 ∧ Real.log (X:ℝ)/2 ≤ Real.log N := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0< X by omega)
  have hN0 : 0 < (N:ℝ) := (Real.sqrt_pos.2 hX0).trans_le hN
  have hn : 1 ≤ N := by exact_mod_cast (show 0< N by exact_mod_cast hN0)
  have hsq : (X:ℝ) ≤ (N:ℝ)^2 := by
    nlinarith [Real.sq_sqrt hX0.le,Real.sqrt_nonneg (X:ℝ)]
  have hsqN : X ≤ N^2 := by exact_mod_cast hsq
  refine ⟨hsqN.trans (pow_le_pow_right₀ hn (by norm_num : 2≤3)),?_⟩
  have hl := Real.log_le_log hX0 hsq
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalGlobalMean
namespace OAI

/-! The same literal typical coefficient is retained while summing all
large dyadic origins. The initial interval remains an explicit error. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

theorem halasz_typical_global_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X Y H K : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → Y ≤ 2*X → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K → 4 ≤ H → H ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → 2*n ≤ Y → ∀ k ∈ ({n,2*n}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ W : ℝ, 1 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) →
        W^2 ≤ P → W ≤ H → Q/(H:ℝ) ≤ W^7 →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y H 0 ≤
        C*(Y:ℝ)*H*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+2*(K:ℝ)*H := by
  obtain ⟨C,hC,hmean⟩ := halasz_typical_short_mean_sharp hprime hhigh
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hmean
  refine ⟨4*(C+1),by positivity,N₀,?_⟩
  intro X Y H K hX hLX hYX hKN hK hKX hH hHK P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP hWH hWQ F hF1 hFc hFb M hM hd
  let B := mrtTypicalCoefficient (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F
  let R := Real.exp (-2*M/5)+Real.sqrt
    (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  let ε := 2*(C+1)*R
  have hW0 : 0 < W := by linarith
  have hRinv : W⁻¹ ≤ R := by
    dsimp only [R]
    linarith [Real.exp_pos (-2*M/5),Real.sqrt_nonneg
      (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))]
  have hR : 0 ≤ R := (inv_pos.mpr hW0).le.trans hRinv
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hRe : R ≤ ε := by dsimp only [ε]; nlinarith
  have hbudget' : 1 ≤ ε*K := by
    have hh : 1 ≤ W⁻¹*(K:ℝ) := by
      have hh : 1 ≤ (K:ℝ)/W := (le_div_iff₀ hW0).mpr (by simpa using hWK)
      simpa only [div_eq_mul_inv,mul_comm] using hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hRinv.trans hRe) (Nat.cast_nonneg K))
  rw [shortExponentialIntegral_eq_sum]
  have hpref := mrt_dyadic_prefix_bound (fun n => ‖shortExponentialSum B H 0 n‖)
    Y K H ε hK (Nat.cast_nonneg H) hε hbudget' (fun _ => norm_nonneg _)
    (fun n => minor_arc_short_sum_trivial B (mrtTypicalCoefficient_oneBounded _ _ F hFb) H n 0) ?_
  · convert (preTransparency := .instances) hpref using 1
    dsimp [ε,R]
    ring
  intro n hn hny
  have hn0 : 0 < n := by omega
  have hnX : n ≤ X := by omega
  have hnxr : Real.sqrt (X:ℝ) ≤ n := hKX.trans (by exact_mod_cast hn)
  obtain ⟨hXN,hlogn⟩ := halasz_dyadic_original_scale hX hnxr
  have hm := hN₀ n (hKN.trans hn) P Q hP hPQ hLP hLQ hbudget hres J hJ
    (hbands n hn hny) X hnX hXN H hH (hHK.trans hn)
    (hQK.trans (by exact_mod_cast hn)) W hW hWR hWP hWH hWQ F hF1 hFc hFb M hM hd
  have hupper : Real.log (n:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnX)
  have herr := halasz_sharp_root_error_comparison hLX hlogn hupper
  have hcmp : C*(Real.exp (-2*M/5)+Real.sqrt
      (Real.log (Real.log n)/(Real.log n)^(1/80:ℝ))+W⁻¹) ≤ ε := by
    have hr : Real.exp (-2*M/5)+Real.sqrt
        (Real.log (Real.log n)/(Real.log n)^(1/80:ℝ))+W⁻¹ ≤ 2*R := by
      dsimp only [R]
      linarith [Real.exp_pos (-2*M/5),inv_pos.mpr hW0]
    exact (mul_le_mul_of_nonneg_left hr hC.le).trans (by dsimp [ε]; nlinarith)
  rw [halasz_short_dyadic_cells]
  have hs := hm.trans hcmp
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hhr : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  simpa only [B,mul_assoc] using (div_le_iff₀ (mul_pos hnr hhr)).mp hs

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalGlobalRange
namespace OAI

/-! Keep the actual outer volume when quotient rounding adds a bounded
number of origins beyond the range of the original distance hypothesis. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_short_truncate_outer (B : ℕ → ℂ) (hB : OneBounded B)
    (X Y H D : ℕ) (hY : Y ≤ X+D) (a b : ℝ) (ha : 0 ≤ a)
    (hmean : ∀ Z : ℕ, Z ≤ Y → Z ≤ X →
      shortExponentialIntegral B Z H 0 ≤ a*(Z:ℝ)+b) :
    shortExponentialIntegral B Y H 0 ≤ a*(Y:ℝ)+b+(D:ℝ)*H := by
  have hz : Y ≤ min Y X+D := by omega
  have hm := hmean (min Y X) (min_le_left _ _) (min_le_right _ _)
  have hv : ((min Y X:ℕ):ℝ) ≤ Y := by exact_mod_cast min_le_left Y X
  calc
    _ ≤ shortExponentialIntegral B (min Y X) H 0+(D:ℝ)*H :=
      halasz_short_outer_endpoint B hB Y (min Y X) D H hz 0
    _ ≤ (a*((min Y X:ℕ):ℝ)+b)+(D:ℝ)*H := add_le_add hm le_rfl
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hv ha]

theorem halasz_typical_global_range
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X Y H K D : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → Y ≤ 2*X+D → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K → 4 ≤ H → H ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
      ∀ W : ℝ, 1 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) →
        W^2 ≤ P → W ≤ H → Q/(H:ℝ) ≤ W^7 →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y H 0 ≤
        C*(Y:ℝ)*H*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+(2*(K:ℝ)+D)*H := by
  obtain ⟨C,hC,N₀,hmean⟩ := halasz_typical_global_mean hprime hhigh
  refine ⟨C,hC,N₀,?_⟩
  intro X Y H K D hX hLX hY hKN hK hKX hH hHK P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP hWH hWQ F hF1 hFc hFb M hM hd
  let R := Real.exp (-2*M/5)+
    Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let B := mrtTypicalCoefficient (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F
  have hs := halasz_short_truncate_outer B
    (mrtTypicalCoefficient_oneBounded (Icc 1 J)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F hFb) (2*X) Y H D hY
    (C*H*R) (2*(K:ℝ)*H) (by positivity) ?_
  · dsimp only [R,B] at hs
    convert (preTransparency := .instances) hs using 1
    ring
  intro Z _ hZX
  have hb : ∀ n : ℕ, K ≤ n → 2*n ≤ Z → ∀ k ∈ ({n,2*n}:Finset ℕ),
      200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
      ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k)) := by
    intro n hn hnZ k hk
    simp only [mem_insert,mem_singleton] at hk
    rcases hk with hk | hk
    · subst k
      exact hbands n hn (by omega)
    · subst k
      exact hbands (2*n) (by omega) (by omega)
  have hm := hmean X Z H K hX hLX hZX hKN hK hKX hH hHK
    P Q hP hPQ hLP hLQ hbudget hres hQK J hJ hb W hW hWK hWR hWP hWH hWQ
    F hF1 hFc hFb M hM hd
  convert (preTransparency := .instances) hm using 1
  dsimp [R]
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcGlobalMean
namespace OAI

/-! Global typical means for each character in the exact gcd decomposition.
The quotient volume is retained before the divisor sum is taken. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma major_arc_character_volume {C R I : ℝ} {V H K q d : ℕ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hdq : d ≤ q)
    (hdV : d ≤ V) (hdH : d ≤ H)
    (hmean : I ≤ C*(V/d+1:ℕ)*(H/d+1:ℕ)*R+
      (2*(K:ℝ)+1)*(H/d+1:ℕ)) :
    (d:ℝ)*I ≤ (4*C*V*H*R+2*(q:ℝ)*(2*(K:ℝ)+1)*H)/(d:ℝ) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hx := mrt_quotient_length_le_two hd hdV
  have hh := mrt_quotient_length_le_two hd hdH
  have hmain : C*(V/d+1:ℕ)*(H/d+1:ℕ)*R ≤
      C*(2*((V:ℝ)/d))*(2*((H:ℝ)/d))*R := by gcongr
  have herr : (2*(K:ℝ)+1)*(H/d+1:ℕ) ≤
      (2*(K:ℝ)+1)*(2*((H:ℝ)/d)) := by gcongr
  have hq : (d:ℝ) ≤ q := by exact_mod_cast hdq
  calc
    _ ≤ (d:ℝ)*(C*(2*((V:ℝ)/d))*(2*((H:ℝ)/d))*R+
        (2*(K:ℝ)+1)*(2*((H:ℝ)/d))) :=
      mul_le_mul_of_nonneg_left (hmean.trans (add_le_add hmain herr)) hdr.le
    _ = (4*C*V*H*R+2*(d:ℝ)*(2*(K:ℝ)+1)*H)/(d:ℝ) := by field_simp; ring
    _ ≤ _ := by gcongr

theorem major_arc_typical_rational_global_oai
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
      ∀ q : ℕ, 0 < q → q ≤ V → q ≤ H → (q:ℝ) ≤ mrtModulusCutoff X H₀ →
      (∀ d ∈ q.divisors, mrtPrimeAvoids ((Icc 1 J).biUnion
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) d) →
      (∀ d ∈ q.divisors, 4 ≤ H/d+1 ∧ H/d+1 ≤ K ∧
        W ≤ (H/d+1:ℕ) ∧ Q/(H/d+1:ℕ) ≤ W^7) →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M → MRTDistanceLowerBound F X H₀ M → ∀ r : ℤ,
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) V H ((r:ℝ)/q) ≤
      Real.sqrt (q:ℝ)*((1+Real.log q)*
        (4*C*V*H*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+
          2*(q:ℝ)*(2*(K:ℝ)+1)*H)+(q:ℝ)*V) := by
  obtain ⟨C,hC,N₀,hglobal⟩ := halasz_typical_global_range hprime hhigh
  refine ⟨C,hC,N₀,?_⟩
  intro X V H K H₀ hX hLX hV hKN hK hKX P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP q hq hqV hqH hqmax havoid hwindow F hF1 hFc hFb M hM hd r
  let R := Real.exp (-2*M/5)+
    Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply major_arc_typical_rational_sharp _ _
    (fun j _ p hp => mrtPrimeBand_prime hp) F hFc hFb q hq r V H
    (4*C*V*H*R+2*(q:ℝ)*(2*(K:ℝ)+1)*H) (by positivity) havoid
  intro d χ
  have hd0 : 0 < d.val := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 hq
  have hdq : d.val ≤ q := Nat.le_of_dvd hq (Nat.mem_divisors.mp d.property).1
  have hwin := hwindow d.val d.property
  have hY : V/d.val+1 ≤ 2*X+1 := (Nat.add_le_add_right (Nat.div_le_self V d.val) 1).trans
    (Nat.add_le_add_right hV 1)
  have hχ1 : twistByCharacter F χ 1=1 := by simp [twistByCharacter,hF1]
  have hm := hglobal X (V/d.val+1) (H/d.val+1) K 1 hX hLX hY hKN hK hKX
    hwin.1 hwin.2.1 P Q hP hPQ hLP hLQ hbudget hres hQK J hJ hbands
    W hW hWK hWR hWP hwin.2.2.1 hwin.2.2.2
    (twistByCharacter F χ) hχ1 (major_arc_twist_complete F hFc χ) (hFb.twistByCharacter χ) M hM
    (fun t ht => major_arc_divisor_distance hd q hq hqmax d χ t ht)
  apply major_arc_character_volume hC.le hR hd0 hdq (hdq.trans hqV) (hdq.trans hqH)
  simpa only [R,Nat.cast_one] using hm

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.major_arc_typical_rational_global_oai := @OAI.TwoPointCorrelations.major_arc_typical_rational_global_oai
