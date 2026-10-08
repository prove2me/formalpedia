-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_short_exponential_of_prime_estimates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:43:08.457983+00:00
-- url     : https://prove2.me/submissions/ba4ed920-b4dd-4a1c-83c1-d8e890eea22a

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_actual_band_interval_density
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_typical_actual_working_mean

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShortBoundedLength
namespace OAI

/-! The bounded short-length cases are absorbed by the positive
logarithmic term of the published error. -/

namespace TwoPointCorrelations

lemma halasz_loglog_ten_pos : 0 < Real.log (Real.log (10:ℝ)) := by
  apply Real.log_pos
  have hh := Real.log_lt_log (Real.exp_pos 1)
    (show Real.exp 1 < (10:ℝ) by linarith [Real.exp_one_lt_three])
  simpa only [Real.log_exp] using hh

lemma halasz_bounded_length_ratio {B : ℝ} (hB : 10 ≤ B) {H : ℕ}
    (hH : 10 ≤ H) (hHB : (H:ℝ) ≤ B) :
    1 ≤ (Real.log B/Real.log (Real.log (10:ℝ)))*
      (Real.log (Real.log (H:ℝ))/Real.log H) := by
  have hHr : (10:ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : 0 < (H:ℝ) := by linarith
  have hB0 : 0 < B := by linarith
  have hlH : 0 < Real.log (H:ℝ) := Real.log_pos (by linarith)
  have hlB : 0 < Real.log B := Real.log_pos (by linarith)
  have hc := halasz_loglog_ten_pos
  have hLH : Real.log (10:ℝ) ≤ Real.log (H:ℝ) := Real.log_le_log (by norm_num) hHr
  have hLL : Real.log (Real.log (10:ℝ)) ≤ Real.log (Real.log (H:ℝ)) :=
    Real.log_le_log (Real.log_pos (by norm_num)) hLH
  have hlogHB : Real.log (H:ℝ) ≤ Real.log B := Real.log_le_log hH0 hHB
  have hr : Real.log (Real.log (10:ℝ))/Real.log B ≤
      Real.log (Real.log (H:ℝ))/Real.log H :=
    (div_le_div_of_nonneg_left hc.le hlH hlogHB).trans
      (div_le_div_of_nonneg_right hLL hlH.le)
  have hh := mul_le_mul_of_nonneg_left hr (div_pos hlB hc).le
  have he : (Real.log B/Real.log (Real.log (10:ℝ)))*
      (Real.log (Real.log (10:ℝ))/Real.log B) = 1 := by field_simp
  rwa [he] at hh


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszShortNormalization
namespace OAI

/-! The allowed zero multiplicative function causes no normalization
restriction in the short-sum estimates. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

lemma Multiplicative.one_zero_or_one {F : ℕ → ℂ} (hF : Multiplicative F) :
    F 1 = 0 ∨ F 1 = 1 := by
  apply eq_zero_or_one_of_sq_eq_self
  simpa only [pow_two,one_mul] using
    (hF 1 1 Nat.one_pos Nat.one_pos (by decide)).symm

lemma Multiplicative.zero_of_one_zero {F : ℕ → ℂ} (hF : Multiplicative F)
    (hF1 : F 1 = 0) {n : ℕ} (hn : 0 < n) : F n = 0 := by
  have hh := hF 1 n Nat.one_pos hn (Nat.coprime_one_left n)
  simpa only [one_mul,hF1,zero_mul] using hh

lemma shortExponentialSum_of_one_zero {F : ℕ → ℂ} (hF : Multiplicative F)
    (hF1 : F 1 = 0) (H : ℕ) (α x : ℝ) :
    shortExponentialSum F H α x = 0 := by
  unfold shortExponentialSum
  apply sum_eq_zero
  intro n hn
  have hp : 0 < n := by have hh := (mem_Icc.mp hn).1; omega
  rw [hF.zero_of_one_zero hF1 hp,zero_mul]

lemma shortExponentialIntegral_of_one_zero {F : ℕ → ℂ} (hF : Multiplicative F)
    (hF1 : F 1 = 0) (X H : ℕ) (α : ℝ) :
    shortExponentialIntegral F X H α = 0 := by
  unfold shortExponentialIntegral
  simp only [shortExponentialSum_of_one_zero hF hF1,norm_zero,
    intervalIntegral.integral_zero]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortSubdivision
namespace OAI

/-! Subdivision into fixed short lengths, retaining the additive
frequency and allowing all shifted origins in one enlarged prefix. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma mrt_short_sum_append (F : ℕ → ℂ) (a b v : ℕ) (α : ℝ) :
    shortExponentialSum F (a+b) α v =
      shortExponentialSum F a α v + shortExponentialSum F b α (v+a:ℕ) := by
  simp only [shortExponentialSum_at_nat, sum_Icc_shift]
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [Nat.add_assoc]

lemma mrt_short_sum_blocks (F : ℕ → ℂ) (h K v : ℕ) (α : ℝ) :
    shortExponentialSum F (K*h) α v =
      ∑ j ∈ range K, shortExponentialSum F h α (v+j*h:ℕ) := by
  induction K with
  | zero =>
    simp only [zero_mul, shortExponentialSum_at_nat, sum_Icc_shift, sum_range_zero]
  | succ K ih =>
    rw [show (K+1)*h = K*h+h by ring, mrt_short_sum_append, ih, sum_range_succ]

lemma mrt_short_subdivision_pointwise (F : ℕ → ℂ) (hF : OneBounded F)
    (H h v : ℕ) (hh : 0 < h) (α : ℝ) :
    ‖shortExponentialSum F H α v‖ ≤
      (∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(h:ℝ) := by
  have he : H = (H/h)*h+H%h := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod H h).symm
  have hs := mrt_short_sum_append F ((H/h)*h) (H%h) v α
  rw [← he] at hs
  have hsum : ‖∑ j ∈ range (H/h), shortExponentialSum F h α (v+j*h:ℕ)‖ ≤
      ∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖ :=
    norm_sum_le _ _
  have hrest₀ : ‖shortExponentialSum F (H%h) α (v+(H/h)*h:ℕ)‖ ≤ (H%h:ℕ) :=
    minor_arc_short_sum_trivial F hF (H%h) (v+(H/h)*h) α
  have hrest : ‖shortExponentialSum F (H%h) α (v+(H/h)*h:ℕ)‖ ≤ (h:ℝ) :=
    hrest₀.trans (by exact_mod_cast (Nat.mod_lt H hh).le)
  rw [hs, mrt_short_sum_blocks]
  exact (norm_add_le _ _).trans (add_le_add hsum hrest)


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortSubdivisionSharp
namespace OAI

/-! Subdivision with the exact common outer cutoff.  The last complete
block starts no later than H-h, so its short window stays below X+H. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_subdivision_shift_le {H h j : ℕ} (hj : j ∈ range (H/h)) :
    j*h ≤ H-h := by
  have hs : (j+1)*h ≤ H :=
    (Nat.mul_le_mul_right h (Nat.succ_le_of_lt (mem_range.mp hj))).trans
      (Nat.div_mul_le_self H h)
  rw [Nat.add_mul,one_mul] at hs
  omega

theorem mrt_short_integral_subdivision_sharp (F : ℕ → ℂ) (hF : OneBounded F)
    (X H h : ℕ) (hh : 0 < h) (hhH : h ≤ H) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      (H/h:ℕ)*shortExponentialIntegral F (X+H-h) h α+(X:ℝ)*h := by
  have hshift (j : ℕ) (hj : j ∈ range (H/h)) :
      (∑ v ∈ range X, ‖shortExponentialSum F h α (v+j*h:ℕ)‖) ≤
        ∑ v ∈ range (X+H-h), ‖shortExponentialSum F h α v‖ := by
    have hle := mrt_subdivision_shift_le hj
    have hinj : Set.InjOn (fun v : ℕ => v+j*h) (range X) := by
      intro v _ w _ hvw
      exact Nat.add_right_cancel hvw
    calc
      _ = ∑ v ∈ (range X).image (fun v => v+j*h), ‖shortExponentialSum F h α v‖ := by
        rw [sum_image hinj]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro v hv
          obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
          exact mem_range.mpr (by have hw' := mem_range.mp hw; omega)
        · intro v _ _
          exact norm_nonneg _
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X,
        ((∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(h:ℝ)) :=
      sum_le_sum (fun v _ => mrt_short_subdivision_pointwise F hF H h v hh α)
    _ = (∑ j ∈ range (H/h), ∑ v ∈ range X,
        ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(X:ℝ)*h := by
      rw [sum_add_distrib,sum_comm]
      simp
    _ ≤ (∑ _j ∈ range (H/h), ∑ v ∈ range (X+H-h),
        ‖shortExponentialSum F h α v‖)+(X:ℝ)*h :=
      add_le_add (sum_le_sum hshift) le_rfl
    _ = _ := by simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortTrivialCases
namespace OAI

/-! Uniform absorption of the bounded outer scales and small values of
the common arc parameter in the exact published short-interval error. -/

namespace TwoPointCorrelations

lemma mrt_allowed_short_log {H : ℕ} (hH : 10 ≤ H) :
    1 ≤ Real.log (H:ℝ) := by
  have hHr : (10:ℝ) ≤ H := by exact_mod_cast hH
  have hh := Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ (H:ℝ) by linarith [Real.exp_one_lt_three])
  simpa only [Real.log_exp] using hh

lemma mrt_large_parameter_logs {L M : ℝ} {H : ℕ} (hH : 10≤ H)
    (hlarge : Real.exp 5 ≤ majorArcParameter L H M) :
    1 ≤ Real.log (H:ℝ) ∧ 1 ≤ Real.log (Real.log (H:ℝ)) := by
  have hLH := mrt_allowed_short_log hH
  have hp : (Real.exp 1)^5 ≤ (Real.log (H:ℝ))^5 := by
    calc
      _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ majorArcParameter L H M := hlarge
      _ ≤ _ := min_le_left _ _
  have he : Real.exp 1 ≤ Real.log (H:ℝ) :=
    (pow_le_pow_iff_left₀ (Real.exp_pos 1).le (by linarith) (by decide : 5≠0)).mp hp
  refine ⟨hLH,?_⟩
  have hh := Real.log_le_log (Real.exp_pos 1) he
  simpa only [Real.log_exp] using hh

lemma mrt_short_error_nonneg {X H : ℕ} (hH : 10 ≤ H) (hHX : H ≤ X) :
    0 ≤ mrtShortError X H := by
  have hLH := mrt_allowed_short_log hH
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  unfold mrtShortError
  exact add_nonneg
    (div_nonneg (Real.log_nonneg hLH) (by linarith))
    (Real.rpow_nonneg (Real.log_nonneg hX1) _)

/-- A bounded arc parameter forces either a bounded short length or a
bounded exponential-distance parameter. -/
lemma mrt_small_arc_parameter {X H : ℕ} {B M : ℝ}
    (hB : 2 ≤ B) (hH : 10 ≤ H) (hHX : H ≤ X)
    (hsmall : majorArcParameter (Real.log (X:ℝ)) H M ≤ B) :
    (H:ℝ) ≤ Real.exp (B^(125:ℕ)) ∨ Real.exp (M/3) ≤ B := by
  have hLH := mrt_allowed_short_log hH
  have hLX := mrt_allowed_short_log (hH.trans hHX)
  have hHp : (0:ℝ)< H := by exact_mod_cast (show 0< H by omega)
  have hB1 : 1 ≤ B := by linarith
  have hconvert (hlog : Real.log (H:ℝ) ≤ B^(125:ℕ)) :
      (H:ℝ) ≤ Real.exp (B^(125:ℕ)) := by
    calc
      _ = Real.exp (Real.log (H:ℝ)) := (Real.exp_log hHp).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  simp only [majorArcParameter,min_le_iff] at hsmall
  rcases hsmall with hh | hx | hm
  · left
    apply hconvert
    exact (le_self_pow₀ hLH (by decide : 5 ≠ 0)).trans
      (hh.trans (le_self_pow₀ hB1 (by decide : 125 ≠ 0)))
  · left
    have hp : Real.log (X:ℝ) ≤ B^(125:ℕ) := by
      calc
        _ = ((Real.log (X:ℝ))^(1/125:ℝ))^(125:ℕ) := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0≤ Real.log (X:ℝ))]
          norm_num
        _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hx 125
    apply hconvert
    exact (Real.log_le_log hHp (by exact_mod_cast hHX)).trans hp
  · exact Or.inr hm

lemma mrt_small_exponential_parameter {B M : ℝ} (hB : 2 ≤ B)
    (hM : Real.exp (M/3) ≤ B) :
    1 ≤ B*Real.exp (-M/20) := by
  have hB0 : 0< B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hm := Real.log_le_log (Real.exp_pos (M/3)) hM
  rw [Real.log_exp] at hm
  have he : Real.exp (-Real.log B) ≤ Real.exp (-M/20) :=
    Real.exp_le_exp.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left he hB0.le
  rw [Real.exp_neg,Real.exp_log hB0,mul_inv_cancel₀ hB0.ne'] at hh
  exact hh

/-- No lower-distance assumption is needed in any bounded-scale case.
The constant is independent of the original function and frequency. -/
theorem mrt_short_trivial_absorption (B₀ : ℝ) (X₀ : ℕ) :
    ∃ C : ℝ, 0< C ∧ ∀ X H : ℕ, 10≤ H → H≤ X → ∀ M : ℝ,
      (majorArcParameter (Real.log (X:ℝ)) H M ≤ B₀ ∨ X≤ X₀) →
      1 ≤ C*(Real.exp (-M/20)+mrtShortError X H) := by
  let B := max 2 B₀
  let Z := max 10 (max (Real.exp (B^(125:ℕ))) (X₀:ℝ))
  let K := Real.log Z/Real.log (Real.log (10:ℝ))
  have hB : 2≤ B := le_max_left _ _
  have hZ : 10≤ Z := le_max_left _ _
  have hK : 0≤ K := div_nonneg
    (Real.log_nonneg (by linarith)) halasz_loglog_ten_pos.le
  refine ⟨K+B+1,by positivity,?_⟩
  intro X H hH hHX M hcase
  have hδ := mrt_short_error_nonneg hH hHX
  have hR : 0 ≤ Real.exp (-M/20)+mrtShortError X H := by positivity
  have hbound (hHZ : (H:ℝ)≤ Z) :
      1 ≤ (K+B+1)*(Real.exp (-M/20)+mrtShortError X H) := by
    have hh := halasz_bounded_length_ratio hZ hH hHZ
    have hr : Real.log (Real.log (H:ℝ))/Real.log H ≤
        Real.exp (-M/20)+mrtShortError X H := by
      unfold mrtShortError
      linarith [Real.exp_pos (-M/20),
        Real.rpow_nonneg (Real.log_nonneg
          (show (1:ℝ)≤ X by exact_mod_cast (show 1≤ X by omega))) (-1/700:ℝ)]
    calc
      _ ≤ K*(Real.log (Real.log (H:ℝ))/Real.log H) := hh
      _ ≤ K*(Real.exp (-M/20)+mrtShortError X H) := mul_le_mul_of_nonneg_left hr hK
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hR
  rcases hcase with hsmall | hX
  · rcases mrt_small_arc_parameter hB hH hHX
      (hsmall.trans (le_max_right _ _)) with hlength | hexp
    · apply hbound
      exact hlength.trans ((le_max_left _ _).trans (le_max_right _ _))
    · have hh := mrt_small_exponential_parameter hB hexp
      calc
        _ ≤ B*Real.exp (-M/20) := hh
        _ ≤ B*(Real.exp (-M/20)+mrtShortError X H) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hR
  · apply hbound
    have hHXr : (H:ℝ)≤ X₀ := by exact_mod_cast hHX.trans hX
    exact hHXr.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem mrt_short_trivial_cases (B₀ : ℝ) (X₀ : ℕ) :
    ∃ C : ℝ, 0< C ∧ ∀ X H : ℕ, 10≤ H → H≤ X →
      ∀ F : ℕ → ℂ, OneBounded F → ∀ M : ℝ,
      (majorArcParameter (Real.log (X:ℝ)) H M ≤ B₀ ∨ X≤ X₀) →
      ∀ α : ℝ, shortExponentialIntegral F X H α ≤
        C*(H:ℝ)*X*(Real.exp (-M/20)+mrtShortError X H) := by
  obtain ⟨C,hC,hbound⟩ := mrt_short_trivial_absorption B₀ X₀
  refine ⟨C,hC,?_⟩
  intro X H hH hHX F hF M hcase α
  have hh := mul_le_mul_of_nonneg_left (hbound X H hH hHX M hcase)
    (show 0≤(X:ℝ)*H by positivity)
  calc
    _ ≤ (X:ℝ)*H := minor_arc_short_integral_trivial F hF X H α
    _ ≤ _ := by convert (preTransparency := .instances) hh using 1 <;> ring

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

lemma mrt_working_length_upper {H : ℕ} {W : ℝ} :
    mrtWorkingLength H W ≤ H := by
  unfold mrtWorkingLength
  split_ifs with h
  · exact le_rfl
  · have hh : (mrtWorkingCap W : ℝ) ≤ H :=
      (mrt_working_cap_upper W).trans
        ((Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg W])).trans (le_of_not_ge h))
    exact_mod_cast hh

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

theorem mrt_working_cap_log :
    ∀ᶠ W : ℝ in atTop, Real.sqrt W / 4 ≤ Real.log (mrtWorkingCap W : ℝ) := by
  have hs := Real.tendsto_sqrt_atTop.eventually
    (eventually_ge_atTop (max (4 * Real.log 2) (2 * Real.log 2)))
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with W hs hW
  have hroot : 4 * Real.log 2 ≤ Real.sqrt W := (le_max_left _ _).trans hs
  have hroot' : 2 * Real.log 2 ≤ Real.sqrt W := (le_max_right _ _).trans hs
  have hexp : (2 : ℝ) ≤ Real.exp (Real.sqrt W / 2) := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hfloor := Nat.lt_floor_add_one (Real.exp (Real.sqrt W / 2))
  change Real.exp (Real.sqrt W / 2) < (mrtWorkingCap W : ℝ) + 1 at hfloor
  have hlo : Real.exp (Real.sqrt W / 2) / 2 ≤ (mrtWorkingCap W : ℝ) := by linarith
  have hh := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hlo
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at hh
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

lemma major_arc_working_length_le (H : ℕ) (W : ℝ) :
    majorArcWorkingLength H W ≤ H := mrt_working_length_upper

lemma major_arc_working_length_loglog {H : ℕ} {W : ℝ}
    (hW : 0 < W) (hH : (1:ℝ) < majorArcWorkingLength H W) :
    Real.log (Real.log (majorArcWorkingLength H W:ℝ)) ≤ (1/5:ℝ)*Real.log W := by
  have hh := mrt_working_length_loglog (Real.rpow_pos_of_pos hW (2/5)) hH
  rw [Real.log_rpow hW] at hh
  dsimp only [majorArcWorkingLength]
  linarith


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

theorem major_arc_working_length_remainder :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℕ,
      majorArcWorkingLength H W=H ∨
        (majorArcWorkingLength H W:ℝ)/H ≤ W^(-1/4:ℝ) := by
  have ht := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/5 by norm_num)).bound
    (show (0:ℝ)<2 by norm_num)
  filter_upwards [ht,eventually_gt_atTop (0:ℝ)] with W ht hW
  simp only [Real.norm_eq_abs] at ht
  rw [abs_of_nonneg (Real.rpow_nonneg hW.le _)] at ht
  have hlog : Real.log W ≤ 2*W^(1/5:ℝ) := (le_abs_self _).trans ht
  intro H
  unfold majorArcWorkingLength mrtWorkingLength
  rw [major_arc_working_root hW.le]
  split_ifs with h
  · exact Or.inl rfl
  · right
    have hH : Real.exp (W^(1/5:ℝ)) ≤ (H:ℝ) := le_of_not_ge h
    have hH0 : (0:ℝ) < H := (Real.exp_pos _).trans_le hH
    calc
      _ ≤ Real.exp (W^(1/5:ℝ)/2)/(H:ℝ) := by
        apply div_le_div_of_nonneg_right _ hH0.le
        simpa only [major_arc_working_root hW.le] using mrt_working_cap_upper (W^(2/5:ℝ))
      _ ≤ Real.exp (W^(1/5:ℝ)/2)/Real.exp (W^(1/5:ℝ)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hH
      _ = Real.exp (-W^(1/5:ℝ)/2) := by rw [← Real.exp_sub]; congr 1; ring
      _ ≤ _ := by
        rw [Real.rpow_def_of_pos hW (-1/4:ℝ)]
        apply Real.exp_le_exp.mpr
        nlinarith

theorem major_arc_working_cap_log :
    ∀ᶠ W : ℝ in atTop, W^(1/5:ℝ)/4 ≤
      Real.log (mrtWorkingCap (W^(2/5:ℝ)):ℝ) := by
  have ht : Tendsto (fun W:ℝ => W^(2/5:ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [ht.eventually mrt_working_cap_log,eventually_ge_atTop (0:ℝ)] with W hcap hW
  simpa only [major_arc_working_root hW] using hcap

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcTypicalRemoval
namespace OAI

/-! Removing the typical-set restriction costs its actual missing density.
This comparison is uniform in the additive frequency and pays the discarded
integers once, before either the major- or minor-arc estimate is applied. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma minor_arc_typical_pointwise_error {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {n : ℕ} (hn : 0 < n) :
    ‖F n - mrtTypicalCoefficient J P F n‖ ≤
      if ¬mrtTypical J P n then (1 : ℝ) else 0 := by
  unfold mrtTypicalCoefficient
  by_cases h : mrtTypical J P n
  · simp [h]
  · simpa [h] using hF n hn

lemma minor_arc_typical_error_sum {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α +
        (H : ℝ) * ∑ n ∈ range (X + H),
          if ¬mrtTypical J P (n + 1) then (1 : ℝ) else 0 := by
  have herr := window_error_from_density F (mrtTypicalCoefficient J P F)
    (fun n => if ¬mrtTypical J P n then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> positivity)
    (fun n hn => minor_arc_typical_pointwise_error J P F hF hn) H X α
  simp only [shortExponentialIntegral_eq_sum, norm_shortExponentialSum_eq_window]
  calc
    _ ≤ ∑ v ∈ range X,
        (‖shortWindowSum (mrtTypicalCoefficient J P F) H α v‖ +
          ‖shortWindowSum F H α v -
            shortWindowSum (mrtTypicalCoefficient J P F) H α v‖) := by
      apply sum_le_sum
      intro v _
      calc
        _ = ‖shortWindowSum (mrtTypicalCoefficient J P F) H α v +
            (shortWindowSum F H α v -
              shortWindowSum (mrtTypicalCoefficient J P F) H α v)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by rw [sum_add_distrib]; exact add_le_add le_rfl herr

lemma minor_arc_typical_density_sum {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (N : ℕ) [NeZero N] :
    (∑ n ∈ range N, if ¬mrtTypical J P (n + 1) then (1 : ℝ) else 0) =
      (N : ℝ) * (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical J P (1 + n.val)) := by
  unfold FiniteLaw.probability FiniteLaw.average uniformFiniteLaw
  dsimp only
  rw [← mul_sum, Fintype.card_fin, ← mul_assoc]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [mul_one_div_cancel hN, one_mul]
  symm
  apply sum_bij (fun n _ => n.val)
  · intro n _
    exact mem_range.mpr n.isLt
  · intro n _ m _ he
    exact Fin.ext he
  · intro n hn
    exact ⟨⟨n, mem_range.mp hn⟩, mem_univ _, rfl⟩
  · intro n _
    simp only [Nat.add_comm 1]

theorem minor_arc_remove_typical {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) [NeZero (X + H)] (α δ : ℝ)
    (hdensity : (uniformFiniteLaw (Fin (X + H))).probability
      (fun n => ¬mrtTypical J P (1 + n.val)) ≤ δ) :
    shortExponentialIntegral F X H α ≤
      shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α +
        (H : ℝ) * (X + H) * δ := by
  apply (minor_arc_typical_error_sum J P F hF X H α).trans
  rw [minor_arc_typical_density_sum]
  apply add_le_add le_rfl
  calc
    _ ≤ (H : ℝ) * ((X + H : ℕ) * δ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg _)) (Nat.cast_nonneg H)
    _ = _ := by push_cast; ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingBand
namespace OAI

/-! Prime-band costs for the fifth-root working length. Both density
and the minor-arc fourth root have the same elementary rate. -/
namespace TwoPointCorrelations

open _root_.Filter

lemma major_arc_working_log_lower {H : ℕ} {W : ℝ}
    (hW : 1 ≤ W) (hH : 1 ≤ Real.log (H:ℝ))
    (hWH : W ≤ Real.log (H:ℝ)^5)
    (hcap : W^(1/5:ℝ)/4 ≤ Real.log (mrtWorkingCap (W^(2/5:ℝ)):ℝ)) :
    W^(1/5:ℝ)/4 ≤ Real.log (majorArcWorkingLength H W:ℝ) := by
  have hW0 : 0 < W := by linarith
  have hroot : W^(1/5:ℝ) ≤ Real.log (H:ℝ) := by
    calc
      _ ≤ (Real.log (H:ℝ)^5)^(1/5:ℝ) := Real.rpow_le_rpow hW0.le hWH (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0 ≤ Real.log (H:ℝ))]
        norm_num
  unfold majorArcWorkingLength mrtWorkingLength
  split_ifs
  · nlinarith [Real.rpow_nonneg hW0.le (1/5:ℝ)]
  · exact hcap

lemma major_arc_working_upper_log {H : ℕ} {W : ℝ} (hW : 2 ≤ W)
    (hpower : W^6 ≤ (majorArcWorkingLength H W:ℝ)) :
    2 ≤ (majorArcWorkingLength H W:ℝ)/W^3 ∧
    Real.log (majorArcWorkingLength H W:ℝ)/2 ≤
      Real.log ((majorArcWorkingLength H W:ℝ)/W^3) := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hthird : 2 ≤ W^3 := hW.trans (le_self_pow₀ hW1 (by decide))
  have hdiv : W^3 ≤ (majorArcWorkingLength H W:ℝ)/W^3 := by
    apply (le_div_iff₀ (pow_pos hW0 3)).mpr
    simpa only [← pow_add] using hpower
  have hpos : (0:ℝ) < majorArcWorkingLength H W := (pow_pos hW0 6).trans_le hpower
  have hl := Real.log_le_log (pow_pos hW0 6) hpower
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  refine ⟨hthird.trans hdiv,?_⟩
  rw [Real.log_div hpos.ne' (pow_ne_zero 3 hW0.ne'),Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

lemma major_arc_working_band_density (A : ℕ) {H : ℕ} {W : ℝ}
    (hW : 2 ≤ W) (hH : 1 ≤ Real.log (H:ℝ))
    (hWH : W ≤ Real.log (H:ℝ)^5)
    (hpower : W^6 ≤ (majorArcWorkingLength H W:ℝ))
    (hcap : W^(1/5:ℝ)/4 ≤ Real.log (mrtWorkingCap (W^(2/5:ℝ)):ℝ)) :
    Real.log (W^A)/Real.log ((majorArcWorkingLength H W:ℝ)/W^3) ≤
      8*(A:ℝ)*majorArcWorkingError W := by
  have hW0 : 0 < W := by linarith
  have hl := major_arc_working_log_lower (by linarith : 1 ≤ W) hH hWH hcap
  have hQ := (major_arc_working_upper_log hW hpower).2
  have hlow : W^(1/5:ℝ)/8 ≤ Real.log ((majorArcWorkingLength H W:ℝ)/W^3) := by linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  rw [Real.log_pow]
  calc
    _ ≤ ((A:ℝ)*Real.log W)/(W^(1/5:ℝ)/8) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
    _ = 8*(A:ℝ)*(Real.log W*W^(-1/5:ℝ)) := by
      rw [show (-1/5:ℝ)=-(1/5:ℝ) by ring,Real.rpow_neg hW0.le]
      ring
    _ ≤ _ := by
      unfold majorArcWorkingError
      gcongr
      linarith


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingDensity
namespace OAI

/-! Uniform finite-interval density for the actual working prime bands.
The outer and working-parameter thresholds are independent. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.Classical


/-- For the actual working first band the missing density has exactly the
working error rate, uniformly in translation and all longer intervals. -/
theorem mrt_working_interval_density :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
      ∀ W : ℝ, W₀ ≤ W → ∀ H : ℕ, 0 < H →
      1 ≤ Real.log (H:ℝ) → W ≤ Real.log (H:ℝ)^5 →
      ∀ X : ℕ, X₀ ≤ X → ∀ J : ℕ,
      let P := W^(500000:ℕ)
      let Q := (majorArcWorkingLength H W:ℝ)/W^3
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤
        Real.exp (Real.sqrt (Real.log (X:ℝ))/2)) →
      ∀ (A N : ℕ) [NeZero N], X ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
          (A+n.val)) ≤ C*majorArcWorkingError W := by
  obtain ⟨C,hC,hd⟩ := mrt_actual_band_interval_density
  obtain ⟨X₀,hX₀⟩ := Filter.eventually_atTop.mp hd
  have hw := (mrt_working_prime_parameters.and
    ((major_arc_working_length_power 6).and major_arc_working_cap_log))
  obtain ⟨W₀,hW₀⟩ := Filter.eventually_atTop.mp hw
  refine ⟨C*(8*500000),by positivity,W₀,X₀,?_⟩
  intro W hW H hH hLH hWH X hX J
  dsimp only
  intro hu A N _ hXN
  have hw := hW₀ W hW
  have hp := hw.1.2 H hH hLH hWH
  have hb := major_arc_working_band_density 500000 hw.1.1 hLH hWH
    (hw.2.1 H hH hLH hWH) hw.2.2
  have hd := hX₀ X hX (W^(500000:ℕ))
    ((majorArcWorkingLength H W:ℝ)/W^3) J hp.1 hp.2.1 hp.2.2.2.1 hu A N hXN
  calc
    _ ≤ C*Real.log (W^(500000:ℕ))/
        Real.log ((majorArcWorkingLength H W:ℝ)/W^3) := hd
    _ = C*(Real.log (W^(500000:ℕ))/
        Real.log ((majorArcWorkingLength H W:ℝ)/W^3)) := by ring
    _ ≤ C*(8*(500000:ℝ)*majorArcWorkingError W) :=
      mul_le_mul_of_nonneg_left hb hC.le
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFullWorkingMean
namespace OAI

/-! Remove the literal typical-factor restriction using its proved
uniform density, after the major/minor arc alternative is complete. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem mrt_full_actual_working_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
    ∀ X H : ℕ, X₀ ≤ X → 10 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter (Real.log X) H M
      let h := majorArcWorkingLength H W
      W₀ ≤ W → ∀ Y : ℕ, X ≤ Y → Y+h ≤ 2*X →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
        MRTDistanceLowerBound F X H M → ∀ α : ℝ,
        shortExponentialIntegral F Y h α ≤
        C*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
  obtain ⟨C₁,hC₁,W₁,X₁,htypical⟩ := mrt_typical_actual_working_mean hprime hhigh
  obtain ⟨C₂,hC₂,W₂,X₂,hdensity⟩ := mrt_working_interval_density
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₃,hX₃⟩ := eventually_atTop.mp
    ((hlog.eventually major_arc_parameter_rate).and
      ((hlog.eventually (eventually_ge_atTop (1:ℝ))).and
        (eventually_ge_atTop (max X₁ (max X₂ 2)))))
  refine ⟨C₁+42*C₂,by positivity,max W₁ W₂,X₃,?_⟩
  intro X H hX hH hHX hLH hLL M hM
  dsimp only
  intro hWlarge Y hXY hY F hF1 hFm hFb hd α
  let W := majorArcParameter (Real.log X) H M
  let h := majorArcWorkingLength H W
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  let E := Real.exp (-M/20)+mrtShortError X H
  obtain ⟨hrate,hLX,hXs⟩ := hX₃ X hX
  have hX₁ : X₁ ≤ X := (le_max_left _ _).trans hXs
  have hX₂ : X₂ ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hXs)
  have hXpos : 2 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hXs)
  have hW₁ : W₁ ≤ W := (le_max_left _ _).trans hWlarge
  have hW₂ : W₂ ≤ W := (le_max_right _ _).trans hWlarge
  obtain ⟨hW,hWH,_,_⟩ := major_arc_parameter_bounds hLX hLH hM
  obtain ⟨J,hJ,hup,ht⟩ := htypical X H hX₁ hH hHX hLH hLL M hM hW₁
  have ht' := ht Y hXY hY F hF1 hFm hFb hd α
  have hu : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log X)/2) := by
    intro j hj
    have hh := Real.exp_le_exp.mpr (hup j hj)
    change Real.exp (Real.log (mrtBandUpper Q j)) ≤ _ at hh
    rwa [Real.exp_log (show 0 < mrtBandUpper Q j from Real.exp_pos _)] at hh
  let : NeZero (Y+h) := ⟨by omega⟩
  have hden := hdensity W hW₂ H (by omega) hLH hWH X hX₂ J hu 1 (Y+h) (by omega)
  have hk : majorArcWorkingError W ≤ 21*E := by
    have hh := hrate H M hLH hLL hM
    rw [mul_div_assoc] at hh
    have hshort : 0 ≤ Real.log (Real.log (H:ℝ))/Real.log H := by positivity
    have herr : 0 ≤ (Real.log X)^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    dsimp only [E,mrtShortError]
    linarith only [hh,hshort,herr]
  have hE : 0 ≤ E := by dsimp [E,mrtShortError]; positivity
  have hN : ((Y+h:ℕ):ℝ) ≤ 2*(Y:ℝ) := by
    have hh : h ≤ Y := (major_arc_working_length_le H W).trans (hHX.trans hXY)
    exact_mod_cast (show Y+h ≤ 2*Y by omega)
  have he : (h:ℝ)*(Y+h)*(C₂*majorArcWorkingError W) ≤ 42*C₂*(Y:ℝ)*h*E := by
    calc
      _ ≤ (h:ℝ)*(2*Y)*(C₂*majorArcWorkingError W) := by
        have hκ : 0 ≤ majorArcWorkingError W := mul_nonneg
          (by linarith [Real.log_nonneg hW]) (Real.rpow_nonneg (by linarith) _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add] using hN)
            (Nat.cast_nonneg h)) (mul_nonneg hC₂.le hκ)
      _ ≤ (h:ℝ)*(2*Y)*(C₂*(21*E)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hC₂.le) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α+
        (h:ℝ)*(Y+h)*(C₂*majorArcWorkingError W) :=
      minor_arc_remove_typical _ _ F hFb Y h α _ hden
    _ ≤ C₁*(Y:ℝ)*h*E+42*C₂*(Y:ℝ)*h*E := add_le_add ht' he
    _ = _ := by dsimp only [E]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortTheorem
namespace OAI

/-! Corrected MRT Theorem 1.7 at every natural scale, reduced only to the
sparse-prime and high-prime estimates used in the analytic argument. -/
namespace TwoPointCorrelations

open _root_.Filter

theorem mrt_short_exponential_of_prime_estimates_oai
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    MRTShortExponentialInput := by
  obtain ⟨C,hC,W₀,X₀,hfull⟩ := mrt_full_actual_working_mean hprime hhigh
  obtain ⟨W₁,hrem⟩ := eventually_atTop.mp major_arc_working_length_remainder
  obtain ⟨W₂,hpower⟩ := eventually_atTop.mp (major_arc_working_length_power 1)
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₁,hX₁⟩ := eventually_atTop.mp
    ((hlog.eventually major_arc_parameter_rate).and
      ((hlog.eventually (eventually_ge_atTop (1:ℝ))).and (eventually_ge_atTop X₀)))
  let B := max (Real.exp 5) (max W₀ (max W₁ W₂))
  obtain ⟨C₀,hC₀,htrivial⟩ := mrt_short_trivial_cases B X₁
  refine ⟨C₀+2*C+21,by positivity,?_⟩
  intro X H hH hHX F hFm hFb M hd α
  let W := majorArcParameter (Real.log X) H M
  let h := majorArcWorkingLength H W
  let E := Real.exp (-M/20)+mrtShortError X H
  have hE : 0 ≤ E := add_nonneg (Real.exp_pos _).le (mrt_short_error_nonneg hH hHX)
  have hsmall (hcase : W ≤ B ∨ X ≤ X₁) :
      shortExponentialIntegral F X H α ≤ (C₀+2*C+21)*(H:ℝ)*X*E := by
    have hs := htrivial X H hH hHX F hFb M hcase α
    apply hs.trans
    have hc : C₀ ≤ C₀+2*C+21 := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg H))
        (Nat.cast_nonneg X)) hE
  by_cases hwsmall : W ≤ B
  · exact hsmall (Or.inl hwsmall)
  by_cases hxsmall : X ≤ X₁
  · exact hsmall (Or.inr hxsmall)
  have hBW : B ≤ W := (le_of_not_ge hwsmall)
  have hW₀ : W₀ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hBW)
  have hW₁ : W₁ ≤ W := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hBW))
  have hW₂ : W₂ ≤ W := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hBW))
  have heW : Real.exp 5 ≤ W := (le_max_left _ _).trans hBW
  have hM : 0 ≤ M := by
    have hWe : W ≤ Real.exp (M/3) := (min_le_right _ _).trans (min_le_right _ _)
    have hMe := Real.exp_le_exp.mp (heW.trans hWe)
    linarith
  obtain ⟨hLH,hLL⟩ := mrt_large_parameter_logs hH heW
  obtain ⟨hrate,hLX,hXX₀⟩ := hX₁ X (le_of_not_ge hxsmall)
  obtain ⟨hW,hWH,_,_⟩ := major_arc_parameter_bounds hLX hLH hM
  have hW0 : 0 < W := by linarith
  have hWh : W ≤ (h:ℝ) := by
    simpa only [pow_one] using hpower W hW₂ H (by omega) hLH hWH
  have hh : 0 < h := by exact_mod_cast hW0.trans_le hWh
  have hhH : h ≤ H := major_arc_working_length_le H W
  have hH0 : (0:ℝ) < H := by exact_mod_cast (show 0< H by omega)
  rcases hFm.one_zero_or_one with hzero | hone
  · rw [shortExponentialIntegral_of_one_zero hFm hzero]
    positivity
  have hmean := hfull X H hXX₀ hH hHX hLH hLL M hM hW₀
  have htail : W^(-1/4:ℝ) ≤ 21*E := by
    have hk := hrate H M hLH hLL hM
    rw [mul_div_assoc] at hk
    have hw : W^(-1/4:ℝ) ≤ majorArcWorkingError W := by
      apply (Real.rpow_le_rpow_of_exponent_le hW (show (-1/4:ℝ)≤-1/5 by norm_num)).trans
      exact le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _)
        (by linarith [Real.log_nonneg hW])
    have hs : 0 ≤ Real.log (Real.log (H:ℝ))/Real.log H := by positivity
    have hl : 0 ≤ (Real.log X)^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    dsimp only [E,mrtShortError]
    linarith only [hk,hw,hs,hl]
  have hlarge : shortExponentialIntegral F X H α ≤ (2*C+21)*(X:ℝ)*H*E := by
    rcases hrem W hW₁ H with heq | hratio
    · have hm := hmean X le_rfl (by change X+h ≤ 2*X; omega) F hone hFm hFb hd α
      change h=H at heq
      change shortExponentialIntegral F X h α ≤ C*(X:ℝ)*h*E at hm
      rw [heq] at hm
      have hconstant : C ≤ 2*C+21 := by linarith
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant
          (Nat.cast_nonneg X)) (Nat.cast_nonneg H)) hE)
    · let Y := X+H-h
      have hXY : X ≤ Y := by dsimp [Y]; omega
      have hY : Y+h ≤ 2*X := by dsimp [Y]; omega
      have hm := hmean Y hXY hY F hone hFm hFb hd α
      have hcount : ((H/h:ℕ):ℝ)*(h:ℝ) ≤ H := by exact_mod_cast Nat.div_mul_le_self H h
      have hYreal : (Y:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast (show Y≤2*X by omega)
      have hmain : ((H/h:ℕ):ℝ)*shortExponentialIntegral F Y h α ≤ 2*C*X*H*E := by
        calc
          _ ≤ ((H/h:ℕ):ℝ)*(C*(Y:ℝ)*h*E) :=
            mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
          _ = (C*(Y:ℝ)*E)*(((H/h:ℕ):ℝ)*h) := by ring
          _ ≤ (C*(2*X)*E)*(H:ℝ) := by gcongr
          _ = _ := by ring
      have hboundary : (X:ℝ)*h ≤ 21*(X:ℝ)*H*E := by
        have hb : (h:ℝ) ≤ (21*E)*H := (div_le_iff₀ hH0).mp (hratio.trans htail)
        have hs := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg X)
        convert (preTransparency := .instances) hs using 1; ring
      have hs := mrt_short_integral_subdivision_sharp F hFb X H h hh hhH α
      change shortExponentialIntegral F X H α ≤
        ((H/h:ℕ):ℝ)*shortExponentialIntegral F Y h α+(X:ℝ)*h at hs
      apply hs.trans
      have ht := add_le_add hmain hboundary
      convert (preTransparency := .instances) ht using 1; ring
  apply hlarge.trans
  have hc : 2*C+21 ≤ C₀+2*C+21 := by linarith
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg X))
      (Nat.cast_nonneg H)) hE
  convert (preTransparency := .instances) hh using 1; ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_short_exponential_of_prime_estimates_oai := @OAI.TwoPointCorrelations.mrt_short_exponential_of_prime_estimates_oai
