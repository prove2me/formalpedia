-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_actual_band_interval_density
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:45:58.598536+00:00
-- url     : https://prove2.me/submissions/ccaff7b4-010f-4446-864e-77e98296d31f

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]




lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))


lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]













end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Bonferroni
namespace OAI

/-! The finite even-order sieve, before any independence or prime estimates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma eventIntersectionCount_eq_choose {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (j : ℕ) (x : α) :
    eventIntersectionCount P E j x = ((P.filter (fun i => E i x)).card.choose j : ℝ) := by
  have hfilter : (P.powersetCard j).filter (fun S => eventIntersection E S x) =
      (P.filter (fun i => E i x)).powersetCard j := by
    apply Finset.ext
    intro S
    rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_powersetCard]
    simp only [eventIntersection]
    constructor
    · rintro ⟨⟨hS, hcard⟩, hE⟩
      exact ⟨fun i hi => mem_filter.mpr ⟨hS hi, hE i hi⟩, hcard⟩
    · rintro ⟨hS, hcard⟩
      exact ⟨⟨fun i hi => (mem_filter.mp (hS hi)).1, hcard⟩,
        fun i hi => (mem_filter.mp (hS hi)).2⟩
  unfold eventIntersectionCount
  rw [← sum_filter, hfilter]
  simp

lemma truncatedEventCount_eq_choose {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E r x =
      ∑ j ∈ range (r + 1), (-1 : ℝ) ^ j *
        ((P.filter (fun i => E i x)).card.choose j : ℝ) := by
  simp only [truncatedEventCount, eventIntersectionCount_eq_choose]

lemma avoidsEvents_iff_card_zero {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (x : α) :
    avoidsEvents P E x ↔ (P.filter (fun i => E i x)).card = 0 := by
  simp only [avoidsEvents, card_eq_zero, filter_eq_empty_iff]

lemma real_alternating_choose (n r : ℕ) :
    (∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ)) =
      (-1 : ℝ) ^ r * (n.choose r : ℝ) := by
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := r))

lemma alternating_choose_zero (r : ℕ) :
    (∑ j ∈ range (r + 1), (-1 : ℝ) ^ j * (Nat.choose 0 j : ℝ)) = 1 := by
  rw [sum_eq_single 0]
  · simp
  · intro j _ hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp
  · intro h
    exact False.elim (h (mem_range.mpr (Nat.zero_lt_succ r)))

lemma even_binomial_lower (k r : ℕ) :
    (if k = 0 then (1 : ℝ) else 0) ≤
      ∑ j ∈ range (2 * r + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) := by
  cases k with
  | zero => simp only [ite_true]; rw [alternating_choose_zero]
  | succ k =>
      rw [real_alternating_choose k (2 * r)]
      have he : (-1 : ℝ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
      simp only [Nat.succ_ne_zero, ite_false, he, one_mul]
      positivity

lemma odd_binomial_upper (k r : ℕ) :
    (∑ j ∈ range ((2 * r + 1) + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ)) ≤
      if k = 0 then (1 : ℝ) else 0 := by
  cases k with
  | zero => simp only [ite_true]; rw [alternating_choose_zero]
  | succ k =>
      rw [real_alternating_choose k (2 * r + 1)]
      have he : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      simp only [Nat.succ_ne_zero, ite_false, he, neg_one_mul]
      exact neg_nonpos.mpr (Nat.cast_nonneg _)

/-- Even truncation dominates the actual avoidance indicator pointwise. -/
theorem bonferroni_even_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    (if avoidsEvents P E x then (1 : ℝ) else 0) ≤ truncatedEventCount P E (2 * r) x := by
  rw [truncatedEventCount_eq_choose, avoidsEvents_iff_card_zero]
  simpa using even_binomial_lower (P.filter (fun i => E i x)).card r

/-- Odd truncation gives the opposite bound. -/
theorem bonferroni_odd_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r + 1) x ≤
      if avoidsEvents P E x then (1 : ℝ) else 0 := by
  rw [truncatedEventCount_eq_choose, avoidsEvents_iff_card_zero]
  simpa using odd_binomial_upper (P.filter (fun i => E i x)).card r

lemma truncatedEventCount_odd {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r + 1) x =
      truncatedEventCount P E (2 * r) x - eventIntersectionCount P E (2 * r + 1) x := by
  unfold truncatedEventCount
  rw [sum_range_succ]
  have he : (-1 : ℝ) ^ (2 * r + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [he]
  ring

/-- The excess of the even truncation is bounded by the very next
intersection layer. No convergence argument is involved. -/
theorem bonferroni_remainder_pointwise {ι α : Type*}
    (P : Finset ι) (E : ι → α → Prop) (r : ℕ) (x : α) :
    truncatedEventCount P E (2 * r) x ≤
      (if avoidsEvents P E x then (1 : ℝ) else 0) +
        eventIntersectionCount P E (2 * r + 1) x := by
  have hh := bonferroni_odd_pointwise P E r x
  rw [truncatedEventCount_odd] at hh
  linarith



lemma average_eventIntersectionCount {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (j : ℕ) :
    μ.average (eventIntersectionCount P E j) = eventIntersectionMass μ P E j := by
  unfold eventIntersectionCount eventIntersectionMass FiniteLaw.probability FiniteLaw.average
  simp only [mul_sum]
  rw [sum_comm]

lemma average_truncatedEventCount {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    μ.average (truncatedEventCount P E r) = truncatedEventMass μ P E r := by
  unfold truncatedEventCount truncatedEventMass FiniteLaw.average
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  calc
    _ = (-1 : ℝ) ^ j * μ.average (eventIntersectionCount P E j) := by
      unfold FiniteLaw.average
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [average_eventIntersectionCount]

theorem bonferroni_even {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    μ.probability (avoidsEvents P E) ≤ truncatedEventMass μ P E (2 * r) := by
  rw [← average_truncatedEventCount]
  exact μ.average_mono (bonferroni_even_pointwise P E r)

theorem bonferroni_remainder {ι α : Type*} [Fintype α]
    (μ : FiniteLaw α) (P : Finset ι) (E : ι → α → Prop) (r : ℕ) :
    truncatedEventMass μ P E (2 * r) ≤ μ.probability (avoidsEvents P E) +
      eventIntersectionMass μ P E (2 * r + 1) := by
  rw [← average_truncatedEventCount, ← average_eventIntersectionCount]
  have hh := μ.average_mono (bonferroni_remainder_pointwise P E r)
  simpa only [FiniteLaw.probability, FiniteLaw.average, mul_add, sum_add_distrib] using hh


lemma truncatedEventMass_comparison {ι α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (P : Finset ι)
    (E : ι → α → Prop) (F : ι → β → Prop) (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ P.powerset, S.card ≤ r →
      |μ.probability (eventIntersection E S) -
        ν.probability (eventIntersection F S)| ≤ err S) :
    truncatedEventMass μ P E r ≤ truncatedEventMass ν P F r +
      sieveIntersectionError P err r := by
  have heq : truncatedEventMass μ P E r - truncatedEventMass ν P F r =
      ∑ j ∈ range (r + 1), ∑ S ∈ P.powersetCard j,
        (-1 : ℝ) ^ j * (μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S)) := by
    simp only [truncatedEventMass, eventIntersectionMass, mul_sum,
      mul_sub, sum_sub_distrib]
  have hb : truncatedEventMass μ P E r - truncatedEventMass ν P F r ≤
      sieveIntersectionError P err r := by
    rw [heq]
    apply sum_le_sum
    intro j hj
    apply sum_le_sum
    intro S hS
    obtain ⟨hSP, hcard⟩ := mem_powersetCard.mp hS
    calc
      _ ≤ |(-1 : ℝ) ^ j * (μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S))| := le_abs_self _
      _ = |μ.probability (eventIntersection E S) -
          ν.probability (eventIntersection F S)| := by
        simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ err S := herr S (mem_powerset.mpr hSP)
        (by rw [hcard]; exact Nat.le_of_lt_succ (mem_range.mp hj))
  linarith

/-- Exact finite sieve transfer. An independent residue model can be
inserted only after its intersections have actually been counted. -/
theorem bonferroni_transfer {ι α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (P : Finset ι)
    (E : ι → α → Prop) (F : ι → β → Prop) (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ P.powerset, S.card ≤ 2 * r →
      |μ.probability (eventIntersection E S) -
        ν.probability (eventIntersection F S)| ≤ err S) :
    μ.probability (avoidsEvents P E) ≤ ν.probability (avoidsEvents P F) +
      eventIntersectionMass ν P F (2 * r + 1) + sieveIntersectionError P err (2 * r) := by
  have h₁ := bonferroni_even μ P E r
  have h₂ := truncatedEventMass_comparison μ ν P E F (2 * r) err herr
  have h₃ := bonferroni_remainder ν P F r
  linarith

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueCounts
namespace OAI

/-!
# Residue counts on arbitrary finite consecutive intervals

An interval is represented by its starting residue `A` and its length `N`.
Thus this includes arbitrary translates, including intervals starting at
negative integers. We prove the exact quotient-and-remainder count, the
one-count discrepancy, and the total-variation estimate used by the finite
residue comparison in the manuscript.
-/

namespace TwoPointCorrelations

open _root_.Finset


lemma residueCount_add {D : ℕ} [NeZero D] (A : ZMod D) (M N : ℕ) (r : ZMod D) :
    residueCount A (M + N) r = residueCount A M r + residueCount (A + (M : ZMod D)) N r := by
  unfold residueCount
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.cast_add, add_assoc]

lemma residueCount_period {D : ℕ} [NeZero D] (A r : ZMod D) :
    residueCount A D r = 1 := by
  unfold residueCount
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin D ≃ ZMod D :=
    { toFun := fun i => (i.val : ZMod D)
      invFun := fun z => ⟨z.val, z.val_lt⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := fun z => ZMod.natCast_zmod_val z }
  change (∑ i : Fin D, (fun z : ZMod D => if A + z = r then (1 : ℕ) else 0) (e i)) = 1
  rw [e.sum_comp (fun z : ZMod D => if A + z = r then (1 : ℕ) else 0)]
  have htest (j : ZMod D) : A + j = r ↔ j = r - A := by
    constructor
    · intro h
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using h
    · intro h
      rw [h]
      ring
  simp_rw [htest]
  simp

lemma residueCount_multiple {D : ℕ} [NeZero D] (A r : ZMod D) (k : ℕ) :
    residueCount A (D * k) r = k := by
  induction k with
  | zero => simp [residueCount]
  | succ k ih =>
      rw [Nat.mul_succ, residueCount_add, ih, residueCount_period]

lemma residueCount_short {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ)
    (hN : N ≤ D) : residueCount A N r = if (r - A).val < N then 1 else 0 := by
  unfold residueCount
  have htest (j : ℕ) (hj : j ∈ Finset.range N) :
      A + (j : ZMod D) = r ↔ j = (r - A).val := by
    have hjD : j < D := (Finset.mem_range.mp hj).trans_le hN
    constructor
    · intro h
      have heq : (j : ZMod D) = r - A := by
        apply eq_sub_iff_add_eq.mpr
        simpa [add_comm] using h
      have hv := congrArg ZMod.val heq
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hjD] using hv
    · intro h
      rw [h, ZMod.natCast_zmod_val]
      ring
  calc
    (∑ j ∈ Finset.range N, if A + (j : ZMod D) = r then 1 else 0) =
        ∑ j ∈ Finset.range N, if j = (r - A).val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [htest j hj]
    _ = if (r - A).val < N then 1 else 0 := by simp

/-- Exact residue count on an arbitrary translated interval. -/
theorem residueCount_exact {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ) :
    residueCount A N r = N / D + if (r - A).val < N % D then 1 else 0 := by
  have hsplit := residueCount_add A (D * (N / D)) (N % D) r
  have hN : D * (N / D) + N % D = N := Nat.div_add_mod N D
  rw [hN, residueCount_multiple] at hsplit
  simpa only [Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    residueCount_short A r (N % D) (Nat.le_of_lt (Nat.mod_lt N (NeZero.pos D)))] using hsplit

/-- The count differs from interval length divided by modulus by at most one. -/
theorem residueCount_discrepancy {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ) :
    |(residueCount A N r : ℝ) - (N : ℝ) / D| ≤ 1 := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hrem₀ : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) := by positivity
  have hrem₁ : ((N % D : ℕ) : ℝ) < D := by exact_mod_cast Nat.mod_lt N (NeZero.pos D)
  have hdiv₀ : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) / D := div_nonneg hrem₀ hD.le
  have hdiv₁ : ((N % D : ℕ) : ℝ) / D < 1 := (div_lt_one hD).mpr hrem₁
  have hquot : (N : ℝ) / D = (N / D : ℕ) + ((N % D : ℕ) : ℝ) / D := by
    have hN : (N : ℝ) = (D : ℝ) * (N / D : ℕ) + (N % D : ℕ) := by
      exact_mod_cast (Nat.div_add_mod N D).symm
    apply (div_eq_iff hD.ne').mpr
    field_simp
    nlinarith [hN]
  rw [residueCount_exact, Nat.cast_add, hquot]
  split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero] <;> rw [abs_le] <;>
    constructor <;> linarith




lemma residueProbability_discrepancy {D : ℕ} [NeZero D] (A r : ZMod D)
    (N : ℕ) (hN : 0 < N) : |residueProbability A N r - 1 / (D : ℝ)| ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have heq : residueProbability A N r - 1 / (D : ℝ) =
      ((residueCount A N r : ℝ) - (N : ℝ) / D) / N := by
    unfold residueProbability
    field_simp
  rw [heq, abs_div, abs_of_pos hN']
  exact div_le_div_of_nonneg_right (residueCount_discrepancy A r N) hN'.le


/-- The stronger `D/(2N)` bound implies the `D/N` estimate used in the paper. -/
theorem residueTotalVariation_le {D : ℕ} [NeZero D] (A : ZMod D)
    (N : ℕ) (hN : 0 < N) : residueTotalVariation A N ≤ (D : ℝ) / (2 * N) := by
  unfold residueTotalVariation
  have hsum : (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) ≤
      (D : ℝ) / N := by
    calc
      (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) ≤
          ∑ _r : ZMod D, 1 / (N : ℝ) :=
        Finset.sum_le_sum (fun r _ => residueProbability_discrepancy A r N hN)
      _ = (D : ℝ) / N := by simp [ZMod.card, nsmul_eq_mul, div_eq_mul_inv]
  have := div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)
  convert (preTransparency := .instances) this using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CRTComparison
namespace OAI

/-!
# Finite CRT marginals and contraction under independent randomization

A selected finite set of pairwise coprime residue coordinates has the law
of one residue modulo their product. The exact interval count from
`ResidueCounts` gives total variation at most `D / (2N)`. Applying any
finite stochastic kernel preserves this bound; in particular one may add
independent finite randomness and project to any selected encoded bits.
These are the finite arithmetic and data-processing steps in `q:crt-bits`.
-/

open _root_.Finset

namespace TwoPointCorrelations






/-- A bounded observable has expectation difference at most twice TV. -/
lemma finite_observable_difference {α : Type*} [Fintype α]
    (f g u : α → ℝ) (hu : ∀ x, |u x| ≤ 1) :
    |(∑ x, f x * u x) - ∑ x, g x * u x| ≤ 2 * finiteTotalVariation f g := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (f x * u x - g x * u x)| = |∑ x, (f x - g x) * u x| := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, |(f x - g x) * u x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |f x - g x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hu x)
    _ = 2 * finiteTotalVariation f g := by unfold finiteTotalVariation; ring















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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueBox
namespace OAI

/-! Exact residue laws for one interval and three independent intervals.
The box discrepancy is derived by tensoring the one-dimensional count,
without estimating each individual three-dimensional residue atom. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma intervalResidueLaw_totalVariation {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) :
    finiteTotalVariation (intervalResidueLaw A N hN).weight (uniformZModLaw D).weight ≤
      (D : ℝ) / (2 * N) :=
  residueTotalVariation_le A N hN

/-- The residue mass is the exact pushforward of uniform interval sampling. -/
lemma intervalResidueLaw_average {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (f : ZMod D → ℝ) :
    (intervalResidueLaw A N hN).average f =
      (∑ j ∈ range N, f (A + (j : ZMod D))) / N := by
  unfold FiniteLaw.average intervalResidueLaw residueProbability residueCount
  simp only [div_mul_eq_mul_div, ← sum_div, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, sum_mul]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [ite_mul, one_mul, zero_mul]
  simp





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FourFormLocal
namespace OAI

/-! Exact local density of the four rough-sieve forms. All coefficients
needed to solve pairs are units already over every nonzero modulus;
there is no exceptional argument at the prime two. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical












lemma oneFormBadDensity (D : ℕ) [NeZero D] :
    (uniformZModLaw D).probability (fun x => x = 0) = 1 / (D : ℝ) := by
  simp [FiniteLaw.probability, FiniteLaw.average, uniformZModLaw]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveModel
namespace OAI

/-! The exact independent model and a generating-function bound for its
Bonferroni remainder, using only finite probability identities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw


lemma dependentIndependent_average_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (dependentIndependent μ).average (fun x => ∏ i, f i (x i)) =
      ∏ i, (μ i).average (f i) := by
  simp only [average, dependentIndependent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

lemma dependentIndependent_probability_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (dependentIndependent μ).probability (fun x => ∀ i, E i (x i)) =
      ∏ i, (μ i).probability (E i) := by
  unfold probability
  calc
    _ = (dependentIndependent μ).average
        (fun x => ∏ i, if E i (x i) then (1 : ℝ) else 0) := by
      congr 1
      funext x
      by_cases hx : ∀ i, E i (x i) <;> simp [Fintype.prod_boole, hx]
    _ = _ := dependentIndependent_average_product μ
      (fun i x => if E i x then (1 : ℝ) else 0)

lemma probability_complement {α : Type*} [Fintype α] (μ : FiniteLaw α) (E : α → Prop) :
    μ.probability (fun x => ¬E x) = 1 - μ.probability E := by
  have hsum : μ.probability E + μ.probability (fun x => ¬E x) = 1 := by
    unfold probability average
    rw [← sum_add_distrib]
    calc
      _ = ∑ x, μ.weight x := by
        apply sum_congr rfl
        intro x _
        by_cases hx : E x <;> simp [hx]
      _ = 1 := μ.total
  linarith

lemma dependentIndependent_intersection {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) (S : Finset ι) :
    (dependentIndependent μ).probability (eventIntersection (fun i x => E i (x i)) S) =
      ∏ i ∈ S, (μ i).probability (E i) := by
  have he : eventIntersection (fun i (x : ∀ i, A i) => E i (x i)) S =
      (fun (x : ∀ i, A i) => ∀ i, i ∈ S → E i (x i)) := rfl
  rw [he, dependentIndependent_probability_all μ (fun i a => i ∈ S → E i a)]
  have hi (i : ι) : (μ i).probability (fun x => i ∈ S → E i x) =
      if i ∈ S then (μ i).probability (E i) else 1 := by
    by_cases h : i ∈ S
    · simp [h]
    · simp [probability, h]
  simp only [hi]
  simp

lemma dependentIndependent_avoid {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (dependentIndependent μ).probability (avoidsEvents univ (fun i x => E i (x i))) =
      ∏ i, (1 - (μ i).probability (E i)) := by
  have he : avoidsEvents univ (fun i (x : ∀ i, A i) => E i (x i)) =
      (fun (x : ∀ i, A i) => ∀ i, ¬E i (x i)) := by funext x; simp [avoidsEvents]
  rw [he, dependentIndependent_probability_all μ (fun i a => ¬E i a)]
  simp only [probability_complement]

end FiniteLaw


lemma independent_intersectionMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) (P : Finset ι) (j : ℕ) :
    eventIntersectionMass (FiniteLaw.dependentIndependent μ) P
      (fun i x => E i (x i)) j = elementarySymmetric P
        (fun i => (μ i).probability (E i)) j := by
  simp only [eventIntersectionMass, elementarySymmetric,
    FiniteLaw.dependentIndependent_intersection]

/-- Exponential weighting bounds one elementary symmetric layer. This
avoids factorial estimates and gives the same finite-sieve tail. -/
theorem elementarySymmetric_exp_bound {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0 ≤ a i) (j : ℕ) (t : ℝ) (ht : 0 < t) :
    elementarySymmetric P a j ≤ Real.exp (t * ∑ i ∈ P, a i) / t ^ j := by
  have hm : t ^ j * elementarySymmetric P a j =
      ∑ S ∈ P.powersetCard j, ∏ i ∈ S, t * a i := by
    unfold elementarySymmetric
    rw [mul_sum]
    apply sum_congr rfl
    intro S hS
    rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp hS).2]
  have hsub : P.powersetCard j ⊆ P.powerset := by
    intro S hS
    exact mem_powerset.mpr (mem_powersetCard.mp hS).1
  have hb : t ^ j * elementarySymmetric P a j ≤ Real.exp (t * ∑ i ∈ P, a i) := by
    rw [hm]
    calc
      _ ≤ ∑ S ∈ P.powerset, ∏ i ∈ S, t * a i := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro S hS _
        exact prod_nonneg (fun i hi => mul_nonneg ht.le
          (ha i ((mem_powerset.mp hS) hi)))
      _ = ∏ i ∈ P, (1 + t * a i) := (prod_one_add P).symm
      _ ≤ ∏ i ∈ P, Real.exp (t * a i) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact add_nonneg zero_le_one (mul_nonneg ht.le (ha i hi))
        · intro i _
          linarith [Real.add_one_le_exp (t * a i)]
      _ = Real.exp (∑ i ∈ P, t * a i) := (Real.exp_sum P _).symm
      _ = _ := by rw [mul_sum]
  exact (le_div_iff₀ (pow_pos ht j)).mpr (by simpa [mul_comm] using hb)



/-- Finite sieve upper bound with the independent local model fully
evaluated. The only arithmetic premise is the error of each actual
intersection count. -/
theorem finite_independent_sieve_bound {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    {A : ι → Type*} [∀ i, Fintype (A i)]
    (actual : FiniteLaw α) (E : ι → α → Prop)
    (laws : ∀ i, FiniteLaw (A i)) (bad : ∀ i, A i → Prop)
    (r : ℕ) (err : Finset ι → ℝ)
    (herr : ∀ S ∈ (univ : Finset ι).powerset, S.card ≤ 2 * r →
      |actual.probability (eventIntersection E S) -
        ∏ i ∈ S, (laws i).probability (bad i)| ≤ err S) :
    actual.probability (avoidsEvents univ E) ≤
      (∏ i, (1 - (laws i).probability (bad i))) +
      elementarySymmetric univ (fun i => (laws i).probability (bad i)) (2 * r + 1) +
      sieveIntersectionError univ err (2 * r) := by
  have hh := bonferroni_transfer actual (FiniteLaw.dependentIndependent laws) univ
    E (fun i x => bad i (x i)) r err (fun S hS hcard => by
      rw [FiniteLaw.dependentIndependent_intersection]
      exact herr S hS hcard)
  simpa only [FiniteLaw.dependentIndependent_avoid, independent_intersectionMass] using hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveBoundary
namespace OAI

/-! Explicit accumulation of the finitely many CRT counting errors. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma elementarySymmetric_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y : ℝ) (hY : 0 ≤ Y) (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (j : ℕ) :
    elementarySymmetric P a j ≤ ((P.card : ℝ) * Y) ^ j := by
  calc
    _ ≤ ∑ _S ∈ P.powersetCard j, Y ^ j := by
      apply sum_le_sum
      intro S hS
      obtain ⟨hSP, hcard⟩ := mem_powersetCard.mp hS
      have hh : (∏ i ∈ S, a i) ≤ ∏ _i ∈ S, Y := by
        exact Finset.prod_le_prod (fun i hi => (ha i (hSP hi)).1)
          (fun i hi => (ha i (hSP hi)).2)
      simpa only [prod_const, hcard] using hh
    _ = (P.card.choose j : ℝ) * Y ^ j := by
      simp only [sum_const, card_powersetCard, nsmul_eq_mul]
    _ ≤ (P.card : ℝ) ^ j * Y ^ j := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hY j)
      exact_mod_cast Nat.choose_le_pow P.card j
    _ = _ := (mul_pow _ _ _).symm

lemma truncatedElementary_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y : ℝ) (hY : 0 ≤ Y) (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (R : ℕ) :
    (∑ j ∈ range (R + 1), elementarySymmetric P a j) ≤
      (R + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ R := by
  have hb : 1 ≤ (P.card : ℝ) * Y + 1 := by
    linarith [show 0 ≤ (P.card : ℝ) * Y by positivity]
  calc
    _ ≤ ∑ _j ∈ range (R + 1), ((P.card : ℝ) * Y + 1) ^ R := by
      apply sum_le_sum
      intro j hj
      calc
        _ ≤ ((P.card : ℝ) * Y) ^ j := elementarySymmetric_crude P a Y hY ha j
        _ ≤ ((P.card : ℝ) * Y + 1) ^ j := by gcongr; linarith
        _ ≤ ((P.card : ℝ) * Y + 1) ^ R :=
          pow_le_pow_right₀ hb (Nat.le_of_lt_succ (mem_range.mp hj))
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]

lemma sieveIntersectionError_factor {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (C : ℝ) (N R : ℕ) :
    sieveIntersectionError P (fun S => C / N * ∏ i ∈ S, a i) R =
      C / N * ∑ j ∈ range (R + 1), elementarySymmetric P a j := by
  simp only [sieveIntersectionError, elementarySymmetric, mul_sum]

/-- If an intersection indexed by `S` has normalized CRT error at most
`C * (∏ i∈S, a i) / N`, the whole finite truncation costs this explicit
quantity. In the application `a i` is the selected prime and `C=1` or `3`. -/
theorem sieveIntersectionError_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y C : ℝ) (hY : 0 ≤ Y) (hC : 0 ≤ C)
    (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (N R : ℕ) :
    sieveIntersectionError P (fun S => C / N * ∏ i ∈ S, a i) R ≤
      C / N * (R + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ R := by
  rw [sieveIntersectionError_factor]
  exact (mul_le_mul_of_nonneg_left (truncatedElementary_crude P a Y hY ha R)
    (div_nonneg hC (Nat.cast_nonneg N))).trans_eq (by ring)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveCRT
namespace OAI

/-! Exact CRT factorization of the one- and three-variable local sieve
models. The interval/box errors are kept separate in `ResidueBox`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma FiniteLaw.probability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (e : α ≃ β)
    (hweight : ∀ x, μ.weight x = ν.weight (e x)) (E : β → Prop) :
    μ.probability (fun x => E (e x)) = ν.probability E := by
  unfold FiniteLaw.probability FiniteLaw.average
  simp_rw [hweight]
  exact e.sum_comp (fun y => ν.weight y * if E y then 1 else 0)


lemma uniformZModLaw_crt_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j))) (x : ZMod (∏ i, s i)) :
    (uniformZModLaw (∏ i, s i)).weight x =
      (FiniteLaw.dependentIndependent (fun i => uniformZModLaw (s i))).weight
        (ZMod.prodEquivPi s hcop x) := by
  simp [uniformZModLaw, FiniteLaw.dependentIndependent, one_div,
    prod_inv_distrib, Nat.cast_prod]


/-- CRT evaluates an intersection of one-variable local conditions exactly. -/
theorem sieveCRT_one_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (E : ∀ i, ZMod (s i) → Prop) :
    (uniformZModLaw (∏ i, s i)).probability
      (fun x => ∀ i, E i (ZMod.prodEquivPi s hcop x i)) =
      ∏ i, (uniformZModLaw (s i)).probability (E i) := by
  calc
    _ = (FiniteLaw.dependentIndependent (fun i => uniformZModLaw (s i))).probability
        (fun x => ∀ i, E i (x i)) :=
      FiniteLaw.probability_equiv _ _ (ZMod.prodEquivPi s hcop).toEquiv
        (uniformZModLaw_crt_weight s hcop) (fun x => ∀ i, E i (x i))
    _ = _ := FiniteLaw.dependentIndependent_probability_all
      (fun i => uniformZModLaw (s i)) E


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueSampling
namespace OAI

/-! A fixed finite interval sample space for every sieve intersection.
The modulus may vary with the selected primes, but the actual sample law
in these identities never changes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma uniformFiniteLaw_average {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (uniformFiniteLaw α).average f = uniformAverage f := by
  simp only [FiniteLaw.average, uniformFiniteLaw, ← mul_sum, uniformAverage]
  ring

lemma intervalResidueLaw_average_uniform {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (f : ZMod D → ℝ) :
    (intervalResidueLaw A N hN).average f =
      uniformAverage (fun j : Fin N => f (A + (j.val : ZMod D))) := by
  rw [intervalResidueLaw_average]
  unfold uniformAverage
  rw [Fintype.card_fin]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => f (A + (j : ZMod D))) N).symm




lemma uniformInterval_probability_residues {D N : ℕ} [NeZero D] [NeZero N]
    (A : ZMod D) (E : ZMod D → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E (A + (j.val : ZMod D))) =
      (intervalResidueLaw A N (NeZero.pos N)).probability E := by
  unfold FiniteLaw.probability
  rw [uniformFiniteLaw_average, intervalResidueLaw_average_uniform]

lemma interval_probability_discrepancy {D : ℕ} [NeZero D]
    (A : ZMod D) (N : ℕ) (hN : 0 < N) (E : ZMod D → Prop) :
    |(intervalResidueLaw A N hN).probability E - (uniformZModLaw D).probability E| ≤
      (D : ℝ) / N := by
  have hd := finite_observable_difference (intervalResidueLaw A N hN).weight
    (uniformZModLaw D).weight (fun x => if E x then 1 else 0)
    (fun x => by split_ifs <;> norm_num)
  have hv := intervalResidueLaw_totalVariation A N hN
  change |(intervalResidueLaw A N hN).probability E -
    (uniformZModLaw D).probability E| ≤ _ at hd
  calc
    _ ≤ 2 * finiteTotalVariation (intervalResidueLaw A N hN).weight
        (uniformZModLaw D).weight := hd
    _ ≤ 2 * ((D : ℝ) / (2 * N)) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ = _ := by ring

theorem sieveCRT_one_sample_discrepancy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) :
    |(uniformFiniteLaw (Fin N)).probability
        (fun j => ∀ i, E i (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))) i)) -
      ∏ i, (uniformZModLaw (s i)).probability (E i)| ≤ (∏ i, s i : ℕ) / (N : ℝ) := by
  rw [uniformInterval_probability_residues A
    (fun x => ∀ i, E i (ZMod.prodEquivPi s hcop x i)), ← sieveCRT_one_probability s hcop E]
  exact interval_probability_discrepancy A N (NeZero.pos N) _


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveIntersections
namespace OAI

/-! Exact selected-modulus intersection estimates on a single fixed
interval or cube. These discharge the arithmetic premise of Bonferroni. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma selected_pairwise_coprime {ι : Type*} [DecidableEq ι]
    (s : ι → ℕ) (hcop : Pairwise (fun i j => (s i).Coprime (s j))) (S : Finset ι) :
    Pairwise (fun i j : S => (s i).Coprime (s j)) := by
  intro i j hij
  exact hcop (fun h => hij (Subtype.ext h))

theorem sieve_one_intersection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) (S : Finset ι) :
    |(uniformFiniteLaw (Fin N)).probability
        (eventIntersection (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i))) S) -
      ∏ i ∈ S, (uniformZModLaw (s i)).probability (E i)| ≤
        (∏ i ∈ S, (s i : ℝ)) / N := by
  let q : S → ℕ := fun i => s i
  have hc := selected_pairwise_coprime s hcop S
  have hmap (j : Fin N) (i : S) :
      ZMod.prodEquivPi q hc ((A : ZMod (∏ i, q i)) + (j.val : ZMod (∏ i, q i))) i =
        ((A + j.val : ℕ) : ZMod (s i)) := by
    rw [← Nat.cast_add]
    simp only [ZMod.prodEquivPi_apply, map_natCast]
  have hh := sieveCRT_one_sample_discrepancy q hc (A : ZMod (∏ i, q i)) N
    (fun i => E i)
  simp_rw [hmap] at hh
  have he : (fun j : Fin N => ∀ i : S, E i ((A + j.val : ℕ) : ZMod (s i))) =
      eventIntersection (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i))) S := by
    funext j
    simp only [eventIntersection, Subtype.forall]
  rw [he, Nat.cast_prod] at hh
  rw [← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (uniformZModLaw (s i)).probability (E i)),
    ← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (s i : ℝ))] at hh
  exact hh


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveProducts
namespace OAI

/-! Local-density products for the rough sieve. The only prime information
needed is a lower bound for the ordinary reciprocal sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma one_sub_product_le_exp {ι : Type*} [Fintype ι] (ν : ι → ℝ)
    (hν : ∀ i, ν i ≤ 1) :
    (∏ i, (1 - ν i)) ≤ Real.exp (-(∑ i, ν i)) := by
  calc
    _ ≤ ∏ i, Real.exp (-ν i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact sub_nonneg.mpr (hν i)
      · intro i _
        have hh := Real.add_one_le_exp (-ν i)
        linarith
    _ = Real.exp (∑ i, -ν i) := (Real.exp_sum univ _).symm
    _ = _ := by rw [sum_neg_distrib]


theorem oneForm_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ Real.exp (-(∑ p ∈ P, 1 / (p : ℝ))) := by
  have hp (p : P) : 1 / (p : ℝ) ≤ 1 := by
    have hpr : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hP p p.property
    exact (div_le_one (by linarith : (0 : ℝ) < (p : ℕ))).mpr (by linarith)
  have hh := one_sub_product_le_exp (fun p : P => 1 / (p : ℝ)) hp
  rw [← prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 - 1 / (p : ℝ)),
    ← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 / (p : ℝ))] at hh
  exact hh



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteRoughSieve
namespace OAI

/-! Finite rough-sieve bounds with every intersection error discharged by
CRT on the actual interval sample space. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem finite_interval_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A N : ℕ) [NeZero N] (E : ∀ i, ZMod (s i) → Prop) (r : ℕ) (Y : ℝ)
    (hY : 0 ≤ Y) (hs : ∀ i, (s i : ℝ) ≤ Y) :
    (uniformFiniteLaw (Fin N)).probability
      (avoidsEvents univ (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i)))) ≤
      (∏ i, (1 - (uniformZModLaw (s i)).probability (E i))) +
        elementarySymmetric univ (fun i => (uniformZModLaw (s i)).probability (E i))
          (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) * ((Fintype.card ι : ℝ) * Y + 1) ^ (2 * r) := by
  have hh := finite_independent_sieve_bound (uniformFiniteLaw (Fin N))
    (fun i (j : Fin N) => E i ((A + j.val : ℕ) : ZMod (s i)))
    (fun i => uniformZModLaw (s i)) E r
    (fun S => 1 / (N : ℝ) * ∏ i ∈ S, (s i : ℝ)) (fun S _ _ => by
      exact (sieve_one_intersection s hcop A N E S).trans_eq (by ring))
  apply hh.trans
  gcongr
  simpa only [card_univ] using sieveIntersectionError_crude univ (fun i => (s i : ℝ))
    Y 1 hY zero_le_one (fun i _ => ⟨Nat.cast_nonneg _, hs i⟩) N (2 * r)


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

lemma sievePrimesUpTo_card_le (y : ℝ) (hy : 0 ≤ y) :
    ((sievePrimesUpTo y).card : ℝ) ≤ y := by
  have hs : sievePrimesUpTo y ⊆ Icc 1 ⌊y⌋₊ := by
    intro p hp
    exact mem_Icc.mpr ⟨(sievePrimesUpTo_prime y p hp).pos,
      mem_Iic.mp (mem_filter.mp hp).1⟩
  have hc : (sievePrimesUpTo y).card ≤ ⌊y⌋₊ := by
    simpa using card_le_card hs
  exact (show ((sievePrimesUpTo y).card : ℝ) ≤ (⌊y⌋₊ : ℝ) by exact_mod_cast hc).trans
    (Nat.floor_le hy)

/-- Precisely the prime reciprocal bounds used in the rough sieve, at
`y=exp(L^.99)`. The upper coefficient leaves room below `5/4`. -/
theorem PrimeReciprocalInput.rough_scale (hM : PrimeReciprocalInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ L : ℝ in atTop,
      (99 / 100 : ℝ) * Real.log L - C ≤
        ∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ) ∧
      (∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ)) ≤
        (5 / 4 : ℝ) * Real.log L := by
  obtain ⟨C, hC⟩ := hM
  have hC₀ : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨C, hC₀, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp (4 * C + 1))] with L hL
  have hL₁ : 1 ≤ L := (Real.one_le_exp (by linarith)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL₁
  have hlog : 4 * C + 1 ≤ Real.log L := by
    rw [← Real.log_exp (4 * C + 1)]
    exact Real.log_le_log (Real.exp_pos _) hL
  have hX : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL₁ (by norm_num)
  have hy : 2 ≤ Real.exp (L ^ (99 / 100 : ℝ)) := by
    linarith [Real.add_one_le_exp (L ^ (99 / 100 : ℝ))]
  have hm := abs_le.mp (hC (Real.exp (L ^ (99 / 100 : ℝ))) hy)
  rw [Real.log_exp, Real.log_rpow hLp] at hm
  constructor <;> linarith [Real.log_nonneg hL₁]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughSieveProbability
namespace OAI

/-! The finite sieve applied to the actual one- and four-form rough events.
Only the classical reciprocal-prime estimates remain in the quantitative
bounds; all finite local and intersection calculations are proved. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma primeSet_pairwise_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
  intro p q hpq
  exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
    (fun h => hpq (Subtype.ext h))





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveScale
namespace OAI

/-! The logarithmic truncation length is negligible compared with the
physical interval exponent in the finite rough sieve. -/

namespace TwoPointCorrelations

open _root_.Filter

/-- Any fixed `exp(O(L^.99 log L))` counting cost is absorbed by the
interval length `exp(L^.995)`, with the explicit power needed below. -/
theorem eventually_sieve_boundary_exponent (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (K * L ^ (99 / 100 : ℝ) * Real.log L - L ^ (199 / 200 : ℝ)) ≤
        L ^ (-100 : ℝ) := by
  have hden : 0 < K + 100 := by linarith
  have hs := (isLittleO_log_rpow_atTop
    (show 0 < (1 / 200 : ℝ) by norm_num)).bound (show 0 < 1 / (K + 100) by positivity)
  filter_upwards [eventually_ge_atTop 1, hs] with L hL hsL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hsL
  have hc : Real.log L * (K + 100) ≤ L ^ (1 / 200 : ℝ) := by
    apply (le_div_iff₀ hden).mp
    convert (preTransparency := .instances) hsL using 1
    ring
  have hm := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg hLp.le (99 / 100 : ℝ))
  have he : L ^ (1 / 200 : ℝ) * L ^ (99 / 100 : ℝ) = L ^ (199 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  rw [he] at hm
  have hx : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hlogx : 100 * Real.log L ≤ 100 * L ^ (99 / 100 : ℝ) * Real.log L := by
    have hh := mul_le_mul_of_nonneg_right hx (show 0 ≤ 100 * Real.log L by positivity)
    nlinarith only [hh]
  rw [Real.rpow_def_of_pos hLp (-100 : ℝ)]
  apply Real.exp_le_exp.mpr
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveBoundaryScale
namespace OAI

/-! Explicit accounting for the finite CRT boundary term. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma sieve_boundary_numerator (X T C C₀ B : ℝ) (R : ℕ)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hB : 0 ≤ B) (hBexp : B ≤ Real.exp (3 * X)) (hR : (R : ℝ) ≤ C * T) :
    C₀ * (R + 1 : ℕ) * B ^ R ≤ Real.exp ((C₀ + 4 * C) * X * T) := by
  have hXT : 1 ≤ X * T := by nlinarith
  have hpow : B ^ R ≤ Real.exp ((R : ℝ) * (3 * X)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hB hBexp R
  have hRexp : (R + 1 : ℕ) ≤ Real.exp (R : ℝ) := by
    exact_mod_cast Real.add_one_le_exp (R : ℝ)
  have hCexp : C₀ ≤ Real.exp C₀ := by linarith [Real.add_one_le_exp C₀]
  calc
    _ ≤ Real.exp C₀ * Real.exp (R : ℝ) * Real.exp ((R : ℝ) * (3 * X)) := by
      gcongr
    _ = Real.exp (C₀ + (R : ℝ) + (R : ℝ) * (3 * X)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h₀ : C₀ ≤ C₀ * (X * T) := by nlinarith
      have h₁ : (R : ℝ) ≤ C * X * T := by
        have hh := mul_le_mul_of_nonneg_left hX (mul_nonneg hC (by linarith : 0 ≤ T))
        nlinarith
      have h₂ := mul_le_mul_of_nonneg_right hR (show 0 ≤ 3 * X by linarith)
      nlinarith

lemma sieve_base_le_exp (X Y n : ℝ) (hX : 1 ≤ X)
    (hY : 0 ≤ Y) (_hn : 0 ≤ n) (hnY : n ≤ Y) (hYexp : Y ≤ Real.exp X) :
    n * Y + 1 ≤ Real.exp (3 * X) := by
  have he : 2 ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
  have he₂ : 1 ≤ Real.exp (2 * X) := Real.one_le_exp (by linarith)
  calc
    _ ≤ Real.exp X * Real.exp X + 1 := by
      gcongr
      exact hnY.trans hYexp
    _ = Real.exp (2 * X) + 1 := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp (2 * X) * Real.exp X := by nlinarith
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniformly in the modulus cutoff, number of moduli and logarithmic
truncation order, the literal finite boundary term is `O(L^-100)`. -/
theorem eventually_sieve_boundary_cost (C C₀ : ℝ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (Y n : ℝ) (N R : ℕ),
      0 ≤ Y → 0 ≤ n → n ≤ Y → Y ≤ Real.exp (L ^ (99 / 100 : ℝ)) →
      (R : ℝ) ≤ C * Real.log L →
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      C₀ / (N : ℝ) * (R + 1 : ℕ) * (n * Y + 1) ^ R ≤ L ^ (-100 : ℝ) := by
  have hK : 0 ≤ C₀ + 4 * C + 1 := by positivity
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_sieve_boundary_exponent (C₀ + 4 * C + 1) hK] with L hL hsmall
  intro Y n N R hY hn hnY hYexp hR hN
  have hL₁ : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL₁
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  have hX : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL₁ (by norm_num)
  have hXT : 1 ≤ L ^ (99 / 100 : ℝ) * Real.log L := by nlinarith
  have hnum := sieve_boundary_numerator (L ^ (99 / 100 : ℝ)) (Real.log L) C C₀
    (n * Y + 1) R hX hlog hC hC₀ (by positivity)
    (sieve_base_le_exp _ _ _ hX hY hn hnY hYexp) hR
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hdiv : (1 / (N : ℝ)) ≤ 2 * Real.exp (-(L ^ (199 / 200 : ℝ))) := by
    apply (div_le_iff₀ hNp).mpr
    have hh := mul_le_mul_of_nonneg_left hN
      (show 0 ≤ 2 * Real.exp (-(L ^ (199 / 200 : ℝ))) by positivity)
    have hc : (2 * Real.exp (-(L ^ (199 / 200 : ℝ)))) *
        ((1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ))) = 1 := by
      calc
        _ = Real.exp (-(L ^ (199 / 200 : ℝ))) *
            Real.exp (L ^ (199 / 200 : ℝ)) := by ring
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [hc] at hh
    nlinarith only [hh]
  calc
    _ = (C₀ * (R + 1 : ℕ) * (n * Y + 1) ^ R) * (1 / (N : ℝ)) := by ring
    _ ≤ Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
        (2 * Real.exp (-(L ^ (199 / 200 : ℝ)))) := by gcongr
    _ ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) *
        Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
          Real.exp (-(L ^ (199 / 200 : ℝ))) := by
      have he : 2 ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) := by
        linarith [Real.add_one_le_exp (L ^ (99 / 100 : ℝ) * Real.log L)]
      calc
        _ = 2 * (Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
            Real.exp (-(L ^ (199 / 200 : ℝ)))) := by ring
        _ ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) *
            (Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
              Real.exp (-(L ^ (199 / 200 : ℝ)))) :=
          mul_le_mul_of_nonneg_right he (by positivity)
        _ = _ := by ring
    _ = Real.exp ((C₀ + 4 * C + 1) * L ^ (99 / 100 : ℝ) * Real.log L -
        L ^ (199 / 200 : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := hsmall

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting
namespace OAI

/-! Finite descriptions used by the reciprocal crude count. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical









/-- A finite union bound for arbitrary events under the concrete finite law. -/
theorem FiniteLaw.probability_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (μ : FiniteLaw A) (E : I → A → Prop) :
    μ.probability (fun x => ∃ i, E i x) ≤ ∑ i, μ.probability (E i) := by
  classical
  unfold FiniteLaw.probability
  rw [← μ.average_sum]
  apply μ.average_mono
  intro x
  by_cases hx : ∃ i, E i x
  · obtain ⟨i, hi⟩ := hx
    simp only [if_pos (show ∃ j, E j x from ⟨i, hi⟩)]
    apply (le_trans ?_ (single_le_sum (f := fun i => if E i x then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)))
    simp [hi]
  · simp only [if_neg hx]
    exact sum_nonneg (fun i _ => by split_ifs <;> norm_num)




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

lemma mrtPrimeBand_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) =
      (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
        ∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ) := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => (1 : ℝ) / p) (mrt_sievePrimesUpTo_mono hPQ)

/-- Uniform bounded-error reciprocal mass for every positive prime band. -/
theorem mrt_prime_band_mertens : ∃ C : ℝ, 0 ≤ C ∧
    ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      |(∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) -
        (Real.log (Real.log Q) - Real.log (Real.log P))| ≤ C := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨2 * C, by positivity, ?_⟩
  intro P Q hP hPQ
  rw [mrtPrimeBand_mass hPQ]
  have hQ := hP.trans hPQ
  have he : (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
      (∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) -
      (Real.log (Real.log Q) - Real.log (Real.log P)) =
      ((∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) - Real.log (Real.log Q)) -
      ((∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) - Real.log (Real.log P)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hC Q hQ, hC P hP])

theorem mrt_prime_band_product : ∃ C : ℝ, 0 < C ∧
    ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      Real.exp (-(∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ))) ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC0, hC⟩ := mrt_prime_band_mertens
  refine ⟨Real.exp C, Real.exp_pos C, ?_⟩
  intro P Q hP hPQ
  have hP1 : 1 < P := lt_of_lt_of_le (by norm_num) hP
  have hQ1 : 1 < Q := hP1.trans_le hPQ
  have hm := (abs_le.mp (hC P Q hP hPQ)).1
  calc
    _ ≤ Real.exp (C + Real.log (Real.log P) - Real.log (Real.log Q)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_log (Real.log_pos hP1),
        Real.exp_log (Real.log_pos hQ1)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMissingBandSieve
namespace OAI

/-! The finite missing-band sieve in MRT, with its full Bonferroni and
interval-boundary errors.  CRT, not an independence assumption on integers,
supplies every intersection estimate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.BigOperators

theorem mrt_prime_avoidance_probability (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (A N : ℕ) [NeZero N] (r : ℕ) (Y : ℝ)
    (hY : 0 ≤ Y) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y) :
    (uniformFiniteLaw (Fin N)).probability (fun j => mrtPrimeAvoids P (A + j.val)) ≤
      Real.exp (-(∑ p ∈ P, 1 / (p : ℝ))) +
        Real.exp (2 * ∑ p ∈ P, 1 / (p : ℝ)) / (2 : ℝ) ^ (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ (2 * r) := by
  let (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  have hh := finite_interval_sieve (fun p : P => (p : ℕ)) (primeSet_pairwise_coprime P hP)
    A N (fun _ x => x = 0) r Y hY (fun p => hmax p p.property)
  have he : avoidsEvents univ (fun p : P => fun j : Fin N =>
      ((A + j.val : ℕ) : ZMod (p : ℕ)) = 0) =
      (fun j => mrtPrimeAvoids P (A + j.val)) := by
    funext j
    simp only [avoidsEvents, mem_univ, forall_true_left, mrtPrimeAvoids,
      Subtype.forall, ZMod.natCast_eq_zero_iff]
  simp only [he, oneFormBadDensity, Fintype.card_coe] at hh
  have ht := elementarySymmetric_exp_bound (univ : Finset P)
    (fun p => 1 / (p : ℝ)) (fun p _ => by positivity) (2 * r + 1) 2 (by norm_num)
  have hp := oneForm_product_bound P (fun p hp => (hP p hp).two_le)
  rw [prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)] at hp
  have hsum : (∑ p : P, 1 / (p : ℝ)) = ∑ p ∈ P, 1 / (p : ℝ) :=
    (sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => (1 : ℝ) / p)).symm
  rw [hsum] at ht
  exact hh.trans (add_le_add (add_le_add hp ht) le_rfl)

/-- Mertens supplies the main term `log P/log Q`; both finite-sieve errors
remain explicit for choosing the typical-factorization parameters. -/
theorem mrt_missing_band_probability : ∃ C : ℝ, 0 < C ∧
    ∀ (P Q : ℝ), 2 ≤ P → P ≤ Q → ∀ (A N : ℕ) [NeZero N] (r : ℕ),
    (uniformFiniteLaw (Fin N)).probability
      (fun j => mrtPrimeAvoids (mrtPrimeBand P Q) (A + j.val)) ≤
      C * Real.log P / Real.log Q +
        Real.exp (2 * ∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) / (2 : ℝ) ^ (2 * r + 1) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) *
          (((mrtPrimeBand P Q).card : ℝ) * Q + 1) ^ (2 * r) := by
  obtain ⟨C, hC, hprod⟩ := mrt_prime_band_product
  refine ⟨C, hC, ?_⟩
  intro P Q hP hPQ A N _ r
  have hQ : 0 ≤ Q := (by linarith : (0 : ℝ) ≤ P).trans hPQ
  have hh := mrt_prime_avoidance_probability (mrtPrimeBand P Q)
    (fun _ hp => mrtPrimeBand_prime hp) A N r Q hQ
    (fun _ hp => (mrtPrimeBand_bounds (by linarith) hQ hp).2)
  exact hh.trans (add_le_add (add_le_add (hprod P Q hP hPQ) le_rfl) le_rfl)

/-- Failure of typical factorization is a union of the literal missing-band
events, so the numerical single-band bounds add without any independence. -/
theorem mrtTypical_missing_union {ι α : Type*} [Fintype ι] [Fintype α]
    (P : ι → Finset ℕ) (μ : FiniteLaw α) (n : α → ℕ) :
    μ.probability (fun x => ¬mrtTypical univ P (n x)) ≤
      ∑ i, μ.probability (fun x => mrtPrimeAvoids (P i) (n x)) := by
  have he : (fun x => ¬mrtTypical univ P (n x)) =
      (fun x => ∃ i, mrtPrimeAvoids (P i) (n x)) := by
    funext x
    simp only [mrtTypical, mem_univ, forall_true_left, mrtPrimeAvoids]
    push Not
    rfl
  rw [he]
  exact μ.probability_exists_le _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalSieveScale
namespace OAI

/-! Uniform finite-interval error in the sieve for MRT's prime bands.
The prime mass uses the proved Mertens theorem; the remaining errors are
the explicit Bonferroni and CRT boundary errors. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma mrt_exponential_sieve_tail (M L : ℝ) (j : ℕ) (hL : 1 ≤ L)
    (hM : M ≤ 5 * Real.log L) (hj : 220 * Real.log L ≤ (j : ℝ)) :
    Real.exp (2 * M) / (2 : ℝ) ^ j ≤ L ^ (-100 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    linarith
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num),
    ← Real.exp_sub, Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have horder : 110 * Real.log L ≤ (j : ℝ) * Real.log 2 := by
    calc
      _ = (220 * Real.log L) * (1 / 2 : ℝ) := by ring
      _ ≤ (j : ℝ) * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hj (by norm_num)
      _ ≤ (j : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg j)
  nlinarith

lemma mrt_prime_band_card_le (P Q : ℝ) (hQ : 0 ≤ Q) :
    ((mrtPrimeBand P Q).card : ℝ) ≤ Q := by
  have hc : (mrtPrimeBand P Q).card ≤ (sievePrimesUpTo Q).card :=
    card_le_card sdiff_subset
  exact (show ((mrtPrimeBand P Q).card : ℝ) ≤ (sievePrimesUpTo Q).card by
    exact_mod_cast hc).trans (sievePrimesUpTo_card_le Q hQ)

/-- A single prime band has its Mertens main term, uniformly in the
interval's starting point, plus an error smaller than `2 L^-100`. -/
theorem mrt_eventually_missing_band : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      Q ≤ Real.exp (L ^ (99 / 100 : ℝ)) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand P Q) (A + j.val)) ≤
        C * Real.log P / Real.log Q + 2 * L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hband⟩ := mrt_missing_band_probability
  obtain ⟨CM, _, hmass⟩ := primeReciprocalInput.rough_scale
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1), hmass,
    eventually_sieve_boundary_cost 222 1 (by norm_num) (by norm_num)] with
      L hL hmass hboundary
  intro P Q hP hPQ hQmax A N _ hN
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  let r : ℕ := ⌈110 * Real.log L⌉₊
  have hrlo : 110 * Real.log L ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < 110 * Real.log L + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hR : ((2 * r : ℕ) : ℝ) ≤ 222 * Real.log L := by
    push_cast
    nlinarith
  have hj : 220 * Real.log L ≤ ((2 * r + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hsub : mrtPrimeBand P Q ⊆
      sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))) :=
    sdiff_subset.trans (mrt_sievePrimesUpTo_mono hQmax)
  have hM : (∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) ≤ 5 * Real.log L := by
    calc
      _ ≤ ∑ p ∈ sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ))), 1 / (p : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ ≤ (5 / 4 : ℝ) * Real.log L := hmass.2
      _ ≤ _ := by nlinarith
  have ht := mrt_exponential_sieve_tail _ L (2 * r + 1) hL1 hM hj
  have hb := hboundary Q ((mrtPrimeBand P Q).card : ℝ) N (2 * r) hQ0
    (Nat.cast_nonneg _) (mrt_prime_band_card_le P Q hQ0) hQmax hR hN
  have hh := hband P Q hP hPQ A N r
  simp only [one_div] at hb hh ht
  linarith

/-- The uniform band errors add over the actual family of bands; the
main term is the sum of their logarithmic endpoint ratios. -/
theorem mrt_eventually_atypical_family : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] (P Q : ι → ℝ),
      (∀ i, 2 ≤ P i) → (∀ i, P i ≤ Q i) →
      (∀ i, Q i ≤ Real.exp (L ^ (99 / 100 : ℝ))) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun j => ¬mrtTypical univ (fun i => mrtPrimeBand (P i) (Q i)) (A + j.val)) ≤
        C * ∑ i, Real.log (P i) / Real.log (Q i) +
          2 * Fintype.card ι * L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hband⟩ := mrt_eventually_missing_band
  refine ⟨C, hC, ?_⟩
  filter_upwards [hband] with L hband
  intro ι _ P Q hP hPQ hQ A N _ hN
  calc
    _ ≤ ∑ i, (uniformFiniteLaw (Fin N)).probability
        (fun j => mrtPrimeAvoids (mrtPrimeBand (P i) (Q i)) (A + j.val)) :=
      mrtTypical_missing_union _ _ _
    _ ≤ ∑ i, (C * Real.log (P i) / Real.log (Q i) + 2 * L ^ (-100 : ℝ)) :=
      sum_le_sum (fun i _ => hband (P i) (Q i) (hP i) (hPQ i) (hQ i) A N hN)
    _ = _ := by
      simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro i _
        ring
      · ring

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




lemma mrtBandUpper_one (Q : ℝ) (hQ : 0 < Q) : mrtBandUpper Q 1 = Q := by
  simp [mrtBandUpper, Real.exp_log hQ]

lemma mrt_band_log_ratio (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j) (hQ : 1 < Q) :
    Real.log (mrtBandLower P Q j) / Real.log (mrtBandUpper Q j) =
      (Real.log P / Real.log Q) / (j : ℝ) ^ 2 := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hq0 : Real.log Q ≠ 0 := (Real.log_pos hQ).ne'
  have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
    rw [← pow_succ]
    congr 1
    omega
  simp only [mrtBandLower, mrtBandUpper, Real.log_exp]
  rw [pow_add, hpow]
  field_simp [hj0, hq0]

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

lemma mrt_band_index_le_log_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hlogQ : 1 ≤ Real.log Q) : (j : ℝ) ≤ Real.log (mrtBandUpper Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  simp only [mrtBandUpper, Real.log_exp]
  calc
    (j : ℝ) ≤ (j : ℝ) ^ (4 * j + 2) := by
      simpa using pow_le_pow_right₀ hj1 (show 1 ≤ 4 * j + 2 by omega)
    _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by
      have hh := one_le_pow₀ (n := j) hlogQ
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ j) (4 * j + 2)]

lemma mrt_band_ratio_sum (P Q : ℝ) (J : ℕ) (hP : 1 ≤ P) (hQ : 1 < Q) :
    (∑ j ∈ Icc 1 J, Real.log (mrtBandLower P Q j) /
      Real.log (mrtBandUpper Q j)) ≤ 2 * Real.log P / Real.log Q := by
  have hr : 0 ≤ Real.log P / Real.log Q := div_nonneg
    (Real.log_nonneg hP) (Real.log_pos hQ).le
  have hs : (∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have he : Icc 1 J = Ioo 0 (J + 1) := by ext j; simp; omega
    rw [he]
    simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1))
  calc
    _ = (Real.log P / Real.log Q) * ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [mrt_band_log_ratio P Q j (mem_Icc.mp hj).1 hQ]
      ring
    _ ≤ (Real.log P / Real.log Q) * 2 := mul_le_mul_of_nonneg_left hs hr
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalDensity
namespace OAI

/-! The dense typical set in MRT Lemma 2.2, with a uniform translated
finite-interval formulation.  No fundamental-lemma-of-sieve input remains:
the finite Bonferroni estimate and the proved Mertens bound suffice here. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma mrt_band_count_le_scale (Q L : ℝ) (J : ℕ) (hL : 1 ≤ L)
    (hlogQ : 1 ≤ Real.log Q)
    (hmax : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L ^ (99 / 100 : ℝ))) :
    (J : ℝ) ≤ L := by
  by_cases hJ : J = 0
  · simp [hJ, le_trans zero_le_one hL]
  have hJ1 : 1 ≤ J := by omega
  calc
    (J : ℝ) ≤ Real.log (mrtBandUpper Q J) :=
      mrt_band_index_le_log_upper Q J hJ1 hlogQ
    _ ≤ Real.log (Real.exp (L ^ (99 / 100 : ℝ))) :=
      Real.log_le_log (Real.exp_pos _)
        (hmax J (mem_Icc.mpr ⟨hJ1, le_rfl⟩))
    _ = L ^ (99 / 100 : ℝ) := Real.log_exp _
    _ ≤ L := Real.rpow_le_self_of_one_le hL (by norm_num)

lemma mrt_band_small_error (P Q L : ℝ) (J : ℕ) (hL : 1 ≤ L)
    (hP : 2 ≤ P) (hQ : 1 < Q) (hlogQ : Real.log Q ≤ L) (hJ : (J : ℝ) ≤ L) :
    2 * J * L ^ (-100 : ℝ) ≤ 4 * Real.log P / Real.log Q := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlP : (1 / 2 : ℝ) ≤ Real.log P := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    have hmono := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hP
    norm_num at hh
    linarith
  have hp : L ^ (-100 : ℝ) ≤ (L ^ 2)⁻¹ := by
    calc
      _ ≤ L ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = _ := by rw [Real.rpow_neg hLp.le, Real.rpow_two]
  calc
    _ ≤ 2 * L * (L ^ 2)⁻¹ := by gcongr
    _ = 2 / L := by field_simp
    _ ≤ _ := by
      apply (div_le_div_iff₀ hLp (Real.log_pos hQ)).mpr
      nlinarith

/-- Every family of the explicit MRT bands below the allowed upper
cutoff has missing density `O(log P / log Q)`, uniformly in translation.
The family need not be chosen maximal. -/
theorem mrt_typical_density : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L ^ (99 / 100 : ℝ))) →
      ∀ (A N : ℕ) [NeZero N],
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical univ
          (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} =>
            mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) (A + n.val)) ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC, hfamily⟩ := mrt_eventually_atypical_family
  refine ⟨2 * C + 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1, hfamily] with L hL hfamily
  intro P Q J hP hPQ hlogQ hmax A N _ hN
  have hQ : 1 < Q := lt_of_lt_of_le (by norm_num) (hP.trans hPQ)
  let ι := {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)}
  have hh := hfamily ι (fun j => mrtBandLower P Q j) (fun j => mrtBandUpper Q j)
    (fun j => (mrt_band_endpoints P Q j (mem_Icc.mp j.property).1 hP hPQ hlogQ).1)
    (fun j => (mrt_band_endpoints P Q j (mem_Icc.mp j.property).1 hP hPQ hlogQ).2)
    (fun j => hmax j j.property) A N hN
  have hcard : Fintype.card ι = J := by simp [ι]
  have hsum : (∑ j : ι, Real.log (mrtBandLower P Q j) /
      Real.log (mrtBandUpper Q j)) =
      ∑ j ∈ Icc 1 J, Real.log (mrtBandLower P Q j) /
        Real.log (mrtBandUpper Q j) := by
    exact (sum_subtype (p := fun j : ℕ => j ∈ Icc 1 J) (Icc 1 J)
      (fun _ => Iff.rfl) (fun j => Real.log (mrtBandLower P Q j) /
        Real.log (mrtBandUpper Q j))).symm
  rw [hcard, hsum] at hh
  have hmain := mrt_band_ratio_sum P Q J (by linarith) hQ
  have hcount := mrt_band_count_le_scale Q L J hL hlogQ hmax
  by_cases hJ : J = 0
  · have hnonneg : 0 ≤ (2 * C + 4) * Real.log P / Real.log Q := by
      exact div_nonneg (mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith))) (Real.log_pos hQ).le
    exact hh.trans (by simpa [hJ] using hnonneg)
  have hQmax : Q ≤ Real.exp (L ^ (99 / 100 : ℝ)) := by
    have hx := hmax 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)
    rwa [mrtBandUpper_one Q (by linarith)] at hx
  have hlogmax : Real.log Q ≤ L := by
    calc
      _ ≤ Real.log (Real.exp (L ^ (99 / 100 : ℝ))) :=
        Real.log_le_log (by linarith) hQmax
      _ = L ^ (99 / 100 : ℝ) := Real.log_exp _
      _ ≤ L := Real.rpow_le_self_of_one_le hL (by norm_num)
  have herr := mrt_band_small_error P Q L J hL hP hQ hlogmax hcount
  have hscaled := mul_le_mul_of_nonneg_left hmain hC.le
  convert (preTransparency := .instances) hh.trans (add_le_add hscaled herr) using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCommonFinalBand
namespace OAI

/-! One final original band works for both dyadic polynomials at N and
2N. The lower-endpoint margin absorbs the change in log-log scale, while
the upper endpoint remains below the smaller square-root cutoff. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset




lemma mrt_common_density_power {L : ℝ} (hL : 1 ≤ L) :
    Real.sqrt L ≤ L^(99/100:ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)





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

/-- The explicit natural-indexed bands have the same density estimate on
every translated interval of length at least the original outer cutoff. -/
theorem mrt_actual_band_interval_density :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P Q : ℝ) (J : ℕ), 2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤
        Real.exp (Real.sqrt (Real.log (X:ℝ))/2)) →
      ∀ (A N : ℕ) [NeZero N], X ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
          (A+n.val)) ≤ C*Real.log P/Real.log Q := by
  obtain ⟨C,hC,hd⟩ := mrt_typical_density
  have hlog : Tendsto (fun X:ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C,hC,?_⟩
  filter_upwards [hlog.eventually hd,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop (2:ℕ)]
    with X hd hL hX
  intro P Q J hP hPQ hQ hu A N _ hXN
  have hXp : (0:ℝ)< X := by exact_mod_cast (by omega : 0< X)
  have hu' : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤
      Real.exp ((Real.log (X:ℝ))^(99/100:ℝ)) := by
    intro j hj
    apply (hu j hj).trans (Real.exp_le_exp.mpr ?_)
    exact (by nlinarith [Real.sqrt_nonneg (Real.log (X:ℝ))] :
      Real.sqrt (Real.log (X:ℝ))/2 ≤ Real.sqrt (Real.log (X:ℝ))).trans
      (mrt_common_density_power hL)
  have hsize : (1/2:ℝ)*Real.exp ((Real.log (X:ℝ))^(199/200:ℝ)) ≤ N := by
    calc
      _ ≤ Real.exp ((Real.log (X:ℝ))^(199/200:ℝ)) := by
        nlinarith [Real.exp_pos ((Real.log (X:ℝ))^(199/200:ℝ))]
      _ ≤ Real.exp (Real.log (X:ℝ)) := Real.exp_le_exp.mpr
        (Real.rpow_le_self_of_one_le hL (by norm_num))
      _ = (X:ℝ) := Real.exp_log hXp
      _ ≤ N := by exact_mod_cast hXN
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  have heq (n:ℕ) : mrtTypical univ
      (fun j : {j:ℕ // j ∈ (Icc 1 J : Finset ℕ)} => V j) n ↔
      mrtTypical (Icc 1 J) V n := by simp [mrtTypical]
  have hp := hd P Q J hP hPQ hQ hu' A N hsize
  change (uniformFiniteLaw (Fin N)).probability
    (fun n => ¬mrtTypical univ
      (fun j : {j:ℕ // j ∈ (Icc 1 J : Finset ℕ)} => V j) (A+n.val)) ≤ _ at hp
  simpa only [heq] using hp


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_actual_band_interval_density := @OAI.TwoPointCorrelations.mrt_actual_band_interval_density
