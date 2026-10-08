-- Prove2me | solution 1 for OAI.TwoPointCorrelations.PrimeReciprocalInput.qualitative_rough_fourier
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:39:49.035422+00:00
-- url     : https://prove2.me/submissions/ccafa167-524e-49e9-b03e-b806e287a8f2

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

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



lemma average_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.average f := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))

lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))









lemma average_product (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α × β → ℝ) :
    (μ.product ν).average f = μ.average (fun x => ν.average (fun y => f (x, y))) := by
  simp only [average, product, Fintype.sum_prod_type, mul_sum, mul_assoc]



lemma probability_nonneg (μ : FiniteLaw α) (E : α → Prop) : 0 ≤ μ.probability E := by
  classical
  apply μ.average_nonneg
  intro x
  split_ifs <;> norm_num

lemma probability_le_one (μ : FiniteLaw α) (E : α → Prop) : μ.probability E ≤ 1 := by
  classical
  apply (μ.average_mono (g := fun _ => 1) ?_).trans_eq (μ.average_const 1)
  intro x
  split_ifs <;> norm_num


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


lemma uniformAverage_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformAverage (fun x : α × β => f x.1 x.2) =
      uniformAverage (fun x => uniformAverage (f x)) := by
  unfold uniformAverage
  rw [Fintype.sum_prod_type', Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div]
  rw [div_div]
  congr 1
  ring






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

lemma finiteTotalVariation_product {α β : Type*} [Fintype α] [Fintype β]
    (μ₁ ν₁ : FiniteLaw α) (μ₂ ν₂ : FiniteLaw β) :
    finiteTotalVariation (μ₁.product μ₂).weight (ν₁.product ν₂).weight ≤
      finiteTotalVariation μ₁.weight ν₁.weight + finiteTotalVariation μ₂.weight ν₂.weight := by
  have hpoint (x : α) (y : β) :
      |μ₁.weight x * μ₂.weight y - ν₁.weight x * ν₂.weight y| ≤
        |μ₁.weight x - ν₁.weight x| * μ₂.weight y +
          ν₁.weight x * |μ₂.weight y - ν₂.weight y| := by
    calc
      _ = |(μ₁.weight x - ν₁.weight x) * μ₂.weight y +
          ν₁.weight x * (μ₂.weight y - ν₂.weight y)| := by congr 1; ring
      _ ≤ |(μ₁.weight x - ν₁.weight x) * μ₂.weight y| +
          |ν₁.weight x * (μ₂.weight y - ν₂.weight y)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (μ₂.nonneg y),
        abs_of_nonneg (ν₁.nonneg x)]
  have hsum := sum_le_sum (fun x (_ : x ∈ (univ : Finset α)) =>
    sum_le_sum (fun y (_ : y ∈ (univ : Finset β)) => hpoint x y))
  have heq : (∑ x : α, ∑ y : β,
      (|μ₁.weight x - ν₁.weight x| * μ₂.weight y +
        ν₁.weight x * |μ₂.weight y - ν₂.weight y|)) =
      (∑ x, |μ₁.weight x - ν₁.weight x|) +
        ∑ y, |μ₂.weight y - ν₂.weight y| := by
    simp only [sum_add_distrib, ← mul_sum, μ₂.total, mul_one]
    rw [← sum_mul, ν₁.total, one_mul]
  rw [heq] at hsum
  unfold finiteTotalVariation
  simp only [FiniteLaw.product, Fintype.sum_prod_type]
  exact (div_le_div_of_nonneg_right hsum (by norm_num)).trans_eq (add_div _ _ 2)



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



theorem residueCube_totalVariation {D : ℕ} [NeZero D]
    (A : ZMod D × ZMod D × ZMod D) (N : ℕ) (hN : 0 < N) :
    finiteTotalVariation (residueCubeLaw A N hN).weight (uniformResidueCubeLaw D).weight ≤
      3 * D / (2 * (N : ℝ)) := by
  have h₁ := intervalResidueLaw_totalVariation A.1 N hN
  have h₂ := intervalResidueLaw_totalVariation A.2.1 N hN
  have h₃ := intervalResidueLaw_totalVariation A.2.2 N hN
  have h₂₃ := finiteTotalVariation_product
    (intervalResidueLaw A.2.1 N hN) (uniformZModLaw D)
    (intervalResidueLaw A.2.2 N hN) (uniformZModLaw D)
  have h₁₂₃ := finiteTotalVariation_product
    (intervalResidueLaw A.1 N hN) (uniformZModLaw D)
    ((intervalResidueLaw A.2.1 N hN).product (intervalResidueLaw A.2.2 N hN))
    ((uniformZModLaw D).product (uniformZModLaw D))
  change finiteTotalVariation
    ((intervalResidueLaw A.1 N hN).product
      ((intervalResidueLaw A.2.1 N hN).product (intervalResidueLaw A.2.2 N hN))).weight
    ((uniformZModLaw D).product ((uniformZModLaw D).product (uniformZModLaw D))).weight ≤ _
  calc
    _ ≤ 3 * ((D : ℝ) / (2 * N)) := by linarith
    _ = _ := by ring

/-- Any simultaneous collection of congruence conditions has the same
`3D/N` box error; the number of allowed residue vectors is irrelevant. -/
theorem residueCube_probability_discrepancy {D : ℕ} [NeZero D]
    (A : ZMod D × ZMod D × ZMod D) (N : ℕ) (hN : 0 < N)
    (E : (ZMod D × ZMod D × ZMod D) → Prop) :
    |(residueCubeLaw A N hN).probability E - (uniformResidueCubeLaw D).probability E| ≤
      3 * D / (N : ℝ) := by
  have hb := finite_observable_difference (residueCubeLaw A N hN).weight
    (uniformResidueCubeLaw D).weight (fun x => if E x then 1 else 0)
    (fun x => by split_ifs <;> norm_num)
  have hv := residueCube_totalVariation A N hN
  change |(residueCubeLaw A N hN).probability E -
    (uniformResidueCubeLaw D).probability E| ≤ _ at hb
  calc
    _ ≤ 2 * finiteTotalVariation (residueCubeLaw A N hN).weight
        (uniformResidueCubeLaw D).weight := hb
    _ ≤ 2 * (3 * D / (2 * (N : ℝ))) := mul_le_mul_of_nonneg_left hv (by norm_num)
    _ = _ := by ring

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



lemma fourFormBad_indicator {D : ℕ} [NeZero D] (x y z : ZMod D) :
    (if fourFormBad (x, y, z) then (1 : ℝ) else 0) =
      zeroResidueIndicator x + zeroResidueIndicator y + zeroResidueIndicator z +
      zeroResidueIndicator (x + y - z) -
      (zeroResidueIndicator x * zeroResidueIndicator y +
        zeroResidueIndicator x * zeroResidueIndicator z +
        zeroResidueIndicator x * zeroResidueIndicator (x + y - z) +
        zeroResidueIndicator y * zeroResidueIndicator z +
        zeroResidueIndicator y * zeroResidueIndicator (x + y - z) +
        zeroResidueIndicator z * zeroResidueIndicator (x + y - z)) +
      (zeroResidueIndicator x * zeroResidueIndicator y * zeroResidueIndicator z +
        zeroResidueIndicator x * zeroResidueIndicator y *
          zeroResidueIndicator (x + y - z) +
        zeroResidueIndicator x * zeroResidueIndicator z *
          zeroResidueIndicator (x + y - z) +
        zeroResidueIndicator y * zeroResidueIndicator z *
          zeroResidueIndicator (x + y - z)) -
      zeroResidueIndicator x * zeroResidueIndicator y * zeroResidueIndicator z *
        zeroResidueIndicator (x + y - z) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hz : z = 0 <;>
    by_cases hw : x + y - z = 0 <;>
    simp only [fourFormBad, zeroResidueIndicator, hx, hy, hz, hw,
      ite_true, ite_false, true_or, false_or, or_true, or_false] <;> norm_num <;> ring

private lemma add_zero_iff_right {D : ℕ} [NeZero D] (x y : ZMod D) :
    x + y = 0 ↔ y = -x := by
  constructor
  · intro h
    calc
      y = (x + y) - x := by ring
      _ = -x := by rw [h]; ring
  · intro h
    rw [h]
    ring

/-- The count is exact for every nonzero modulus, not only prime moduli. -/
lemma fourFormBad_count (D : ℕ) [NeZero D] :
    (∑ x : ZMod D, ∑ y : ZMod D, ∑ z : ZMod D,
      if fourFormBad (x, y, z) then (1 : ℝ) else 0) =
        4 * (D : ℝ) ^ 2 - 6 * D + 3 := by
  simp only [fourFormBad_indicator, sum_add_distrib, sum_sub_distrib]
  simp [zeroResidueIndicator, mul_ite, sub_eq_zero,
    add_zero_iff_right, nsmul_eq_mul, ZMod.card]
  ring

lemma uniformResidueCube_probability {D : ℕ} [NeZero D]
    (E : (ZMod D × ZMod D × ZMod D) → Prop) :
    (uniformResidueCubeLaw D).probability E =
      (∑ x : ZMod D, ∑ y : ZMod D, ∑ z : ZMod D,
        if E (x, y, z) then (1 : ℝ) else 0) / (D : ℝ) ^ 3 := by
  unfold FiniteLaw.probability FiniteLaw.average uniformResidueCubeLaw
    FiniteLaw.product uniformZModLaw
  simp only [Fintype.sum_prod_type]
  simp_rw [← mul_assoc, ← mul_sum]
  ring


theorem fourFormBadDensity_exact (D : ℕ) [NeZero D] :
    fourFormBadDensity D = (4 * (D : ℝ) ^ 2 - 6 * D + 3) / (D : ℝ) ^ 3 := by
  rw [fourFormBadDensity, uniformResidueCube_probability, fourFormBad_count]

lemma fourFormBadDensity_nonneg (D : ℕ) [NeZero D] : 0 ≤ fourFormBadDensity D :=
  (uniformResidueCubeLaw D).probability_nonneg fourFormBad

theorem fourFormBadDensity_bounds (D : ℕ) [NeZero D] :
    4 / (D : ℝ) - 6 / (D : ℝ) ^ 2 ≤ fourFormBadDensity D ∧
      fourFormBadDensity D ≤ 4 / (D : ℝ) := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast NeZero.pos D
  rw [fourFormBadDensity_exact]
  constructor
  · apply (le_div_iff₀ (pow_pos hD 3)).mpr
    field_simp
    nlinarith
  · apply (div_le_iff₀ (pow_pos hD 3)).mpr
    field_simp
    nlinarith


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

/-- A direct useful specialization: tail order `j` and total local mass
`M` give `exp(2M) / 2^j`. -/
lemma elementarySymmetric_two_bound {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0 ≤ a i) (j : ℕ) :
    elementarySymmetric P a j ≤ Real.exp (2 * ∑ i ∈ P, a i) / (2 : ℝ) ^ j :=
  elementarySymmetric_exp_bound P a ha j 2 (by norm_num)

/-- The next-layer tail is already at most `L⁻¹⁰⁰` once its order exceeds
`220 log L` and the total local mass is at most `5 log L`. The manuscript
uses the considerably larger order `1000 log L`. -/
theorem elementarySymmetric_log_tail {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ P, 0 ≤ a i) (j : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hmass : (∑ i ∈ P, a i) ≤ 5 * Real.log L)
    (hj : 220 * Real.log L ≤ (j : ℝ)) :
    elementarySymmetric P a j ≤ L ^ (-100 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    linarith
  apply (elementarySymmetric_two_bound P a ha j).trans
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num),
    ← Real.exp_sub, Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have horder : 110 * Real.log L ≤ (j : ℝ) * Real.log 2 := by
    calc
      _ = (220 * Real.log L) * (1 / 2 : ℝ) := by ring
      _ ≤ (j : ℝ) * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hj (by norm_num)
      _ ≤ (j : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg j)
  nlinarith

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

lemma uniformCube_crt_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (x : ZMod (∏ i, s i) × ZMod (∏ i, s i) × ZMod (∏ i, s i)) :
    (uniformResidueCubeLaw (∏ i, s i)).weight x =
      (FiniteLaw.dependentIndependent (fun i => uniformResidueCubeLaw (s i))).weight
        (sieveCubeCRT s hcop x) := by
  simp only [uniformResidueCubeLaw, FiniteLaw.product, uniformZModLaw,
    FiniteLaw.dependentIndependent, prod_mul_distrib, one_div, prod_inv_distrib, Nat.cast_prod]

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

/-- CRT evaluates an intersection of local three-variable conditions
exactly, retaining the dependence among the forms at each individual prime. -/
theorem sieveCRT_cube_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (E : ∀ i, (ZMod (s i) × ZMod (s i) × ZMod (s i)) → Prop) :
    (uniformResidueCubeLaw (∏ i, s i)).probability
      (fun x => ∀ i, E i (sieveCubeCRT s hcop x i)) =
      ∏ i, (uniformResidueCubeLaw (s i)).probability (E i) := by
  calc
    _ = (FiniteLaw.dependentIndependent (fun i => uniformResidueCubeLaw (s i))).probability
        (fun x => ∀ i, E i (x i)) :=
      FiniteLaw.probability_equiv _ _ (sieveCubeCRT s hcop)
        (uniformCube_crt_weight s hcop) (fun x => ∀ i, E i (x i))
    _ = _ := FiniteLaw.dependentIndependent_probability_all
      (fun i => uniformResidueCubeLaw (s i)) E

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

lemma uniformCube_average_residues {D N : ℕ} [NeZero D] [NeZero N]
    (A : ZMod D × ZMod D × ZMod D)
    (f : (ZMod D × ZMod D × ZMod D) → ℝ) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).average
      (fun j => f (A.1 + (j.1.val : ZMod D),
        A.2.1 + (j.2.1.val : ZMod D), A.2.2 + (j.2.2.val : ZMod D))) =
      (residueCubeLaw A N (NeZero.pos N)).average f := by
  let μ₁ := intervalResidueLaw A.1 N (NeZero.pos N)
  let μ₂ := intervalResidueLaw A.2.1 N (NeZero.pos N)
  let μ₃ := intervalResidueLaw A.2.2 N (NeZero.pos N)
  have h₃ (i j : Fin N) :
      uniformAverage (fun k : Fin N => f (A.1 + (i.val : ZMod D),
        A.2.1 + (j.val : ZMod D), A.2.2 + (k.val : ZMod D))) =
      μ₃.average (fun z => f (A.1 + (i.val : ZMod D), A.2.1 + (j.val : ZMod D), z)) :=
    (intervalResidueLaw_average_uniform A.2.2 N (NeZero.pos N)
      (fun z => f (A.1 + (i.val : ZMod D), A.2.1 + (j.val : ZMod D), z))).symm
  have h₂ (i : Fin N) :
      uniformAverage (fun j : Fin N =>
        μ₃.average (fun z => f (A.1 + (i.val : ZMod D), A.2.1 + (j.val : ZMod D), z))) =
      μ₂.average (fun y => μ₃.average (fun z => f (A.1 + (i.val : ZMod D), y, z))) :=
    (intervalResidueLaw_average_uniform A.2.1 N (NeZero.pos N)
      (fun y => μ₃.average (fun z => f (A.1 + (i.val : ZMod D), y, z)))).symm
  have hprod (i : Fin N) := uniformAverage_prod
    (fun (j k : Fin N) => f (A.1 + (i.val : ZMod D),
      A.2.1 + (j.val : ZMod D), A.2.2 + (k.val : ZMod D)))
  rw [uniformFiniteLaw_average, uniformAverage_prod
    (fun (i : Fin N) (jk : Fin N × Fin N) => f (A.1 + (i.val : ZMod D),
      A.2.1 + (jk.1.val : ZMod D), A.2.2 + (jk.2.val : ZMod D)))]
  simp_rw [hprod, h₃, h₂]
  change _ = (μ₁.product (μ₂.product μ₃)).average f
  rw [FiniteLaw.average_product]
  simp_rw [FiniteLaw.average_product]
  exact (intervalResidueLaw_average_uniform A.1 N (NeZero.pos N)
    (fun x => μ₂.average (fun y => μ₃.average (fun z => f (x, y, z))))).symm

lemma uniformCube_probability_residues {D N : ℕ} [NeZero D] [NeZero N]
    (A : ZMod D × ZMod D × ZMod D)
    (E : (ZMod D × ZMod D × ZMod D) → Prop) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
      (fun j => E (A.1 + (j.1.val : ZMod D),
        A.2.1 + (j.2.1.val : ZMod D), A.2.2 + (j.2.2.val : ZMod D))) =
      (residueCubeLaw A N (NeZero.pos N)).probability E :=
  uniformCube_average_residues A (fun z => if E z then 1 else 0)

/-- Exact CRT intersections on a fixed uniform interval cube, with their
complete finite boundary error. -/
theorem sieveCRT_cube_sample_discrepancy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i) × ZMod (∏ i, s i) × ZMod (∏ i, s i))
    (N : ℕ) [NeZero N]
    (E : ∀ i, (ZMod (s i) × ZMod (s i) × ZMod (s i)) → Prop) :
    |(uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
        (fun j => ∀ i, E i (sieveCubeCRT s hcop
          (A.1 + (j.1.val : ZMod (∏ i, s i)),
            A.2.1 + (j.2.1.val : ZMod (∏ i, s i)),
            A.2.2 + (j.2.2.val : ZMod (∏ i, s i))) i)) -
      ∏ i, (uniformResidueCubeLaw (s i)).probability (E i)| ≤
      3 * (∏ i, s i : ℕ) / (N : ℝ) := by
  rw [uniformCube_probability_residues A (fun x => ∀ i, E i (sieveCubeCRT s hcop x i)),
    ← sieveCRT_cube_probability s hcop E]
  exact residueCube_probability_discrepancy A N (NeZero.pos N) _

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

lemma sieveCubeCRT_natCast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j))) (a b c : ℕ) (i : ι) :
    sieveCubeCRT s hcop (a, b, c) i =
      ((a : ZMod (s i)), (b : ZMod (s i)), (c : ZMod (s i))) := by
  simp [sieveCubeCRT, ZMod.prodEquivPi_apply,
    ZMod.cast_natCast (dvd_prod_of_mem s (mem_univ i))]

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

theorem sieve_cube_intersection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ℕ × ℕ × ℕ) (N : ℕ) [NeZero N]
    (E : ∀ i, (ZMod (s i) × ZMod (s i) × ZMod (s i)) → Prop) (S : Finset ι) :
    |(uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
        (eventIntersection (fun i (j : Fin N × Fin N × Fin N) => E i
          (((A.1 + j.1.val : ℕ) : ZMod (s i)),
            ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
            ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i)))) S) -
      ∏ i ∈ S, (uniformResidueCubeLaw (s i)).probability (E i)| ≤
        3 / (N : ℝ) * ∏ i ∈ S, (s i : ℝ) := by
  let q : S → ℕ := fun i => s i
  have hc := selected_pairwise_coprime s hcop S
  have hmap (j : Fin N × Fin N × Fin N) (i : S) :
      sieveCubeCRT q hc
        ((A.1 : ZMod (∏ i, q i)) + (j.1.val : ZMod (∏ i, q i)),
          (A.2.1 : ZMod (∏ i, q i)) + (j.2.1.val : ZMod (∏ i, q i)),
          (A.2.2 : ZMod (∏ i, q i)) + (j.2.2.val : ZMod (∏ i, q i))) i =
        (((A.1 + j.1.val : ℕ) : ZMod (s i)),
          ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
          ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i))) := by
    simp only [← Nat.cast_add]
    exact sieveCubeCRT_natCast q hc _ _ _ i
  have hh := sieveCRT_cube_sample_discrepancy q hc
    ((A.1 : ZMod (∏ i, q i)), (A.2.1 : ZMod (∏ i, q i)), (A.2.2 : ZMod (∏ i, q i))) N
    (fun i => E i)
  simp_rw [hmap] at hh
  have he : (fun j : Fin N × Fin N × Fin N => ∀ i : S, E i
      (((A.1 + j.1.val : ℕ) : ZMod (s i)), ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
        ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i)))) =
      eventIntersection (fun i (j : Fin N × Fin N × Fin N) => E i
        (((A.1 + j.1.val : ℕ) : ZMod (s i)), ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
          ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i)))) S := by
    funext j
    simp only [eventIntersection, Subtype.forall]
  rw [he, Nat.cast_prod] at hh
  rw [← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (uniformResidueCubeLaw (s i)).probability (E i)),
    ← prod_subtype (p := fun i => i ∈ S) S (fun _ => Iff.rfl)
      (fun i => (s i : ℝ))] at hh
  convert (preTransparency := .instances) hh using 1
  ring

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

lemma reciprocal_square_sum_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  have hsub : P ⊆ Ioo 1 (P.sup id + 1) := by
    intro p hp
    exact mem_Ioo.mpr ⟨by have := hP p hp; omega,
      Nat.lt_succ_of_le (le_sup (f := id) hp)⟩
  calc
    _ ≤ ∑ p ∈ Ioo 1 (P.sup id + 1), ((p : ℝ) ^ 2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 := by
      have hh := sum_Ioo_inv_sq_le (α := ℝ) 1 (P.sup id + 1)
      norm_num at hh
      exact hh

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

/-- Four-form local avoidance loses precisely four reciprocal prime sums,
up to an absolute constant from the convergent square sum. -/
theorem fourForm_product_bound (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, 2 ≤ p) :
    (∏ p : P, (1 - fourFormBadDensity (p : ℕ))) ≤
      Real.exp 6 * Real.exp (-4 * ∑ p ∈ P, 1 / (p : ℝ)) := by
  have hν (p : P) : fourFormBadDensity (p : ℕ) ≤ 1 :=
    (uniformResidueCubeLaw (p : ℕ)).probability_le_one fourFormBad
  have hlower : 4 * (∑ p ∈ P, 1 / (p : ℝ)) - 6 ≤
      ∑ p : P, fourFormBadDensity (p : ℕ) := by
    have hs := sum_le_sum (fun (p : P) (_ : p ∈ (univ : Finset P)) =>
      (fourFormBadDensity_bounds (p : ℕ)).1)
    have he₁ : (∑ p : P, 4 / (p : ℝ)) = 4 * ∑ p ∈ P, 1 / (p : ℝ) := by
      rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
        (fun p => 4 / (p : ℝ))]
      simp only [div_eq_mul_inv, one_mul, ← mul_sum]
    have he₂ : (∑ p : P, 6 / (p : ℝ) ^ 2) = 6 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
        (fun p => 6 / (p : ℝ) ^ 2)]
      simp only [div_eq_mul_inv, one_mul, ← mul_sum]
    rw [sum_sub_distrib, he₁, he₂] at hs
    have hsq := reciprocal_square_sum_le_one P hP
    linarith
  calc
    _ ≤ Real.exp (-(∑ p : P, fourFormBadDensity (p : ℕ))) :=
      one_sub_product_le_exp _ hν
    _ ≤ Real.exp (6 - 4 * ∑ p ∈ P, 1 / (p : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; congr 2; ring

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

theorem finite_cube_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ℕ × ℕ × ℕ) (N : ℕ) [NeZero N]
    (E : ∀ i, (ZMod (s i) × ZMod (s i) × ZMod (s i)) → Prop) (r : ℕ) (Y : ℝ)
    (hY : 0 ≤ Y) (hs : ∀ i, (s i : ℝ) ≤ Y) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
      (avoidsEvents univ (fun i (j : Fin N × Fin N × Fin N) => E i
        (((A.1 + j.1.val : ℕ) : ZMod (s i)), ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
          ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i))))) ≤
      (∏ i, (1 - (uniformResidueCubeLaw (s i)).probability (E i))) +
        elementarySymmetric univ
          (fun i => (uniformResidueCubeLaw (s i)).probability (E i)) (2 * r + 1) +
        3 / (N : ℝ) * (2 * r + 1 : ℕ) * ((Fintype.card ι : ℝ) * Y + 1) ^ (2 * r) := by
  have hh := finite_independent_sieve_bound (uniformFiniteLaw (Fin N × Fin N × Fin N))
    (fun i (j : Fin N × Fin N × Fin N) => E i
      (((A.1 + j.1.val : ℕ) : ZMod (s i)), ((A.2.1 + j.2.1.val : ℕ) : ZMod (s i)),
        ((A.2.2 + j.2.2.val : ℕ) : ZMod (s i))))
    (fun i => uniformResidueCubeLaw (s i)) E r
    (fun S => 3 / (N : ℝ) * ∏ i ∈ S, (s i : ℝ))
    (fun S _ _ => sieve_cube_intersection s hcop A N E S)
  apply hh.trans
  gcongr
  simpa only [card_univ] using sieveIntersectionError_crude univ (fun i => (s i : ℝ))
    Y 3 hY (by norm_num) (fun i _ => ⟨Nat.cast_nonneg _, hs i⟩) N (2 * r)

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

lemma avoidsPrimeSet_iff_residues (P : Finset ℕ) (n : ℕ) :
    avoidsPrimeSet P n ↔ ∀ p : P, (n : ZMod (p : ℕ)) ≠ 0 := by
  simp only [avoidsPrimeSet, Subtype.forall, ne_eq, ZMod.natCast_eq_zero_iff]

lemma fourFormsAvoidPrimeSet_iff_residues (P : Finset ℕ)
    [∀ p : P, NeZero (p : ℕ)] (x : ℕ × ℕ × ℕ) :
    fourFormsAvoidPrimeSet P x ↔ ∀ p : P,
      ¬fourFormBad ((x.1 : ZMod (p : ℕ)), (x.2.1 : ZMod (p : ℕ)),
        (x.2.2 : ZMod (p : ℕ))) := by
  have hlast (p : P) :
      ((x.1 : ZMod (p : ℕ)) + (x.2.1 : ZMod (p : ℕ)) - (x.2.2 : ZMod (p : ℕ)) = 0) ↔
      (p : ℤ) ∣ (x.1 : ℤ) + x.2.1 - x.2.2 := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_natCast] using
      ZMod.intCast_zmod_eq_zero_iff_dvd ((x.1 : ℤ) + x.2.1 - x.2.2) (p : ℕ)
  simp only [fourFormsAvoidPrimeSet, avoidsPrimeSet_iff_residues,
    fourFormBad, not_or, hlast, forall_and, Subtype.forall]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughCutoffProbability
namespace OAI

/-! The finite rough sieve with its cutoff left explicit, for both one
linear form and the additive four-form system. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem rough_interval_probability_cutoff (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (A N : ℕ) [NeZero N] (r : ℕ) (B C X Y : ℝ) (hB : 1 ≤ B) (hX : 0 < X)
    (hY : 0 ≤ Y) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y)
    (hlower : Real.log X - C ≤ ∑ p ∈ P, 1 / (p : ℝ))
    (hupper : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 * Real.log B)
    (hr : 220 * Real.log B ≤ (2 * r + 1 : ℕ)) :
    (uniformFiniteLaw (Fin N)).probability (fun j => avoidsPrimeSet P (A + j.val)) ≤
      Real.exp C / X + B ^ (-100 : ℝ) +
        1 / (N : ℝ) * (2 * r + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ (2 * r) := by
  let (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  have hh := finite_interval_sieve (fun p : P => (p : ℕ)) (primeSet_pairwise_coprime P hP)
    A N (fun _ x => x = 0) r Y hY (fun p => hmax p p.property)
  have he : avoidsEvents univ (fun p : P => fun j : Fin N =>
      ((A + j.val : ℕ) : ZMod (p : ℕ)) = 0) =
      (fun j => avoidsPrimeSet P (A + j.val)) := by
    funext j
    simp only [avoidsEvents, mem_univ, forall_true_left, avoidsPrimeSet_iff_residues]
  simp only [he, oneFormBadDensity, Fintype.card_coe] at hh
  have hsum : (∑ p : P, 1 / (p : ℝ)) ≤ 5 * Real.log B := by
    rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
      (fun p => 1 / (p : ℝ))]
    exact hupper
  have ht := elementarySymmetric_log_tail (univ : Finset P)
    (fun p => 1 / (p : ℝ)) (fun p _ => by positivity) (2 * r + 1) B hB hsum hr
  have hp : (∏ p ∈ P, (1 - 1 / (p : ℝ))) ≤ Real.exp C / X := by
    apply (oneForm_product_bound P (fun p hp => (hP p hp).two_le)).trans
    calc
      _ ≤ Real.exp (C - Real.log X) := Real.exp_le_exp.mpr (by linarith only [hlower])
      _ = _ := by rw [Real.exp_sub, Real.exp_log hX]
  rw [prod_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)] at hp
  exact hh.trans (by gcongr)

theorem rough_cube_probability_cutoff (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (A : ℕ × ℕ × ℕ) (N : ℕ) [NeZero N] (r : ℕ) (B C X Y : ℝ)
    (hB : 1 ≤ B) (hX : 0 < X) (hY : 0 ≤ Y) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Y)
    (hlower : Real.log X - C ≤ ∑ p ∈ P, 1 / (p : ℝ))
    (hupper : (∑ p ∈ P, 1 / (p : ℝ)) ≤ (5 / 4 : ℝ) * Real.log B)
    (hr : 220 * Real.log B ≤ (2 * r + 1 : ℕ)) :
    (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability (fun j =>
      fourFormsAvoidPrimeSet P (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val)) ≤
      Real.exp (4 * C + 6) / X ^ 4 + B ^ (-100 : ℝ) +
        3 / (N : ℝ) * (2 * r + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ (2 * r) := by
  let (p : P) : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
  have hh := finite_cube_sieve (fun p : P => (p : ℕ)) (primeSet_pairwise_coprime P hP)
    A N (fun _ => fourFormBad) r Y hY (fun p => hmax p p.property)
  have he : avoidsEvents univ (fun p : P => fun j : Fin N × Fin N × Fin N =>
      fourFormBad (((A.1 + j.1.val : ℕ) : ZMod (p : ℕ)),
        ((A.2.1 + j.2.1.val : ℕ) : ZMod (p : ℕ)),
        ((A.2.2 + j.2.2.val : ℕ) : ZMod (p : ℕ)))) =
      (fun j => fourFormsAvoidPrimeSet P
        (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val)) := by
    funext j
    simp only [avoidsEvents, mem_univ, forall_true_left, fourFormsAvoidPrimeSet_iff_residues]
  change _ ≤ (∏ p : P, (1 - fourFormBadDensity (p : ℕ))) +
    elementarySymmetric univ (fun p : P => fourFormBadDensity (p : ℕ)) (2 * r + 1) + _ at hh
  rw [he] at hh
  simp only [Fintype.card_coe] at hh
  have hsum : (∑ p : P, fourFormBadDensity (p : ℕ)) ≤ 5 * Real.log B := by
    calc
      _ ≤ ∑ p : P, 4 / (p : ℝ) :=
        sum_le_sum (fun p _ => (fourFormBadDensity_bounds (p : ℕ)).2)
      _ = 4 * ∑ p ∈ P, 1 / (p : ℝ) := by
        rw [← sum_subtype (p := fun p : ℕ => p ∈ P) P (fun _ => Iff.rfl)
          (fun p => 4 / (p : ℝ))]
        simp only [div_eq_mul_inv, one_mul, ← mul_sum]
      _ ≤ _ := by linarith
  have ht := elementarySymmetric_log_tail (univ : Finset P)
    (fun p => fourFormBadDensity (p : ℕ)) (fun p _ => fourFormBadDensity_nonneg _)
    (2 * r + 1) B hB hsum hr
  have hp : (∏ p : P, (1 - fourFormBadDensity (p : ℕ))) ≤
      Real.exp (4 * C + 6) / X ^ 4 := by
    apply (fourForm_product_bound P (fun p hp => (hP p hp).two_le)).trans
    calc
      _ = Real.exp (6 - 4 * ∑ p ∈ P, 1 / (p : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (4 * C + 6 - 4 * Real.log X) :=
        Real.exp_le_exp.mpr (by linarith only [hlower])
      _ = _ := by
        rw [Real.exp_sub]
        have he : Real.exp (4 * Real.log X) = X ^ 4 := by
          calc
            _ = (Real.exp (Real.log X)) ^ (4 : ℕ) := Real.exp_nat_mul (Real.log X) 4
            _ = _ := by rw [Real.exp_log hX]
        rw [he]
  exact hh.trans (by gcongr)

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


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeSieveParameters
namespace OAI

/-! A small sieve cutoff for the qualitative multiplier. Truncation uses
the same proved finite four-form sieve; its cutoff is chosen so that the
entire CRT boundary cost lies far below the available interval length. -/

namespace TwoPointCorrelations

open _root_.Filter





theorem eventually_qualitativeSieveParameters :
    ∀ᶠ B : ℝ in atTop, QualitativeSieveParameters B := by
  have hs := (isLittleO_log_rpow_atTop
    (show 0 < (9999 / 10000 : ℝ) by norm_num)).bound
      (show 0 < (1 / 100300 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop (Real.exp 1), hs] with B hB hsB
  have hB₁ : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB₁
  have ht : 1 ≤ Real.log B := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hB
  have hBa : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have ht₀ : 0 ≤ Real.log B := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg ht₀, Real.norm_eq_abs, abs_of_pos hBa] at hsB
  have hdom : 100300 * Real.log B ≤ B ^ (9999 / 10000 : ℝ) := by linarith
  let r := qualitativeSieveHalfOrder B
  have hrlo : 500 * Real.log B ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < 500 * Real.log B + 1 := Nat.ceil_lt_add_one (by positivity)
  have hJlo : 1000 * Real.log B ≤ (2 * r + 1 : ℕ) := by push_cast; linarith
  have hJhi : (2 * r + 1 : ℕ) ≤ 1003 * Real.log B := by push_cast; linarith
  have hden : 0 < (100 : ℝ) * (2 * r + 1 : ℕ) := by positivity
  have hden₁ : 1 ≤ (100 : ℝ) * (2 * r + 1 : ℕ) := by
    have hr₀ : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    push_cast
    nlinarith only [hr₀]
  have hX₁ : 1 ≤ qualitativeSieveLogCutoff B := by
    change 1 ≤ B ^ (9999 / 10000 : ℝ) / (100 * (2 * r + 1 : ℕ))
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hJhi, hdom]
  refine ⟨ht, ?_, ?_, hX₁, ?_, ?_, ?_⟩
  · change 220 * Real.log B ≤ (2 * r + 1 : ℕ)
    linarith
  · change (2 * r : ℕ) ≤ 1002 * Real.log B
    push_cast
    linarith
  · calc
      qualitativeSieveLogCutoff B ≤ B ^ (9999 / 10000 : ℝ) :=
        div_le_self hBa.le hden₁
      _ ≤ B := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB₁
          (show (9999 / 10000 : ℝ) ≤ 1 by norm_num)
  · have htdiv : Real.log B / (100 * (2 * r + 1 : ℕ)) ≤ (1 / 100000 : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hJlo]
    calc
      qualitativeSieveLogCutoff B * Real.log B =
          B ^ (9999 / 10000 : ℝ) * (Real.log B / (100 * (2 * r + 1 : ℕ))) := by
        unfold qualitativeSieveLogCutoff
        dsimp [r]
        ring
      _ ≤ B ^ (9999 / 10000 : ℝ) * (1 / 100000 : ℝ) :=
        mul_le_mul_of_nonneg_left htdiv hBa.le
      _ = _ := by ring
  · calc
      1 / qualitativeSieveLogCutoff B =
          (100 * (2 * r + 1 : ℕ)) / B ^ (9999 / 10000 : ℝ) := by
        unfold qualitativeSieveLogCutoff
        dsimp [r]
        field_simp [hBa.ne', hden.ne']
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hJhi]) hBa.le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativePrimeScale
namespace OAI

/-! The published Mertens estimate on the smaller qualitative sieve
cutoff, and the exact inclusion of its primes in the roughness condition. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma qualitativeSieveLogCutoff_lt_power (B : ℝ) (hB : 0 < B) :
    qualitativeSieveLogCutoff B < B ^ (9999 / 10000 : ℝ) := by
  apply div_lt_self (Real.rpow_pos_of_pos hB _)
  have hr : (0 : ℝ) ≤ qualitativeSieveHalfOrder B := Nat.cast_nonneg _
  push_cast
  nlinarith only [hr]

lemma HasNoPrimeFactorBelow.qualitativeSieve {B : ℝ} (hB : 0 < B) {n : ℕ}
    (hn : HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) n) :
    avoidsPrimeSet (qualitativeSievePrimes B) n := by
  intro p hp
  apply hn p (sievePrimesUpTo_prime _ p hp)
  exact (sievePrimesUpTo_le _ (Real.exp_pos _).le p hp).trans_lt
    (Real.exp_lt_exp.mpr (qualitativeSieveLogCutoff_lt_power B hB))

theorem PrimeReciprocalInput.qualitative_scale (hM : PrimeReciprocalInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℝ in atTop,
      |(∑ p ∈ qualitativeSievePrimes B, 1 / (p : ℝ)) -
        Real.log (qualitativeSieveLogCutoff B)| ≤ C ∧
      (∑ p ∈ qualitativeSievePrimes B, 1 / (p : ℝ)) ≤ (5 / 4 : ℝ) * Real.log B := by
  obtain ⟨C, hC⟩ := hM
  have hC₀ : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨C, hC₀, ?_⟩
  filter_upwards [eventually_qualitativeSieveParameters,
    eventually_ge_atTop (Real.exp (4 * C + 1))] with B hpar hB
  have hX : 0 < qualitativeSieveLogCutoff B := zero_lt_one.trans_le hpar.cutoff_one
  have hy : 2 ≤ Real.exp (qualitativeSieveLogCutoff B) := by
    linarith [Real.add_one_le_exp (qualitativeSieveLogCutoff B), hpar.cutoff_one]
  have hm := hC (Real.exp (qualitativeSieveLogCutoff B)) hy
  rw [Real.log_exp] at hm
  refine ⟨hm, ?_⟩
  have hlogC : 4 * C + 1 ≤ Real.log B := by
    rw [← Real.log_exp (4 * C + 1)]
    exact Real.log_le_log (Real.exp_pos _) hB
  have hlogX := Real.log_le_log hX hpar.cutoff_le
  have hu := (abs_le.mp hm).2
  change (∑ p ∈ qualitativeSievePrimes B, 1 / (p : ℝ)) -
    Real.log (qualitativeSieveLogCutoff B) ≤ C at hu
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeSieveBoundary
namespace OAI

/-! The literal CRT boundary error at the qualitative sieve cutoff. -/

namespace TwoPointCorrelations

lemma qualitative_sieve_boundary_cost (B : ℝ) (hpar : QualitativeSieveParameters B)
    (hB : 0 < B) (C₀ Y n : ℝ) (N : ℕ)
    (hC₀ : 0 ≤ C₀) (hC₃ : C₀ ≤ 3) (hY : 0 ≤ Y) (hn : 0 ≤ n)
    (hnY : n ≤ Y) (hYexp : Y ≤ Real.exp (qualitativeSieveLogCutoff B))
    (hN : (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ N) :
    C₀ / (N : ℝ) * (2 * qualitativeSieveHalfOrder B + 1 : ℕ) *
      (n * Y + 1) ^ (2 * qualitativeSieveHalfOrder B) ≤ B ^ (-100 : ℝ) := by
  let X := qualitativeSieveLogCutoff B
  let A := B ^ (9999 / 10000 : ℝ)
  have hA : 0 < A := Real.rpow_pos_of_pos hB _
  have hXT : 1 ≤ X * Real.log B := by
    nlinarith only [hpar.cutoff_one, hpar.log_one]
  have hdom : 100000 * Real.log B ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hpar.cutoff_one
      (show 0 ≤ Real.log B by linarith [hpar.log_one])
    nlinarith only [hh, hpar.cutoff_cost]
  have hA₄ : 4 ≤ A := by linarith [hpar.log_one]
  have hnum := sieve_boundary_numerator X (Real.log B) 1002 C₀ (n * Y + 1)
    (2 * qualitativeSieveHalfOrder B) hpar.cutoff_one hpar.log_one (by norm_num)
    hC₀ (by positivity) (sieve_base_le_exp X Y n hpar.cutoff_one hY hn hnY hYexp)
    hpar.order_small
  have hnumexp : Real.exp ((C₀ + 4 * 1002) * X * Real.log B) ≤ Real.exp (A / 4) := by
    apply Real.exp_le_exp.mpr
    have hcost : X * Real.log B ≤ A / 100000 := hpar.cutoff_cost
    have hXT₀ : 0 ≤ X * Real.log B := by linarith
    nlinarith only [hC₃, hC₀, hcost, hXT₀, hA]
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hdiv : 1 / (N : ℝ) ≤ 2 * Real.exp (-A) := by
    apply (div_le_iff₀ hNp).mpr
    have hh := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 * Real.exp (-A) by positivity)
    have hc : (2 * Real.exp (-A)) * ((1 / 2 : ℝ) * Real.exp A) = 1 := by
      calc
        _ = Real.exp (-A) * Real.exp A := by ring
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    change (2 * Real.exp (-A)) * ((1 / 2 : ℝ) * Real.exp A) ≤ _ at hh
    rw [hc] at hh
    nlinarith only [hh]
  have he : 2 ≤ Real.exp (A / 4) := by
    linarith [Real.add_one_le_exp (A / 4)]
  calc
    _ = (C₀ * (2 * qualitativeSieveHalfOrder B + 1 : ℕ) *
        (n * Y + 1) ^ (2 * qualitativeSieveHalfOrder B)) * (1 / (N : ℝ)) := by ring
    _ ≤ Real.exp (A / 4) * (2 * Real.exp (-A)) := by
      exact mul_le_mul (hnum.trans hnumexp) hdiv (by positivity) (Real.exp_pos _).le
    _ ≤ Real.exp (A / 4) * (Real.exp (A / 4) * Real.exp (-A)) := by gcongr
    _ = Real.exp (-A / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-100 * Real.log B) := Real.exp_le_exp.mpr (by linarith only [hdom, hpar.log_one])
    _ = B ^ (-100 : ℝ) := by rw [Real.rpow_def_of_pos hB]; congr 1; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughFourier
namespace OAI

/-!
# Exact finite Fourier identities for rough shifts

Orthogonality, convolution and the fourth moment are proved for arbitrary
finite coefficients. The sieve bounds on the number of rough integers are
not hypotheses of these identities. Haar measure on `AddCircle (1 : ℝ)` is the
ordinary integral over one period.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators _root_.ComplexConjugate
open _root_.MeasureTheory




theorem integral_fourier_character (n : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), fourier n θ ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

theorem integrable_fourier_character (n : ℤ) :
    Integrable (fun θ : AddCircle (1 : ℝ) => fourier n θ)
      AddCircle.haarAddCircle := by
  simpa only [smul_eq_mul, mul_one] using
    (integrable_const (1 : ℂ) (μ := (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))))).fourier_smul n

theorem integral_fourierPolynomial {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) :
    (∫ θ, fourierPolynomial S frequency coefficient θ ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S, if frequency i = 0 then coefficient i else 0 := by
  classical
  unfold fourierPolynomial
  rw [integral_finsetSum S (fun i _ =>
    (integrable_fourier_character (frequency i)).const_mul (coefficient i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_fourier_character]
  split_ifs <;> simp_all

theorem norm_fourierPolynomial_le {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (θ : AddCircle (1 : ℝ)) :
    ‖fourierPolynomial S frequency coefficient θ‖ ≤ ∑ i ∈ S, ‖coefficient i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, le_refl]

theorem fourierPolynomial_mul {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) (θ : AddCircle (1 : ℝ)) :
    fourierPolynomial S f a θ * fourierPolynomial T g b θ =
      fourierPolynomial (S ×ˢ T) (fun i => f i.1 + g i.2)
        (fun i => a i.1 * b i.2) θ := by
  classical
  simp only [fourierPolynomial, Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [fourier_add]
  ring

theorem fourierPolynomial_conj {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ) (θ : AddCircle (1 : ℝ)) :
    conj (fourierPolynomial S f a θ) =
      fourierPolynomial S (fun i => -f i) (fun i => conj (a i)) θ := by
  simp only [fourierPolynomial, map_sum, map_mul, fourier_neg]

/-- Exact Fourier selection of all frequency-zero terms in a product. -/
theorem integral_fourier_product {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (a : ι → ℂ) (b : κ → ℂ) :
    (∫ θ, fourierPolynomial S f a θ * fourierPolynomial T g b θ
        ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S ×ˢ T, if f i.1 + g i.2 = 0 then a i.1 * b i.2 else 0 := by
  simp_rw [fourierPolynomial_mul]
  exact integral_fourierPolynomial _ _ _

/-- Parseval for finite polynomials, retaining collisions of frequencies. -/
theorem integral_norm_fourierPolynomial_sq {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ) :
    (∫ θ, ‖fourierPolynomial S f a θ‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑ i ∈ S ×ˢ S, if f i.1 = f i.2 then (a i.1 * conj (a i.2)).re else 0 := by
  classical
  have hc : ((∫ θ, ‖fourierPolynomial S f a θ‖ ^ 2
        ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
      ∑ i ∈ S ×ˢ S, if f i.1 = f i.2 then a i.1 * conj (a i.2) else 0 := by
    rw [← integral_complex_ofReal]
    simp_rw [Complex.ofReal_pow, ← Complex.mul_conj', fourierPolynomial_conj]
    rw [integral_fourier_product]
    apply Finset.sum_congr rfl
    intro i _
    simp only [add_neg_eq_zero]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.re_sum, apply_ite, Complex.zero_re] using hr

/-- The exact weighted additive-energy identity. In particular a positive
integer dilation of the frequencies leaves its additive relation unchanged. -/
theorem integral_norm_fourierPolynomial_fourth {ι : Type*} (S : Finset ι)
    (f : ι → ℤ) (a : ι → ℂ) :
    (∫ θ, ‖fourierPolynomial S f a θ‖ ^ 4 ∂AddCircle.haarAddCircle) =
      ∑ i ∈ (S ×ˢ S) ×ˢ (S ×ˢ S),
        if f i.1.1 + f i.1.2 = f i.2.1 + f i.2.2 then
          (a i.1.1 * a i.1.2 * conj (a i.2.1 * a i.2.2)).re else 0 := by
  have h := integral_norm_fourierPolynomial_sq (S ×ˢ S)
    (fun i => f i.1 + f i.2) (fun i => a i.1 * a i.2)
  convert (preTransparency := .instances) h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    dsimp only
    rw [← fourierPolynomial_mul, norm_mul]
    ring





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughSieveCounts
namespace OAI

/-! Passing from actual uniform samples to subset and additive-energy
counts. Every additive quadruple is injected into its first three entries. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma uniformFiniteLaw_probability {α : Type*} [Fintype α] [Nonempty α]
    (E : α → Prop) : (uniformFiniteLaw α).probability E =
      ((univ.filter E).card : ℝ) / Fintype.card α := by
  simp only [FiniteLaw.probability, FiniteLaw.average, uniformFiniteLaw, ← mul_sum,
    sum_boole]
  ring



lemma roughIntervalSamples_probability (P : Finset ℕ) (A N : ℕ) [NeZero N] :
    (roughIntervalSamples P A N).card = (N : ℝ) *
      (uniformFiniteLaw (Fin N)).probability (fun j => avoidsPrimeSet P (A + j.val)) := by
  rw [uniformFiniteLaw_probability]
  simp only [Fintype.card_fin, roughIntervalSamples]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp [hN]

lemma roughCubeSamples_probability (P : Finset ℕ) (A : ℕ × ℕ × ℕ) (N : ℕ)
    [NeZero N] :
    (roughCubeSamples P A N).card = (N : ℝ) ^ 3 *
      (uniformFiniteLaw (Fin N × Fin N × Fin N)).probability
        (fun j => fourFormsAvoidPrimeSet P
          (A.1 + j.1.val, A.2.1 + j.2.1.val, A.2.2 + j.2.2.val)) := by
  rw [uniformFiniteLaw_probability]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, roughCubeSamples]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp [hN]

theorem rough_subset_card_le (P Z : Finset ℕ) (A N : ℕ)
    (hZ : ∀ z ∈ Z, A ≤ z ∧ z < A + N ∧ avoidsPrimeSet P z) :
    Z.card ≤ (roughIntervalSamples P A N).card := by
  let offset (z : Z) : Fin N := ⟨(z : ℕ) - A, by
    have hz := hZ z z.property
    omega⟩
  let f : Z → roughIntervalSamples P A N := fun z => ⟨offset z, by
    have hz := hZ z z.property
    simp only [roughIntervalSamples, mem_filter, mem_univ, true_and]
    change avoidsPrimeSet P (A + ((z : ℕ) - A))
    rw [Nat.add_sub_of_le hz.1]
    exact hz.2.2⟩
  have hf : Function.Injective f := by
    intro z w he
    have hv := congrArg (fun t : roughIntervalSamples P A N => (t : Fin N).val) he
    have hz := hZ z z.property
    have hw := hZ w w.property
    apply Subtype.ext
    change (z : ℕ) - A = (w : ℕ) - A at hv
    omega
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf


lemma mem_additiveQuadruples {Z : Finset ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hq : q ∈ additiveQuadruples Z) :
    q.1.1 ∈ Z ∧ q.1.2 ∈ Z ∧ q.2.1 ∈ Z ∧ q.2.2 ∈ Z ∧
      q.1.1 + q.1.2 = q.2.1 + q.2.2 := by
  simpa only [additiveQuadruples, mem_filter, mem_product, and_assoc] using hq

theorem rough_additiveQuadruples_card_le (P Z : Finset ℕ) (A N : ℕ)
    (hZ : ∀ z ∈ Z, A ≤ z ∧ z < A + N ∧ avoidsPrimeSet P z) :
    (additiveQuadruples Z).card ≤ (roughCubeSamples P (A, A, A) N).card := by
  let Q := additiveQuadruples Z
  have hq (q : Q) := mem_additiveQuadruples q.property
  let off (z : ℕ) (hz : z ∈ Z) : Fin N := ⟨z - A, by have := hZ z hz; omega⟩
  let f : Q → roughCubeSamples P (A, A, A) N := fun q =>
    ⟨(off q.val.1.1 (hq q).1, off q.val.1.2 (hq q).2.1,
        off q.val.2.1 (hq q).2.2.1), by
      have h₁ := hZ q.val.1.1 (hq q).1
      have h₂ := hZ q.val.1.2 (hq q).2.1
      have h₃ := hZ q.val.2.1 (hq q).2.2.1
      have h₄ := hZ q.val.2.2 (hq q).2.2.2.1
      simp only [roughCubeSamples, mem_filter, mem_univ, true_and]
      change fourFormsAvoidPrimeSet P
        (A + (q.val.1.1 - A), A + (q.val.1.2 - A), A + (q.val.2.1 - A))
      rw [Nat.add_sub_of_le h₁.1, Nat.add_sub_of_le h₂.1, Nat.add_sub_of_le h₃.1]
      refine ⟨h₁.2.2, h₂.2.2, h₃.2.2, ?_⟩
      intro p hp hd
      have he : (q.val.1.1 : ℤ) + q.val.1.2 - q.val.2.1 = q.val.2.2 := by
        have := (hq q).2.2.2.2
        omega
      rw [he] at hd
      exact h₄.2.2 p hp (Int.natCast_dvd_natCast.mp hd)⟩
  have hf : Function.Injective f := by
    intro q r he
    have he₁ := congrArg (fun t : roughCubeSamples P (A, A, A) N =>
      ((t : Fin N × Fin N × Fin N).1).val) he
    have he₂ := congrArg (fun t : roughCubeSamples P (A, A, A) N =>
      ((t : Fin N × Fin N × Fin N).2.1).val) he
    have he₃ := congrArg (fun t : roughCubeSamples P (A, A, A) N =>
      ((t : Fin N × Fin N × Fin N).2.2).val) he
    change q.val.1.1 - A = r.val.1.1 - A at he₁
    change q.val.1.2 - A = r.val.1.2 - A at he₂
    change q.val.2.1 - A = r.val.2.1 - A at he₃
    have hq₁ := (hZ q.val.1.1 (hq q).1).1
    have hq₂ := (hZ q.val.1.2 (hq q).2.1).1
    have hq₃ := (hZ q.val.2.1 (hq q).2.2.1).1
    have hr₁ := (hZ r.val.1.1 (hq r).1).1
    have hr₂ := (hZ r.val.1.2 (hq r).2.1).1
    have hr₃ := (hZ r.val.2.1 (hq r).2.2.1).1
    have hqe := (hq q).2.2.2.2
    have hre := (hq r).2.2.2.2
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext <;> omega
    · apply Prod.ext <;> omega
  simpa only [Q, Fintype.card_coe] using Fintype.card_le_of_injective f hf


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedRoughFourier
namespace OAI

/-! Arbitrary bounded complex coefficients on the same rough support.
These are needed for the qualitative Fourier multiplier. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.ComplexConjugate _root_.Classical


lemma rough_coefficient_norm_le (Z : Finset ℕ) (c : ℕ → ℂ) (D : ℝ)
    (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ)) (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1)
    (z : ℕ) (hz : z ∈ Z) : ‖c z / (z : ℂ)‖ ≤ D⁻¹ := by
  rw [norm_div, Complex.norm_natCast]
  calc
    _ ≤ 1 / (z : ℝ) := div_le_div_of_nonneg_right (hc z hz) (Nat.cast_nonneg _)
    _ ≤ _ := by simpa only [one_div] using inv_anti₀ hD (hZ z hz)

theorem norm_weightedRoughFourier_le (Z : Finset ℕ) (c : ℕ → ℂ) (h : ℕ)
    (D : ℝ) (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ))
    (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1) (θ : AddCircle (1 : ℝ)) :
    ‖weightedRoughFourier Z c h θ‖ ≤ Z.card / D := by
  apply (norm_fourierPolynomial_le Z _ _ θ).trans
  calc
    _ ≤ ∑ _z ∈ Z, D⁻¹ := sum_le_sum (rough_coefficient_norm_le Z c D hD hZ hc)
    _ = _ := by simp [div_eq_mul_inv]

theorem weightedRoughFourier_fourth_le (Z : Finset ℕ) (c : ℕ → ℂ) (h : ℕ)
    (hh : 0 < h) (D : ℝ) (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ))
    (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1) :
    (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
      (additiveQuadruples Z).card * (D⁻¹) ^ 4 := by
  have hrel (q : (ℕ × ℕ) × (ℕ × ℕ)) :
      (h : ℤ) * q.1.1 + (h : ℤ) * q.1.2 =
        (h : ℤ) * q.2.1 + (h : ℤ) * q.2.2 ↔
      q.1.1 + q.1.2 = q.2.1 + q.2.2 := by
    rw [← mul_add, ← mul_add,
      mul_right_inj' (show (h : ℤ) ≠ 0 by exact_mod_cast hh.ne')]
    exact_mod_cast Iff.rfl
  rw [weightedRoughFourier, integral_norm_fourierPolynomial_fourth]
  simp_rw [hrel]
  rw [← sum_filter]
  calc
    _ ≤ ∑ _q ∈ additiveQuadruples Z, (D⁻¹) ^ 4 := by
      apply sum_le_sum
      intro q hq
      have hm := mem_additiveQuadruples hq
      have h₁ := rough_coefficient_norm_le Z c D hD hZ hc q.1.1 hm.1
      have h₂ := rough_coefficient_norm_le Z c D hD hZ hc q.1.2 hm.2.1
      have h₃ := rough_coefficient_norm_le Z c D hD hZ hc q.2.1 hm.2.2.1
      have h₄ := rough_coefficient_norm_le Z c D hD hZ hc q.2.2 hm.2.2.2.1
      calc
        _ ≤ ‖c q.1.1 / (q.1.1 : ℂ) * (c q.1.2 / (q.1.2 : ℂ)) *
            conj (c q.2.1 / (q.2.1 : ℂ) * (c q.2.2 / (q.2.2 : ℂ)))‖ :=
          Complex.re_le_norm _
        _ ≤ D⁻¹ * D⁻¹ * (D⁻¹ * D⁻¹) := by
          simp only [Complex.norm_conj, norm_mul]
          gcongr
        _ = _ := by ring
    _ = _ := by simp

theorem weightedRoughFourier_bounds_of_sieve (P Z : Finset ℕ) (c : ℕ → ℂ)
    (D h : ℕ) [NeZero D] (hh : 0 < h) (A B : ℝ)
    (hZ : ∀ z ∈ Z, D ≤ z ∧ z < D + D ∧ avoidsPrimeSet P z)
    (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1)
    (h₁ : (uniformFiniteLaw (Fin D)).probability
      (fun j => avoidsPrimeSet P (D + j.val)) ≤ A)
    (h₄ : (uniformFiniteLaw (Fin D × Fin D × Fin D)).probability
      (fun j => fourFormsAvoidPrimeSet P
        (D + j.1.val, D + j.2.1.val, D + j.2.2.val)) ≤ B) :
    (∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ A) ∧
      (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤ B / D := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hzr (z : ℕ) (hz : z ∈ Z) : (D : ℝ) ≤ z := by exact_mod_cast (hZ z hz).1
  have hcard : (Z.card : ℝ) ≤ (D : ℝ) * A := by
    calc
      _ ≤ ((roughIntervalSamples P D D).card : ℝ) := by
        exact_mod_cast rough_subset_card_le P Z D D hZ
      _ = _ := roughIntervalSamples_probability P D D
      _ ≤ _ := mul_le_mul_of_nonneg_left h₁ hD.le
  have hquad : ((additiveQuadruples Z).card : ℝ) ≤ (D : ℝ) ^ 3 * B := by
    calc
      _ ≤ ((roughCubeSamples P (D, D, D) D).card : ℝ) := by
        exact_mod_cast rough_additiveQuadruples_card_le P Z D D hZ
      _ = _ := roughCubeSamples_probability P (D, D, D) D
      _ ≤ _ := mul_le_mul_of_nonneg_left h₄ (by positivity)
  constructor
  · intro θ
    apply (norm_weightedRoughFourier_le Z c h (D : ℝ) hD hzr hc θ).trans
    exact (div_le_iff₀ hD).mpr (by nlinarith only [hcard])
  · calc
      _ ≤ ((additiveQuadruples Z).card : ℝ) * ((D : ℝ)⁻¹) ^ 4 :=
        weightedRoughFourier_fourth_le Z c h hh (D : ℝ) hD hzr hc
      _ ≤ ((D : ℝ) ^ 3 * B) * ((D : ℝ)⁻¹) ^ 4 :=
        mul_le_mul_of_nonneg_right hquad (by positivity)
      _ = _ := by field_simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QualitativeRoughFourier
namespace OAI

/-! The qualitative rough multiplier, with arbitrary bounded complex
coefficients, obtained directly from the finite four-form sieve. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.Classical

lemma rpow_neg_hundred_le_qualitative_rate (B : ℝ) (hB : 1 ≤ B)
    (hlog : 1 ≤ Real.log B) (k : ℕ) (hk : k ≤ 100) :
    B ^ (-100 : ℝ) ≤ (Real.log B / B ^ (9999 / 10000 : ℝ)) ^ k := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hA : 0 < B ^ (9999 / 10000 : ℝ) := Real.rpow_pos_of_pos hBp _
  have hAB : B ^ (9999 / 10000 : ℝ) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB
      (show (9999 / 10000 : ℝ) ≤ 1 by norm_num)
  have hi : B⁻¹ ≤ Real.log B / B ^ (9999 / 10000 : ℝ) := by
    calc
      _ ≤ (B ^ (9999 / 10000 : ℝ))⁻¹ := inv_anti₀ hA hAB
      _ ≤ _ := by
        change (B ^ (9999 / 10000 : ℝ))⁻¹ ≤
          Real.log B * (B ^ (9999 / 10000 : ℝ))⁻¹
        nlinarith only [hlog, inv_pos.mpr hA]
  calc
    _ ≤ B ^ (-(k : ℝ)) := Real.rpow_le_rpow_of_exponent_le hB (by
      have hk' : (k : ℝ) ≤ 100 := by exact_mod_cast hk
      linarith only [hk'])
    _ = (B⁻¹) ^ k := by
      rw [show -(k : ℝ) = (-1 : ℝ) * k by ring,
        Real.rpow_mul_natCast hBp.le, Real.rpow_neg_one]
    _ ≤ _ := pow_le_pow_left₀ (inv_nonneg.mpr hBp.le) hi k

/-- The manuscript qualitative multiplier estimate.  Its fourth moment
has only four logarithmic factors, which is stronger than the six needed
in the analytic transfer. -/
theorem PrimeReciprocalInput.qualitative_rough_fourier_oai (hM : PrimeReciprocalInput) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (D h : ℕ), (1 / 2 : ℝ) * Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ D → 0 < h →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      (∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤
        U * (Real.log B / B ^ (9999 / 10000 : ℝ))) ∧
      (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
        V / (D : ℝ) * (Real.log B / B ^ (9999 / 10000 : ℝ)) ^ 4 := by
  obtain ⟨C, hC, hprime⟩ := hM.qualitative_scale
  let U := Real.exp C * 100300 + 2
  let V := Real.exp (4 * C + 6) * 100300 ^ 4 + 2
  refine ⟨U, V, by dsimp [U]; positivity, by dsimp [V]; positivity, ?_⟩
  filter_upwards [hprime, eventually_qualitativeSieveParameters,
    eventually_ge_atTop (Real.exp 1)] with B hp hpar hB
  intro D h hD hh Z c hZ hc
  have hB₁ : 1 ≤ B := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB₁
  have hDp : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  let : NeZero D := ⟨by exact_mod_cast hDp.ne'⟩
  let P := qualitativeSievePrimes B
  let X := qualitativeSieveLogCutoff B
  let Y := Real.exp X
  let r := qualitativeSieveHalfOrder B
  let q := Real.log B / B ^ (9999 / 10000 : ℝ)
  have hX : 0 < X := zero_lt_one.trans_le hpar.cutoff_one
  have hY : 0 ≤ Y := (Real.exp_pos _).le
  have hP (p : ℕ) (hp : p ∈ P) : Nat.Prime p := sievePrimesUpTo_prime Y p hp
  have hmax (p : ℕ) (hp : p ∈ P) : (p : ℝ) ≤ Y := sievePrimesUpTo_le Y hY p hp
  have hcard : (P.card : ℝ) ≤ Y := sievePrimesUpTo_card_le Y hY
  have hlo : Real.log X - C ≤ ∑ p ∈ P, 1 / (p : ℝ) := by
    have ht := (abs_le.mp hp.1).1
    change -C ≤ (∑ p ∈ P, 1 / (p : ℝ)) - Real.log X at ht
    linarith only [ht]
  have hup : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 * Real.log B := by
    have ht := hp.2
    change (∑ p ∈ P, 1 / (p : ℝ)) ≤ (5 / 4 : ℝ) * Real.log B at ht
    linarith [hpar.log_one]
  have he₁ := qualitative_sieve_boundary_cost B hpar hBp 1 Y P.card D
    zero_le_one (by norm_num) hY (Nat.cast_nonneg _) hcard le_rfl hD
  have he₃ := qualitative_sieve_boundary_cost B hpar hBp 3 Y P.card D
    (by norm_num) le_rfl hY (Nat.cast_nonneg _) hcard le_rfl hD
  have hprob₁ := rough_interval_probability_cutoff P hP D D r B C X Y hB₁ hX hY
    hmax hlo hup hpar.nextOrder_large
  have hprob₄ := rough_cube_probability_cutoff P hP (D, D, D) D r B C X Y hB₁ hX hY
    hmax hlo hp.2 hpar.nextOrder_large
  have hsmall₁ : B ^ (-100 : ℝ) ≤ q := by
    simpa only [pow_one] using rpow_neg_hundred_le_qualitative_rate B hB₁ hpar.log_one 1 (by norm_num)
  have hsmall₄ : B ^ (-100 : ℝ) ≤ q ^ 4 :=
    rpow_neg_hundred_le_qualitative_rate B hB₁ hpar.log_one 4 (by norm_num)
  have hinv : 1 / X ≤ 100300 * q := by
    calc
      _ ≤ 100300 * Real.log B / B ^ (9999 / 10000 : ℝ) := hpar.inverse_cutoff
      _ = _ := by dsimp [q]; ring
  have hmain₁ : Real.exp C / X ≤ (Real.exp C * 100300) * q := by
    convert (preTransparency := .instances) mul_le_mul_of_nonneg_left hinv (Real.exp_pos C).le using 1 <;> ring
  have hmain₄ : Real.exp (4 * C + 6) / X ^ 4 ≤
      (Real.exp (4 * C + 6) * 100300 ^ 4) * q ^ 4 := by
    have ht := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0 ≤ 1 / X) hinv 4) (Real.exp_pos (4 * C + 6)).le
    convert (preTransparency := .instances) ht using 1 <;> ring
  have hzsmall : ∀ z ∈ Z, D ≤ z ∧ z < D + D ∧ avoidsPrimeSet P z := by
    intro z hz
    exact ⟨(hZ z hz).1, (hZ z hz).2.1,
      (hZ z hz).2.2.qualitativeSieve hBp⟩
  have hb := weightedRoughFourier_bounds_of_sieve P Z c D h hh (U * q) (V * q ^ 4)
    hzsmall hc (hprob₁.trans (by dsimp [U]; nlinarith only [hmain₁, he₁, hsmall₁]))
    (hprob₄.trans (by dsimp [V]; nlinarith only [hmain₄, he₃, hsmall₄]))
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.PrimeReciprocalInput.qualitative_rough_fourier_oai := @OAI.TwoPointCorrelations.PrimeReciprocalInput.qualitative_rough_fourier_oai
