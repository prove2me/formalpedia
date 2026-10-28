-- Prove2me | solution 1 for OAI.Problem337.one_expansions_finite_and_bounded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:01:13.560028+00:00
-- url     : https://prove2.me/submissions/a12e44ab-a9d5-4e9d-b5d0-c9bb37a0364d

import Mathlib
import Definitions.Def_EgyptianFractions

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrefixGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- The reduced denominator of a finite rational sum divides the product of
its summands' reduced denominators. -/
theorem sum_den_dvd_prod {α : Type*} [DecidableEq α]
    (s : Finset α) (q : α → ℚ) :
    (∑ j ∈ s, q j).den ∣ ∏ j ∈ s, (q j).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

/-- A positive rational with denominator dividing `P` is at least `1/P`. -/
theorem one_div_le_of_den_dvd {q : ℚ} {P : ℕ}
    (hq : 0 < q) (hP : 0 < P) (hd : q.den ∣ P) :
    (1 : ℚ) / P ≤ q := by
  have hden : q.den ≤ P := Nat.le_of_dvd hP hd
  have hnum : (1 : ℚ) ≤ q.num := by
    exact_mod_cast (Rat.num_pos.mpr hq)
  calc
    (1 : ℚ) / P ≤ 1 / q.den := by
      exact one_div_le_one_div_of_le (by exact_mod_cast q.den_pos) (by exact_mod_cast hden)
    _ ≤ (q.num : ℚ) / q.den :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = q := Rat.num_div_den q

/-- The remainder after subtracting finitely many positive unit fractions
from one has a gap of at least the reciprocal of the denominator product. -/
theorem prefix_remainder_gap {α : Type*} [DecidableEq α]
    (s : Finset α) (n : α → ℕ)
    (hn : ∀ j ∈ s, 0 < n j)
    (hrem : 0 < 1 - ∑ j ∈ s, (1 : ℚ) / (n j : ℚ)) :
    (1 : ℚ) / (∏ j ∈ s, n j : ℕ) ≤
      1 - ∑ j ∈ s, (1 : ℚ) / (n j : ℚ) := by
  apply one_div_le_of_den_dvd hrem
  · exact Finset.prod_pos hn
  · have hd := sum_den_dvd_prod s (fun j => (1 : ℚ) / (n j : ℚ))
    have heq : (∏ j ∈ s, ((1 : ℚ) / (n j : ℚ)).den) = ∏ j ∈ s, n j := by
      apply Finset.prod_congr rfl
      intro j hj
      simpa only [one_div] using Rat.inv_natCast_den_of_pos (hn j hj)
    simpa only [Rat.ofNat_sub_den, heq] using hd

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrefixGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- The elementary growth estimate for successive products of denominators. -/
theorem prefix_growth_bound (k t : ℕ) (P : ℕ → ℕ)
    (hzero : P 0 = 1)
    (hstep : ∀ i < t, P (i + 1) ≤ k * (P i) ^ 2) :
    ∀ i ≤ t, P i ≤ k ^ (2 ^ i - 1) := by
  intro i hi
  induction i with
  | zero => simp [hzero]
  | succ i ih =>
    have hit : i < t := by omega
    have hip := ih (by omega)
    have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
    have hexp : 1 + (2 ^ i - 1) * 2 = 2 ^ (i + 1) - 1 := by
      rw [pow_succ]
      omega
    calc
      P (i + 1) ≤ k * (P i) ^ 2 := hstep i hit
      _ ≤ k * (k ^ (2 ^ i - 1)) ^ 2 := Nat.mul_le_mul_left k (Nat.pow_le_pow_left hip 2)
      _ = k ^ (2 ^ (i + 1) - 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega

/-- The bound for the next denominator follows from the prefix-product bound. -/
theorem denominator_growth_bound (k i P n : ℕ)
    (hP : P ≤ k ^ (2 ^ i - 1)) (hn : n ≤ k * P) :
    n ≤ k ^ (2 ^ i) := by
  have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
  calc
    n ≤ k * P := hn
    _ ≤ k * k ^ (2 ^ i - 1) := Nat.mul_le_mul_left k hP
    _ = k ^ (2 ^ i) := by
      rw [← pow_succ']
      congr 1
      omega

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DenominatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

 theorem ordered_unit_tail_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) (i : Fin k) :
    0 < 1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j ∧
    1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j ≤
      (k : ℚ) / n i := by
  let s : Finset (Fin k) := Finset.univ.filter (· < i)
  let t : Finset (Fin k) := Finset.univ.filter (i ≤ ·)
  have hsplit : (∑ j ∈ s, (1 : ℚ) / n j) + (∑ j ∈ t, (1 : ℚ) / n j) = 1 := by
    calc
      _ = ∑ j : Fin k, (1 : ℚ) / n j := by
        simpa [s, t, not_lt] using
          (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin k)))
            (p := fun j => j < i) (f := fun j => (1 : ℚ) / n j))
      _ = 1 := hsum
  have hrem : 1 - ∑ j ∈ s, (1 : ℚ) / n j = ∑ j ∈ t, (1 : ℚ) / n j := by
    linarith
  change 0 < 1 - ∑ j ∈ s, (1 : ℚ) / n j ∧ _
  rw [hrem]
  constructor
  · apply lt_of_lt_of_le (show 0 < (1 : ℚ) / n i from div_pos zero_lt_one (by exact_mod_cast hn i))
    apply Finset.single_le_sum (f := fun j => (1 : ℚ) / n j) (a := i)
    · intro j hj
      positivity
    · simp [t]
  · calc
      ∑ j ∈ t, (1 : ℚ) / n j ≤ ∑ _j ∈ t, (1 : ℚ) / n i := by
        apply Finset.sum_le_sum
        intro j hj
        apply one_div_le_one_div_of_le
        · exact_mod_cast hn i
        · exact_mod_cast hmono (by simpa [t] using hj)
      _ = (t.card : ℚ) / n i := by simp [div_eq_mul_inv]
      _ ≤ (k : ℚ) / n i := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (show t.card ≤ k from (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ.trans (Fintype.card_fin k)))
        · positivity

 theorem denominator_le_prefix_product {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) (i : Fin k)
    (hgap : (1 : ℚ) / (∏ j ∈ Finset.univ.filter (· < i), n j : ℕ) ≤
      1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j) :
    n i ≤ k * ∏ j ∈ Finset.univ.filter (· < i), n j := by
  have hle := hgap.trans (ordered_unit_tail_bound n hn hmono hsum i).2
  have hp : (0 : ℚ) < (∏ j ∈ Finset.univ.filter (· < i), n j : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => hn j)
  have hi : (0 : ℚ) < n i := by exact_mod_cast hn i
  have hcross := (div_le_div_iff₀ hp hi).mp hle
  norm_num only [one_mul] at hcross
  exact_mod_cast hcross

/-- The coordinate estimate only needs weak ordering, so it also applies to
expansions with repeated denominators. -/
theorem ordered_unit_denominator_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) :
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val) := by
  let P : ℕ → ℕ := fun t => ∏ j ∈ Finset.univ.filter (fun j : Fin k => j.val < t), n j
  have hrec : ∀ i : Fin k, n i ≤ k * P i.val := by
    intro i
    apply denominator_le_prefix_product n hn hmono hsum i
    exact prefix_remainder_gap _ n (fun j _ => hn j)
      (ordered_unit_tail_bound n hn hmono hsum i).1
  have hzero : P 0 = 1 := by simp [P]
  have hstep : ∀ t < k, P (t + 1) ≤ k * (P t) ^ 2 := by
    intro t ht
    let i : Fin k := ⟨t, ht⟩
    have hs : Finset.univ.filter (fun j : Fin k => j.val < t + 1) =
        insert i (Finset.univ.filter (fun j : Fin k => j.val < t)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          have hne : j.val ≠ t := by
            intro he
            apply hji
            apply Fin.ext
            exact he
          omega
      · rintro (rfl | hj)
        · exact Nat.lt_succ_self t
        · omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin k => j.val < t) := by
      simp [i]
    have heq : P (t + 1) = n i * P t := by
      simp only [P, hs, Finset.prod_insert hnot]
    calc
      P (t + 1) = n i * P t := heq
      _ ≤ (k * P t) * P t := Nat.mul_le_mul_right (P t) (hrec i)
      _ = k * (P t) ^ 2 := by ring
  intro i
  exact denominator_growth_bound k i.val (P i.val) (n i)
    (prefix_growth_bound k k P hzero hstep i.val i.isLt.le) (hrec i)

 theorem one_expansion_denominator_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : IsOneExpansion n) : ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val) :=
  ordered_unit_denominator_bound n (fun i => hn.1 i) hn.2.1.monotone hn.2.2

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Counting positive integer functions in a varying finite box. -/
theorem finite_ncard_le_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℕ)) (B : ι → ℕ)
    (hS : ∀ n ∈ S, ∀ i, 1 ≤ n i ∧ n i ≤ B i) :
    S.Finite ∧ S.ncard ≤ ∏ i, B i := by
  classical
  have hsub : S ⊆ Set.pi Set.univ (fun i => Set.Icc 1 (B i)) := by
    intro n hn i _
    exact hS n hn i
  have hcard : (Set.pi Set.univ (fun i => Set.Icc 1 (B i))).encard =
      (∏ i, B i : ℕ) := by
    rw [Set.encard_pi_eq_prod_encard, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [← (Set.finite_Icc 1 (B i)).cast_ncard_eq]
    simp
  apply Set.encard_le_coe_iff_finite_ncard_le.mp
  rw [← hcard]
  exact Set.encard_le_encard hsub

/-- Geometric exponent sum for the denominator box. -/
theorem sum_two_pow_fin (k : ℕ) :
    (∑ i : Fin k, 2 ^ i.val) = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    have hpos : 0 < 2 ^ k := pow_pos (by decide) _
    omega

/-- The denominator box appearing in the counting bound has the stated size. -/
theorem prod_egyptian_bounds (k : ℕ) :
    (∏ i : Fin k, k ^ (2 ^ i.val)) = k ^ (2 ^ k - 1) := by
  rw [Finset.prod_pow_eq_pow_sum, sum_two_pow_fin]

/-- Pointwise denominator bounds give finiteness and the sharp box-count estimate. -/
theorem finite_ncard_le_egyptian_box (k : ℕ) (S : Set (Fin k → ℕ))
    (hpos : ∀ n ∈ S, ∀ i, 1 ≤ n i)
    (hbound : ∀ n ∈ S, ∀ i, n i ≤ k ^ (2 ^ i.val)) :
    S.Finite ∧ S.ncard ≤ k ^ (2 ^ k - 1) := by
  simpa only [prod_egyptian_bounds] using
    finite_ncard_le_box S (fun i => k ^ (2 ^ i.val))
      (fun n hn i => ⟨hpos n hn i, hbound n hn i⟩)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

theorem one_expansions_finite_and_bounded_oai :
    (∀ k : ℕ, Set.Finite (OneExpansions k) ∧
    F k ≤ k ^ (2 ^ k - 1)) ∧
  (∀ k : ℕ, ∀ n : Fin k → ℕ, IsOneExpansion n →
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val)) := by
  constructor
  · intro k
    exact finite_ncard_le_egyptian_box k (OneExpansions k)
      (fun n hn => hn.1) (fun n hn => one_expansion_denominator_bound n hn)
  · intro k n hn
    exact one_expansion_denominator_bound n hn

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.one_expansions_finite_and_bounded_oai := @OAI.Problem337.one_expansions_finite_and_bounded_oai
