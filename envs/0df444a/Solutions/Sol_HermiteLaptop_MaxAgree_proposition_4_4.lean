-- Prove2me | solution 1 for HermiteLaptop.MaxAgree.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-18T15:22:52.431992+00:00
-- url     : https://prove2.me/submissions/d0a54bd7-1234-45b5-87f0-237956bfc0f1

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Hermite
import Theorems.Thm_HermiteLaptop_MaxAgree_four_spoke_degree20_lower_bounds
import Theorems.Thm_HermiteLaptop_MaxAgree_five_spoke_degree20_lower_bounds

set_option autoImplicit false

namespace HermiteLaptop.MaxAgree

/-- Numerators of the lower coefficient bounds with common denominator one million. -/
def momentTableFour : List ℕ :=
  [250000, 353204, 101321, 38488, 37526, 17395, 19263, 11063, 11857, 7898, 8181,
    5988, 6079, 4729, 4749, 3850, 3845, 3210, 3197, 2728, 2713]

def momentTableFive : List ℕ :=
  [200000, 338121, 133340, 36608, 44451, 19403, 21276, 13169, 12703, 9536, 8708,
    7209, 6493, 5651, 5104, 4567, 4158, 3784, 3476, 3199, 2962]

def momentTableLower (k m : ℕ) : ℚ :=
  ((if k = 4 then momentTableFour else if k = 5 then momentTableFive else [])[m]?.getD 0 : ℕ) /
    (1000000 : ℚ)

private def val {R : Type*} [Semiring R] : List ℕ → R → R
  | [], _ => 0
  | c :: cs, x => (c : R) + x * val cs x

private def slope {R : Type*} [Semiring R] : List ℕ → R → R
  | [], _ => 0
  | _ :: cs, x => val cs x + x * slope cs x

private theorem val_slope_nonneg (cs : List ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ val cs t ∧ 0 ≤ slope cs t := by
  induction cs with
  | nil => simp [val, slope]
  | cons c cs ih =>
    exact ⟨add_nonneg (Nat.cast_nonneg _) (mul_nonneg ht ih.1),
      add_nonneg ih.1 (mul_nonneg ht ih.2)⟩

private theorem tangent_lower (cs : List ℕ) (t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    val cs t + slope cs t * (x - t) ≤ val cs x := by
  induction cs with
  | nil => simp [val, slope]
  | cons c cs ih =>
    simp only [val, slope]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr ih),
      mul_nonneg (val_slope_nonneg cs t ht).2 (sq_nonneg (x-t))]

private theorem val_eq_sum (cs : List ℕ) (n : ℕ) (hle : cs.length ≤ n) (x : ℝ) :
    (∑ m ∈ Finset.range n, ((cs[m]?.getD 0 : ℕ) : ℝ) * x^m) = val cs x := by
  induction n generalizing cs with
  | zero =>
    have : cs = [] := List.length_eq_zero_iff.mp (by omega)
    simp [this, val]
  | succ n ih =>
    cases cs with
    | nil => simp [val]
    | cons c cs =>
      rw [Finset.sum_range_succ']
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
        pow_zero, mul_one, pow_succ]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, ih cs (by simpa using hle)]
      simp [val, add_comm, mul_comm]

private theorem val_ratCast (cs : List ℕ) (q : ℚ) : ((val cs q : ℚ) : ℝ) = val cs (q:ℝ) := by
  induction cs with
  | nil => simp [val]
  | cons c cs ih => simp [val, ih]

private theorem slope_ratCast (cs : List ℕ) (q : ℚ) : ((slope cs q : ℚ) : ℝ) = slope cs (q:ℝ) := by
  induction cs with
  | nil => simp [slope]
  | cons c cs ih => simp [slope, val_ratCast, ih]

private def t : ℚ := 7530039 / 10000000

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem tangent_checks :
    t * (364 * slope momentTableFour t + 636 * slope momentTableFive t) ≤
      364 * val momentTableFour t + 636 * val momentTableFive t ∧
    781800000 ≤ 364 * slope momentTableFour t + 636 * slope momentTableFive t := by
  decide +kernel

private theorem table_sum (cs : List ℕ) (hle : cs.length ≤ 25) (x : ℝ) :
    (∑ m ∈ Finset.range 25, (((((cs[m]?.getD 0 : ℕ) : ℚ) / 1000000 : ℚ) : ℝ)) * x^m) =
      val cs x / 1000000 := by
  rw [← val_eq_sum cs 25 hle x, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  push_cast
  ring

/-- The six-decimal lower table, padded with zeros through degree 24, has the required
positive-edge polynomial bound. The proof applies on the whole nonnegative half-line. -/
theorem momentTable_positive_edge (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (0.7818 : ℝ) * ρ ≤
      0.364 * ∑ m ∈ Finset.range 25, (momentTableLower 4 m : ℝ) * ρ^m +
      0.636 * ∑ m ∈ Finset.range 25, (momentTableLower 5 m : ℝ) * ρ^m := by
  simp only [momentTableLower, ↓reduceIte, show (5 : ℕ) ≠ 4 by decide]
  rw [table_sum momentTableFour (by decide), table_sum momentTableFive (by decide)]
  have ht : 0 ≤ (t : ℝ) := by norm_num [t]
  have h₄ := tangent_lower momentTableFour (t:ℝ) ρ ht hρ
  have h₅ := tangent_lower momentTableFive (t:ℝ) ρ ht hρ
  have ha := (Rat.cast_le (K := ℝ)).mpr tangent_checks.1
  have hb := (Rat.cast_le (K := ℝ)).mpr tangent_checks.2
  push_cast at ha hb
  simp only [val_ratCast, slope_ratCast] at ha hb
  nlinarith [mul_nonneg hρ (sub_nonneg.mpr hb)]

/-- To establish Proposition 4.4 it suffices to verify the two degree-20 tables
against the actual Hermite coefficients. The remaining entries are zero. -/
theorem positive_polynomial_of_table_bounds
    (h : ∀ k ∈ ({4, 5} : Finset ℕ), ∀ m ≤ 20, (momentTableLower k m : ℝ) ≤ coeffC k m) :
    ∃ cl : ℕ → ℕ → ℚ,
      (∀ k ∈ ({4, 5} : Finset ℕ), ∀ m ≤ 24, (cl k m : ℝ) ≤ coeffC k m) ∧
      ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (0.7818 : ℝ) * ρ ≤
          0.364 * ∑ m ∈ Finset.range 25, (cl 4 m : ℝ) * ρ^m +
          0.636 * ∑ m ∈ Finset.range 25, (cl 5 m : ℝ) * ρ^m := by
  refine ⟨momentTableLower, ?_, fun ρ hρ => momentTable_positive_edge ρ hρ.1⟩
  intro k hk m _
  by_cases hm : m ≤ 20
  · exact h k hk m hm
  have h4 : momentTableFour.length ≤ m := by
    change 21 ≤ m
    omega
  have h5 : momentTableFive.length ≤ m := by
    change 21 ≤ m
    omega
  have hn : 0 ≤ coeffC k m := by
    unfold coeffC levelWeight
    positivity
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl <;>
    simpa [momentTableLower, List.getElem?_eq_none h4, List.getElem?_eq_none h5] using hn

end HermiteLaptop.MaxAgree

open HermiteLaptop.MaxAgree

theorem solution :
    ∃ cl : ℕ → ℕ → ℚ,
      (∀ k ∈ ({4, 5} : Finset ℕ), ∀ m ≤ 24, (cl k m : ℝ) ≤ coeffC k m) ∧
      ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (0.7818 : ℝ) * ρ ≤
          0.364 * ∑ m ∈ Finset.range 25, (cl 4 m : ℝ) * ρ ^ m +
          0.636 * ∑ m ∈ Finset.range 25, (cl 5 m : ℝ) * ρ ^ m := by
  apply positive_polynomial_of_table_bounds
  intro k hk m hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · simpa [momentTableLower, momentTableFour] using four_spoke_degree20_lower_bounds m hm
  · simpa [momentTableLower, momentTableFive] using five_spoke_degree20_lower_bounds m hm

