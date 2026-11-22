-- Prove2me | solution 1 for MasulloRepair.pole_cell_overlap
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T19:31:46.932536+00:00
-- url     : https://prove2.me/submissions/ac2f8548-4305-484d-8118-0e7b5a441714

import Definitions.Def_MasulloRepair_PoleCells
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open MasulloRepair

private lemma exp_affine_integral (a b c : ℝ) :
    (∫ x in a..b, Real.exp (x + c)) = Real.exp (b + c) - Real.exp (a + c) := by
  simp_rw [Real.exp_add]
  rw [intervalIntegral.integral_mul_const, integral_exp]
  ring

private lemma pole_cell_product (L t x : ℝ) (k : ℕ) :
    poleCell L k (x - t) * poleCell L k x =
      Real.exp (x + (-((k : ℝ) + 1) * L - t / 2)) := by
  simp only [poleCell, neg_mul_neg, ← Real.exp_add]
  congr 1
  ring

private lemma pole_cell_cross_product (L t x : ℝ) (k : ℕ) :
    poleCell L k (x - t + L) * poleCell L (k + 1) x =
      Real.exp (x + (-((k : ℝ) + 1) * L - t / 2)) := by
  simp only [poleCell, neg_mul_neg, ← Real.exp_add, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

private lemma pole_overlap_zero (L t : ℝ) :
    poleCellOverlap L 0 t = Real.exp (-t / 2) - Real.exp (-L + t / 2) := by
  simp only [poleCellOverlap, pole_cell_product, exp_affine_integral, Nat.cast_zero]
  congr 1 <;> congr 1 <;> ring

private lemma pole_overlap_succ (L t : ℝ) (k : ℕ) :
    poleCellOverlap L (k + 1) t =
      Real.exp (-L) ^ (k + 1) * (1 - Real.exp (-L)) * Real.exp (t / 2) := by
  simp only [poleCellOverlap, pole_cell_cross_product, pole_cell_product,
    exp_affine_integral, Nat.cast_add, Nat.cast_one, zero_add]
  have h1 : t + (-((k : ℝ) + 1) * L - t / 2) =
      -((k : ℝ) + 1) * L + t / 2 := by ring
  have h2 : L + (-((k : ℝ) + 1 + 1) * L - t / 2) =
      -((k : ℝ) + 1) * L - t / 2 := by ring
  have h3 : t + (-((k : ℝ) + 1 + 1) * L - t / 2) =
      -((k : ℝ) + 1) * L + (-L + t / 2) := by ring
  rw [h1, h2, h3]
  simp only [Real.exp_add]
  have he : Real.exp (-((k : ℝ) + 1) * L) = Real.exp (-L) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem solution (L : ℝ) (hL : 0 < L) (t : ℝ) (ht : t ∈ Set.Icc 0 L) :
    poleCellOverlap L 0 t = Real.exp (-t / 2) - Real.exp (-L + t / 2) ∧
    (∀ k : ℕ, poleCellOverlap L (k + 1) t =
      Real.exp (-L) ^ (k + 1) * (1 - Real.exp (-L)) * Real.exp (t / 2)) ∧
    HasSum (fun k : ℕ => poleCellOverlap L k t) (Real.exp (-t / 2)) := by
  refine ⟨pole_overlap_zero L t, pole_overlap_succ L t, ?_⟩
  have hr : Real.exp (-L) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hL)
  have hrne : 1 - Real.exp (-L) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
  have hgeo := (hasSum_geometric_of_lt_one (le_of_lt (Real.exp_pos (-L))) hr).mul_left
    (Real.exp (-L) * (1 - Real.exp (-L)) * Real.exp (t / 2))
  have htail : HasSum (fun k : ℕ => poleCellOverlap L (k + 1) t)
      (Real.exp (-L + t / 2)) := by
    convert! hgeo using 1
    · funext k
      rw [pole_overlap_succ, pow_succ]
      ring
    · rw [Real.exp_add]
      field_simp [hrne]
  have hcancel : Real.exp (-L + t / 2) +
      (Real.exp (-t / 2) - Real.exp (-L + t / 2)) = Real.exp (-t / 2) := by ring
  simpa only [Finset.sum_range_one, pole_overlap_zero, hcancel] using
    (hasSum_nat_add_iff (f := fun k : ℕ => poleCellOverlap L k t) 1).mp htail

#print axioms solution
