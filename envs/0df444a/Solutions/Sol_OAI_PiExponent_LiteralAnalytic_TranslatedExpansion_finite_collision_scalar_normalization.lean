-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.finite_collision_scalar_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:56:32.513497+00:00
-- url     : https://prove2.me/submissions/c378663f-acda-4c07-9b09-10f65cc040ac

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Mathlib.Data.Nat.Choose.Cast

open scoped BigOperators Topology
open OAI.PiExponent
open OAI.PiExponent.Collision
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (ell : ι → ℕ)
    {H budgetCoeff v : ℝ} (hH : 0 < H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    (((Fintype.card ι).factorial : ℝ) *
      Real.exp (H * budgetCoeff) ^ Fintype.card ι *
      (2 : ℝ) ^ (∑ r, ell r)) *
      Collision.collisionRatio ^
        (∑ A : κ, (((Finset.univ : Finset ι).filter
          (fun r => group r = A)).card.choose 2)) *
      ((1 - Collision.collisionRatio)⁻¹) ^ Fintype.card ι ≤
    Real.exp (-(Real.log 2 / 4) *
      (∑ A : κ,
        (((Finset.univ : Finset ι).filter (fun r => group r = A)).card : ℝ) ^ 2) +
      (Fintype.card ι : ℝ) * H *
        (budgetCoeff + Real.log 2 / v +
          Collision.collisionRemainder (Fintype.card ι) H)) := by
  let n : ℕ := Fintype.card ι
  let d : κ → ℕ := fun A =>
    ((Finset.univ : Finset ι).filter (fun r => group r = A)).card
  let P : ℕ := ∑ A : κ, (d A).choose 2
  let Q : ℝ := ∑ A : κ, (d A : ℝ) ^ 2
  let S : ℕ := ∑ r, ell r

  -- The fibers partition the row set, including when that set is empty.
  have hsum_nat : (∑ A : κ, d A) = n := by
    simpa [d, n] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset ι) (Finset.univ : Finset κ) group)
  have hsum : (∑ A : κ, (d A : ℝ)) = (n : ℝ) := by
    exact_mod_cast hsum_nat
  have hpairs : (∑ A : κ, ((d A).choose 2 : ℝ)) = (P : ℝ) := by
    simp only [P, Nat.cast_sum]
  have hpair : Q = (n : ℝ) + 2 * (P : ℝ) := by
    change (∑ A : κ, (d A : ℝ) ^ 2) = (n : ℝ) + 2 * (P : ℝ)
    calc
      _ = ∑ A : κ, ((d A : ℝ) + 2 * ((d A).choose 2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro A _
        rw [Nat.cast_choose_two ℝ]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hpairs]

  -- This factorial estimate also covers n = 0, since both powers are 1.
  have hfact : (n.factorial : ℝ) ≤ Real.exp ((n : ℝ) * Real.log (n : ℝ)) := by
    calc
      (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
        exact_mod_cast (Nat.factorial_le_pow n)
      _ ≤ Real.exp (Real.log (n : ℝ)) ^ n :=
        pow_le_pow_left₀ (Nat.cast_nonneg n) (Real.le_exp_log (n : ℝ)) n
      _ = _ := (Real.exp_nat_mul _ _).symm

  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hratio : Collision.collisionRatio < 1 := by
    unfold Collision.collisionRatio
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hbase : 0 < 1 - Collision.collisionRatio := sub_pos.mpr hratio
  have hcoef : Real.exp (H * budgetCoeff) ^ n =
      Real.exp ((n : ℝ) * (H * budgetCoeff)) :=
    (Real.exp_nat_mul _ _).symm
  have htwo : (2 : ℝ) ^ S = Real.exp ((S : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hcollision : Collision.collisionRatio ^ P =
      Real.exp ((P : ℝ) * (-Real.log 2 / 2)) := by
    unfold Collision.collisionRatio
    rw [Real.exp_nat_mul]
  have hinverse : ((1 - Collision.collisionRatio)⁻¹) ^ n =
      Real.exp ((n : ℝ) * (-Real.log (1 - Collision.collisionRatio))) := by
    rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hbase]
  have hrow : (S : ℝ) * Real.log 2 ≤
      ((n : ℝ) * H / v) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hell hlog2.le
  have hrem : H * Collision.collisionRemainder n H =
      Real.log (n : ℝ) + Real.log 2 / 4 -
        Real.log (1 - Collision.collisionRatio) := by
    unfold Collision.collisionRemainder
    exact mul_div_cancel₀ _ hH.ne'
  have hnormalize :
      -(Real.log 2 / 4) * Q + (n : ℝ) * H *
          (budgetCoeff + Real.log 2 / v + Collision.collisionRemainder n H) =
        (n : ℝ) * Real.log (n : ℝ) +
          ((n : ℝ) * (H * budgetCoeff) + ((n : ℝ) * H / v) * Real.log 2 +
            (P : ℝ) * (-Real.log 2 / 2) +
            (n : ℝ) * (-Real.log (1 - Collision.collisionRatio))) := by
    rw [hpair]
    linear_combination (n : ℝ) * hrem

  change (((n.factorial : ℝ) * Real.exp (H * budgetCoeff) ^ n * (2 : ℝ) ^ S) *
      Collision.collisionRatio ^ P * ((1 - Collision.collisionRatio)⁻¹) ^ n) ≤
    Real.exp (-(Real.log 2 / 4) * Q + (n : ℝ) * H *
      (budgetCoeff + Real.log 2 / v + Collision.collisionRemainder n H))
  calc
    _ = (n.factorial : ℝ) * Real.exp
        ((n : ℝ) * (H * budgetCoeff) + (S : ℝ) * Real.log 2 +
          (P : ℝ) * (-Real.log 2 / 2) +
          (n : ℝ) * (-Real.log (1 - Collision.collisionRatio))) := by
      rw [hcoef, htwo, hcollision, hinverse]
      simp only [Real.exp_add]
      ring
    _ ≤ Real.exp ((n : ℝ) * Real.log (n : ℝ)) * Real.exp
        ((n : ℝ) * (H * budgetCoeff) + (S : ℝ) * Real.log 2 +
          (P : ℝ) * (-Real.log 2 / 2) +
          (n : ℝ) * (-Real.log (1 - Collision.collisionRatio))) :=
      mul_le_mul_of_nonneg_right hfact (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) * Real.log (n : ℝ) +
        ((n : ℝ) * (H * budgetCoeff) + (S : ℝ) * Real.log 2 +
          (P : ℝ) * (-Real.log 2 / 2) +
          (n : ℝ) * (-Real.log (1 - Collision.collisionRatio)))) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [hnormalize]
      nlinarith only [hrow]