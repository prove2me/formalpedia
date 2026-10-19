-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_dichotomy_collision
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:57:39.486147+00:00
-- url     : https://prove2.me/submissions/89ee256e-f451-4009-82d1-5f6f7c59e30c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators

universe u v

theorem solution
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (low : Finset κ)
    {eta N : ℝ}
    (heta : 0 ≤ eta) (hN : 0 < N)
    (hcapacity : (low.card : ℝ) ≤ N)
    (hlowMass :
      eta * (Fintype.card ι : ℝ) ≤
        ∑ a ∈ low,
          (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)) :
    eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤
      ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) ^ 2 := by
  let occ : κ → ℝ := fun a =>
    (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)
  change eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 / N ≤ ∑ a : κ, occ a ^ 2
  have hmass : eta * (Fintype.card ι : ℝ) ≤ ∑ a ∈ low, occ a := hlowMass
  have hbase : 0 ≤ eta * (Fintype.card ι : ℝ) :=
    mul_nonneg heta (Nat.cast_nonneg _)
  have hmass_sq : (eta * (Fintype.card ι : ℝ)) ^ 2 ≤ (∑ a ∈ low, occ a) ^ 2 :=
    pow_le_pow_left₀ hbase hmass 2
  have hcs : (∑ a ∈ low, occ a) ^ 2 ≤
      (low.card : ℝ) * ∑ a ∈ low, occ a ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hlowSq_nonneg : 0 ≤ ∑ a ∈ low, occ a ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg (occ a))
  have hsumSq : (∑ a ∈ low, occ a ^ 2) ≤ ∑ a : κ, occ a ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ low)
      (fun a _ _ => sq_nonneg (occ a))
  have hbound : eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 ≤
      N * ∑ a : κ, occ a ^ 2 := by
    calc
      eta ^ 2 * (Fintype.card ι : ℝ) ^ 2 =
          (eta * (Fintype.card ι : ℝ)) ^ 2 := (mul_pow _ _ _).symm
      _ ≤ (∑ a ∈ low, occ a) ^ 2 := hmass_sq
      _ ≤ (low.card : ℝ) * ∑ a ∈ low, occ a ^ 2 := hcs
      _ ≤ N * ∑ a ∈ low, occ a ^ 2 :=
        mul_le_mul_of_nonneg_right hcapacity hlowSq_nonneg
      _ ≤ N * ∑ a : κ, occ a ^ 2 :=
        mul_le_mul_of_nonneg_left hsumSq hN.le
  exact (div_le_iff₀ hN).2 (hbound.trans_eq (mul_comm _ _))
