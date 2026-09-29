-- Prove2me | solution 1 for Maldacena1999.poincareEmbedding_mem_AdS
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:29:50.126327+00:00
-- url     : https://prove2.me/submissions/6a2e3481-ea7f-4c40-9958-832d4b123608

import Mathlib
import Definitions.Def_Maldacena1999_Defs

set_option autoImplicit false

open Filter Topology

open Maldacena1999 in
theorem solution (p : ℕ) (R : ℝ) (hR : 0 < R)
    (U : ℝ) (hU : 0 < U) (x : Fin (p + 1) → ℝ) :
    poincareEmbedding p R (U, x) ∈ AdS p R := by
  set M := minkowskiForm p x with hM
  set X := poincareEmbedding p R (U, x) with hX
  have h0 : X 0 = (U + (M * U / R ^ 2 + R ^ 2 / U)) / 2 := by
    simp [X, poincareEmbedding, M]
  have hmid : ∀ a : Fin (p + 1), X a.castSucc.succ = x a * U / R := by
    intro a
    have h1 : ¬ ((a.castSucc.succ : Fin (p + 3)).val = 0) := by simp
    have h2 : (a.castSucc.succ : Fin (p + 3)).val ≤ p + 1 := by
      have := a.isLt
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    simp only [X, poincareEmbedding]
    rw [if_neg h1, dif_pos h2]
    simp
  have hlast : X (Fin.last (p + 1)).succ = (U - (M * U / R ^ 2 + R ^ 2 / U)) / 2 := by
    have h1 : ¬ (((Fin.last (p + 1)).succ : Fin (p + 3)).val = 0) := by simp
    have h2 : ¬ (((Fin.last (p + 1)).succ : Fin (p + 3)).val ≤ p + 1) := by simp
    simp only [X, poincareEmbedding]
    rw [if_neg h1, dif_neg h2]
  have s0 : ambientSign p 0 = -1 := by simp [ambientSign]
  have smid : ∀ a : Fin (p + 1), ambientSign p a.castSucc.succ
      = if a.val = 0 then (-1 : ℝ) else 1 := by
    intro a
    simp only [ambientSign, Fin.val_succ, Fin.val_castSucc]
    by_cases ha : a.val = 0
    · simp [ha]
    · rw [if_neg ha, if_neg (by omega)]
  have slast : ambientSign p (Fin.last (p + 1)).succ = 1 := by
    simp [ambientSign]
  have hsum : ∑ a : Fin (p + 1), ambientSign p a.castSucc.succ * X a.castSucc.succ ^ 2
      = (U / R) ^ 2 * M := by
    rw [hM, minkowskiForm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smid a, hmid a]
    ring
  show ambientForm p X = -R ^ 2
  unfold ambientForm
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, hsum, s0, slast, h0, hlast]
  field_simp
  ring
#print axioms solution
