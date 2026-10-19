-- Prove2me | solution 1 for OAI.C0Absorption.seminorm_sign_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:04:05.047853+00:00
-- url     : https://prove2.me/submissions/66f9e0ac-7244-49f1-acab-cd6141f1f883

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    2 * (q (m i)) ^ 2 ≤
      (q (∑ j, realSign (ε j) • m j)) ^ 2 +
      (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2 := by
  set S1 := ∑ j, realSign (ε j) • m j
  set S2 := ∑ j, realSign (flipSign i ε j) • m j
  have key : S1 - S2 = (2 * realSign (ε i)) • m i := by
    simp only [S1, S2, ← Finset.sum_sub_distrib, ← sub_smul]
    rw [Finset.sum_eq_single i]
    · congr 1
      simp only [flipSign, Equiv.coe_fn_mk, if_true, realSign_not]; ring
    · intro j _ hj
      simp [flipSign, hj]
    · simp
  have hq : q ((2 * realSign (ε i)) • m i) = 2 * q (m i) := by
    rw [map_smul_eq_mul]; simp [abs_mul]
  have h1 : 2 * q (m i) ≤ q S1 + q S2 := by
    rw [← hq, ← key]; exact map_sub_le_add q S1 S2
  have h0 : 0 ≤ q (m i) := apply_nonneg q _
  have hS1 : 0 ≤ q S1 := apply_nonneg q _
  have hS2 : 0 ≤ q S2 := apply_nonneg q _
  nlinarith [sq_nonneg (q S1 - q S2), mul_le_mul h1 h1 (by positivity) (by positivity)]

