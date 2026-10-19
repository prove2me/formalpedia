-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.realWeightedSimplex_mem_of_pos_weighted_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:34:26.112887+00:00
-- url     : https://prove2.me/submissions/0a2a2cf6-c7bd-4b01-9dd3-c10602497fd0

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
open OAI.PiExponent

theorem solution
    {m : ℕ} (w : Fin m → ℝ) {T : ℝ} (a : Fin m → ℕ)
    (hT : 0 < T) (hw : ∀ i, 0 < w i)
    (ha : ∑ i, w i * (a i : ℝ) ≤ T) :
    a ∈ realWeightedSimplex w T := by
  classical
  simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  refine ⟨?_, ha⟩
  intro i
  have hterm : w i * (a i : ℝ) ≤ T := by
    have hle := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin m => w j * (a j : ℝ))
      (fun j hj => mul_nonneg (le_of_lt (hw j)) (Nat.cast_nonneg _))
      (Finset.mem_univ i)
    exact le_trans hle ha
  have hratio : (a i : ℝ) ≤ T / w i := by
    rw [le_div_iff₀ (hw i)]
    simpa [mul_comm] using hterm
  exact Nat.lt_succ_of_le (Nat.le_floor hratio)