-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.floor_vector_mem_shifted_weighted_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:12:32.982475+00:00
-- url     : https://prove2.me/submissions/6190f13b-02b8-4de1-864b-c93b95850dfe

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T)
    (x : Fin n → Real)
    (hx : (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T) :
    (fun i => Nat.floor (x i)) ∈ realWeightedSimplex w (T + Finset.univ.sum w) := by
  classical
  let H : Real := T + Finset.univ.sum w
  have hweights : 0 ≤ Finset.univ.sum w := by
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (hw i)
  have hterm (i : Fin n) : w i * x i ≤ ∑ j, w j * x j := by
    change w i * x i ≤ Finset.univ.sum (fun j : Fin n => w j * x j)
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin n => w j * x j)
      (fun j hj => mul_nonneg (le_of_lt (hw j)) (hx.1 j))
      (Finset.mem_univ i)
  have hcoord (i : Fin n) : x i ≤ H / w i := by
    rw [le_div_iff₀ (hw i)]
    dsimp [H]
    nlinarith [hterm i, hx.2, hweights]
  have hfloorSum :
      (∑ i, w i * (Nat.floor (x i) : Real)) ≤ H := by
    apply le_of_lt
    calc
      (∑ i, w i * (Nat.floor (x i) : Real)) ≤ ∑ i, w i * x i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (hx.1 i)) (le_of_lt (hw i))
      _ < T := hx.2
      _ ≤ H := by
        dsimp [H]
        linarith [hweights]
  rw [realWeightedSimplex]
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · intro i
    exact Nat.lt_succ_of_le (Nat.floor_mono (hcoord i))
  · exact hfloorSum