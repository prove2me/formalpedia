-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weightedStrictSimplex_mem_of_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:52:10.649737+00:00
-- url     : https://prove2.me/submissions/3c2bb254-f0bb-4f81-92c1-bacb37424bff

import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

open scoped BigOperators
open OAI.PiExponent

theorem solution
    {d : ℕ} (u : Fin d → ℝ) (H : ℝ)
    (hu : ∀ i, 0 < u i) (a : Fin d → ℕ)
    (ha : (∑ i, u i * (a i : ℝ)) < H) :
    a ∈ strictWeightedSimplex u H := by
  classical
  have hterm (i : Fin d) : u i * (a i : ℝ) < H := by
    have hle : u i * (a i : ℝ) ≤ ∑ j, u j * (a j : ℝ) :=
      Finset.single_le_sum
        (fun j hj => mul_nonneg (le_of_lt (hu j)) (Nat.cast_nonneg (a j)))
        (Finset.mem_univ i)
    exact lt_of_le_of_lt hle ha
  have hcoord (i : Fin d) : (a i : ℝ) < H / u i := by
    apply (lt_div_iff₀ (hu i)).2
    nlinarith [hterm i]
  rw [strictWeightedSimplex, realWeightedSimplex]
  simp only [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · constructor
    · intro i
      apply Finset.mem_range.mpr
      have hfloor : a i ≤ ⌊H / u i⌋₊ := Nat.le_floor (le_of_lt (hcoord i))
      exact Nat.lt_succ_of_le hfloor
    · exact le_of_lt ha
  · exact ha