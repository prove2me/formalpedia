-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.strictWeightedSimplex_card_ge_shifted_volume_covered_by_boxes_pointwise_cover
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:03:54.377579+00:00
-- url     : https://prove2.me/submissions/a76df28f-a01c-4315-8b0e-3f41eff15c52

import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_floor_vector_mem_shifted_weighted_simplex
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_floor_sum_lt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T)
    (x : Fin n → Real)
    (hx : (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T) :
    ∃ a : Fin n → Nat,
      a ∈ strictWeightedSimplex w (T + Finset.univ.sum w) ∧
      ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1 := by
  classical
  refine ⟨fun i => Nat.floor (x i), ?_, ?_⟩
  · have hbase := floor_vector_mem_shifted_weighted_simplex n w hw T hT x hx
    have hfloor := weighted_floor_sum_lt n w hw T hT x hx
    have hweight : 0 ≤ ∑ i, w i :=
      Finset.sum_nonneg fun i _ => le_of_lt (hw i)
    have hshift :
        (∑ i, w i * ((Nat.floor (x i) : Nat) : Real)) <
          T + Finset.univ.sum w :=
      lt_of_lt_of_le hfloor (le_add_of_nonneg_right hweight)
    simpa [strictWeightedSimplex] using And.intro hbase hshift
  · intro i
    exact ⟨Nat.floor_le (hx.1 i), Nat.lt_floor_add_one (x i)⟩