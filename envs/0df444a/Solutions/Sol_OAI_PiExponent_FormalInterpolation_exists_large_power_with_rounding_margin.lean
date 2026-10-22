-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_large_power_with_rounding_margin
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:28:00.812806+00:00
-- url     : https://prove2.me/submissions/2de59ff3-c8b3-4fdd-8a4f-fafc5bb5c1c5

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

/-!
# Choose a power exceeding finitely many coordinate weights

Given `c < a` and positive weights `w i`, pick a positive integer `k ≥ N`
large enough that `k (a - c)` strictly exceeds every coordinate weight.
-/

theorem solution
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (a c : Rat) (hca : c < a) (N : Nat) :
    ∃ k : Nat, 0 < k ∧ N ≤ k ∧
      ∀ i, (k : Real) * ((a - c : Rat) : Real) > (w i : Real) := by
  classical
  have hgap : (0 : Real) < ((a - c : Rat) : Real) := by
    have : (0 : Rat) < a - c := sub_pos.mpr hca
    exact_mod_cast this
  -- Bound all weights by their finite sum (vacuous when `d = 0`).
  set W : Real := ∑ i, (w i : Real) with hW
  have hWnonneg : 0 ≤ W := Finset.sum_nonneg fun i _ => le_of_lt (hw i)
  have hwW : ∀ i, (w i : Real) ≤ W := fun i =>
    Finset.single_le_sum (fun j _ => le_of_lt (hw j)) (Finset.mem_univ i)
  -- Pick any natural strictly above `W / (a - c)`, then take `max` with `N` and `1`.
  obtain ⟨n, hn⟩ := exists_nat_gt (W / ((a - c : Rat) : Real))
  have hn' : W < (n : Real) * ((a - c : Rat) : Real) := by
    rw [div_lt_iff₀ hgap] at hn
    exact hn
  refine ⟨max (max n 1) N, ?_, ?_, ?_⟩
  · exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right n 1) (le_max_left _ _))
  · exact le_max_right _ _
  · intro i
    have hnle : (n : Real) ≤ ((max (max n 1) N : Nat) : Real) := by
      exact_mod_cast (le_trans (le_max_left n 1) (le_max_left _ N))
    have hgap_nonneg : 0 ≤ ((a - c : Rat) : Real) := le_of_lt hgap
    calc
      (w i : Real) ≤ W := hwW i
      _ < (n : Real) * ((a - c : Rat) : Real) := hn'
      _ ≤ ((max (max n 1) N : Nat) : Real) * ((a - c : Rat) : Real) :=
          mul_le_mul_of_nonneg_right hnle hgap_nonneg
