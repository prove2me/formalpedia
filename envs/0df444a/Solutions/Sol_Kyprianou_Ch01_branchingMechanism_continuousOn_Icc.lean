-- Prove2me | solution 1 for Kyprianou.Ch01.branchingMechanism_continuousOn_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:09:11.978705+00:00
-- url     : https://prove2.me/submissions/c3c78204-1b62-4393-8f6b-b2068f9cd5c9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingMechanism_expUniformBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false

theorem solution
    (rate : ℝ) (offspring : PMF ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ContinuousOn (branchingMechanism rate offspring) (Icc a b) := by
  have hsumm : Summable (fun k : ℕ => (offspring k).toReal) :=
    ENNReal.summable_toReal offspring.tsum_coe_ne_top
  let f : ℕ → ℝ → ℝ := fun k y =>
    (offspring k).toReal * (1 - Real.exp (-y * ((k : ℝ) - 1)))
  let u : ℕ → ℝ := fun k => (1 + Real.exp b) * (offspring k).toReal
  have hsum : Summable u := hsumm.mul_left _
  have hcont : ∀ k : ℕ, ContinuousOn (f k) (Icc a b) := by
    intro k
    dsimp [f]
    fun_prop
  have hbound : ∀ (k : ℕ) (y : ℝ), y ∈ Icc a b → ‖f k y‖ ≤ u k := by
    intro k y hy
    have hy0 : 0 ≤ y := le_trans ha hy.1
    have habs := Kyprianou.Ch01.branchingMechanism_expUniformBound
      b (le_trans ha hab) k y hy0 hy.2
    calc
      ‖f k y‖ =
          (offspring k).toReal * |1 - Real.exp (-y * ((k : ℝ) - 1))| := by
            simp [f, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (ENNReal.toReal_nonneg)]
      _ ≤ (offspring k).toReal * (1 + Real.exp b) :=
        mul_le_mul_of_nonneg_left habs ENNReal.toReal_nonneg
      _ = u k := by simp [u, mul_comm]
  have htsum : ContinuousOn (fun y => ∑' k, f k y) (Icc a b) :=
    continuousOn_tsum hcont hsum hbound
  change ContinuousOn (fun y => rate * (∑' k, f k y)) (Icc a b)
  exact continuousOn_const.mul htsum
