-- Prove2me | solution 1 for Kyprianou.Ch05.nonnegativeHalfOpenGridPartition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:48:07.452302+00:00
-- url     : https://prove2.me/submissions/70947ac5-a634-44b5-bc0e-a938b874a898

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Nonnegative half-open uniform grid is a disjoint partition. -/
theorem solution
    (d : Real) (hd : 0 < d) :
    (⋃ k : Nat, Set.Ico ((k : Real)*d) (((k : Real)+1)*d)) = Set.Ici 0 ∧
      Pairwise (Function.onFun Disjoint (fun k : Nat => Set.Ico ((k : Real)*d) (((k : Real)+1)*d))) := by
  constructor
  · ext y
    constructor
    · intro hy
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hy
      exact (mul_nonneg (Nat.cast_nonneg k) hd.le).trans hk.1
    · intro hy
      let k := Nat.floor (y/d)
      have h1 : (k : Real) ≤ y/d := Nat.floor_le (div_nonneg hy hd.le)
      have h2 : y/d < (k : Real)+1 := Nat.lt_floor_add_one _
      exact Set.mem_iUnion.mpr ⟨k, (le_div_iff₀ hd).mp h1, (div_lt_iff₀ hd).mp h2⟩
  · intro i j hij
    rw [Function.onFun]
    apply Set.disjoint_left.mpr
    intro y hi hj
    rcases lt_or_gt_of_ne hij with h | h
    · have hc : (i : Real)+1 ≤ (j : Real) := by exact_mod_cast Nat.succ_le_of_lt h
      exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hc hd.le).trans hj.1)) hi.2
    · have hc : (j : Real)+1 ≤ (i : Real) := by exact_mod_cast Nat.succ_le_of_lt h
      exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hc hd.le).trans hi.1)) hj.2
