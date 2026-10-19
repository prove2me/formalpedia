-- Prove2me | solution 1 for MetricCodes.Hamming.choose_le_mul_hammingFibreDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/0a4f0fa7-e426-4ad1-b75b-456a496bd65f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_hammingFibreDimension_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution
    {n k : ℕ} (hk : 2 * k ≤ n) :
    n.choose k ≤ (n + 1) * MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero => simp [MetricCodes.hammingFibreDimension, MetricCodes.booleanHarmonicDimension]
  | succ j =>
      change n.choose (j + 1) ≤
        (n + 1) * (n.choose (j + 1) - n.choose j)
      have hpositive :=
        hammingFibreDimension_pos (n := n) (k := j + 1) hk
      change 0 < n.choose (j + 1) - n.choose j at hpositive
      have hmono : n.choose j ≤ n.choose (j + 1) :=
        (Nat.sub_pos_iff_lt.mp hpositive).le
      have hrec :
          (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
            (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq n j
      have hidentity :
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) =
            (n.choose (j + 1) : ℝ) *
              (((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) := by
        rw [Nat.cast_sub hmono]
        calc
          ((n.choose (j + 1) : ℝ) - (n.choose j : ℝ)) *
              ((n - j : ℕ) : ℝ) =
            (n.choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) -
              (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by ring
          _ = (n.choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) -
              (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
                rw [← hrec]
          _ = (n.choose (j + 1) : ℝ) *
              (((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) := by ring
      have hfactorNat : j + 2 ≤ n - j := by omega
      have hfactorReal :
          (1 : ℝ) ≤
            ((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) := by
        have hcast : ((j + 2 : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
          exact_mod_cast hfactorNat
        have hcastj : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
          norm_num
        rw [hcastj]
        push_cast at hcast
        linarith
      have hlower :
          (n.choose (j + 1) : ℝ) ≤
            ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) := by
        rw [hidentity]
        nlinarith [Nat.cast_nonneg (α := ℝ) (n.choose (j + 1))]
      have hrange :
          ((n - j : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n - j ≤ n + 1 by omega)
      have hupper :
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) ≤
            ((n + 1 : ℕ) : ℝ) *
              ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) := by
        calc
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) ≤
            ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hrange (Nat.cast_nonneg _)
          _ = ((n + 1 : ℕ) : ℝ) *
              ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) := by ring
      exact_mod_cast hlower.trans hupper
end MetricCodes.Hamming
