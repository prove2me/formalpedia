-- Prove2me | solution 1 for MetricCodes.Hamming.hammingFibreDimension_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/4153222a-1131-4ce9-a059-51df95e1cc2d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {n k : ℕ} (hk : 2 * k ≤ n) :
    0 < MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero => simp [MetricCodes.hammingFibreDimension, MetricCodes.booleanHarmonicDimension]
  | succ j =>
      change 0 < n.choose (j + 1) - n.choose j
      apply Nat.sub_pos_of_lt
      have hchoose : 0 < n.choose j := Nat.choose_pos (by omega)
      have hfactor : j + 1 < n - j := by omega
      have hmul :
          n.choose j * (j + 1) < n.choose j * (n - j) :=
        Nat.mul_lt_mul_of_pos_left hfactor hchoose
      have hmul' :
          n.choose j * (j + 1) < n.choose (j + 1) * (j + 1) := by
        calc
          n.choose j * (j + 1) < n.choose j * (n - j) := hmul
          _ = n.choose (j + 1) * (j + 1) :=
            (Nat.choose_succ_right_eq n j).symm
      exact (Nat.mul_lt_mul_right (by omega : 0 < j + 1)).mp hmul'
end MetricCodes.Hamming
