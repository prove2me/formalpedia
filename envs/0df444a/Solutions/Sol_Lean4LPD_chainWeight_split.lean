-- Prove2me | solution 1 for Lean4LPD.chainWeight_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:46.819947+00:00
-- url     : https://prove2.me/submissions/79601093-cd4a-4dde-8a52-071220bb9c21

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution (kh1 c a : ℝ) {j m : ℕ} (hjm : j ≤ m) :
    chainWeight kh1 c a m = a ^ j * chainWeight kh1 c a (m - j)
      * ∏ i ∈ range j, rungW kh1 c (m - j + i + 2) := by
  have hprod := Finset.prod_range_add (fun i => rungW kh1 c (i + 2)) (m - j) j
  rw [Nat.sub_add_cancel hjm] at hprod
  have hpow : a ^ j * a ^ (m - j) = a ^ m := by
    rw [← pow_add]
    congr 1
    omega
  unfold chainWeight
  rw [hprod, ← hpow]
  ring
end Lean4LPD
