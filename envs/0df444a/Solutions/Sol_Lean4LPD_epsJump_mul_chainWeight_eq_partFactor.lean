-- Prove2me | solution 1 for Lean4LPD.epsJump_mul_chainWeight_eq_partFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:08:00.842403+00:00
-- url     : https://prove2.me/submissions/685e8b5f-259b-489c-9ece-ebc79d2b1a66

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_chainWeight_split
public import Theorems.Thm_Lean4LPD_partFactor_mul_tail_rungs

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (kh1 a : ℝ)
    {j m : ℕ} (hjm : j ≤ m) :
    epsJump kh1 c a j m * chainWeight kh1 c a (m - j)
      = partFactor j ((m : ℝ) + c) * chainWeight kh1 c a m := by
  rw [chainWeight_split kh1 c a hjm, epsJump, mul_pow]
  calc (rungW kh1 c (m + j) ^ j * a ^ j / (Nat.factorial j : ℝ))
        * chainWeight kh1 c a (m - j)
      = (rungW kh1 c (m + j) ^ j / (Nat.factorial j : ℝ))
          * (a ^ j * chainWeight kh1 c a (m - j)) := by ring
    _ = (partFactor j ((m : ℝ) + c)
          * ∏ i ∈ range j, rungW kh1 c (m - j + i + 2))
          * (a ^ j * chainWeight kh1 c a (m - j)) := by
        rw [partFactor_mul_tail_rungs hc kh1 hjm]
    _ = _ := by ring
end Lean4LPD
