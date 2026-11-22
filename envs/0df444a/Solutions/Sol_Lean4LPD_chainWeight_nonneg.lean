-- Prove2me | solution 1 for Lean4LPD.chainWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:46.014055+00:00
-- url     : https://prove2.me/submissions/5bee5a51-5614-4116-b805-8efe78dc5eed

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_rungW_nonneg


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (m : ℕ) : 0 ≤ chainWeight kh1 c a m := by
  apply mul_nonneg (pow_nonneg ha m)
  exact Finset.prod_nonneg fun i _ => rungW_nonneg hkh hc (by omega)
end Lean4LPD
