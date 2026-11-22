-- Prove2me | solution 1 for Lean4LPD.betaOf_nonneg_for_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:25.365015+00:00
-- url     : https://prove2.me/submissions/8efd7db2-fffb-4e16-8be2-f277f71b8f7f

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
theorem _root_.solution {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) : 0 ≤ betaOf kh1 c a := by
  unfold betaOf
  have hw := rungW_nonneg hkh hc (m := 2) (by decide)
  positivity
end Lean4LPD
