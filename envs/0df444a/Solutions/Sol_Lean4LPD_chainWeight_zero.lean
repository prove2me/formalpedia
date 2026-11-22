-- Prove2me | solution 1 for Lean4LPD.chainWeight_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:36.092011+00:00
-- url     : https://prove2.me/submissions/bd06946b-f5b4-45da-8a1d-5a205b3924c4

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
theorem _root_.solution (kh1 c a : ℝ) : chainWeight kh1 c a 0 = 1 := by
  simp [chainWeight]
end Lean4LPD
