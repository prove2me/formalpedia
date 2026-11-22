-- Prove2me | solution 1 for Lean4LPD.partFactor_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:48.775024+00:00
-- url     : https://prove2.me/submissions/805c4bbc-7d92-4f52-bc3e-c204377ede70

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_chainWeight_zero
attribute [local simp] Lean4LPD.chainWeight_zero

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {s : ℝ} (hs : 0 < s) : partFactor 1 s = 1 := by
  simp [partFactor, ne_of_gt hs]
end Lean4LPD
