-- Prove2me | solution 1 for Lean4LPD.tZeroModel_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:59:48.537808+00:00
-- url     : https://prove2.me/submissions/4ffe0e10-ce6f-469d-b5e2-202396cf76d4

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {G kh a : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a) :
    0 < tZeroModel G kh a := by
  have h1 : (0 : ℝ) < kh - 1 := by linarith
  unfold tZeroModel
  positivity
end Lean4LPD
