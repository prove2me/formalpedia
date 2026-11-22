-- Prove2me | solution 1 for Lean4LPD.decayBase_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:01:38.881927+00:00
-- url     : https://prove2.me/submissions/0bee507e-794c-4b67-9eea-29f8ce37c547

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Theorems.Thm_Lean4LPD_tZeroModel_pos

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {G kh a t : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a)
    (ht : t < tZeroModel G kh a) : decayBase G kh a t < 1 := by
  have h0 := tZeroModel_pos hG hkh ha
  unfold decayBase
  rw [div_lt_one h0]
  exact ht
end Lean4LPD
