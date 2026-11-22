-- Prove2me | solution 1 for Lean4LPD.decayBase_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:00:27.33701+00:00
-- url     : https://prove2.me/submissions/48f2466b-7d9a-464e-9e5e-5b905d6c7303

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
theorem _root_.solution {G kh a t : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a) (ht : 0 ≤ t) :
    0 ≤ decayBase G kh a t :=
  div_nonneg ht (le_of_lt (tZeroModel_pos hG hkh ha))
end Lean4LPD
