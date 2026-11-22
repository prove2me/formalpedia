-- Prove2me | solution 1 for Lean4LPD.pow_decayBase_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:39.453618+00:00
-- url     : https://prove2.me/submissions/31ba0693-8fa5-4b29-8324-ff7794190a53

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Theorems.Thm_Lean4LPD_decayBase_nonneg
public import Theorems.Thm_Lean4LPD_decayBase_lt_one

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {G kh a t : ℝ} (hG : 0 < G) (hkh : 1 < kh) (ha : 0 < a) (ht0 : 0 ≤ t)
    (ht : t < tZeroModel G kh a) (m : ℕ) :
    decayBase G kh a t ^ (m + 2) ≤ decayBase G kh a t ^ (m + 1) :=
  pow_le_pow_of_le_one (decayBase_nonneg hG hkh ha ht0)
    (le_of_lt (decayBase_lt_one hG hkh ha ht)) (by omega)
end Lean4LPD
