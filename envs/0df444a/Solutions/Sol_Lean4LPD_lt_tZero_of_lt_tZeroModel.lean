-- Prove2me | solution 1 for Lean4LPD.lt_tZero_of_lt_tZeroModel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:33.35014+00:00
-- url     : https://prove2.me/submissions/4f949aef-dab2-4036-9f7b-b3f8efff481b

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Theorems.Thm_Lean4LPD_tZeroModel_le_tZero

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {r m G B kh a t : ℝ} (h : Admissible r m G) (hm1 : 1 ≤ m)
    (hr5 : 5 ≤ r) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh : 1 < kh) (ha : 0 < a)
    (ht : t < tZeroModel G kh a) : t < tZero (cZero r m G B) G kh a :=
  lt_of_lt_of_le ht (tZeroModel_le_tZero h hm1 hr5 hB0 hB1 hkh ha)
end Lean4LPD
