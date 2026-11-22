-- Prove2me | solution 1 for Lean4LPD.source_beta_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:04:32.54751+00:00
-- url     : https://prove2.me/submissions/00765067-2ada-4b94-a886-53282fad86c7

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerError
public import Theorems.Thm_Lean4LPD_source_entry_inflation_le_one
public import Theorems.Thm_Lean4LPD_betaOf_nonneg_for_chain


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
namespace Lean4LPD
theorem _root_.solution {kh1 c a A r : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hr : 0 < r) (haA : a ≤ A / r)
    (hsteps : 8 * (Real.exp 1) ^ 2 * rungW kh1 c 2 * A ≤ r) :
    betaOf kh1 c a ≤ 1 / 2 := by
  have hB := source_entry_inflation_le_one hkh hc hr haA hsteps
  have hb0 := betaOf_nonneg_for_chain hkh hc ha
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  nlinarith [mul_nonneg (sub_nonneg.mpr he) hb0]
end Lean4LPD
