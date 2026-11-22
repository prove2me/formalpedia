-- Prove2me | solution 1 for Lean4LPD.chain_entry_inflation_le_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:04:53.92148+00:00
-- url     : https://prove2.me/submissions/fd46481b-d6a1-4035-bccf-3c33d776ab6f

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_betaOf_nonneg_for_chain

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    1 + 2 * betaOf kh1 c a ≤ 1 + 4 * Real.exp 1 * betaOf kh1 c a := by
  have hb0 := betaOf_nonneg_for_chain hkh hc ha
  have he := Real.add_one_le_exp (1 : ℝ)
  have hnum : (2 : ℝ) ≤ 4 * Real.exp 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hnum hb0
  linarith
end Lean4LPD
