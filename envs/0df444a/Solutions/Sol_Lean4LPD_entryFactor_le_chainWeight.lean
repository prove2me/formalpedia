-- Prove2me | solution 1 for Lean4LPD.entryFactor_le_chainWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:49.90656+00:00
-- url     : https://prove2.me/submissions/5c8fc778-20b0-44be-ac43-7db248375315

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_epsJump_diag_le_chainWeight
public import Theorems.Thm_Lean4LPD_betaOf_nonneg_for_chain
public import Theorems.Thm_Lean4LPD_entryFactor_le


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    entryFactor kh1 c a m
      ≤ (1 + 2 * betaOf kh1 c a) * (9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m := by
  have hC : 0 ≤ 1 + 2 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  calc entryFactor kh1 c a m
      ≤ epsJump kh1 c a m m * (1 + 2 * betaOf kh1 c a) :=
        entryFactor_le hkh hc ha hm hb
    _ ≤ ((9 / 4 : ℝ) ^ (m - 1) * chainWeight kh1 c a m)
          * (1 + 2 * betaOf kh1 c a) :=
        mul_le_mul_of_nonneg_right (epsJump_diag_le_chainWeight hkh hc ha hm) hC
    _ = _ := by ring
end Lean4LPD
