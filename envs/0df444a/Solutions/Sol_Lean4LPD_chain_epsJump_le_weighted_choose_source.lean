-- Prove2me | solution 1 for Lean4LPD.chain_epsJump_le_weighted_choose_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:32.960154+00:00
-- url     : https://prove2.me/submissions/d972e6bd-4dfd-4d79-8890-5b19ef339219

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_PartFactor
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Theorems.Thm_Lean4LPD_epsJump_mul_chainWeight_le
public import Theorems.Thm_Lean4LPD_betaOf_nonneg_for_chain
public import Theorems.Thm_Lean4LPD_epsJump_nonneg_for_chain
public import Theorems.Thm_Lean4LPD_entryFactor_le_chainWeight_source
public import Theorems.Thm_Lean4LPD_chain_le_weighted_choose


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : betaOf kh1 c a ≤ 1 / 2) (k m : ℕ) (hm : 1 ≤ m) :
    chain (epsJump kh1 c a) (entryFactor kh1 c a) (k + 1) m
      ≤ (1 + 4 * Real.exp 1 * betaOf kh1 c a) * (9 / 4 : ℝ) ^ (m - (k + 1))
        * chainWeight kh1 c a m * ((m - 1).choose k : ℝ) := by
  have hC : 0 ≤ 1 + 4 * Real.exp 1 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  exact chain_le_weighted_choose (epsJump_nonneg_for_chain hkh hc ha) hC (by norm_num)
    (fun _ hm => entryFactor_le_chainWeight_source hkh hc ha hb hm)
    (fun _ _ hj hjm => epsJump_mul_chainWeight_le hkh hc ha hj (Nat.le_of_lt hjm)) k m hm
end Lean4LPD
