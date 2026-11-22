-- Prove2me | solution 1 for Lean4LPD.MultiLadder.sum_block_epsJump_le_exp_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:16.954694+00:00
-- url     : https://prove2.me/submissions/336b0496-4e25-4d1c-95a1-c6df791df864

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_MultiLadder_sum_block_inflow_le_exp
public import Theorems.Thm_Lean4LPD_betaOf_nonneg_for_chain
public import Theorems.Thm_Lean4LPD_chainWeight_nonneg
public import Theorems.Thm_Lean4LPD_entryFactor_le_chainWeight_source
public import Theorems.Thm_Lean4LPD_epsJump_mul_chainWeight_le
public import Theorems.Thm_Lean4LPD_epsJump_nonneg_for_chain


set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
namespace MultiLadder
theorem _root_.solution {kh1 c a M : ℝ}
    (L : MultiLadder (epsJump kh1 c a) (entryFactor kh1 c a) M)
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : betaOf kh1 c a ≤ 1 / 2)
    (hM : 0 ≤ M) {m G : ℕ} (hm : 1 ≤ m) (hG : 1 ≤ G)
    (r : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 m, epsJump kh1 c a j m * L.N (m - j) (d * G + i)) +
        entryFactor kh1 c a m * M) :
    (∑ d ∈ range r, x d G) ≤
      M * ((1 + 4 * Real.exp 1 * betaOf kh1 c a) * chainWeight kh1 c a m *
        (((r : ℝ) + 1) * G) ^ m / (Nat.factorial m : ℝ) *
          Real.exp (9 / 4 * (m : ℝ) ^ 2 / (((r : ℝ) + 1) * G))) := by
  have hE (m : ℕ) : 0 ≤ entryFactor kh1 c a m := by
    unfold entryFactor
    exact tsum_nonneg fun i => epsJump_nonneg_for_chain hkh hc ha (m + i) m
  have hC : 0 ≤ 1 + 4 * Real.exp 1 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  exact MultiLadder.sum_block_inflow_le_exp L (epsJump_nonneg_for_chain hkh hc ha)
    hE hM hC (by norm_num) hm hG (chainWeight_nonneg hkh hc ha m) r x hreset hinflow
    (fun _ hm => entryFactor_le_chainWeight_source hkh hc ha hb hm)
    (fun _ _ hj hjm => epsJump_mul_chainWeight_le hkh hc ha hj hjm.le)
end MultiLadder
end Lean4LPD
