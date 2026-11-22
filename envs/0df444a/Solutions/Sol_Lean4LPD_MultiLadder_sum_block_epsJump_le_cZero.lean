-- Prove2me | solution 1 for Lean4LPD.MultiLadder.sum_block_epsJump_le_cZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:13:04.387046+00:00
-- url     : https://prove2.me/submissions/e7c72a6b-9a0e-4578-8bca-2bc307c381ba

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_ChainWeights
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_AssemblyBound
public import Theorems.Thm_Lean4LPD_sector_bound_le_cZero
public import Theorems.Thm_Lean4LPD_MultiLadder_sum_block_epsJump_le_exp_source
public import Theorems.Thm_Lean4LPD_betaOf_nonneg_for_chain
public import Theorems.Thm_Lean4LPD_chainWeight_zero
public import Theorems.Thm_Lean4LPD_rungW_nonneg
attribute [local simp] Lean4LPD.chainWeight_zero



set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
namespace MultiLadder
theorem _root_.solution {kh1 c a A M : ℝ}
    (L : MultiLadder (epsJump kh1 c a) (entryFactor kh1 c a) M)
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : betaOf kh1 c a ≤ 1 / 2)
    (hA : 0 ≤ A) (hM : 0 ≤ M) {G r : ℕ} (hG : 1 ≤ G) (hr : 1 ≤ r)
    (haA : a ≤ A / (r : ℝ)) (m : ℕ) (x : ℕ → ℕ → ℝ)
    (hreset : ∀ d, d < r → x d 0 = 0)
    (hinflow : ∀ d, d < r → ∀ i, i < G → x d (i + 1) ≤ x d i +
      (∑ j ∈ Ico 1 (m + 1), epsJump kh1 c a j (m + 1) * L.N (m + 1 - j) (d * G + i)) +
        entryFactor kh1 c a (m + 1) * M) :
    (∑ d ∈ range r, x d G) ≤
      (cZero (r : ℝ) (m : ℝ) (G : ℝ) (4 * Real.exp 1 * betaOf kh1 c a) * G * A) ^ (m + 1) *
        (∏ j ∈ range (m + 1), rungW kh1 c (j + 2)) /
          (Nat.factorial (m + 1) : ℝ) * M := by
  have hfirst := MultiLadder.sum_block_epsJump_le_exp_source L hkh hc ha hb hM
    (m := m + 1) (by omega) hG r x hreset hinflow
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  have hB : 0 ≤ 4 * Real.exp 1 * betaOf kh1 c a := by
    have hb0 := betaOf_nonneg_for_chain hkh hc ha
    positivity
  have hP : 0 ≤ ∏ j ∈ range (m + 1), rungW kh1 c (j + 2) := by
    exact Finset.prod_nonneg fun j _ => rungW_nonneg hkh hc (by omega)
  refine hfirst.trans ?_
  simpa only [chainWeight, Nat.cast_add, Nat.cast_one] using
    sector_bound_le_cZero hrpos hGpos hB ha hA haA hP hM m
end MultiLadder
end Lean4LPD
