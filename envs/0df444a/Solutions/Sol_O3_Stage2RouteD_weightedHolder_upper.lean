-- Prove2me | solution 1 for O3.Stage2RouteD.weightedHolder_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:40.929047+00:00
-- url     : https://prove2.me/submissions/11317e04-b4e3-4e18-a4c7-b79f30f3f1a2

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_lpNorm_weightVector
import Theorems.Thm_O3_Stage2RouteD_lpNorm_squareVector
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_nonneg
import Theorems.Thm_O3_lpNorm_pos_of_ne_zero
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_le_lpNorm_mul
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right


attribute [local simp] O3.Stage2RouteD.dualityMap_zero

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {q : ℝ} (hq : 2 < q) {d : ℕ}
    (z h : Point d) (hz : z ≠ 0) :
    (lpNorm q z) ^ (2 - q) *
        (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
      (lpNorm q h) ^ (2 : ℕ) := by
  have hden : 0 < q - 2 := by linarith
  have hr1 : 1 < q / (q - 2) := (lt_div_iff₀ hden).2 (by linarith)
  have hrs : (q / (q - 2)).HolderConjugate (q / 2) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hr1, ?_⟩
    field_simp
    ring
  have hholder := pairing_le_lpNorm_mul hrs (weightVector q z) (squareVector h)
  have hholder' :
      (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
        (lpNorm q z) ^ (q - 2) * (lpNorm q h) ^ (2 : ℕ) := by
    simpa only [pairing, weightVector, squareVector,
      lpNorm_weightVector hq z, lpNorm_squareVector (by linarith : 0 < q) h] using hholder
  have hfactor : 0 ≤ (lpNorm q z) ^ (2 - q) :=
    Real.rpow_nonneg (lpNorm_nonneg q z) _
  have hmul := mul_le_mul_of_nonneg_left hholder' hfactor
  calc
    (lpNorm q z) ^ (2 - q) *
        (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
      (lpNorm q z) ^ (2 - q) *
        ((lpNorm q z) ^ (q - 2) * (lpNorm q h) ^ (2 : ℕ)) := hmul
    _ = (lpNorm q h) ^ (2 : ℕ) := by
      have hn : 0 < lpNorm q z := lpNorm_pos_of_ne_zero hz
      rw [← mul_assoc, ← Real.rpow_add hn]
      norm_num
end O3.Stage2RouteD
