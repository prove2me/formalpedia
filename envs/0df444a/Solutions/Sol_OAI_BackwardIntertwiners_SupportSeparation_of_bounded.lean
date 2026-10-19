-- Prove2me | solution 1 for OAI.BackwardIntertwiners.SupportSeparation.of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:00:55.995133+00:00
-- url     : https://prove2.me/submissions/cef70dbd-14aa-47a7-8c2c-b1f7038342ae

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/WeightSeparation.lean:L260-L290
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.SupportSeparation.of_bounded. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation

-- ---- from OAI.Analysis.BackwardIntertwiners.WeightSeparation ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

lemma SupportSeparation.of_bounded {w : ℤ → ℝ} (hsep : SupportSeparation w)
    {b c : ℤ → ℂ} (hbn : ∃ j, b j ≠ 0) (hcn : ∃ j, c j ≠ 0)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hb : ∀ j, ‖b j‖ ≤ B*w j) (hc : ∀ j, ‖c j‖*w j ≤ C)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) :
    ∃ t h : ℤ, b t ≠ 0 ∧ c h ≠ 0 ∧
      (∀ j, t < j → b j = 0) ∧ (∀ j, j < h → c j = 0) ∧ t ≤ h := by
  have hBC : (B:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have hCC : (C:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
  let b' := fun j => b j / (B:ℂ)
  let c' := fun j => c j / (C:ℂ)
  have hbn' : ∃ j, b' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hbn
    exact ⟨j, div_ne_zero hj hBC⟩
  have hcn' : ∃ j, c' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hcn
    exact ⟨j, div_ne_zero hj hCC⟩
  have hb' (j : ℤ) : ‖b' j‖ ≤ w j := by
    dsimp [b']
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hB.le]
    exact (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hb j)
  have hc' (j : ℤ) : ‖c' j‖*w j ≤ 1 := by
    dsimp [c']
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hC.le, div_mul_eq_mul_div]
    exact (div_le_one hC).mpr (hc j)
  have hz' (r : ℕ) (hr : 1 ≤ r) : (∑' j : ℤ, b' j * c' (j-r)) = 0 := by
    have he (j : ℤ) : b' j * c' (j-r) = (b j*c (j-r)) / ((B:ℂ)*(C:ℂ)) := by
      dsimp [b', c']; ring
    simp only [he, tsum_div_const, hz r hr, zero_div]
  have hh := hsep b' c' hbn' hcn' hb' hc' hz'
  simpa [b', c', hBC, hCC] using hh

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.SupportSeparation.of_bounded := @_root_.OAI.BackwardIntertwiners.SupportSeparation.of_bounded
