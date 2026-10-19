-- Prove2me | solution 1 for OAI.BackwardIntertwiners.quadratic_support_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:59:24.391981+00:00
-- url     : https://prove2.me/submissions/365e1106-24e8-4ef5-873a-56643f6b855b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/WeightSeparation.lean:L184-L257
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.quadratic_support_separation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Theorems.Thm_OAI_BackwardIntertwiners_normalized_support_separation

-- ---- from OAI.Analysis.BackwardIntertwiners.WeightSeparation ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

lemma DiscreteConvex.add_const {G : ℕ → ℝ} (h : DiscreteConvex G) (c : ℝ) :
    DiscreteConvex (fun n => G n+c) := by
  intro i j hij
  simpa only [add_sub_add_right_eq_sub] using h hij

lemma eventually_quadratic_lower {G : ℕ → ℝ} {a δ : ℝ} (hδa : δ < a)
    (ht : Tendsto (fun n => G n / (n:ℝ)^2) atTop (𝓝 a)) :
    ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ G n := by
  filter_upwards [ht (eventually_gt_nhds hδa), eventually_ge_atTop 1] with n hn hn1
  have hnpos : 0 < (n:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (by omega))
  exact ((lt_div_iff₀ hnpos).mp hn).le

theorem quadratic_support_separation (w : ℤ → ℝ) (hw : QuadraticWeights w) :
    SupportSeparation w := by
  let W := fun j : ℤ => w j / w 0
  have hw0 : 0 < w 0 := hw.positive 0
  have hWpos (j : ℤ) : 0 < W j := div_pos (hw.positive j) hw0
  have hWdec : Antitone W := by
    intro i j hij
    exact div_le_div_of_nonneg_right (hw.decreasing hij) hw0.le
  have hW0 : W 0 = 1 := div_self (ne_of_gt hw0)
  have hlog (j : ℤ) : Real.log (w j / w 0) = Real.log (w j) - Real.log (w 0) :=
    Real.log_div (ne_of_gt (hw.positive j)) (ne_of_gt hw0)
  have hP : DiscreteConvex (negativeLog W) := by
    have heq : negativeLog W = fun n : ℕ => Real.log (w (-(n:ℤ))) + -Real.log (w 0) := by
      funext n
      simp only [negativeLog, W, hlog, sub_eq_add_neg]
    rw [heq]
    exact hw.convex_negative.add_const _
  have hQ : DiscreteConvex (positiveLog W) := by
    have heq : positiveLog W = fun n : ℕ => -Real.log (w n) + Real.log (w 0) := by
      funext n
      simp only [positiveLog, W, hlog]
      ring
    rw [heq]
    exact hw.concave_positive.add_const _
  obtain ⟨a, ha, hqa, hpa⟩ := hw.quadratic
  have hnat : Tendsto (fun n : ℕ => (n:ℝ)^2) atTop atTop := by
    exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => Real.log (w 0) / (n:ℝ)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hnat).const_mul (Real.log (w 0))
  have htP : Tendsto (fun n : ℕ => negativeLog W n / (n:ℝ)^2) atTop (𝓝 a) := by
    simpa only [negativeLog, W, hlog, sub_div, sub_zero] using hpa.sub hsmall
  have htQ : Tendsto (fun n : ℕ => positiveLog W n / (n:ℝ)^2) atTop (𝓝 a) := by
    have heq : (fun n : ℕ => positiveLog W n / (n:ℝ)^2) =
        (fun n : ℕ => -(Real.log (w n) / (n:ℝ)^2) + Real.log (w 0) / (n:ℝ)^2) := by
      funext n
      simp only [positiveLog, W, hlog]
      ring
    rw [heq]
    simpa only [neg_neg, add_zero] using hqa.neg.add hsmall
  obtain ⟨lam, hlam, hlama⟩ := exists_between ha
  obtain ⟨δ, hδ, hδa⟩ := exists_between hlama
  have hsep := normalized_support_separation hWpos hWdec hW0 hP hQ hlam hδ
    (eventually_quadratic_lower hδa htP) (eventually_quadratic_lower hδa htQ)
  intro b c hbn hcn hb hc hz
  let C : ℂ := (w 0 : ℂ)
  have hC : C ≠ 0 := by dsimp [C]; exact_mod_cast (ne_of_gt hw0)
  have hCnorm : ‖C‖ = w 0 := by simpa [C] using Real.norm_of_nonneg hw0.le
  let b' := fun j => b j / C
  let c' := fun j => C * c j
  have hbn' : ∃ j, b' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hbn
    exact ⟨j, div_ne_zero hj hC⟩
  have hcn' : ∃ j, c' j ≠ 0 := by
    obtain ⟨j, hj⟩ := hcn
    exact ⟨j, mul_ne_zero hC hj⟩
  have hb' (j : ℤ) : ‖b' j‖ ≤ W j := by
    dsimp [b', W]
    rw [norm_div, hCnorm]
    exact div_le_div_of_nonneg_right (hb j) hw0.le
  have hc' (j : ℤ) : ‖c' j‖ * W j ≤ 1 := by
    dsimp [c', W]
    rw [norm_mul, hCnorm]
    have he : w 0 * ‖c j‖ * (w j / w 0) = ‖c j‖ * w j := by field_simp
    rw [he]
    exact hc j
  have hz' (r : ℕ) (hr : 1 ≤ r) : (∑' j : ℤ, b' j * c' (j-r)) = 0 := by
    have he (j : ℤ) : b' j * c' (j-r) = b j * c (j-r) := by
      dsimp [b', c']
      field_simp
    simp only [he]
    exact hz r hr
  have hh := hsep b' c' hbn' hcn' hb' hc' hz'
  simpa [b', c', hC] using hh

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.quadratic_support_separation := @_root_.OAI.BackwardIntertwiners.quadratic_support_separation
