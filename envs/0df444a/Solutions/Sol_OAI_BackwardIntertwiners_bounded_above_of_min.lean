-- Prove2me | solution 1 for OAI.BackwardIntertwiners.bounded_above_of_min
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:56:04.309815+00:00
-- url     : https://prove2.me/submissions/51251087-c1a5-4b72-b070-055e53bfc2dc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean:L288-L308
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.bounded_above_of_min. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Theorems.Thm_OAI_BackwardIntertwiners_CoefficientEnvelope_properties
import Theorems.Thm_OAI_BackwardIntertwiners_bounds_of_weight
import Theorems.Thm_OAI_BackwardIntertwiners_no_unbounded_against_min

-- ---- from OAI.Analysis.BackwardIntertwiners.CoefficientSupport ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace CoefficientEnvelope

variable {d : ℕ → ℂ} {G : ℕ → ℝ}
variable (hu : ∀ n : ℕ, ∃ k, n < k ∧ d k ≠ 0)
variable (hG : DiscreteConvex G) (hG0 : G 0 = 0)
variable (hb : ∀ n, ‖d n‖ ≤ Real.exp (-G n))

end CoefficientEnvelope

lemma boundedSideTail_nonneg (B : ℕ → ℝ) (c : ℤ → ℂ) (h : ℤ) (p k : ℕ) :
    0 ≤ boundedSideTail B c h p k := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

lemma boundedSideTail_summable {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    (hdec : Antitone w) (hs : Summable (stepRatio w))
    {B : ℕ → ℝ} (hBw : ∀ n : ℕ, Real.exp (-B n) ≤ w n)
    {c : ℤ → ℂ} (hc : ∀ j, ‖c j‖ * w j ≤ 1)
    (h : ℤ) {p₀ : ℕ} (hp₀ : h+1 ≤ (p₀:ℤ)) :
    Summable (boundedSideTail B c h p₀) := by
  have hsm := hs.comp_injective (i := fun k : ℕ => h+(k:ℤ)+1) (by
    intro a b hab; dsimp only at hab; omega)
  apply (hsm.mul_left (Real.exp (B p₀))).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (boundedSideTail_nonneg _ _ _ _ _)]
  change boundedSideTail B c h p₀ k ≤ Real.exp (B p₀) * stepRatio w (h+(k:ℤ)+1)
  have hwle : Real.exp (-B (p₀+k+1)) ≤ w (h+(k:ℤ)+1+1) := by
    exact (hBw _).trans (hdec (by omega))
  have hcw : ‖c (h+(k:ℤ)+1)‖ ≤ 1 / w (h+(k:ℤ)+1) :=
    (le_div_iff₀ (hw _)).mpr (hc _)
  unfold boundedSideTail stepRatio
  rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc Real.exp (-B (p₀+k+1)) * ‖c (h+(k:ℤ)+1)‖ ≤
      w (h+(k:ℤ)+1+1) * (1 / w (h+(k:ℤ)+1)) :=
        mul_le_mul hwle hcw (norm_nonneg _) (hw _).le
    _ = _ := by ring

lemma nat_support_unbounded {d : ℤ → ℂ}
    (hu : ¬∃ m : ℤ, ∀ j : ℤ, d j ≠ 0 → j ≤ m) :
    ∀ n : ℕ, ∃ k, n < k ∧ d (k:ℤ) ≠ 0 := by
  push Not at hu
  intro n
  obtain ⟨j, hd, hj⟩ := hu n
  refine ⟨j.toNat, by omega, ?_⟩
  have he : (j.toNat:ℤ) = j := by omega
  simpa only [he] using hd

lemma bounded_above_of_min {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    (hdec : Antitone w) (hw0 : w 0 = 1) (hs : Summable (stepRatio w))
    (hQ : DiscreteConvex (positiveLog w)) {δ : ℝ} (hδ : 0 < δ)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n)
    {b c : ℤ → ℂ} (hb : ∀ j, ‖b j‖ ≤ w j) (hc : ∀ j, ‖c j‖*w j ≤ 1)
    {h : ℤ} (hch : c h ≠ 0) (hcmin : ∀ j : ℤ, j < h → c j = 0)
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) :
    ∃ m : ℤ, ∀ j : ℤ, b j ≠ 0 → j ≤ m := by
  by_contra hu
  have hbu := nat_support_unbounded hu
  have hQ0 : positiveLog w 0 = 0 := by simp [positiveLog, hw0]
  obtain ⟨hB0, hB, hQB, hbB, hcontactB⟩ :=
    CoefficientEnvelope.properties hbu hQ hQ0 (bounds_of_weight hw hb hc).b_pos
  let B := coefficientEnvelope (fun n => b (n:ℤ))
  have hquad : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ B n := by
    filter_upwards [hqq] with n hn using hn.trans (hQB n)
  have hBw (n : ℕ) : Real.exp (-B n) ≤ w n := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg (hQB n))
    simpa only [positiveLog, neg_neg, Real.exp_log (hw _)] using hh
  exact no_unbounded_against_min hB hB0 hδ hquad hbB hcontactB hch hcmin
    (boundedSideTail_summable hw hdec hs hBw hc h (p₀ := h.toNat+1) (by omega)) hz

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.bounded_above_of_min := @_root_.OAI.BackwardIntertwiners.bounded_above_of_min
