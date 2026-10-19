-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_decay
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:17:52.150735+00:00
-- url     : https://prove2.me/submissions/d8fd50d3-1861-4cef-8b38-c1c049a1f5ee

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L234-L270
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_decay. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_polynomial_decay

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

/-- Off-box decay in precisely the regime used to truncate the spread spectrum. -/
theorem offbox_decay {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {α β : ℝ} (hα : 0 ≤ α) (hα' : α < 1/2) (hβ : β ≠ 0)
    (hsupp : tsupport g ⊆ Set.Icc (-α) α) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T w : ℝ, 0 < T → T*|β|/2 < |w| →
      (T+|w|)^l * ‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C := by
  let c : ℝ := (1-2*α)/(1+2/|β|)
  have hb : 0 < |β| := abs_pos.mpr hβ
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith) (by positivity)
  obtain ⟨C,hC,htail⟩ := polynomial_decay l c |β| hc (abs_nonneg _) g hg hgs 0
  refine ⟨C,hC,?_⟩
  intro T w hT hw
  have hM : 0 < T+|w| := by positivity
  have ht : |T*β| ≤ |β| *(T+|w|) := by
    rw [abs_mul, abs_of_pos hT]; nlinarith [mul_nonneg (abs_nonneg β) (abs_nonneg w)]
  have hs : ∀ x ∈ tsupport g, c*(T+|w|) ≤ |T*β*x-w| := by
    intro x hx
    have hx' : |x| ≤ α := abs_le.mpr (hsupp hx)
    have h1 : c*(T+|w|) ≤ (1-2*α)*|w| := by
      dsimp [c]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1+2/|β|)]
      have hw' : T ≤ 2*|w|/|β| := by rw [le_div_iff₀ hb]; linarith
      have hh := mul_le_mul_of_nonneg_left hw' (by linarith : 0 ≤ 1-2*α)
      convert add_le_add_right hh ((1-2*α)*|w|) using 1 <;> ring
    have hab : |T*β*x| ≤ T*|β| *α := by
      rw [abs_mul, abs_mul, abs_of_pos hT]
      exact mul_le_mul_of_nonneg_left hx' (by positivity)
    have htri : |w| ≤ |T*β*x-w| + |T*β*x| := by
      have hh := abs_add_le (w-T*β*x) (T*β*x)
      rw [sub_add_cancel, abs_sub_comm] at hh
      exact hh
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hw) hα
    linarith
  have hh := htail (T*β) w (T+|w|) hM ht hs
  simpa [osc, amp] using hh

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_decay := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_decay
