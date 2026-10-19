-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:22:52.980058+00:00
-- url     : https://prove2.me/submissions/539bedb5-185d-41b2-b07c-0cf22f95169d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L356-L382
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_weighted. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_offbox_decay

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma mem_box (T β : ℝ) (w : ℤ) :
    w ∈ box T β ↔ |(w:ℝ)| ≤ T*|β|/2 := by
  rw [box, Finset.mem_Icc, ← abs_le, ← Int.cast_abs, ← Int.le_floor]

/-- A summable majorant for the discarded one-dimensional Fourier tail.
This uses three integrations by parts (or n+2 for the stronger form), and
avoids an unjustified summation of stationary-phase errors. -/
theorem offbox_weighted {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) {β : ℝ} (hβ : β ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ w : ℤ, w ∉ box T β →
      ‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C / T^n * latticeWeight w := by
  obtain ⟨C,hC,hbound⟩ := offbox_decay hg hgs hα0 hα hβ hs (n+2)
  refine ⟨C,hC,?_⟩
  intro T hT w hw
  have hTpos : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hw' : T*|β|/2 < |(w:ℝ)| := lt_of_not_ge (by simpa only [← mem_box] using hw)
  have hb := hbound T w hTpos hw'
  have hp : T^n*(1+|(w:ℝ)|)^2 ≤ (T+|(w:ℝ)|)^(n+2) := by
    rw [pow_add]
    apply mul_le_mul
    · exact pow_le_pow_left₀ hTpos.le (le_add_of_nonneg_right (abs_nonneg _)) n
    · exact pow_le_pow_left₀ (by positivity) (by linarith : 1+|(w:ℝ)|≤T+|(w:ℝ)|) 2
    · positivity
    · positivity
  have hh : T^n*(1+|(w:ℝ)|)^2*‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hb
  dsimp only [latticeWeight]
  calc
    _ ≤ C/(T^n*(1+|(w:ℝ)|)^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hh])
    _ = _ := by rw [div_mul_eq_div_div]; ring

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_weighted := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_weighted
