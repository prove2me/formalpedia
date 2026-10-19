-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.rowTrunc_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:26:33.477003+00:00
-- url     : https://prove2.me/submissions/c18f22b2-3a81-4d4f-bd4d-70640960c40d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L422-L440
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.rowTrunc_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_circleChirp_coefficient
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_fourier_truncation_error
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_latticeWeight_summable
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_offbox_weighted

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma phase_smooth (t u : ℝ) : ContDiff ℝ ∞ (phase t u) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ ↦ 2*Real.pi*(t*x^2/2-u*x)) := by fun_prop
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ Complex.I)).mul
    (Complex.ofRealCLM.contDiff.comp hc)).cexp

lemma cutoff_zero {g : ℝ → ℂ} {α x : ℝ}
    (hs : tsupport g ⊆ Set.Icc (-α) α) (hx : x ∉ Set.Icc (-α) α) : g x=0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))

lemma circleChirp_continuous {g : ℝ → ℂ} (hg : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    Continuous (circleChirp g t) := by
  apply AddCircle.liftIoc_continuous
  · have hleft : g (-1/2)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    have hright : g (-1/2+1)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    simp only [hleft,hright,zero_mul]
  · exact (hg.mul (phase_smooth t 0).continuous).continuousOn

lemma latticeWeight_pos (w : ℤ) : 0 < latticeWeight w := by
  dsimp [latticeWeight]
  positivity

theorem rowTrunc_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ z : UnitAddCircle,
      ‖rowTrunc g T β z-circleChirp g (T*β) z‖ ≤ C/T := by
  obtain ⟨C,hC,hbound⟩ := offbox_weighted hg hgs hα0 hα hs hβ 1
  refine ⟨C*(∑' w, latticeWeight w),mul_nonneg hC (tsum_nonneg (fun w ↦ (latticeWeight_pos w).le)),?_⟩
  intro T hT z
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs.continuous hα hs _⟩
  have hf (w : ℤ) : fourierCoeff f w = ∫ x : ℝ, g x*phase (T*β) w x :=
    circleChirp_coefficient hα hs _ _
  have hh := fourier_truncation_error f (box T β) (fun w ↦ C/T*latticeWeight w)
    (latticeWeight_summable.mul_left (C/T))
    (fun w ↦ mul_nonneg (div_nonneg hC (by linarith)) (latticeWeight_pos w).le)
    (fun w hw ↦ by rw [hf]; simpa only [pow_one] using hbound T hT w hw) z
  change ‖(∑ w ∈ box T β, fourierCoeff f w*fourier w z)-f z‖ ≤ _ at hh
  simp only [hf, tsum_mul_left] at hh
  convert hh using 1 <;> (try dsimp [rowTrunc, f])
  ring

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.rowTrunc_error := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.rowTrunc_error
