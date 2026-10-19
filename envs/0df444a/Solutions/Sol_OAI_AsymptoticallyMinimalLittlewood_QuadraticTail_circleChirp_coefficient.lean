-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:19:29.768052+00:00
-- url     : https://prove2.me/submissions/1134203f-3d3c-4610-9080-7eeb30f059a6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L295-L317
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_coefficient. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma phase_fourier (t x : ℝ) (w : ℤ) :
    fourier (-w) (x : UnitAddCircle) * phase t 0 x = phase t w x := by
  rw [fourier_coe_apply, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cutoff_zero {g : ℝ → ℂ} {α x : ℝ}
    (hs : tsupport g ⊆ Set.Icc (-α) α) (hx : x ∉ Set.Icc (-α) α) : g x=0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))

lemma circleChirp_coefficient {g : ℝ → ℂ} {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) (w : ℤ) :
    fourierCoeff (circleChirp g t) w = ∫ x : ℝ, g x*phase t w x := by
  rw [fourierCoeff_eq_intervalIntegral _ w (-1/2)]
  simp only [div_self (one_ne_zero : (1:ℝ) ≠ 0), one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤ -1/2+1)]
  calc
    _ = ∫ x in Set.Ioc (-1/2:ℝ) (-1/2+1), g x*phase t w x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only [circleChirp]
      rw [AddCircle.liftIoc_coe_apply hx, smul_eq_mul]
      calc
        _ = g x*(fourier (-w) (x : UnitAddCircle)*phase t 0 x) := by ring
        _ = _ := by rw [phase_fourier]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : g x=0 := cutoff_zero hs (by
        intro ⟨hx1,hx2⟩
        apply hx
        constructor <;> linarith)
      rw [hz,zero_mul]

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_coefficient := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_coefficient
