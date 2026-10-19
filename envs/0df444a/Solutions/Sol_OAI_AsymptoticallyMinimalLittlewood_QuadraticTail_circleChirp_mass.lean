-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:28:19.743214+00:00
-- url     : https://prove2.me/submissions/55cd97d8-c51b-457a-a317-ba5abd1b8619

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L448-L468
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_mass. The node keeps its source
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

lemma phase_norm (t u x : ℝ) : ‖phase t u x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

lemma cutoff_zero {g : ℝ → ℂ} {α x : ℝ}
    (hs : tsupport g ⊆ Set.Icc (-α) α) (hx : x ∉ Set.Icc (-α) α) : g x=0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))

lemma circleChirp_mass {g : ℝ → ℂ} {α : ℝ} (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    (∫ z : UnitAddCircle, ‖circleChirp g t z‖^2 ∂AddCircle.haarAddCircle) =
      ∫ x : ℝ, ‖g x‖^2 := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.integral_preimage 1 (-1/2)]
  calc
    _ = ∫ x in Set.Ioc (-1/2:ℝ) (-1/2+1), ‖g x‖^2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change ‖circleChirp g t (x : UnitAddCircle)‖^2 = ‖g x‖^2
      rw [circleChirp, AddCircle.liftIoc_coe_apply hx, norm_mul, phase_norm, mul_one]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : g x=0 := cutoff_zero hs (by
        intro ⟨hx1,hx2⟩
        apply hx
        constructor <;> linarith)
      simp [hz]

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_mass := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_mass
