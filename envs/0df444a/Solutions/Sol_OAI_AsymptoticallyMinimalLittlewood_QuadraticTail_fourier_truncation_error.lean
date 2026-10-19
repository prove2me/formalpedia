-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.fourier_truncation_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:25:01.710932+00:00
-- url     : https://prove2.me/submissions/14e9e53c-2c19-4db4-a08e-76af5440d596

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L387-L417
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.fourier_truncation_error. The node keeps its source
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

lemma circle_fourier_norm (w : ℤ) (z : UnitAddCircle) : ‖fourier w z‖=1 :=
  Circle.norm_coe _

/-- Uniform truncation from a summable majorant outside one finite box. -/
lemma fourier_truncation_error (f : C(UnitAddCircle,ℂ)) (S : Finset ℤ)
    (b : ℤ → ℝ) (hb : Summable b) (hb0 : ∀ w, 0≤b w)
    (hbound : ∀ w, w ∉ S → ‖fourierCoeff f w‖ ≤ b w) (z : UnitAddCircle) :
    ‖(∑ w ∈ S, fourierCoeff f w*fourier w z)-f z‖ ≤ ∑' w, b w := by
  classical
  have hcomp : Summable (fun w : {w : ℤ // w ∉ S} ↦ fourierCoeff f w.val) := by
    exact (hb.subtype _).of_norm_bounded (fun w ↦ hbound w.val w.property)
  have hh : Summable (fourierCoeff f) := (S.summable_compl_iff).mp hcomp
  have hs := has_pointwise_sum_fourier_series_of_summable hh z
  simp only [smul_eq_mul] at hs
  have hterm := hs.summable
  have he := hterm.sum_add_tsum_compl (s := S)
  rw [hs.tsum_eq] at he
  change (∑ w ∈ S, fourierCoeff f w*fourier w z) +
    (∑' w : {w : ℤ // w ∉ S}, fourierCoeff f w.val*fourier w.val z) = f z at he
  have heq : (∑ w ∈ S, fourierCoeff f w*fourier w z)-f z =
      -(∑' w : {w : ℤ // w ∉ S}, fourierCoeff f w.val*fourier w.val z) := by
    linear_combination he
  rw [heq, norm_neg]
  have hbc : Summable (fun w : {w : ℤ // w ∉ S} ↦ b w.val) := hb.subtype _
  calc
    _ ≤ ∑' w : {w : ℤ // w ∉ S}, b w.val := by
      apply ((hterm.subtype _).hasSum).norm_le_of_bounded hbc.hasSum
      intro w
      change ‖fourierCoeff f w.val * fourier w.val z‖ ≤ b w.val
      rw [norm_mul, circle_fourier_norm, mul_one]
      exact hbound w.val w.property
    _ ≤ ∑' w, b w := by
      exact hbc.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun w _ ↦ hb0 w) (fun _ ↦ le_rfl) hb

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.fourier_truncation_error := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.fourier_truncation_error
