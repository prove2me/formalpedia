-- Prove2me | solution 1 for GlobalTheory.LineCos.FsLaw.lintegral_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:50.798392+00:00
-- url     : https://prove2.me/submissions/8fac10e7-268a-46f7-b8fd-a123ef7fb346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_re_det_pos
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_corner_eq
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_hform_single
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_re_hform_mul
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_lintegral_reflect
import Theorems.Thm_GlobalTheory_FibLine_MoebiusLintegral_lintegral_moebius
import Theorems.Thm_GlobalTheory_FibLine_lintegral_comp_fsDens
import Theorems.Thm_GlobalTheory_LineCos_re_corner_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LineCos GlobalTheory.LineCos.FsLaw
open GlobalTheory.LineCos
namespace GlobalTheory.LineCos.FsLaw
theorem _root_.solution {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, ENNReal.ofReal (G.det.re / (Real.pi * (hform G (lineVec true x) (lineVec true x)).re ^ 2)) *
      g (cosSq true G x) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have ha : 0 < a := re_corner_pos hG
  have hD : 0 < D := re_det_pos hG
  have hG0 : G 0 0 = (a : ℂ) := corner_eq hG
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hc : ((a / Real.sqrt D : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (div_pos ha (Real.sqrt_pos.2 hD)).ne'
  have hg' : Measurable fun t : ℝ => g (1 - t) := hg.comp (by fun_prop)
  have hH : Measurable fun x : ℂ =>
      g (1 - 1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) := by
    have : Measurable fun x : ℂ => g (1 - 1 / (1 + ‖x‖ ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← lintegral_reflect, ← GlobalTheory.FibLine.lintegral_comp_fsDens _ hg',
    ← GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius 0 _ hc _ hH,
    ← lintegral_sub_right_eq_self _ (G 1 0 / a)]
  refine lintegral_congr fun x => ?_
  have hsq := re_hform_mul hG (lineVec true (x - G 1 0 / a))
  have hone := hform_single G (lineVec true (x - G 1 0 / a))
  have hw0 : lineVec true (x - G 1 0 / a) 0 = x - G 1 0 / a := rfl
  have hw1 : lineVec true (x - G 1 0 / a) 1 = 1 := rfl
  have hp : (x - G 1 0 / a) * G 0 0 + 1 * G 1 0 = a * x := by
    rw [hG0]; field_simp; ring
  rw [hw0, hw1, hp] at hsq hone
  have hn : ‖(a : ℂ) * x‖ = a * ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hcn : ‖((a / Real.sqrt D : ℝ) : ℂ)‖ ^ 2 = a ^ 2 / D := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hD.le]
  have hy : ‖((a / Real.sqrt D : ℝ) : ℂ) * x / (1 + 0 * x)‖ ^ 2 = a ^ 2 / D * ‖x‖ ^ 2 := by
    rw [zero_mul, add_zero, div_one, norm_mul, mul_pow, hcn]
  have hj : ‖((a / Real.sqrt D : ℝ) : ℂ) / (1 + 0 * x) ^ 2‖ ^ 2 = a ^ 2 / D := by
    rw [zero_mul, add_zero, one_pow, div_one, hcn]
  rw [hn, ← ha_def, ← hD_def, norm_one, one_pow, mul_one] at hsq
  have hh : (hform G (lineVec true (x - G 1 0 / a)) (lineVec true (x - G 1 0 / a))).re = ((a * ‖x‖) ^ 2 + D) / a :=
    eq_div_of_mul_eq ha.ne' hsq
  have hcos : cosSq true G (x - G 1 0 / a) = 1 - 1 / (1 + a ^ 2 / D * ‖x‖ ^ 2) := by
    unfold cosSq
    rw [hone, hn, ← ha_def, hsq]
    field_simp
    ring
  have hpi := Real.pi_pos
  rw [hy, hj, hcos, hh, mul_left_comm, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp
  ring
end GlobalTheory.LineCos.FsLaw
