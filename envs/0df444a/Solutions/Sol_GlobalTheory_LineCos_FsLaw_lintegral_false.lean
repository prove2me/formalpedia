-- Prove2me | solution 1 for GlobalTheory.LineCos.FsLaw.lintegral_false
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:49.913805+00:00
-- url     : https://prove2.me/submissions/cc840009-6bca-48db-855d-3e7372ebdeb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_re_det_pos
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_corner_eq
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_hform_single
import Theorems.Thm_GlobalTheory_LineCos_FsLaw_re_hform_mul
import Theorems.Thm_GlobalTheory_FibLine_MoebiusLintegral_lintegral_moebius
import Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_ae_affine_ne
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
    ∫⁻ x : ℂ, ENNReal.ofReal (G.det.re / (Real.pi * (hform G (lineVec false x) (lineVec false x)).re ^ 2)) *
      g (cosSq false G x) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have ha : 0 < a := re_corner_pos hG
  have hD : 0 < D := re_det_pos hG
  have hG0 : G 0 0 = (a : ℂ) := corner_eq hG
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hc : ((Real.sqrt D / a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (div_pos (Real.sqrt_pos.2 hD) ha).ne'
  have hH : Measurable fun x : ℂ =>
      g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) := by
    have : Measurable fun x : ℂ => g (1 / (1 + ‖x‖ ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← GlobalTheory.FibLine.lintegral_comp_fsDens g hg,
    ← GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius (G 1 0 / a) _ hc _ hH]
  refine lintegral_congr_ae ?_
  filter_upwards [GlobalTheory.FibLine.UnitaryInv.ae_affine_ne 1 (G 1 0 / a) (Or.inl one_ne_zero)] with x hx
  have hsq := re_hform_mul hG (lineVec false x)
  have hone := hform_single G (lineVec false x)
  have hw0 : lineVec false x 0 = 1 := rfl
  have hw1 : lineVec false x 1 = x := rfl
  have hp : 1 * G 0 0 + x * G 1 0 = a * (1 + G 1 0 / a * x) := by
    rw [hG0]; field_simp
  rw [hw0, hw1, hp] at hsq hone
  set q : ℝ := ‖1 + G 1 0 / a * x‖ with hq_def
  have hq : 0 < q := norm_pos_iff.2 hx
  have hn : ‖(a : ℂ) * (1 + G 1 0 / a * x)‖ = a * q := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hcn : ‖((Real.sqrt D / a : ℝ) : ℂ)‖ ^ 2 = D / a ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hD.le]
  have hy : ‖((Real.sqrt D / a : ℝ) : ℂ) * x / (1 + G 1 0 / a * x)‖ ^ 2 = D / a ^ 2 * ‖x‖ ^ 2 / q ^ 2 := by
    rw [norm_div, norm_mul, div_pow, mul_pow, hcn]
  have hj : ‖((Real.sqrt D / a : ℝ) : ℂ) / (1 + G 1 0 / a * x) ^ 2‖ ^ 2 = D / a ^ 2 / q ^ 4 := by
    rw [norm_div, norm_pow, div_pow, hcn, ← pow_mul]
  rw [hn, ← ha_def, ← hD_def] at hsq
  have hh : (hform G (lineVec false x) (lineVec false x)).re = ((a * q) ^ 2 + D * ‖x‖ ^ 2) / a :=
    eq_div_of_mul_eq ha.ne' hsq
  have hcos : cosSq false G x = 1 / (1 + D / a ^ 2 * ‖x‖ ^ 2 / q ^ 2) := by
    unfold cosSq
    rw [hone, hn, ← ha_def, hsq]
    field_simp
  have hpi := Real.pi_pos
  rw [hy, hj, hcos, hh, mul_left_comm, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp
end GlobalTheory.LineCos.FsLaw
