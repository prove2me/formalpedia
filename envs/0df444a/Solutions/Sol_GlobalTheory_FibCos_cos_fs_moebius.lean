-- Prove2me | solution 1 for GlobalTheory.FibCos.cos_fs_moebius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:50.992798+00:00
-- url     : https://prove2.me/submissions/ec24afb6-bdc4-45b6-b3fa-50a0d86be4f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreCosineExplicitFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option autoImplicit false
open GlobalTheory GlobalTheory.FibCos
namespace GlobalTheory.FibCos
theorem _root_.solution (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (x : ℂ)
    (hx : 1 + G 1 0 / G 0 0 * x ≠ 0) :
    GlobalTheory.FibCos.cos G x = 1 / (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ∧
    GlobalTheory.FibCos.fs G x = ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 *
      (1 / (Real.pi * (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ^ 2)) := by
  have h00 : (0 : ℂ) < G 0 0 := hG.diag_pos
  have hdet : (0 : ℂ) < G.det := hG.det_pos
  obtain ⟨ha, ha'⟩ := Complex.pos_iff.mp h00
  obtain ⟨hD, -⟩ := Complex.pos_iff.mp hdet
  have h01 : G 0 1 = (starRingEnd ℂ) (G 1 0) := (hG.isHermitian.apply 0 1).symm
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have hGa : G 0 0 = (a : ℂ) := by
    apply Complex.ext
    · simp [ha_def]
    · simp [← ha']
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set u : ℝ := ‖1 + G 1 0 / G 0 0 * x‖ ^ 2 with hu_def
  set s : ℝ := ‖x‖ ^ 2 with hs_def
  have hu : 0 < u := by positivity
  have hs : 0 ≤ s := by positivity
  have hnum : ‖G 0 0 + x * G 1 0‖ ^ 2 = a ^ 2 * u := by
    have : G 0 0 + x * G 1 0 = (a : ℂ) * (1 + G 1 0 / G 0 0 * x) := by
      rw [hGa]; field_simp
    rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hDe : D = a * (G 1 1).re - ((G 1 0).re ^ 2 + (G 1 0).im ^ 2) := by
    rw [hD_def, Matrix.det_fin_two, h01, hGa]
    simp
    ring
  have hn : nrm G x = a * u + D / a * s := by
    have h1 : a * nrm G x = a ^ 2 * u + D * s := by
      rw [← hnum, hDe, hs_def, nrm, h01, hGa]
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    field_simp
    linarith
  have hc : ‖(Real.sqrt D / a : ℂ)‖ ^ 2 = D / a ^ 2 := by
    rw [norm_div, div_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, Real.sq_sqrt hD.le]
  have hy : ‖(Real.sqrt D / a : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2 = D / a ^ 2 * s / u := by
    rw [norm_div, norm_mul, div_pow, mul_pow, hc]
  have hd : ‖(Real.sqrt D / a : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 = D / a ^ 2 / u ^ 2 := by
    rw [norm_div, norm_pow, div_pow, hc]
  have hpi := Real.pi_pos
  rw [hy, hd]
  constructor
  · rw [cos, hnum, hn, ← ha_def]
    field_simp
  · rw [fs, hn, ← hD_def]
    field_simp
end GlobalTheory.FibCos
