-- Prove2me | solution 1 for GlobalTheory.GaussHerm.integral_exp_neg_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:32:55.639254+00:00
-- url     : https://prove2.me/submissions/d0e78397-4a8a-44a9-a8a2-263bf84da47d

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDef
import Theorems.Thm_GlobalTheory_GaussHerm_finrank_V
import Theorems.Thm_GlobalTheory_GaussHerm_det_toEuclideanLin
import Theorems.Thm_GlobalTheory_GaussHerm_quad_eq
import Theorems.Thm_GlobalTheory_GaussHerm_exists_eq_conjTranspose_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.GaussHerm
namespace GlobalTheory.GaussHerm
theorem _root_.solution : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef →
    Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧
    ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) =
      Real.pi ^ n / H.det.re := by
  intro n H hH
  have hT : H.transpose.PosDef := Matrix.PosDef.transpose_iff.mpr hH
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hT.posSemidef
  set L : V n →ₗ[ℝ] V n := (Matrix.toEuclideanLin C).restrictScalars ℝ with hL
  have hdetL : LinearMap.det L = Complex.normSq C.det := by
    rw [hL, LinearMap.det_restrictScalars, det_toEuclideanLin, Algebra.norm_complex_apply]
  have hdetC : H.det = (Complex.normSq C.det : ℂ) := by
    rw [← Matrix.det_transpose H, hC, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      mul_comm, Complex.mul_conj]
  have hdetH : H.det.re = Complex.normSq C.det := by rw [hdetC, Complex.ofReal_re]
  have hpos : 0 < Complex.normSq C.det := by
    have := hH.det_pos
    rwa [hdetC, Complex.zero_lt_real] at this
  set g : V n → ℝ := fun v => Real.exp (-1 * ‖v‖ ^ 2) with hg
  have hf : (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) =
      fun w => g (L w) := by
    funext w
    rw [quad_eq H C hC w, hg]
    simp [hL]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (V n)) (f := L)
    (by rw [hdetL]; exact hpos.ne')
  have hG : ∫ v : V n, g v = Real.pi ^ n := by
    rw [hg, GaussianFourier.integral_rexp_neg_mul_sq_norm one_pos, finrank_V, div_one]
    rw [show ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hI : ∫ w : V n, g (L w) = Real.pi ^ n / H.det.re := by
    rw [← integral_map (L.continuous_of_finiteDimensional.aemeasurable)
      hgc.aestronglyMeasurable, hmap, integral_smul_measure, hG, hdetL, hdetH,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr hpos), smul_eq_mul,
      div_eq_inv_mul]
  rw [hf]
  refine ⟨Integrable.of_integral_ne_zero ?_, hI⟩
  rw [hI, hdetH]
  exact (div_pos (pow_pos Real.pi_pos n) hpos).ne'
end GlobalTheory.GaussHerm
