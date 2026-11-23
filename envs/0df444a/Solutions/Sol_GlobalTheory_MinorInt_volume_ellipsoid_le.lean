-- Prove2me | solution 1 for GlobalTheory.MinorInt.volume_ellipsoid_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:12.747903+00:00
-- url     : https://prove2.me/submissions/09d3adfd-e812-44b5-b30e-6c534a0d9a57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_form_gram_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (R : ℝ) {H : Matrix ι ι ℂ}
    (hH : H.PosSemidef) (hd : H.det ≠ 0) :
    volume {x : ι → ℂ | (star x ⬝ᵥ H *ᵥ x).re ≤ R} ≤
      ENNReal.ofReal ‖H.det‖⁻¹ * volume (Metric.closedBall (0 : ι → ℂ) (Real.sqrt R)) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  have hB' : H = Bᴴ * B := hB
  have hdG : ‖H.det‖ = Complex.normSq B.det := by
    rw [hB', det_mul, det_conjTranspose, norm_mul, norm_star, Complex.normSq_eq_norm_sq, sq]
  have hpos : 0 < Complex.normSq B.det := hdG ▸ norm_pos_iff.mpr hd
  have hdet : LinearMap.det ((Matrix.toLin' B).restrictScalars ℝ) = Complex.normSq B.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  have := Measure.addHaar_preimage_linearMap (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' B).restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
    (Metric.closedBall (0 : ι → ℂ) (Real.sqrt R))
  rw [hdet, abs_of_pos (inv_pos.mpr hpos), ← hdG] at this
  rw [← this]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_setOf_eq, hB', form_gram_re] at hx
  simp only [Set.mem_preimage, mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
  refine Real.le_sqrt_of_sq_le (le_trans ?_ hx)
  exact Finset.single_le_sum (f := fun k => ‖(B *ᵥ x) k‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ k)
end GlobalTheory.MinorInt
