-- Prove2me | solution 1 for GlobalTheory.MinorInt.lintegral_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:23.156801+00:00
-- url     : https://prove2.me/submissions/22e5e090-b47c-4165-8d58-2d0bab8a2623

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) (F : (κ → ι → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ c, F c = ∫⁻ z : κ → ι → ℂ, ENNReal.ofReal (‖A.det‖ ^ (2 * Fintype.card κ)) *
      F (fun k => z k ᵥ* A) := by
  let L : (κ → ι → ℂ) →ₗ[ℂ] (κ → ι → ℂ) :=
    LinearMap.pi fun k => (Matrix.toLin' Aᵀ).comp (LinearMap.proj k)
  have hL : LinearMap.det L = A.det ^ Fintype.card κ := by
    rw [LinearMap.det_pi]; simp [LinearMap.det_toLin']
  have hdet : LinearMap.det (L.restrictScalars ℝ) = ‖A.det‖ ^ (2 * Fintype.card κ) := by
    rw [LinearMap.det_restrictScalars, hL, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
      norm_pow, ← pow_mul, mul_comm]
  have hpos : 0 < ‖A.det‖ ^ (2 * Fintype.card κ) := pow_pos (norm_pos_iff.2 hA) _
  haveI : (volume : Measure (κ → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (κ → ι → ℂ))
    (f := L.restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
  have hm : Measurable (L.restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have h1 := lintegral_map (μ := volume) hF hm
  rw [hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos)] at h1
  have h2 : ∀ z : κ → ι → ℂ, (L.restrictScalars ℝ) z = fun k => z k ᵥ* A := by
    intro z; ext k i; simp [L, Matrix.toLin'_apply, mulVec_transpose]
  simp only [h2] at h1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← h1, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]
end GlobalTheory.MinorInt
