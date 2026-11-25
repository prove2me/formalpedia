-- Prove2me | solution 1 for GlobalTheory.FlagVolume.lintegral_comp_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:36.787006+00:00
-- url     : https://prove2.me/submissions/44186314-49f9-4ee4-ace0-bf76fb8b362f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralProdPartialSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat
open GlobalTheory GlobalTheory.FlagVolume
namespace GlobalTheory.FlagVolume
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ)
    (hR : R.det ≠ 0) {f : (n → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ b, f b = ENNReal.ofReal (‖R.det‖ ^ 2) * ∫⁻ y, f (Matrix.vecMul y R) := by
  let T : (n → ℂ) →ₗ[ℝ] (n → ℂ) := (Matrix.toLin' R.transpose).restrictScalars ℝ
  have hT : LinearMap.det T = ‖R.det‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hp : 0 < ‖R.det‖ ^ 2 := by positivity
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (n → ℂ))
    (f := T) (hT ▸ hp.ne')
  have hTm : Measurable T := T.continuous_of_finiteDimensional.measurable
  have h1 : ∫⁻ y, f (Matrix.vecMul y R) = ∫⁻ y, f (T y) := by
    simp [T, Matrix.mulVec_transpose]
  rw [h1, ← lintegral_map hf hTm, hmap, lintegral_smul_measure, hT, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hp.le, abs_of_pos (inv_pos.2 hp), mul_inv_cancel₀ hp.ne']
  simp
end GlobalTheory.FlagVolume
