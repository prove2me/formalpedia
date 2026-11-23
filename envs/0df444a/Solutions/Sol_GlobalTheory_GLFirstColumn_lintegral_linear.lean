-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.lintegral_linear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:09.82588+00:00
-- url     : https://prove2.me/submissions/ea87313c-9842-41da-be89-1db858430cf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution {ι κ : Type} [Fintype ι] [Fintype κ]
    (L : (κ → ι → ℂ) →ₗ[ℂ] (κ → ι → ℂ)) (hL : LinearMap.det L ≠ 0)
    (F : (κ → ι → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal (‖LinearMap.det L‖ ^ 2) * ∫⁻ z, F (L z) := by
  have hdet : LinearMap.det (L.restrictScalars ℝ) = ‖LinearMap.det L‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖LinearMap.det L‖ ^ 2 := pow_pos (norm_pos_iff.2 hL) _
  haveI : (volume : Measure (ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (κ → ι → ℂ))
    (f := L.restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
  have hm : Measurable (L.restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have h1 := lintegral_map (μ := volume) hF hm
  rw [hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos)] at h1
  simp only [LinearMap.restrictScalars_apply] at h1
  rw [← h1, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]
end GlobalTheory.GLFirstColumn
