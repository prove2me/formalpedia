-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.lintegral_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:18:37.230914+00:00
-- url     : https://prove2.me/submissions/c24bed60-2e51-47fe-bc6c-4573c1ed2b79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_continuous_sqLen
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_continuous_param
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_sqLen_param
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_continuous_sqLen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeZero
namespace GlobalTheory.HCXi.ConeZero
theorem _root_.solution (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ v, F (sqLen v) ∂coneMeasure n
      = (∫⁻ w : Fin n → ℂ, F (2 * sqLen w)) * ENNReal.ofReal (2 * Real.pi) := by
  have hm : Measurable fun w : Fin n → ℂ => F (2 * sqLen w) :=
    hF.comp ((continuous_sqLen n).measurable.const_mul 2)
  rw [coneMeasure, lintegral_map (f := fun v => F (sqLen v)) (hF.comp (continuous_sqLen _).measurable)
    (continuous_param n).measurable]
  simp only [sqLen_param]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun p : (Fin n → ℂ) × ℝ => F (2 * sqLen p.1)) (hm.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
    Real.volume_Ioc, sub_zero]
  rw [lintegral_mul_const _ hm]
end GlobalTheory.HCXi.ConeZero
