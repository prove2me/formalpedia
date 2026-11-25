-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.gauss_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:05:03.498819+00:00
-- url     : https://prove2.me/submissions/fb1df828-561f-48a4-833e-19c959dbb296

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_continuous_sqLen
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
theorem _root_.solution (n : ℕ) :
    ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (Real.exp (-(2 * sqLen w))) ≠ 0 := by
  have hm : Measurable fun w : Fin n → ℂ => ENNReal.ofReal (Real.exp (-(2 * sqLen w))) := by
    have := (continuous_sqLen n).measurable
    fun_prop
  refine ((lintegral_pos_iff_support hm).2 ?_).ne'
  have : (Function.support fun w : Fin n → ℂ => ENNReal.ofReal (Real.exp (-(2 * sqLen w))))
      = Set.univ := by
    ext w
    simp [Real.exp_pos]
  rw [this]
  exact isOpen_univ.measure_pos _ Set.univ_nonempty
end GlobalTheory.HCXi.ConeZero
