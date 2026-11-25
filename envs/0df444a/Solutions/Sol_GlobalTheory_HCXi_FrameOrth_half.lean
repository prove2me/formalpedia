-- Prove2me | solution 1 for GlobalTheory.HCXi.FrameOrth.half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:14.435642+00:00
-- url     : https://prove2.me/submissions/9a2f84a1-5702-4904-b59e-1087bb76b691

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.FrameOrth
namespace GlobalTheory.HCXi.FrameOrth
theorem _root_.solution : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2) = 1 := by
  have h : (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * 2) = (1 : ℝ) := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  exact_mod_cast h
end GlobalTheory.HCXi.FrameOrth
