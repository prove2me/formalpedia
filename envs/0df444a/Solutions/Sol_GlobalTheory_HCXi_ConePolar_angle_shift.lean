-- Prove2me | solution 1 for GlobalTheory.HCXi.ConePolar.angle_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:00:53.668988+00:00
-- url     : https://prove2.me/submissions/9f38e992-c9d0-417c-b6fd-0e33f666a36d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibration

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConePolar
namespace GlobalTheory.HCXi.ConePolar
theorem _root_.solution (h : ℝ → ℝ≥0∞) (hp : Function.Periodic h (2 * Real.pi)) :
    ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, h θ = ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), h θ := by
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) (-Real.pi) hp.lift
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0 hp.lift
  simp only [Function.Periodic.lift_coe] at h1 h2
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, h1, h2]
end GlobalTheory.HCXi.ConePolar
