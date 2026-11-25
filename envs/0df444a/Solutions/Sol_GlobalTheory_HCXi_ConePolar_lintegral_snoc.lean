-- Prove2me | solution 1 for GlobalTheory.HCXi.ConePolar.lintegral_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:01:03.63718+00:00
-- url     : https://prove2.me/submissions/1166ff0b-f485-4247-9f2a-310410a34991

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
theorem _root_.solution (k : ℕ) (f : (Fin (k + 1) → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v = ∫⁻ w : Fin k → ℂ, ∫⁻ z : ℂ, f (Fin.snoc (α := fun _ => ℂ) w z) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℂ) (Fin.last k)).symm
  rw [← h.lintegral_comp hf, Measure.volume_eq_prod,
    lintegral_prod_symm' _ (by exact hf.comp (MeasurableEquiv.measurable _))]
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
end GlobalTheory.HCXi.ConePolar
