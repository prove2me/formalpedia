-- Prove2me | solution 1 for GlobalTheory.HCXi.ConePolar.measurable_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:01:05.859132+00:00
-- url     : https://prove2.me/submissions/a2eca812-8b92-4d7f-b69c-f3f60edcd493

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
theorem _root_.solution (k : ℕ) :
    Measurable fun q : (Fin k → ℂ) × ℂ => (Fin.snoc (α := fun _ => ℂ) q.1 q.2 : Fin (k + 1) → ℂ) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using measurable_snd
  · simp only [Fin.snoc_castSucc]; fun_prop
end GlobalTheory.HCXi.ConePolar
