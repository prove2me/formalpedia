-- Prove2me | solution 1 for GlobalTheory.HCXi.LineStabiliser.e0_lst_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:15:38.592275+00:00
-- url     : https://prove2.me/submissions/568d3f46-3317-41b5-99cc-41d712cb6992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_e0_eq

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.LineStabiliser
open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser
variable (k r' : ℕ)
namespace GlobalTheory.HCXi.LineStabiliser
theorem _root_.solution : e0 k r' (lst k r') = 0 := by
  rw [e0_eq, Pi.single_apply, if_neg]
  simp only [lst, fst, Fin.ext_iff]
  omega
end GlobalTheory.HCXi.LineStabiliser
