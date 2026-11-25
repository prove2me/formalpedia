-- Prove2me | solution 1 for GlobalTheory.HCXi.LineStabiliser.gram_mulVec_e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:15:40.801594+00:00
-- url     : https://prove2.me/submissions/8251c9e7-0b67-4eae-9d7b-6497bdfed9fb

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
theorem _root_.solution : Hpk k (1 + r') *ᵥ e0 k r' = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  rw [e0_eq, mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end GlobalTheory.HCXi.LineStabiliser
