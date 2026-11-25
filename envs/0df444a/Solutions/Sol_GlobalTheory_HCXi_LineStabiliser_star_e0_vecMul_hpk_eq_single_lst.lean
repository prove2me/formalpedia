-- Prove2me | solution 1 for GlobalTheory.HCXi.LineStabiliser.star_e0_vecMul_hpk_eq_single_lst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:00:31.352418+00:00
-- url     : https://prove2.me/submissions/5881ffb8-7ad9-49da-ae86-88a5f423ebfa

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
theorem _root_.solution : star (e0 k r') ᵥ* Hpk k (1 + r') = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  have h : star (e0 k r') = Pi.single (fst k r') 1 := by
    rw [e0_eq, ← Pi.single_star, star_one]
  rw [h, single_one_vecMul, Matrix.row_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end GlobalTheory.HCXi.LineStabiliser
