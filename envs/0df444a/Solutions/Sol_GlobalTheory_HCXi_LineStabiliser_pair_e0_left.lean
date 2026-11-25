-- Prove2me | solution 1 for GlobalTheory.HCXi.LineStabiliser.pair_e0_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:25:28.657953+00:00
-- url     : https://prove2.me/submissions/7cb0a687-23fe-4276-bee7-f456ba1fcde3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_star_e0_vecMul_hpk_eq_single_lst

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
theorem _root_.solution (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    star (e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ v) = v (lst k r') := by
  rw [dotProduct_mulVec, star_e0_vecMul_hpk_eq_single_lst, single_one_dotProduct]
end GlobalTheory.HCXi.LineStabiliser
