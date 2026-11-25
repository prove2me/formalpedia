-- Prove2me | solution 1 for GlobalTheory.HCXi.LineStabiliser.pair_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:24.01048+00:00
-- url     : https://prove2.me/submissions/ef8a41c3-9316-4fb7-83d7-f41fe4814a0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_gram_mulVec_e0
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_pair_e0_left
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_lift_lst
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_e0_lst_eq_zero
import Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_pair_lift

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
theorem _root_.solution (v w : Fin (2 * r' + k + 1) → ℂ) (c d : ℂ) :
    star (liftVec k 1 r' w + d • e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ (liftVec k 1 r' v + c • e0 k r')) =
      star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [star_add, add_dotProduct, star_smul, smul_dotProduct, pair_e0_left, mulVec_add, dotProduct_add,
    pair_lift, mulVec_smul, gram_mulVec_e0, dotProduct_smul, dotProduct_single_one]
  simp [lift_lst, e0_lst_eq_zero]
end GlobalTheory.HCXi.LineStabiliser
