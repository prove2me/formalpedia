-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.star_e0_dotProduct_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:53.086896+00:00
-- url     : https://prove2.me/submissions/71332ca5-97b4-4f93-9c72-c4d5e2b1e94f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_GlobalTheory_HCXi_VLev_star_e0_dotProduct
import Theorems.Thm_PI_QnLevBasicsW_liftVec_apply_out


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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev
namespace GlobalTheory.HCXi.VLev
theorem _root_.solution (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (e0 k r') ⬝ᵥ liftVec k 1 r' w = 0 := by
  rw [star_e0_dotProduct]; exact PI.QnLevBasicsW.liftVec_apply_out _ _ (by simp [eI, a0])
end GlobalTheory.HCXi.VLev
