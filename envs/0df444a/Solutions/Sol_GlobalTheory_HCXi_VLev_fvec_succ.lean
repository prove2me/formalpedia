-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.fvec_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:26:23.056277+00:00
-- url     : https://prove2.me/submissions/636164f1-73bd-4456-9c73-c0319b29ea75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_P2M_GlobalTheory_HCXi_VLev_liftVec_add__79631f3209d2
import Theorems.Thm_P2M_GlobalTheory_HCXi_VLev_liftVec_smul__cdca075b6107
import Theorems.Thm_PI_QnLevBasicsW_bvec_lift


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
theorem _root_.solution (k r' : ℕ) (j : Fin (1 + r' + 1)) (b : Fin (r' + 1)) (hj : j.val = b.val + 1) :
    fvec k (1 + r') (isoVec k (1 + r')) j = liftVec k 1 r' (fvec k r' (isoVec k r') b) := by
  unfold fvec
  by_cases hb : b.val < r'
  · rw [dif_pos (by omega), dif_pos hb]
    exact (PI.QnLevBasicsW.bvec_lift _ _ (by simp only [eI]; omega)).symm
  · rw [dif_neg (by omega), dif_neg hb]
    unfold isoVec
    rw [liftVec_smul', liftVec_add', PI.QnLevBasicsW.bvec_lift _ (wI k (1 + r') 0) (by simp only [wI]; omega),
      PI.QnLevBasicsW.bvec_lift _ (wI k (1 + r') (Fin.last k)) (by simp only [wI]; omega)]
end GlobalTheory.HCXi.VLev
