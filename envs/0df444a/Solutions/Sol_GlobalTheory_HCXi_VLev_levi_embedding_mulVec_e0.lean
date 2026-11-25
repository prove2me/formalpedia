-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.levi_embedding_mulVec_e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:57.586838+00:00
-- url     : https://prove2.me/submissions/f8ca7485-0ed0-4867-b50e-e10e6eaae4b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_PI_QnLevBasicsW_col_fix


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
theorem _root_.solution (k r' : ℕ) (y : Mat k r') : ιLev k 1 r' y *ᵥ e0 k r' = e0 k r' :=
  PI.QnLevBasicsW.col_fix y _ (fun b hb => by simp [eI, a0] at hb)
end GlobalTheory.HCXi.VLev
