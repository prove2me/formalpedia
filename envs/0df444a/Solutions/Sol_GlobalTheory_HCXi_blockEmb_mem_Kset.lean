-- Prove2me | solution 1 for GlobalTheory.HCXi.blockEmb_mem_Kset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:54.921844+00:00
-- url     : https://prove2.me/submissions/e81e5813-c8e4-4c5b-844c-0c61805a614c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_BlockEmbConjTranspose
import Theorems.Thm_GlobalTheory_HCXi_blockEmb_conjTranspose
import Theorems.Thm_PI_QnLevBasicsW_level_group_homomorphism
import Theorems.Thm_PI_QnLevBasicsW_level_group_unitary_hermitian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B GlobalTheory.HCXi
noncomputable section
open GlobalTheory GlobalTheory.HCXi
namespace GlobalTheory.HCXi
theorem _root_.solution : ∀ k r' : ℕ, ∀ y ∈ Kset k r', ιLev k 1 r' y ∈ Kset k (1 + r') := by
  intro k r' y hy
  refine ⟨PI.QnLevBasicsW.level_group_unitary_hermitian k 1 r' y hy.1, ?_⟩
  rw [blockEmb_conjTranspose, ← (PI.QnLevBasicsW.level_group_homomorphism k 1 r').2, hy.2]
  exact (PI.QnLevBasicsW.level_group_homomorphism k 1 r').1
end GlobalTheory.HCXi
