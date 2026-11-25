-- Prove2me | solution 1 for GlobalTheory.HCXi.blockEmb_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:59:23.084687+00:00
-- url     : https://prove2.me/submissions/ff00f143-a1b1-443e-954e-9c5ab31c42f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_BlockEmbConjTranspose
import Theorems.Thm_P2M_PI_QnLevBasicsW__Lev_eq_c687ca9a93c5


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
theorem _root_.solution (k i r' : ℕ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    (ιLev k i r' g)ᴴ = ιLev k i r' gᴴ := by
  rw [PI.QnLevBasicsW.ιLev_eq, PI.QnLevBasicsW.ιLev_eq, conjTranspose_submatrix, fromBlocks_conjTranspose]
  simp
end GlobalTheory.HCXi
