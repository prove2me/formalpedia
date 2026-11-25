-- Prove2me | solution 1 for GlobalTheory.HypOrbitUnique.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:20.055271+00:00
-- url     : https://prove2.me/submissions/817ffacb-455f-45fb-af42-794b0a20e139

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation
import Theorems.Thm_PI_RhsWLim_W_MB_emb_mul
import Theorems.Thm_PI_RhsWLim_W_blkAct_mul
import Theorems.Thm_PI_RhsWLim_W_opAct_emb
import Theorems.Thm_PI_RhsWLim_W_op_uwb_eq_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypOrbitUnique
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace GlobalTheory.HypOrbitUnique
theorem _root_.solution (g g' : Gp k r) (p : (Fin k → ℂ) × ℂ) : act (g * g') p = act g (act g' p) := by
  unfold act
  have e : (Matrix.of (inc (g * g')) : Mat k r) = Matrix.of (inc g) * Matrix.of (inc g') := rfl
  rw [e, op_uwb_eq_emb (inc_mem g), op_uwb_eq_emb (inc_mem g'), ← emb_mul, opAct_emb, opAct_emb, opAct_emb,
    blkAct_mul]
end GlobalTheory.HypOrbitUnique
