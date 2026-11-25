-- Prove2me | solution 1 for GlobalTheory.HypChartPf.gen_semiconj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:05.4198+00:00
-- url     : https://prove2.me/submissions/202e2a38-dbd1-4078-b412-7e22ffb98d25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula

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
open GlobalTheory GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
namespace GlobalTheory.HypChartPf
theorem _root_.solution (k r : ℕ) (q : TrE k) :
    SemiconjBy (Matrix.diagonal (sgn k r)) (-opGen k r q) (opGen k r q)ᴴ := by
  show _ = _
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
  unfold opGen sgn
  split_ifs <;> (try (exfalso; omega)) <;> simp
end GlobalTheory.HypChartPf
