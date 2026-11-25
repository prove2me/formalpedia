-- Prove2me | solution 1 for GlobalTheory.HodgeChartRow.isOpen_punctured
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:32.460403+00:00
-- url     : https://prove2.me/submissions/b8d9fd2f-d406-42ef-8ff1-bd420c9ce831

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydiscStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeChartBoundsOfSchurLemW
import Theorems.Thm_GlobalTheory_HodgeChartRow_isOpen_polydisc
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_HodgeGramLocal_isOpen_polydisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeChartRow
namespace GlobalTheory.HodgeChartRow
theorem _root_.solution {n a : ℕ} (ha : a ≤ n) (ρ : ℝ) : IsOpen (punctured ha ρ) := by
  have : punctured ha ρ = polydisc n ρ ∩ ⋂ i : Fin a, {z : Fin n → ℂ | z (Fin.castLE ha i) ≠ 0} := by
    ext z; simp [punctured]
  rw [this]
  exact (isOpen_polydisc n ρ).inter
    (isOpen_iInter_of_finite fun i => isOpen_ne_fun (by fun_prop) continuous_const)
end GlobalTheory.HodgeChartRow
