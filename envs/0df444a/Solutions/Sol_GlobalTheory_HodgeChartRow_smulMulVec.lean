-- Prove2me | solution 1 for GlobalTheory.HodgeChartRow.smulMulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:27.22815+00:00
-- url     : https://prove2.me/submissions/422a0cf9-25a4-4067-910d-2339b0a58dcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydiscStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeChartBoundsOfSchurLemW
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
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
theorem _root_.solution {R : Type*} [CommSemiring R] {m : Type*} [Fintype m] (c : R) (A : Matrix m m R)
    (x : m → R) : (c • A) *ᵥ x = c • (A *ᵥ x) := by
  ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
end GlobalTheory.HodgeChartRow
