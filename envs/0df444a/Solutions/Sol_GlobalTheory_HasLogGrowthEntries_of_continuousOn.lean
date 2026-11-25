-- Prove2me | solution 1 for GlobalTheory.HasLogGrowthEntries.of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:36.206943+00:00
-- url     : https://prove2.me/submissions/fb904c8d-e0f6-408f-883b-d4301ebe98f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ X l m n : Type*} [TopologicalSpace X]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
open GlobalTheory.HasLogGrowthEntries
namespace GlobalTheory.HasLogGrowthEntries
theorem _root_.solution {A : X → Matrix m n ℂ} (hA : ContinuousOn A U) :
    HasLogGrowthEntries S w U A :=
  fun i j => .of_continuousOn ((continuous_id.matrix_elem i j).comp_continuousOn hA)
end GlobalTheory.HasLogGrowthEntries
