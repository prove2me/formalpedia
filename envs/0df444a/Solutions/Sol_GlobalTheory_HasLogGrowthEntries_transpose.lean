-- Prove2me | solution 1 for GlobalTheory.HasLogGrowthEntries.transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:52:34.121654+00:00
-- url     : https://prove2.me/submissions/232b91e3-909a-49df-afab-3753988416f1

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
theorem _root_.solution {A : X → Matrix m n ℂ} (hA : HasLogGrowthEntries S w U A) :
    HasLogGrowthEntries S w U fun x => (A x)ᵀ :=
  fun i j => hA j i
end GlobalTheory.HasLogGrowthEntries
