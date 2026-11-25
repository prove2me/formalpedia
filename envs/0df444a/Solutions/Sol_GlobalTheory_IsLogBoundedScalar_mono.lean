-- Prove2me | solution 1 for GlobalTheory.IsLogBoundedScalar.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:52.426258+00:00
-- url     : https://prove2.me/submissions/dd9f5e50-685b-4dac-824d-db22e7b8bbe2

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
variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}
open GlobalTheory.IsLogBoundedScalar
namespace GlobalTheory.IsLogBoundedScalar
theorem _root_.solution (hg : IsLogBoundedScalar S w U g) {V : Set X} (hV : V ⊆ U) :
    IsLogBoundedScalar S w V g :=
  fun K hK => hg K (hK.trans hV)
end GlobalTheory.IsLogBoundedScalar
