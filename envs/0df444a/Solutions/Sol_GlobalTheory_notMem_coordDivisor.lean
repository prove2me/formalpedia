-- Prove2me | solution 1 for GlobalTheory.notMem_coordDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:55.69884+00:00
-- url     : https://prove2.me/submissions/5deeafad-2369-46e9-89f6-7f7b1eb35070

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
variable {κ X : Type*}
namespace GlobalTheory
theorem _root_.solution {S : Finset κ} {w : X → κ → ℂ} {x : X} :
    x ∉ coordDivisor S w ↔ ∀ j ∈ S, w x j ≠ 0 := by
  simp [coordDivisor]
end GlobalTheory
