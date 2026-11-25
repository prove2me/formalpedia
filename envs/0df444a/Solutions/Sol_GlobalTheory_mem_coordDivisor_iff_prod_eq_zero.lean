-- Prove2me | solution 1 for GlobalTheory.mem_coordDivisor_iff_prod_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:18.656706+00:00
-- url     : https://prove2.me/submissions/f2c842b8-53fd-455a-b72b-463394541c21

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
    x ∈ coordDivisor S w ↔ ∏ j ∈ S, w x j = 0 := by
  simp [coordDivisor, Finset.prod_eq_zero_iff]
end GlobalTheory
