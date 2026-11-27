-- Prove2me | solution 1 for GlobalTheory.isClosed_coordDivisor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:32.050449+00:00
-- url     : https://prove2.me/submissions/981ce4cc-d893-48f3-bba4-7661dc3dc861

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_mem_coordDivisor_iff_prod_eq_zero

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
theorem _root_.solution [TopologicalSpace X] (S : Finset κ) {w : X → κ → ℂ}
    (hw : ∀ j ∈ S, Continuous fun x => w x j) : IsClosed (coordDivisor S w) := by
  have : coordDivisor S w = {x | ∏ j ∈ S, w x j = 0} :=
    Set.ext fun _ => mem_coordDivisor_iff_prod_eq_zero
  rw [this]
  exact isClosed_eq (continuous_finset_prod S hw) continuous_const
end GlobalTheory
