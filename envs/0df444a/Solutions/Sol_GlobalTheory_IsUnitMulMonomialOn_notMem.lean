-- Prove2me | solution 1 for GlobalTheory.IsUnitMulMonomialOn.notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:21.204897+00:00
-- url     : https://prove2.me/submissions/ec5058d3-6512-4f98-ba6a-e8dc7e972984

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_notMem_coordDivisor

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
variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
open GlobalTheory.IsUnitMulMonomialOn
variable {S' : Finset κ'} {w' : X' → κ' → ℂ} {U' : Set X'} {v : X' → κ → ℂ}
namespace GlobalTheory.IsUnitMulMonomialOn
theorem _root_.solution (h : IsUnitMulMonomialOn S v S' w' U') {x : X'} (hx : x ∈ U')
    (hB : x ∉ coordDivisor S' w') : x ∉ coordDivisor S v := by
  rw [notMem_coordDivisor] at hB ⊢
  intro j hj
  obtain ⟨u, m, -, hu⟩ := h j hj
  rw [(hu x hx).2]
  exact mul_ne_zero (hu x hx).1 (Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ (hB i hi))
end GlobalTheory.IsUnitMulMonomialOn
