-- Prove2me | solution 1 for GlobalTheory.IsLogBoundedScalar.of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:00.243175+00:00
-- url     : https://prove2.me/submissions/5ca1fa1e-addb-40e2-90a1-54d207fb55d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_IsLogBoundedScalar_rpow

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
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) (h0 : ∀ x ∈ U, x ∉ coordDivisor S w → 0 ≤ g x)
    (hg : IsLogBoundedScalar S w U fun x => g x ^ k) : IsLogBoundedScalar S w U g :=
  (hg.rpow (k : ℝ)⁻¹).congr fun x hx hB => (Real.pow_rpow_inv_natCast (h0 x hx hB) hk).symm
end GlobalTheory.IsLogBoundedScalar
