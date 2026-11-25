-- Prove2me | solution 1 for GlobalTheory.IsLogBoundedScalar.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:52.806814+00:00
-- url     : https://prove2.me/submissions/8fa792dd-8bc2-4589-8aa5-262b747f9436

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
theorem _root_.solution (hg : IsLogBoundedScalar S w U g) (k : ℕ) :
    IsLogBoundedScalar S w U fun x => g x ^ k :=
  (hg.rpow k).congr fun _ _ _ => (Real.rpow_natCast _ _).symm
end GlobalTheory.IsLogBoundedScalar
