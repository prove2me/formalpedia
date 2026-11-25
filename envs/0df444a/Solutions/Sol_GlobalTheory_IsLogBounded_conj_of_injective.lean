-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.conj_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:15:19.230856+00:00
-- url     : https://prove2.me/submissions/14c818f7-0723-43a1-be98-60242d2269c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_HasLogGrowthEntries_of_continuousOn
import Theorems.Thm_GlobalTheory_IsLogBounded_of_continuousOn
import Theorems.Thm_GlobalTheory_IsLogBounded_conj_of_isLogBounded

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
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]
open GlobalTheory.IsLogBounded
variable [Fintype m]
namespace GlobalTheory.IsLogBounded
theorem _root_.solution (hG : IsLogBounded S w U G) {A : X → Matrix n m ℂ}
    (hA : ContinuousOn A U) (hinj : ∀ x ∈ U, Function.Injective (A x).mulVec) :
    IsLogBounded S w U fun x => (A x)ᴴ * G x * A x :=
  hG.conj_of_isLogBounded (of_continuousOn
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).comp_continuousOn hA)
    fun x hx => PosDef.conjTranspose_mul_self _ (hinj x hx))
end GlobalTheory.IsLogBounded
