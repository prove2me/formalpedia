-- Prove2me | solution 1 for GlobalTheory.isLogBounded_of_unique_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:19.90497+00:00
-- url     : https://prove2.me/submissions/734f37d2-ea19-4fd3-a15a-125e9ac8742c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_IsLogBounded_smul_one
import Theorems.Thm_GlobalTheory_IsLogBounded_re_apply_self

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
omit [Fintype n]
namespace GlobalTheory
theorem _root_.solution [Unique n] {g : X → ℝ} :
    (IsLogBounded S w U fun x => Matrix.of fun _ _ : n => (g x : ℂ)) ↔
      IsLogBoundedScalar S w U g := by
  refine ⟨fun h => by simpa using h.re_apply_self default, fun h => ?_⟩
  refine (IsLogBounded.smul_one h).congr fun x _ _ => ?_
  ext i j
  rw [Subsingleton.elim i j]
  simp
end GlobalTheory
