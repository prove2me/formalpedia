-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.det_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:02.885008+00:00
-- url     : https://prove2.me/submissions/8c76891d-5185-484d-a5b4-1bb39d09b670

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_IsLogBounded_re_det_zpow
import Theorems.Thm_GlobalTheory_isLogBounded_of_unique_iff

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
namespace GlobalTheory.IsLogBounded
theorem _root_.solution (hG : IsLogBounded S w U G) (k : ℤ) (p : Type*) [Unique p] [DecidableEq p] :
    IsLogBounded S w U fun x => Matrix.of fun _ _ : p => (G x).det ^ k := by
  refine (isLogBounded_of_unique_iff.2 (hG.re_det_zpow k)).congr fun x hx hB => ?_
  have h : ((G x).det.re : ℂ) = (G x).det :=
    Complex.ext rfl (Complex.pos_iff.1 (hG.posDef hx hB).det_pos).2
  rw [Complex.ofReal_zpow, h]
end GlobalTheory.IsLogBounded
