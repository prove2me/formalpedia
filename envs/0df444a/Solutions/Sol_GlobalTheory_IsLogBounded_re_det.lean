-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.re_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:50.751437+00:00
-- url     : https://prove2.me/submissions/b8bf1107-430b-4c24-b14d-3288108f1a61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_re_det_pos_of_posDef


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
theorem _root_.solution (hG : IsLogBounded S w U G) : IsLogBoundedScalar S w U fun x => (G x).det.re := by
  refine isLogBoundedScalar_iff.2 ⟨fun x hx hB => re_det_pos_of_posDef (hG.posDef hx hB),
    hG.hasLogGrowthEntries.det.of_norm_le fun x _ _ => Complex.abs_re_le_norm _,
    hG.hasLogGrowthEntries_inv.det.of_norm_le fun x hx hB => ?_⟩
  have h := Complex.re_eq_norm.2 (hG.posDef hx hB).det_pos.le
  rw [det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, norm_inv, h, norm_norm]
end GlobalTheory.IsLogBounded
