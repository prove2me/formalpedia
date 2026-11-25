-- Prove2me | solution 1 for GlobalTheory.IsLogBoundedScalar.rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:20.442684+00:00
-- url     : https://prove2.me/submissions/d3980cee-3414-41b5-966a-e9fb3dba992a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_isLogBoundedScalar_iff_abs_log_le

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
theorem _root_.solution (hg : IsLogBoundedScalar S w U g) (t : ℝ) :
    IsLogBoundedScalar S w U fun x => g x ^ t := by
  refine isLogBoundedScalar_iff_abs_log_le.2
    ⟨fun x hx hB => Real.rpow_pos_of_pos (hg.pos hx hB) t, fun K hKU hK => ?_⟩
  obtain ⟨C, N, h⟩ := (isLogBoundedScalar_iff_abs_log_le.1 hg).2 K hKU hK
  refine ⟨⌈|t|⌉₊ * C, ⌈|t|⌉₊ * N, fun x hx hB => ?_⟩
  rw [Real.log_rpow (hg.pos (hKU hx) hB), abs_mul, Nat.cast_mul, mul_assoc, ← mul_add]
  exact mul_le_mul (Nat.le_ceil _) (h x hx hB) (abs_nonneg _) (Nat.cast_nonneg _)
end GlobalTheory.IsLogBoundedScalar
