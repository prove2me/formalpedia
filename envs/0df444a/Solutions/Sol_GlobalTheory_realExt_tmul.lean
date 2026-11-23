-- Prove2me | solution 1 for GlobalTheory.realExt_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:57.888202+00:00
-- url     : https://prove2.me/submissions/0c82dc07-b6ea-4f23-9a74-d902d77f1a3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution (Q : QuadraticMap ℤ X ℝ) (s : ℝ) (x : X) :
    realExt Q (s ⊗ₜ x) = s * s * Q x := by
  simp only [realExt, QuadraticMap.smul_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    realExtBilin_tmul, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, smul_eq_mul,
    two_smul]
  ring
end GlobalTheory
