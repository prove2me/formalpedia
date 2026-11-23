-- Prove2me | solution 1 for GlobalTheory.realExtBilin_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:32.244646+00:00
-- url     : https://prove2.me/submissions/68697b02-95f5-44d1-a095-65ec79c98282

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s t : ℝ) (x y : X) :
    realExtBilin B (s ⊗ₜ x) (t ⊗ₜ y) = s * t * B x y := by
  simp [realExtBilin, mul_assoc]
end GlobalTheory
