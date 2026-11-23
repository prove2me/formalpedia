-- Prove2me | solution 1 for GlobalTheory.CubeLift.pow_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:41.200793+00:00
-- url     : https://prove2.me/submissions/41fc5e43-30cd-42b7-9c84-a575049316ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution (J : Ideal A) (k : ℕ) : J ^ (k + 1) * J ^ (k + 1) ≤ J ^ (k + 1 + 1) := by
  rw [← pow_add]; exact Ideal.pow_le_pow_right (by omega)
end GlobalTheory.CubeLift
