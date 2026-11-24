-- Prove2me | solution 1 for GlobalTheory.TangentRigid.Top.xder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:28.223102+00:00
-- url     : https://prove2.me/submissions/90b23edc-f358-45fc-82e1-4f01d8c093c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TangentRigid
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}
namespace GlobalTheory.TangentRigid
namespace Top
theorem _root_.solution (hp : Top p d c) : Top (X * derivative p) d (d * c) := by
  have key : ∀ j : ℕ, (X * derivative p).coeff j = j * p.coeff j := by
    intro j
    cases j with
    | zero => simp
    | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  refine ⟨natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_, by rw [key, hp.2]⟩
  rw [key, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt hj), mul_zero]
end Top
end GlobalTheory.TangentRigid
