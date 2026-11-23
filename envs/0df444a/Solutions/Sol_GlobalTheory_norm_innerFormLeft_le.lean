-- Prove2me | solution 1 for GlobalTheory.norm_innerFormLeft_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:04.678995+00:00
-- url     : https://prove2.me/submissions/995a3635-0f2a-4ee8-9c83-251f8623541d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
import Theorems.Thm_GlobalTheory_innerFormLeft_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.innerFormLeft_apply

set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution (u v : V) : ‖innerFormLeft V u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [innerFormLeft_apply, mul_comm]; exact norm_inner_le_norm v u
end GlobalTheory
