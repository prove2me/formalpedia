-- Prove2me | solution 1 for GlobalTheory.K5.Basic.zeta_pow_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:48.545844+00:00
-- url     : https://prove2.me/submissions/853222d2-42e7-4144-b03c-f5e6b4b39f2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution (T : Tower p Ω) (k a b : ℕ) :
    T.ζ k ^ a = T.ζ k ^ b ↔ a ≡ b [MOD p ^ k] := by
  rw [(T.prim k).eq_orderOf]
  exact (T.prim k).isOfFinOrder (pow_ne_zero _ hp.out.ne_zero) |>.pow_eq_pow_iff_modEq
end GlobalTheory.K5.Basic
