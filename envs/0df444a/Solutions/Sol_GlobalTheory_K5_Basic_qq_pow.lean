-- Prove2me | solution 1 for GlobalTheory.K5.Basic.qq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:49.22246+00:00
-- url     : https://prove2.me/submissions/b47f249f-3209-41ef-8bb4-ff180e6dc1dc

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
theorem _root_.solution (T : Tower p Ω) (n : ℕ) : T.qq n ^ p ^ n = algebraMap (O0 p) Ω (qO p) := by
  induction n with
  | zero => simp [T.q0]
  | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]
end GlobalTheory.K5.Basic
