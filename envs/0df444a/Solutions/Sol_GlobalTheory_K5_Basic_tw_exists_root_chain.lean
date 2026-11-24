-- Prove2me | solution 1 for GlobalTheory.K5.Basic.tw_exists_root_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:52.230825+00:00
-- url     : https://prove2.me/submissions/a530afa5-9033-4495-8056-c0bc2495ec9f

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
theorem _root_.solution {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (a : Ω) :
    ∃ f : ℕ → Ω, f 0 = a ∧ ∀ n, f (n + 1) ^ p = f n := by
  choose r hr using fun x : Ω => IsAlgClosed.exists_pow_nat_eq x hp.out.pos
  refine ⟨fun n => r^[n] a, rfl, fun n => ?_⟩
  show r^[n + 1] a ^ p = r^[n] a
  rw [Function.iterate_succ_apply', hr]
end GlobalTheory.K5.Basic
