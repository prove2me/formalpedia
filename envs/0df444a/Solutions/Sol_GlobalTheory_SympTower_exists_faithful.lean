-- Prove2me | solution 1 for GlobalTheory.SympTower.exists_faithful
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:38.001924+00:00
-- url     : https://prove2.me/submissions/db6eca5c-b4d2-4278-861f-39af3b22055b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower
namespace GlobalTheory.SympTower
theorem _root_.solution {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (ZMod n) V]
    [Finite V] (h : ∀ c : ZMod n, (∀ y : V, c • y = 0) → c = 0) :
    ∃ x : V, ∀ c : ZMod n, c • x = 0 → c = 0 := by
  obtain ⟨x, hx⟩ := AddMonoid.exists_addOrderOf_eq_exponent (G := V) AddMonoid.ExponentExists.of_finite
  refine ⟨x, fun c hc => h c fun y => ?_⟩
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul] at hc ⊢
  obtain ⟨m, hm⟩ := addOrderOf_dvd_of_nsmul_eq_zero hc
  rw [hm, hx, mul_nsmul, AddMonoid.exponent_nsmul_eq_zero, nsmul_zero]
end GlobalTheory.SympTower
