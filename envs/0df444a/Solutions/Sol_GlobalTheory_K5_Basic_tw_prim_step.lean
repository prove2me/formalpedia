-- Prove2me | solution 1 for GlobalTheory.K5.Basic.tw_prim_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:18.406685+00:00
-- url     : https://prove2.me/submissions/0e23c130-ce41-4f1c-846a-a8276d484c35

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
theorem _root_.solution {Ω : Type*} [Field Ω] {ζ z : Ω} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) (hz : z ^ p = ζ) :
    IsPrimitiveRoot z (p ^ (n + 2)) := by
  have h1 : z ^ (p ^ (n + 2)) = 1 := by
    rw [pow_succ' p (n + 1), pow_mul, hz, hζ.pow_eq_one]
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one h1)
  rcases Nat.lt_or_ge k (n + 2) with hlt | hge
  · exfalso
    have h2 : z ^ (p ^ (n + 1)) = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.1
      rw [hko]
      exact pow_dvd_pow p (by omega)
    have h3 : ζ ^ (p ^ n) = 1 := by
      rw [← hz, ← pow_mul, ← pow_succ']
      exact h2
    have h4 := hζ.dvd_of_pow_eq_one _ h3
    rw [Nat.pow_dvd_pow_iff_le_right hp.out.one_lt] at h4
    omega
  · have hk2 : k = n + 2 := le_antisymm hk hge
    rw [← hk2, ← hko]
    exact IsPrimitiveRoot.orderOf z
end GlobalTheory.K5.Basic
