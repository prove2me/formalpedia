-- Prove2me | solution 1 for GlobalTheory.ShiftMemPowOfMulMemPow.exists_shift_mem_pow_of_mul_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:47:06.552173+00:00
-- url     : https://prove2.me/submissions/3be4c328-6fb5-4541-b931-e7f43720717d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsShiftMemPowOfMulMemPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ShiftMemPowOfMulMemPow
namespace GlobalTheory.ShiftMemPowOfMulMemPow
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (I : Ideal R) {r : R} (hr : r ≠ 0) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : R), r * x ∈ I ^ (n + c) → x ∈ I ^ n := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (Ideal.span {r} : Submodule R R)
  refine ⟨k, fun n x hx => ?_⟩
  have h1 : r * x ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ Ideal.span {r} := by
    refine Submodule.mem_inf.mpr ⟨?_, Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hx
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : r * x ∈ I ^ n * Ideal.span {r} := Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨z, hz, hzr⟩ := Ideal.mem_mul_span_singleton.mp h2
  have hzx : z = x := mul_right_cancel₀ hr (by rw [hzr, mul_comm])
  exact hzx ▸ hz
end GlobalTheory.ShiftMemPowOfMulMemPow
