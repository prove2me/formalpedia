-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.exists_mem_pow_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:37.018184+00:00
-- url     : https://prove2.me/submissions/cba13b89-a07e-490c-94d4-488d4833f939

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}
omit [IsLocalRing S]
namespace GlobalTheory.CoeffSubring
theorem _root_.solution [IsDomain S] [IsNoetherianRing S] (I : Ideal S) {r : S}
    (hr : r ≠ 0) : ∃ c : ℕ, ∀ (n : ℕ) (x : S), r * x ∈ I ^ (n + c) → x ∈ I ^ n := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (M := S) (Ideal.span {r})
  refine ⟨c, fun n x hx => ?_⟩
  have h := hc (n + c) (Nat.le_add_left _ _)
  have hm : r * x ∈ I ^ (n + c) • (⊤ : Submodule S S) ⊓ Ideal.span {r} :=
    ⟨by rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hx,
      Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r)⟩
  rw [h, Nat.add_sub_cancel] at hm
  have hm' : r * x ∈ I ^ n * Ideal.span {r} := Submodule.smul_mono le_rfl inf_le_right hm
  obtain ⟨z, hz, hzx⟩ := Ideal.mem_mul_span_singleton.1 hm'
  rw [mul_comm] at hzx
  rwa [← mul_left_cancel₀ hr hzx]
end GlobalTheory.CoeffSubring
