-- Prove2me | solution 1 for GlobalTheory.AdicCompleteFinite.isPrecomplete_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:24.045809+00:00
-- url     : https://prove2.me/submissions/f853cac3-a83b-47bf-95c6-76d0b4a896cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsAdicCompleteOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.AdicCompleteFinite
namespace GlobalTheory.AdicCompleteFinite
theorem _root_.solution {S : Type} [CommRing S] {I J : Ideal S} (hIJ : I ≤ J) {k : ℕ}
    (hk : J ^ k ≤ I) [h : IsPrecomplete I S] : IsPrecomplete J S := by
  have hk' : J ^ (k + 1) ≤ I := (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk
  refine ⟨fun f hf => ?_⟩
  have hg : ∀ {m n : ℕ}, m ≤ n →
      f ((k + 1) * m) ≡ f ((k + 1) * n) [SMOD (I ^ m • ⊤ : Submodule S S)] := by
    intro m n hmn
    refine (hf (Nat.mul_le_mul_left (k + 1) hmn)).mono ?_
    refine Submodule.smul_mono_left ?_
    rw [pow_mul]
    exact Ideal.pow_right_mono hk' m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec h (f := fun n => f ((k + 1) * n)) hg
  refine ⟨L, fun n => ?_⟩
  refine (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos k))).trans ?_
  exact (hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n))
end GlobalTheory.AdicCompleteFinite
