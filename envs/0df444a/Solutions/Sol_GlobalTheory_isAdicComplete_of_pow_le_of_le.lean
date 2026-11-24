-- Prove2me | solution 1 for GlobalTheory.isAdicComplete_of_pow_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:32.333641+00:00
-- url     : https://prove2.me/submissions/e97e0611-0323-451f-9cca-6449745fa1fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {I J : Ideal R} (hI : IsAdicComplete I M) {n : ℕ} (hJI : J ^ n ≤ I)
    (hIJ : I ≤ J) : IsAdicComplete J M := by
  have h1 : ∀ m : ℕ, (J ^ ((n + 1) * m) • ⊤ : Submodule R M) ≤ I ^ m • ⊤ := fun m => by
    apply Submodule.smul_mono_left
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hJI) m
  have h2 : ∀ m : ℕ, (I ^ m • ⊤ : Submodule R M) ≤ J ^ m • ⊤ := fun m =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ m)
  have hH : IsHausdorff J M := ⟨fun x hx =>
    hI.toIsHausdorff.haus x fun m => (hx ((n + 1) * m)).mono (h1 m)⟩
  have hP : IsPrecomplete J M := ⟨fun f hf => by
    obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec (f := fun m => f ((n + 1) * m))
      (fun {a b} hab => (hf (Nat.mul_le_mul_left (n + 1) hab)).mono (h1 a))
    refine ⟨L, fun k => ?_⟩
    exact (hf (Nat.le_mul_of_pos_left k (Nat.succ_pos n))).trans ((hL k).mono (h2 k))⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
end GlobalTheory
