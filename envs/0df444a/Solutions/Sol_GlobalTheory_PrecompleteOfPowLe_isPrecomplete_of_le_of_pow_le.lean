-- Prove2me | solution 1 for GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:44.985475+00:00
-- url     : https://prove2.me/submissions/d7f27cb7-db19-465d-94c7-ecd1938dae6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPrecompleteOfLeOfPowLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrecompleteOfPowLe
universe u
namespace GlobalTheory.PrecompleteOfPowLe
theorem _root_.solution {A : Type u} [CommRing A] {I J : Ideal A} (hJI : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [hJ : IsPrecomplete J A] : IsPrecomplete I A := by
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m =>
    calc I ^ ((e + 1) * m) ≤ I ^ (e * m) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right m (Nat.le_succ e))
      _ = (I ^ e) ^ m := pow_mul I e m
      _ ≤ J ^ m := Ideal.pow_right_mono he m
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := hJ.prec (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left (e + 1) hmn)).mono (Submodule.smul_mono_left (h1 m)))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ (e + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos e)
  exact (hf hn).trans ((hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)))
end GlobalTheory.PrecompleteOfPowLe
