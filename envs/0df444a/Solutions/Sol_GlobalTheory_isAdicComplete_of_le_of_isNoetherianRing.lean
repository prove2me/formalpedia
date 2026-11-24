-- Prove2me | solution 1 for GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:30.840802+00:00
-- url     : https://prove2.me/submissions/cbc4181c-631d-4bbc-8f2f-41397c8f8de5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteOfLeOfIsNoetherianRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hIJ : I ≤ J) (hJ : IsAdicComplete J R) : IsAdicComplete I R := by
  have hle : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hH : IsHausdorff I R :=
    ⟨fun x hx => hJ.toIsHausdorff.haus x fun n => (hx n).mono (hle n)⟩
  have hP : IsPrecomplete I R := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hJ.toIsPrecomplete.prec (f := f) fun {m n} h => (hf h).mono (hle m)
    refine ⟨L, fun n => ?_⟩
    set N : Submodule R R := I ^ n • ⊤ with hN
    have hK : (⨅ m : ℕ, J ^ m • ⊤ : Submodule R (R ⧸ N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J (IsAdicComplete.le_jacobson_bot J)
    rw [SModEq.sub_mem, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot R, ← hK,
      Submodule.mem_iInf]
    intro m
    have h1 : f n - f (max n m) ∈ N := SModEq.sub_mem.1 (hf (le_max_left n m))
    have h2 : f (max n m) - L ∈ (J ^ m • ⊤ : Submodule R R) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right n m))
        (SModEq.sub_mem.1 (hL (max n m)))
    have h3 : N.mkQ (f (max n m) - L) ∈ (J ^ m • ⊤ : Submodule R (R ⧸ N)) := by
      have := Submodule.mem_map_of_mem (f := N.mkQ) h2
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have h4 : (Submodule.Quotient.mk (f n - L) : R ⧸ N) = N.mkQ (f (max n m) - L) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      convert h1 using 1
      ring
    rw [h4]
    exact h3
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }
end GlobalTheory
