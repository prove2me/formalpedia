-- Prove2me | solution 1 for GlobalTheory.krull_inter_ideal_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:26.2536+00:00
-- url     : https://prove2.me/submissions/3a2b058c-8c5e-4f1b-b967-38167ada6f5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullIntersectionIdealLocalForm

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
theorem _root_.solution (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B)
    (h : ∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) : ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  set N : Submodule B (B ⧸ a') := Submodule.map (Submodule.mkQ a') a with hN
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  have hle : N ≤ I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h k hx)
    have h1 : Submodule.mkQ a' (y + z) = z • Submodule.mkQ a' 1 := by
      have hy0 : Submodule.mkQ a' y = 0 := by
        rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero a').2 hy
      rw [map_add, hy0, zero_add, ← map_smul, smul_eq_mul, mul_one]
    rw [h1]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  have hNI : N ≤ I • N := by
    have e1 : N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := (inf_eq_right.2 hle).symm
    calc N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := e1
      _ = I ^ (k + 1 - k) • (I ^ k • ⊤ ⊓ N) := hk (k + 1) (Nat.le_succ k)
      _ ≤ I • N := by
        rw [Nat.add_sub_cancel_left, pow_one]
        exact Submodule.smul_mono le_rfl inf_le_right
  have hfg : N.FG := IsNoetherian.noetherian N
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N hfg hNI
  refine ⟨r, hr, fun x hx => ?_⟩
  have hx' := hrN (Submodule.mkQ a' x) ⟨x, hx, rfl⟩
  rw [← map_smul, smul_eq_mul] at hx'
  have : Submodule.mkQ a' ((1 - r) * x) = 0 := by
    rw [sub_mul, one_mul, map_sub, hx', sub_self]
  rw [Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero a').1 this
end GlobalTheory
