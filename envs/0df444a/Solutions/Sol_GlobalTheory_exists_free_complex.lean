-- Prove2me | solution 1 for GlobalTheory.exists_free_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:20.745073+00:00
-- url     : https://prove2.me/submissions/5ee1a07c-7dfb-41e3-ab60-1bcf3e240aa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Theorems.Thm_GlobalTheory_exists_free_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory TensorProduct
universe u v w
open GlobalTheory
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
namespace GlobalTheory
theorem _root_.solution (n : ℕ) : ∀ (C : ℕ → ModuleCat.{v} R)
    (d : ∀ p, C p →ₗ[R] C (p + 1)) (B : Submodule R (C 0))
    (_ : ∀ p, n ≤ p → Subsingleton (C p))
    (_ : Module.Finite R (LinearMap.ker (d 0) ⧸ B.comap (LinearMap.ker (d 0)).subtype))
    (_ : ∀ p, Module.Finite R (LinearMap.ker (d (p + 1)) ⧸
      (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)),
    ∃ (m : ℕ → ℕ) (δ : ∀ p, (Fin (m p) → R) →ₗ[R] (Fin (m (p + 1)) → R))
      (φ : ∀ p, (Fin (m p) → R) →ₗ[R] C p),
      (∀ p, n ≤ p → m p = 0) ∧ (∀ p x, δ (p + 1) (δ p x) = 0) ∧
      (∀ p x, d p (φ p x) = φ (p + 1) (δ p x)) ∧
      (∀ c k, d 0 c = φ 1 k → δ 1 k = 0 → ∃ x, c - φ 0 x ∈ B ∧ δ 0 x = k) ∧
      ∀ p c k, d (p + 1) c = φ (p + 2) k → δ (p + 2) k = 0 →
        ∃ c' k', d p c' + φ (p + 1) k' = c ∧ δ (p + 1) k' = k := by
  induction n with
  | zero =>
    intro C d B hC _ _
    have hC' : ∀ p, Subsingleton (C p) := fun p => hC p p.zero_le
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => Subsingleton.elim _ _, fun c k _ _ => ⟨0, ?_, Subsingleton.elim _ _⟩,
      fun p c k _ _ => ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    rw [Subsingleton.elim (c - _) 0]
    exact B.zero_mem
  | succ n ih =>
    intro C d B hC hB hH
    obtain ⟨m, δ, φ, hm, hδ, hφ, h0, h1⟩ := ih (fun p => C (p + 1)) (fun p => d (p + 1))
      (LinearMap.range (d 0)) (fun p hp => hC _ (by omega)) (hH 0) (fun p => hH (p + 1))
    obtain ⟨a, φ₀, δ₀, e1, e2, e3⟩ := exists_free_step (d 0) (φ 0) (δ 0) B
    refine ⟨fun p => Nat.casesOn p a m,
      fun p => match p with | 0 => δ₀ | p + 1 => δ p,
      fun p => match p with | 0 => φ₀ | p + 1 => φ p, ?_, ?_, ?_, e3, ?_⟩
    · rintro (_ | p) hp
      · omega
      · exact hm p (by omega)
    · rintro (_ | p)
      · exact e2
      · exact hδ p
    · rintro (_ | p)
      · exact e1
      · exact hφ p
    · rintro (_ | p)
      · intro c k h h'
        obtain ⟨x, ⟨c', hc'⟩, hx⟩ := h0 c k h h'
        exact ⟨c', x, eq_sub_iff_add_eq.1 hc', hx⟩
      · exact h1 p
end GlobalTheory
