-- Prove2me | solution 1 for MazurTransfer.cyclic_quotient_action_eq_character_smul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T23:29:07.178326+00:00
-- url     : https://prove2.me/submissions/9a49fdbb-2465-4cfc-a178-7577f8e5d9cd

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a vector fixed by the kernel of a cyclic quotient has the
specified scalar character if a lift of its generator acts by that scalar.
Named downstream consumer: actual arithmetic13 norm-kernel characters.
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic

noncomputable section
universe u v w x
namespace MazurTransfer.CyclicQuotientScalarActionProofHelpers20261018
variable {k : Type u} [Field k] {G : Type v} [Group G] {H : Type w} [Group H]
variable {V : Type x} [AddCommGroup V] [Module k V]

theorem pow_apply_of_scalar (ρ : Representation k G V) (g : G) (c : k) (v : V)
    (hv : ρ g v = c • v) (n : ℕ) : ρ (g ^ n) v = c ^ n • v := by
  induction n with
  | zero =>
    rw [pow_zero, map_one, pow_zero, one_smul]
    rfl
  | succ n ih =>
    rw [pow_succ, map_mul]
    change ρ (g ^ n) (ρ g v) = _
    rw [hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem action_eq_character_smul
    (ρ : Representation k G V) (q : G →* H) (χ : H →* kˣ)
    (h : H) (hg : ∀ y : H, ∃ n : ℕ, y = h ^ n) (g : G) (hq : q g = h)
    (v : V) (hfix : ∀ s : G, q s = 1 → ρ s v = v)
    (hv : ρ g v = (χ h : k) • v) (s : G) :
    ρ s v = (χ (q s) : k) • v := by
  obtain ⟨n, hn⟩ := hg (q s)
  have he : q (g ^ n) = q s := by rw [map_pow, hq, ← hn]
  have hk : q ((g ^ n)⁻¹ * s) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have hf := congrArg (fun w : V => ρ (g ^ n) w) (hfix _ hk)
  have hm : ρ (g ^ n) (ρ ((g ^ n)⁻¹ * s) v) = ρ s v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [hm, pow_apply_of_scalar ρ g (χ h : k) v hv n] at hf
  rw [hn, map_pow, Units.val_pow_eq_pow_val]
  exact hf

end MazurTransfer.CyclicQuotientScalarActionProofHelpers20261018
variable {k : Type u} [Field k] {G : Type v} [Group G] {H : Type w} [Group H]
variable {V : Type x} [AddCommGroup V] [Module k V]

theorem solution
    (ρ : Representation k G V) (q : G →* H) (χ : H →* kˣ)
    (h : H) (hg : ∀ y : H, ∃ n : ℕ, y = h ^ n) (g : G) (hq : q g = h)
    (v : V) (hfix : ∀ s : G, q s = 1 → ρ s v = v)
    (hv : ρ g v = (χ h : k) • v) (s : G) :
    ρ s v = (χ (q s) : k) • v := by
  exact MazurTransfer.CyclicQuotientScalarActionProofHelpers20261018.action_eq_character_smul ρ q χ h hg g hq v hfix hv s
#print axioms solution
