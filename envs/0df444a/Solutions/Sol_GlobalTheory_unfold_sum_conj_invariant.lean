-- Prove2me | solution 1 for GlobalTheory.unfold_sum_conj_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:54.61485+00:00
-- url     : https://prove2.me/submissions/6050ddbe-b342-40fd-9c06-83c8ff00da3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldSumInvariantLeviConj

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
theorem _root_.solution : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ F : P → ℂ, (∀ k ∈ KP, ∀ x, F (k⁻¹ * x * k) = F x) → ∀ k ∈ KM, ∀ y : P, (∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * ((s k)⁻¹ * y * s k) * u (Quotient.out x))) = ∑ᶠ x : N ⧸ L, F ((u (Quotient.out x))⁻¹ * y * u (Quotient.out x)) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK hL F hF k hk y
  set c := s k with hc_def
  have hc : c ∈ KP := hsK k hk
  have hπu : ∀ X, π (u X) = 1 := fun X => (hker _).2 ⟨X, rfl⟩
  have hex : ∀ (d : P), ∀ X, ∃ Y, u Y = d * u X * d⁻¹ := by
    intro d X
    exact (hker _).1 (by simp [map_mul, map_inv, hπu])
  choose φ hφ using hex c
  choose ψ hψ using hex c⁻¹
  have h1 : ∀ X, φ (ψ X) = X := fun X => hu (by rw [hφ, hψ]; group)
  have h2 : ∀ X, ψ (φ X) = X := fun X => hu (by rw [hψ, hφ]; group)
  have hconj : ∀ z, c * z * c⁻¹ ∈ KP ↔ z ∈ KP := by
    intro z
    constructor
    · intro h
      have := KP.mul_mem (KP.mul_mem (KP.inv_mem hc) h) hc
      simpa [mul_assoc] using this
    · intro h
      exact KP.mul_mem (KP.mul_mem hc h) (KP.inv_mem hc)
  let eN : N ≃ N := ⟨φ, ψ, h2, h1⟩
  let e : N ⧸ L ≃ N ⧸ L := Quotient.congr eN (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← hL, ← hL]
    simp only [eN, Equiv.coe_fn_mk, map_mul, map_inv, hφ]
    rw [← hconj]
    constructor <;> intro h <;> convert h using 1 <;> group)
  conv_rhs => rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro x
  set X := Quotient.out x with hX
  have hex' : e x = (QuotientGroup.mk (φ X) : N ⧸ L) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  set Z := Quotient.out (e x) with hZ
  have hZL : Z⁻¹ * φ X ∈ L := by
    apply QuotientGroup.eq.mp
    rw [← hex']
    exact Quotient.out_eq _
  have hw : u (Z⁻¹ * φ X) ∈ KP := (hL _).2 hZL
  calc F ((u X)⁻¹ * (c⁻¹ * y * c) * u X) = F (c⁻¹ * ((u (φ X))⁻¹ * y * u (φ X)) * c) := by
        congr 1; rw [hφ]; group
    _ = F ((u (φ X))⁻¹ * y * u (φ X)) := hF c hc _
    _ = F ((u Z * u (Z⁻¹ * φ X))⁻¹ * y * (u Z * u (Z⁻¹ * φ X))) := by
        rw [← map_mul, mul_inv_cancel_left]
    _ = F ((u (Z⁻¹ * φ X))⁻¹ * ((u Z)⁻¹ * y * u Z) * u (Z⁻¹ * φ X)) := by
        congr 1; group
    _ = F ((u Z)⁻¹ * y * u Z) := hF _ hw _
end GlobalTheory
