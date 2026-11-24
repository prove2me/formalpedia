-- Prove2me | solution 1 for GlobalTheory.finite_involution_fixed_unit_isNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:17.318802+00:00
-- url     : https://prove2.me/submissions/643ec023-c094-4715-9995-b7d2e6b4cf4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteInvolutionFixedUnitEqMulConj
import Theorems.Thm_GlobalTheory_finite_involution_hilbert90

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
theorem _root_.solution :
    ∀ (S : Type) [CommRing S] [Finite S] (c : S →+* S), (∀ x, c (c x) = x) →
      (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro S _ _ c hc hω u hcu hu
  obtain ⟨ω, hω⟩ := hω
  let cu : Sˣ →* Sˣ := Units.map (c : S →* S)
  have hcuv : ∀ x : Sˣ, ((cu x : Sˣ) : S) = c x := fun x => rfl
  have hcc : ∀ x : Sˣ, cu (cu x) = x := fun x => Units.ext (by rw [hcuv, hcuv, hc])
  let N : Sˣ →* Sˣ := MonoidHom.id Sˣ * cu
  let ψ : Sˣ →* Sˣ := MonoidHom.id Sˣ / cu
  have hN : ∀ x, N x = x * cu x := fun x => rfl
  have hψ : ∀ x, ψ x = x / cu x := fun x => MonoidHom.div_apply _ _ x
  have hker : N.ker ≤ ψ.range := by
    intro y hy
    rw [MonoidHom.mem_ker, hN] at hy
    have hy' : (y : S) * c y = 1 := by
      have := congrArg Units.val hy
      rwa [Units.val_mul, hcuv, Units.val_one] at this
    obtain ⟨x, hxu, hx⟩ := finite_involution_hilbert90 c hc ω hω y hy'
    refine ⟨hxu.unit, ?_⟩
    rw [hψ, div_eq_iff_eq_mul]
    exact Units.ext (by rw [Units.val_mul, hcuv, IsUnit.unit_spec]; exact hx)
  have hrange : N.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hψ, div_eq_one, hN, map_mul, hcc, mul_comm]
  have hcard : Nat.card ψ.ker ≤ Nat.card N.range := by
    have e1 := N.ker.card_mul_index
    have e2 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker] at e1 e2
    have hle : Nat.card N.ker ≤ Nat.card ψ.range := Subgroup.card_le_of_le hker
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    have h3 : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card N.range * Nat.card ψ.range := by
      rw [e2, ← e1, mul_comm (Nat.card N.range)]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have heq : N.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hrange hcard
  have hmem : hu.unit ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ, div_eq_one]
    exact Units.ext (by rw [hcuv, IsUnit.unit_spec, hcu])
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  have := congrArg Units.val hx
  rwa [hN, Units.val_mul, hcuv, IsUnit.unit_spec] at this
end GlobalTheory
