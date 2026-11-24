-- Prove2me | solution 1 for GlobalTheory.algHom_eq_mul_pow_of_eq_localizationAway
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:12.430179+00:00
-- url     : https://prove2.me/submissions/298e16b4-13d8-40a5-9667-a4f8977ba5e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  intro R' A S _ _ _ _ _ _ χ₁ χ₂ g h
  have key : ∀ x, ∃ n : ℕ, g ^ n * χ₁ x = g ^ n * χ₂ x := by
    intro x
    obtain ⟨⟨c, hc⟩, hcx⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).1 (h x)
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hc
    exact ⟨n, hcx⟩
  choose n hn using key
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' A).FG)
  refine ⟨∑ x ∈ s, n x, fun x => ?_⟩
  set N := ∑ x ∈ s, n x
  have hx : x ∈ Algebra.adjoin R' (s : Set A) := by rw [hs]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hxs =>
    have hle : n x ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxs
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_assoc, hn x]
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, mul_add, mul_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul]
    calc g ^ N * (χ₁ x * χ₁ y) = χ₁ x * (g ^ N * χ₁ y) := by ring
      _ = χ₁ x * (g ^ N * χ₂ y) := by rw [hy]
      _ = (g ^ N * χ₁ x) * χ₂ y := by ring
      _ = (g ^ N * χ₂ x) * χ₂ y := by rw [hx]
      _ = g ^ N * (χ₂ x * χ₂ y) := by ring
end GlobalTheory
