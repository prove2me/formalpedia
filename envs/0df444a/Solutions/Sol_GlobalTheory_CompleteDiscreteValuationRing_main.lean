-- Prove2me | solution 1 for GlobalTheory.CompleteDiscreteValuationRing.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:16.624672+00:00
-- url     : https://prove2.me/submissions/08680b0d-7546-40b5-81eb-869d73defa8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
import Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_exists_complete_dvr
import Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_exists_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing
namespace GlobalTheory.CompleteDiscreteValuationRing
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V)
    (hϖ : Irreducible ϖ) (ψ : R →+* V) (hψ : IsLocalHom ψ) (I : Type) [Finite I] (a : I → R)
    (k : I → ℕ) (h : ∀ i, Associated (ψ (a i)) (ϖ ^ k i)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W)
      (ψ' : R →+* W) (m : ℕ) (m' : ℕ) (k' : I → ℕ),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧
        IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧
        ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by
  obtain ⟨A, _, _, _, g, t, hg, ht0, ht, hm, ha⟩ := exists_chart R V ϖ hϖ ψ hψ I a k h
  obtain ⟨W, _, _, hW, f, hc, hf, hft⟩ := exists_complete_dvr A t ht0 ht
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    ((map_ne_zero_iff f hf).2 ht0) hp
  refine ⟨W, inferInstance, inferInstance, hW, p, f.comp g, 1, n, fun i => n * k i, hc, hp,
    hf.comp hg, ⟨fun r hr => ?_⟩, le_rfl, ?_, fun i => ⟨?_, one_mul _⟩⟩
  · by_contra hnu
    exact hft (isUnit_of_dvd_unit (map_dvd f (hm r hnu)) hr)
  · rw [Nat.one_le_iff_ne_zero]
    rintro rfl
    rw [pow_zero, associated_one_iff_isUnit] at hn
    exact hft hn
  · have h1 := (ha i).map f
    rw [map_pow] at h1
    rw [pow_mul]
    exact h1.trans hn.pow_pow
end GlobalTheory.CompleteDiscreteValuationRing
