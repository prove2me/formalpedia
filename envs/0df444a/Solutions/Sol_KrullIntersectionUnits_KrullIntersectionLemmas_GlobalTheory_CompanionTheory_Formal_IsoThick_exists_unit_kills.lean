-- Prove2me | solution 1 for KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:15.670902+00:00
-- url     : https://prove2.me/submissions/ecd5cb01-824f-43cf-b2a9-fcd5b8044ac5

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Theorems.Thm_KrullIntersectionUnits_KrullIntersectionLemmas_exists_unit_kills_of_idempotent
import Theorems.Thm_KrullIntersectionUnits_KrullIntersectionLemmas_exists_unit_finite_lift
import Theorems.Thm_KrullIntersectionUnits_KrullIntersectionLemmas_exists_mem_mul_eq_of_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KrullIntersectionUnits KrullIntersectionUnits.KrullIntersectionLemmas
namespace KrullIntersectionUnits.KrullIntersectionLemmas
namespace GlobalTheory.CompanionTheory.Formal.IsoThick
theorem _root_.solution :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] [IsNoetherianRing A] (φ : A →+* B), φ.Finite → ∀ (J : Ideal A), (∀ (b : B), ∃ (a : A), b - DFunLike.coe φ a ∈ Ideal.map φ J) → (∀ (a : A), DFunLike.coe φ a = OfNat.ofNat (nat_lit 0) → ∀ (n : ℕ), a ∈ J ^ n) → ∃ (s : A), s - OfNat.ofNat (nat_lit 1) ∈ J ∧ (∀ (k : A), DFunLike.coe φ k = OfNat.ofNat (nat_lit 0) → s * k = OfNat.ofNat (nat_lit 0)) ∧ ∀ (b : B), ∃ (a : A), DFunLike.coe φ s * b = DFunLike.coe φ a := by
  intro A B _ _ _ φ hf J hsurj hker
  obtain ⟨s1, hs1J, hs1⟩ := exists_unit_finite_lift φ hf J hsurj
  obtain ⟨S, hS⟩ : ∃ S : Finset A, Submodule.span A (S : Set A) = RingHom.ker φ :=
    IsNoetherian.noetherian (RingHom.ker φ)
  have hSk : ∀ x ∈ S, ∃ r ∈ J, r * x = x := by
    intro x hx
    have hxk : x ∈ RingHom.ker φ := by
      rw [← hS]
      exact Submodule.subset_span hx
    exact exists_mem_mul_eq_of_mem_pow J x (hker x (RingHom.mem_ker.mp hxk))
  obtain ⟨s2, hs2J, hs2⟩ := exists_unit_kills_of_idempotent J S hSk
  refine ⟨s1 * s2, ?_, ?_, ?_⟩
  · have e : s1 * s2 - 1 = (s1 - 1) * s2 + (s2 - 1) := by ring
    rw [e]
    exact J.add_mem (J.mul_mem_right s2 hs1J) hs2J
  · intro k hk
    have hle : Submodule.span A (S : Set A) ≤ LinearMap.ker (LinearMap.mulLeft A s2) := by
      rw [Submodule.span_le]
      intro x hx
      show x ∈ LinearMap.ker (LinearMap.mulLeft A s2)
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact hs2 x hx
    have hk' : k ∈ Submodule.span A (S : Set A) := by
      rw [hS]
      exact RingHom.mem_ker.mpr hk
    have h2 := hle hk'
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at h2
    rw [mul_assoc, h2, mul_zero]
  · intro b
    obtain ⟨a, ha⟩ := hs1 b
    refine ⟨s2 * a, ?_⟩
    rw [map_mul, map_mul, ← ha]
    ring
end GlobalTheory.CompanionTheory.Formal.IsoThick
end KrullIntersectionUnits.KrullIntersectionLemmas
