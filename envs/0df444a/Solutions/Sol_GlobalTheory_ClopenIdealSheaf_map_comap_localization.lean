-- Prove2me | solution 1 for GlobalTheory.ClopenIdealSheaf.map_comap_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:02.431513+00:00
-- url     : https://prove2.me/submissions/4a6c9b5c-65fd-4d28-b753-5aded537b88e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSheafDataOfIsClopenFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.ClopenIdealSheaf
namespace GlobalTheory.ClopenIdealSheaf
theorem _root_.solution {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra A T] (f : R) [IsLocalization.Away f S] (ρ : R →+* A)
    [IsLocalization.Away (ρ f) T] (τ : S →+* T)
    (hcomm : ∀ a, τ (algebraMap R S a) = algebraMap A T (ρ a)) (I : Ideal A) :
    (I.comap ρ).map (algebraMap R S) = (I.map (algebraMap A T)).comap τ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
    rw [hcomm]
    exact Ideal.mem_map_of_mem _ ha
  · intro s hs
    obtain ⟨⟨⟨x, hx⟩, ⟨_, n, rfl⟩⟩, hxs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers (ρ f)) T).mp (Ideal.mem_comap.mp hs)
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (.powers f) s
    simp only at hxs hb
    have h1 : algebraMap A T (ρ b * ρ f ^ n) = algebraMap A T (x * ρ f ^ k) := by
      calc algebraMap A T (ρ b * ρ f ^ n)
          = τ (algebraMap R S b) * algebraMap A T (ρ f ^ n) := by rw [map_mul, hcomm]
        _ = τ s * τ (algebraMap R S (f ^ k)) * algebraMap A T (ρ f ^ n) := by
          rw [← hb, map_mul]
        _ = τ s * algebraMap A T (ρ f ^ n) * algebraMap A T (ρ f ^ k) := by
          rw [hcomm, map_pow]; ring
        _ = algebraMap A T (x * ρ f ^ k) := by rw [hxs, map_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (.powers (ρ f)) T).mp h1
    simp only at hm
    rw [IsLocalization.mem_map_algebraMap_iff (.powers f)]
    refine ⟨⟨⟨f ^ (m + n) * b, ?_⟩, ⟨f ^ (m + n + k), m + n + k, rfl⟩⟩, ?_⟩
    · have e : ρ (f ^ (m + n) * b) = ρ f ^ m * (ρ b * ρ f ^ n) := by
        rw [map_mul, map_pow, pow_add]; ring
      rw [Ideal.mem_comap, e, hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hx)
    · simp only
      rw [map_mul, pow_add, map_mul, ← hb]
      ring
end GlobalTheory.ClopenIdealSheaf
