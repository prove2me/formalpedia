-- Prove2me | solution 1 for GroundTheory.LocalField.one_mem_spanZ_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:42.250234+00:00
-- url     : https://prove2.me/submissions/191453d2-624f-442c-97f8-06cc0db34412

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionAssembly
import Theorems.Thm_GroundTheory_LocalField_exists_smul_one_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_spanZ_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable (hmono : ∀ K : Subgroup G, IsElementary K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hmono
namespace GroundTheory.LocalField
theorem _root_.solution : (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := by
  let T : ℤ →ₗ[ℤ] (G → ℂ) := LinearMap.toSpanSingleton ℤ (G → ℂ) 1
  let I : Submodule ℤ ℤ := (spanZ (IsElementary (G := G))).comap T
  have hmem : ∀ k : ℤ, k ∈ I ↔ k • (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := fun k ↦ Iff.rfl
  have hprimes : ∀ p : ℕ, p.Prime → ∃ m : ℕ, ¬ p ∣ m ∧ (m : ℤ) ∈ I := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hpm, hm⟩ := exists_smul_one_mem_spanZ (p := p) (Complex.isPrimitiveRoot_exp _
      Nat.card_pos.ne') (fun K hK χ hχ ↦ hmono K ⟨p, hp, hK⟩ χ hχ)
    exact ⟨m, hpm, (hmem _).mpr (spanZ_mono (fun K hK ↦ ⟨p, hp, hK⟩) hm)⟩
  set d := Submodule.IsPrincipal.generator I
  have hdvd : ∀ k ∈ I, d ∣ k := fun k hk ↦ by
    obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hk
    exact ⟨s, by rw [hs, smul_eq_mul, mul_comm]⟩
  have hd : d.natAbs = 1 := by
    by_contra hd
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    obtain ⟨m, hpm, hm⟩ := hprimes p hp
    apply hpm
    have h1 : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
    exact Int.natCast_dvd_natCast.mp (h1.trans (hdvd _ hm))
  have hd1 : (1 : ℤ) ∈ I := by
    have hdI : d ∈ I := Submodule.IsPrincipal.generator_mem I
    rcases Int.natAbs_eq d with h | h
    · rw [hd] at h
      rwa [h] at hdI
    · rw [hd] at h
      have := I.smul_mem (-1) hdI
      rwa [h, smul_eq_mul, Nat.cast_one, neg_mul_neg, one_mul] at this
  simpa using (hmem 1).mp hd1
end GroundTheory.LocalField
