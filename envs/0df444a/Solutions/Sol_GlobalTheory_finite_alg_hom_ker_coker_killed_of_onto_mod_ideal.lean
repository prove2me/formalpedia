-- Prove2me | solution 1 for GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:48:40.068341+00:00
-- url     : https://prove2.me/submissions/08e70399-d5bf-464d-87da-446257b1ddac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitApproximationAdicCompletion

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
theorem _root_.solution
    (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M]
    [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N]
    (φ : M →ₐ[A] N) :
    (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) →
    (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) →
    ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧
      ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by
  intro h1 h2

  set R : Submodule A N := LinearMap.range φ.toLinearMap with hR
  have hQ : (⊤ : Submodule A (N ⧸ R)) ≤ J • ⊤ := by
    rintro q -
    obtain ⟨y, rfl⟩ := R.mkQ_surjective q
    obtain ⟨t, ht⟩ := h1 y
    have hz : y - φ t ∈ J • (⊤ : Submodule A N) := by
      rw [Ideal.smul_top_eq_map]; exact ht
    have hm : R.mkQ (y - φ t) ∈ J • (⊤ : Submodule A (N ⧸ R)) := by
      have := Submodule.mem_map_of_mem (f := R.mkQ) hz
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
      exact this
    have he : R.mkQ (y - φ t) = R.mkQ y := by
      rw [map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨t, rfl⟩
    rwa [he] at hm
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J
    (⊤ : Submodule A (N ⧸ R)) (Module.Finite.fg_top) hQ
  have hrR : ∀ y : N, r • y ∈ R := by
    intro y
    have := hr (R.mkQ y) trivial
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

  set K : Submodule A M := LinearMap.ker φ.toLinearMap with hK
  have hKfg : K.FG := IsNoetherian.noetherian K
  have hKle : K ≤ J • K := by
    intro t ht
    have hφ : φ t = 0 := ht
    have hmem : t ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule A M) := by
      rw [Submodule.mem_iInf]
      intro i
      rw [Ideal.smul_top_eq_map]
      exact h2 i t (by rw [hφ]; exact Ideal.zero_mem _)
    obtain ⟨⟨s, hs⟩, hst⟩ := (J.mem_iInf_smul_pow_eq_bot_iff t).1 hmem
    simp only at hst
    rw [← hst]
    exact Submodule.smul_mem_smul hs ht
  obtain ⟨u, hu1, hu⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J K hKfg hKle
  refine ⟨r * u, ?_, ?_, ?_⟩
  · have : r * u - 1 = r * (u - 1) + (r - 1) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left r hu1) hr1
  · intro y
    rw [← Algebra.smul_def, mul_comm, mul_smul]
    obtain ⟨t, ht⟩ := hrR y
    exact ⟨u • t, by
      change φ (u • t) = u • (r • y)
      rw [map_smul]
      congr 1⟩
  · intro t ht
    rw [← Algebra.smul_def, mul_smul, hu t ht, smul_zero]
end GlobalTheory
