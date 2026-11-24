-- Prove2me | solution 1 for GlobalTheory.Desc.finiteType_away_of_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:21.7888+00:00
-- url     : https://prove2.me/submissions/60db6df3-6f9a-496c-b40e-19b791dfac59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteTypeAwayOfAtPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Desc
open scoped TensorProduct
namespace GlobalTheory.Desc
theorem _root_.solution {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (s : Finset C) (x : C) (h : ∀ c : C, ∃ n : ℕ, x ^ n * c ∈ Algebra.adjoin R (s : Set C)) :
    Algebra.FiniteType R (Localization.Away x) := by
  classical
  let φ := IsScalarTower.toAlgHom R C (Localization.Away x)
  let u : Localization.Away x := IsLocalization.Away.invSelf x
  have hu : φ x * u = 1 := IsLocalization.Away.mul_invSelf x
  refine ⟨⟨insert u (s.image φ), ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  have hU : u ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) :=
    Algebra.subset_adjoin (by simp)
  have hB : ∀ b ∈ Algebra.adjoin R (s : Set C),
      φ b ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) := by
    intro b hb
    have : φ b ∈ (Algebra.adjoin R (s : Set C)).map φ := ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    refine Algebra.adjoin_mono ?_ this
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_image]
    exact Or.inr hz
  obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj x y
  obtain ⟨n, hn⟩ := h c
  have hc' : y * φ x ^ m = φ c := hc
  have : y = φ (x ^ n * c) * u ^ (n + m) := by
    rw [map_mul, map_pow, ← hc']
    calc y = y * (φ x * u) ^ (n + m) := by rw [hu]; simp
      _ = _ := by ring
  rw [this]
  exact mul_mem (hB _ hn) (pow_mem hU _)
end GlobalTheory.Desc
