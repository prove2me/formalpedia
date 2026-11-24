-- Prove2me | solution 1 for GlobalTheory.adjoin_mem_of_away_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:13.269651+00:00
-- url     : https://prove2.me/submissions/f9b67c74-9bff-48b7-ba6a-65b8fcbc62c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowMulMemAdjoinOfLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Algebra
namespace GlobalTheory
theorem _root_.solution {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  have hg : algebraMap A A' (algebraMap R A g) = algebraMap R A' g :=
    (IsScalarTower.algebraMap_apply R A A' g).symm
  have key : ∀ y ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ k : ℕ, ∃ z ∈ Algebra.adjoin R T,
      algebraMap A A' z = algebraMap R A' g ^ k * y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨0, a, Algebra.subset_adjoin ha, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨r0, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A r0, Subalgebra.algebraMap_mem _ r0, ?_⟩
      simp only at hr
      rw [← IsScalarTower.algebraMap_apply R A A', IsScalarTower.algebraMap_apply R R' A', ← hr,
        map_mul, ← IsScalarTower.algebraMap_apply R R' A', map_pow, mul_comm]
    | add x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, algebraMap R A g ^ k2 * z1 + algebraMap R A g ^ k1 * z2, ?_, ?_⟩
      · refine add_mem (mul_mem ?_ hz1) (mul_mem ?_ hz2) <;>
          (rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _)
      · rw [map_add, map_mul, map_mul, map_pow, map_pow, hg, e1, e2]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨k1, z1, hz1, e1⟩ := hx
      obtain ⟨k2, z2, hz2, e2⟩ := hy
      refine ⟨k1 + k2, z1 * z2, mul_mem hz1 hz2, ?_⟩
      rw [map_mul, e1, e2]; ring
  obtain ⟨k, z, hz, e⟩ := key _ hb
  have h0 : algebraMap A A' (z - algebraMap R A g ^ k * b) = 0 := by
    rw [map_sub, map_mul, map_pow, hg, e, sub_self]
  obtain ⟨⟨_, c, rfl⟩, hc⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A g)) A' _).1 h0
  refine ⟨c + k, ?_⟩
  have : algebraMap R A g ^ (c + k) * b = algebraMap R A g ^ c * z := by
    simp only at hc
    rw [mul_sub, sub_eq_zero] at hc
    rw [hc, pow_add]; ring
  rw [this]
  refine mul_mem ?_ hz
  rw [← map_pow]; exact Subalgebra.algebraMap_mem _ _
end GlobalTheory
