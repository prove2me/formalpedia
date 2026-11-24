-- Prove2me | solution 1 for GlobalTheory.Desc.exists_pow_mul_mem_of_finiteType_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:19.498213+00:00
-- url     : https://prove2.me/submissions/5ac96416-d587-438c-beee-bd9fd9638d31

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
    (f : R) (h : Algebra.FiniteType R (Localization.Away (algebraMap R C f))) :
    ∃ s : Finset C, ∀ c : C, ∃ n : ℕ, algebraMap R C f ^ n * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  set x := algebraMap R C f with hx
  let φ := algebraMap C (Localization.Away x)
  obtain ⟨t, ht⟩ := h.out
  choose m a ha using fun y : Localization.Away x => IsLocalization.Away.surj x y
  refine ⟨t.image a, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image a : Finset C) : Set C) with hB
  have hxB : x ∈ B := B.algebraMap_mem f
  have key : ∀ y ∈ Algebra.adjoin R (t : Set (Localization.Away x)),
      ∃ n : ℕ, ∃ b ∈ B, y * φ x ^ n = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨m y, a y, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), ha y⟩
    | algebraMap r =>
      exact ⟨0, algebraMap R C r, B.algebraMap_mem r, by
        rw [pow_zero, mul_one]; exact IsScalarTower.algebraMap_apply R C _ r⟩
    | add y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * x ^ k + d * x ^ n,
        add_mem (mul_mem hb (pow_mem hxB _)) (mul_mem hd (pow_mem hxB _)), ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e, ← e']
      ring
    | mul y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e']
      ring
  obtain ⟨n, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_pow, ← map_mul] at e
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq x e
  refine ⟨k + n, ?_⟩
  have : x ^ (k + n) * c = x ^ k * b := by rw [← hk]; ring
  rw [this]
  exact mul_mem (pow_mem hxB _) hb
end GlobalTheory.Desc
