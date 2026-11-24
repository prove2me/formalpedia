-- Prove2me | solution 1 for GlobalTheory.QcSub.Local.adjoin_mem_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:44:40.674658+00:00
-- url     : https://prove2.me/submissions/007584ff-34d1-4b5b-a587-4aef5c53f2c7

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
open GlobalTheory GlobalTheory.QcSub GlobalTheory.QcSub.Local
namespace GlobalTheory.QcSub.Local
theorem _root_.solution {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R']
    [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  classical
  have hgen : ∀ k : ℕ, algebraMap R A g ^ k ∈ Algebra.adjoin R T := fun k =>
    pow_mem (Subalgebra.algebraMap_mem _ g) k
  have hgA : algebraMap A A' (algebraMap R A g) = algebraMap R' A' (algebraMap R R' g) := by
    rw [← IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply R R' A']
  have key : ∀ x ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ m : ℕ, ∃ s ∈ Algebra.adjoin R T,
      algebraMap A A' (algebraMap R A g) ^ m * x = algebraMap A A' s := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨0, t, Algebra.subset_adjoin ht, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A a, Subalgebra.algebraMap_mem _ a, ?_⟩
      have h2 := congrArg (algebraMap R' A') hr
      simp only [map_mul, map_pow] at h2
      rw [mul_comm, hgA, h2, ← IsScalarTower.algebraMap_apply R R' A',
        ← IsScalarTower.algebraMap_apply R A A']
    | add x y _ _ hx hy =>
      obtain ⟨m1, s1, hs1, e1⟩ := hx
      obtain ⟨m2, s2, hs2, e2⟩ := hy
      refine ⟨m1 + m2, algebraMap R A g ^ m2 * s1 + algebraMap R A g ^ m1 * s2,
        add_mem (mul_mem (hgen _) hs1) (mul_mem (hgen _) hs2), ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e1, ← e2]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨m1, s1, hs1, e1⟩ := hx
      obtain ⟨m2, s2, hs2, e2⟩ := hy
      refine ⟨m1 + m2, s1 * s2, mul_mem hs1 hs2, ?_⟩
      rw [map_mul, ← e1, ← e2]
      ring
  obtain ⟨m, s, hs, hms⟩ := key _ hb
  rw [← map_pow, ← map_mul] at hms
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R A g)) A').mp hms
  refine ⟨k + m, ?_⟩
  have h3 : algebraMap R A g ^ (k + m) * b = algebraMap R A g ^ k * s := by
    rw [pow_add, mul_assoc]
    exact hk
  rw [h3]
  exact mul_mem (hgen k) hs
end GlobalTheory.QcSub.Local
