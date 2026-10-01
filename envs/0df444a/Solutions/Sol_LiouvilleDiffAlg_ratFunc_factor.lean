-- Prove2me | solution 1 for LiouvilleDiffAlg.ratFunc_factor
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:43:02.051834+00:00
-- url     : https://prove2.me/submissions/a88647cb-1144-49b0-bb61-92946de41748

import Mathlib

open scoped Differential
open Polynomial

private lemma poly_factor {K : Type*} [Field K] (A : K[X]) (hA : A ≠ 0) :
    ∃ (a : K) (N : Multiset K[X]), a ≠ 0 ∧ (∀ p ∈ N, Monic p ∧ Irreducible p) ∧
      A = C a * N.prod := by
  classical
  have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hA
  obtain ⟨u, hu⟩ := hassoc
  obtain ⟨a, ha, hau⟩ := Polynomial.isUnit_iff.1 u.isUnit
  refine ⟨a, UniqueFactorizationMonoid.normalizedFactors A, ha.ne_zero, ?_, ?_⟩
  · intro p hp
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
    refine ⟨?_, hirr⟩
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor p hp
    rw [← hn]
    exact Polynomial.monic_normalize hirr.ne_zero
  · rw [hau]; rw [mul_comm]; exact hu.symm

theorem solution {K : Type*} [Field K] (u : RatFunc K) (hu : u ≠ 0) :
    ∃ (a : K) (N D : Multiset K[X]), a ≠ 0 ∧ (∀ p ∈ N, Monic p ∧ Irreducible p) ∧
      (∀ p ∈ D, Monic p ∧ Irreducible p) ∧
      u = algebraMap K (RatFunc K) a * algebraMap K[X] (RatFunc K) N.prod / algebraMap K[X] (RatFunc K) D.prod := by
  have hnum : u.num ≠ 0 := RatFunc.num_ne_zero hu
  have hden : u.denom ≠ 0 := RatFunc.denom_ne_zero u
  obtain ⟨α, N, hα, hN, hnum'⟩ := poly_factor u.num hnum
  obtain ⟨β, D, hβ, hD, hden'⟩ := poly_factor u.denom hden
  refine ⟨α / β, N, D, div_ne_zero hα hβ, hN, hD, ?_⟩
  have hκ : ∀ c : K, algebraMap K (RatFunc K) c = algebraMap K[X] (RatFunc K) (C c) := fun c => by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K) c, Polynomial.algebraMap_eq]
  have hι : ∀ x : K[X], x ≠ 0 → algebraMap K[X] (RatFunc K) x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hx
  have hβ' : algebraMap K (RatFunc K) β ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K (RatFunc K)).injective).2 hβ
  have hDp : D.prod ≠ 0 := by
    intro h0; apply hden; rw [hden', h0, mul_zero]
  have hDp' := hι _ hDp
  have h := RatFunc.num_div_denom u
  conv_lhs => rw [← h]
  rw [hnum', hden', map_mul, map_mul, ← hκ, ← hκ, map_div₀]
  field_simp
