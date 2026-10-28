-- Prove2me | solution 1 for NewtonCartan.classical_christoffel_form
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:30:25.402836+00:00
-- url     : https://prove2.me/submissions/837601c3-3b8b-4e41-8740-3fe9bdbda857

import Definitions.Def_NewtonCartan_defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped ContDiff BigOperators
open Classical
open NewtonCartan

private lemma compat_spatial_sym (Γ : Conn) (hC : Compatible Γ) (x : E)
    (a i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) :
    Γ x i a j + Γ x j a i = 0 := by
  have h := hC.2 x a i j
  have h1 : (∑ n : Fin 4, Γ x i a n * hh n j) = Γ x i a j := by
    calc ∑ n : Fin 4, Γ x i a n * hh n j
        = ∑ n : Fin 4, if n = j then Γ x i a j else 0 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          by_cases hn : n = j
          · subst hn; simp [hh, hj]
          · simp [hh, hn]
        _ = Γ x i a j := by simp [Finset.sum_ite_eq']
  have h2 : (∑ n : Fin 4, Γ x j a n * hh i n) = Γ x j a i := by
    calc ∑ n : Fin 4, Γ x j a n * hh i n
        = ∑ n : Fin 4, if n = i then Γ x j a i else 0 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          by_cases hn : n = i
          · subst hn; simp [hh, hi]
          · simp [hh, hn, Ne.symm hn]
        _ = Γ x j a i := by simp [Finset.sum_ite_eq']
  linarith [h, show (∑ n : Fin 4, (Γ x i a n * hh n j + Γ x j a n * hh i n)) =
      (∑ n, Γ x i a n * hh n j) + (∑ n, Γ x j a n * hh i n) from Finset.sum_add_distrib, h1, h2]

theorem solution (Γ : Conn) (hΓ : IsClassical Γ) :
    (∀ x b c, Γ x 0 b c = 0) ∧
    (∀ x i j k, i ≠ 0 → j ≠ 0 → k ≠ 0 → Γ x i j k = 0) ∧
    (∀ x i j, i ≠ 0 → j ≠ 0 → Γ x i 0 j + Γ x j 0 i = 0) := by
  refine ⟨?gamma0, ?spatial, ?omega⟩
  · intro x b c
    have := hΓ.2.1 x b c
    simpa [tt, Finset.sum_ite_eq'] using this
  · intro x i j k hi hj hk
    have htors := hΓ.1.2 x
    have hs (a u v : Fin 4) (hu : u ≠ 0) (hv : v ≠ 0) :
        Γ x u a v + Γ x v a u = 0 := compat_spatial_sym Γ hΓ.2 x a u v hu hv
    have h1 : Γ x i j k + Γ x k j i = 0 := hs j i k hi hk
    have h2 : Γ x j k i + Γ x i k j = 0 := hs k j i hj hi
    have h3 : Γ x k i j + Γ x j i k = 0 := hs i k j hk hj
    rw [htors k j i] at h1
    rw [htors i k j] at h2
    rw [htors j i k] at h3
    linarith [h1, h2, h3]
  · intro x i j hi hj
    exact compat_spatial_sym Γ hΓ.2 x 0 i j hi hj
