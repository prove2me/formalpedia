-- Prove2me | solution 1 for NearEnemy.dist_image_eq_iff_of_sep
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:33.641426+00:00
-- url     : https://prove2.me/submissions/30ce7aa5-9082-41ca-8167-af6d3d4b3081

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

open NearEnemy in
theorem solution {G : Finset (EuclideanSpace ℝ ι)}
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (hsep : ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
      a - b ≠ c - e → a - b ≠ -(c - e) →
      dist (T a) (T b) ≠ dist (T c) (T e))
    {a b c e : EuclideanSpace ℝ ι}
    (ha : a ∈ G) (hb : b ∈ G) (hc : c ∈ G) (he : e ∈ G) :
    dist (T a) (T b) = dist (T c) (T e) ↔
      (a - b = c - e ∨ a - b = -(c - e)) := by
  constructor
  · intro h
    by_contra hcon
    exact hsep a ha b hb c hc e he (fun h' ↦ hcon (Or.inl h'))
      (fun h' ↦ hcon (Or.inr h')) h
  · rintro (h | h)
    · rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub, h]
    · rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub, h, map_neg,
        norm_neg]
