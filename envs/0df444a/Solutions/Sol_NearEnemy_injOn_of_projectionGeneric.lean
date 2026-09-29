-- Prove2me | solution 1 for NearEnemy.injOn_of_projectionGeneric
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:36.373494+00:00
-- url     : https://prove2.me/submissions/433d9e28-803d-424e-8c25-98f52c420ada

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
theorem solution {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)} {G : Finset (EuclideanSpace ℝ ι)} (hT : ProjectionGeneric T G) :
    Set.InjOn (fun x ↦ T x) ↑G := by
  intro a ha b hb hTab
  by_contra hab
  exact hT.1 a ha b hb hab (by rw [map_sub, sub_eq_zero]; exact hTab)
