-- Prove2me | solution 1 for NearEnemy.eval_innerPoly
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:34.792618+00:00
-- url     : https://prove2.me/submissions/d59108ca-0f5d-4dca-9a10-5290955b407b

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
theorem solution (f : Fin 2 × ι → ℝ) (k : Fin 2)
    (v : EuclideanSpace ℝ ι) :
    eval f (innerPoly k v) = ⟪rowOf f k, v⟫ := by
  simp [innerPoly, rowOf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
