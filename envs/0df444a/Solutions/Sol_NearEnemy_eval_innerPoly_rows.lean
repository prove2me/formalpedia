-- Prove2me | solution 1 for NearEnemy.eval_innerPoly_rows
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:00:06.916566+00:00
-- url     : https://prove2.me/submissions/2843f282-477f-4783-9939-8f35285dd89a

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_eval_innerPoly

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

open NearEnemy in
theorem solution (p q : EuclideanSpace ℝ ι) (k : Fin 2)
    (v : EuclideanSpace ℝ ι) :
    eval (fun ki ↦ ![p, q] ki.1 ki.2) (innerPoly k v) = ⟪![p, q] k, v⟫ :=
  eval_innerPoly _ k v
