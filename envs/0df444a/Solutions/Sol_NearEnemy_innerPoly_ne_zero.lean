-- Prove2me | solution 1 for NearEnemy.innerPoly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:03:23.583833+00:00
-- url     : https://prove2.me/submissions/d0467b4b-d6d9-4f14-868e-7fc26c666e69

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_eval_innerPoly_rows

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

open NearEnemy in
theorem solution {a b : EuclideanSpace ℝ ι} (hab : a ≠ b) :
    innerPoly (ι := ι) 0 (a - b) ≠ 0 := by
  intro h0
  have heval := congrArg (eval fun ki ↦ ![a - b, 0] ki.1 ki.2) h0
  rw [eval_innerPoly_rows, map_zero, Matrix.cons_val_zero] at heval
  exact sub_ne_zero.mpr hab (inner_self_eq_zero.mp heval)
