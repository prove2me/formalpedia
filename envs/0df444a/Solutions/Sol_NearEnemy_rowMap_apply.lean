-- Prove2me | solution 1 for NearEnemy.rowMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:37.888276+00:00
-- url     : https://prove2.me/submissions/2c61011e-86f1-44e5-86ac-8c4fc29ca095

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
theorem solution (r : Fin 2 → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (k : Fin 2) :
    rowMap r x k = ⟪r k, x⟫ := rfl
