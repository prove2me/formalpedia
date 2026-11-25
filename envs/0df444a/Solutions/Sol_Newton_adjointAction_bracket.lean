-- Prove2me | solution 1 for Newton.adjointAction.bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:13:02.302606+00:00
-- url     : https://prove2.me/submissions/b3e20e5f-2821-49e8-8322-438f0e2e47a6

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GaugeTransformation
import Theorems.Thm_Newton_adjointAction_one_action
import Theorems.Thm_Newton_adjointAction_zero
import Theorems.Thm_Newton_SuNAlgebra_lie_def
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix


attribute [local simp] Newton.adjointAction.one_action
attribute [local simp] Newton.adjointAction.zero

set_option autoImplicit false
open Matrix
open Newton
variable {N : ℕ}
open Newton.adjointAction
namespace Newton.adjointAction
theorem _root_.solution (g : SUNGroup N) (A B : SuNAlgebra N) :
    adjointAction g ⁅A, B⁆ = ⁅adjointAction g A, adjointAction g B⁆ := by
  apply SuNAlgebra.ext
  simp only [adjointAction, SuNAlgebra.lie_def]
  -- g [A, B] g† = g (AB - BA) g† = gAg† gBg† - gBg† gAg† = [gAg†, gBg†]
  -- Using g† g = 1
  have h := g.unitary'
  -- LHS: g(AB - BA)g† = gABg† - gBAg†
  -- RHS: (gAg†)(gBg†) - (gBg†)(gAg†)
  -- Since g†g = 1, we have gABg† = gA(g†g)Bg† = (gAg†)(gBg†)
  let gm := g.matrix
  let gh := conjTranspose g.matrix
  let am := A.matrix
  let bm := B.matrix
  have eq1 : gm * am * bm * gh = gm * am * gh * (gm * bm * gh) := by
    calc gm * am * bm * gh
        = gm * am * (gh * gm) * bm * gh := by rw [h]; simp only [mul_one]
      _ = gm * am * gh * (gm * bm * gh) := by simp only [Matrix.mul_assoc]
  have eq2 : gm * bm * am * gh = gm * bm * gh * (gm * am * gh) := by
    calc gm * bm * am * gh
        = gm * bm * (gh * gm) * am * gh := by rw [h]; simp only [mul_one]
      _ = gm * bm * gh * (gm * am * gh) := by simp only [Matrix.mul_assoc]
  calc gm * (am * bm - bm * am) * gh
      = gm * am * bm * gh - gm * bm * am * gh := by simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = gm * am * gh * (gm * bm * gh) - gm * bm * gh * (gm * am * gh) := by rw [eq1, eq2]
end Newton.adjointAction
