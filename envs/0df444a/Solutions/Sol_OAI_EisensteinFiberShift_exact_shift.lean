-- Prove2me | solution 1 for OAI.EisensteinFiberShift.exact_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:00.062757+00:00
-- url     : https://prove2.me/submissions/75ad0e31-3ae9-4a50-a17e-eea6204f470f

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.EisensteinFiberShift
namespace OAI.EisensteinFiberShift
theorem _root_.solution (a b x y m n : ℝ) (hq : q a b ≠ 0) :
    Q (x+a*m-b*n) (y+b*m+(a-b)*n) =
      q a b * Q (m+shiftX a b x y) (n+shiftY a b x y) := by
  dsimp [shiftX, shiftY, Q]
  field_simp [hq]
  dsimp [q, Q]
  ring
end OAI.EisensteinFiberShift
