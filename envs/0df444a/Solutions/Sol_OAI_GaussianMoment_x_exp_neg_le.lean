-- Prove2me | solution 1 for OAI.GaussianMoment.x_exp_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:13.914198+00:00
-- url     : https://prove2.me/submissions/44c41446-0297-496e-a680-da288e079dc7

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments

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
open Filter Real Asymptotics
open OAI.GaussianMoment
namespace OAI.GaussianMoment
theorem _root_.solution (x : ℝ) (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-x)).le
  calc
    x * Real.exp (-x) = 2 * ((x / 2) * Real.exp (-x)) := by ring
    _ ≤ 2 * (Real.exp (x / 2) * Real.exp (-x)) := by
      gcongr
    _ = 2 * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
end OAI.GaussianMoment
