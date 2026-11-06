-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_O_fiber_gaussian_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:54:25.681572+00:00
-- url     : https://prove2.me/submissions/e6f94de9-0e1b-46f7-b422-d45bd45e4604

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_fiber_gaussian_mass
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
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
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (c r : O) (hc : c ≠ 0) :
    let a := (ActualEisensteinCoordinates.coords c).1
    let b := (ActualEisensteinCoordinates.coords c).2
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' w : O, Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding (r+c*w)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  dsimp only
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let x := (ActualEisensteinCoordinates.coords r).1
  let y := (ActualEisensteinCoordinates.coords r).2
  have hceq : c = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords c).symm
  have hreq : r = ActualEisensteinCoordinates.eval x y :=
    (ActualEisensteinCoordinates.eval_coords r).symm
  have hcE : ActualEisensteinCoordinates.eval a b ≠ 0 := by
    rw [← hceq]
    exact hc
  have hmass := actual_fiber_gaussian_mass a b x y hcE
  convert hmass using 1
  funext η
  congr 1
  let W : O → ℂ := fun w => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖eisEmbedding (r+c*w)‖ ^ 2 : ℂ))
  have hsum := (latticeCoordEquiv.symm.tsum_eq W).symm
  have happly (z : ℤ × ℤ) : latticeCoordEquiv.symm z =
      ActualEisensteinCoordinates.eval z.1 z.2 := rfl
  simpa only [W, hceq, hreq, happly] using hsum
end OAI.ActualEisensteinCubic
