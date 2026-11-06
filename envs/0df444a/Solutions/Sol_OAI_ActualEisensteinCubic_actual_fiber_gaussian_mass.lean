-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.actual_fiber_gaussian_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:53:06.08729+00:00
-- url     : https://prove2.me/submissions/e1579a38-996e-42d2-983f-accd71582e1b

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_ActualEisensteinCubic_actual_fiber_gaussian_eq_shifted
import Theorems.Thm_OAI_EisensteinAbelFiber_scaled_shifted_gaussian_mass
import Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_pos_of_nonzero


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
theorem _root_.solution (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ,
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding
            (ActualEisensteinCoordinates.eval x y +
              ActualEisensteinCoordinates.eval a b *
                ActualEisensteinCoordinates.eval z.1 z.2)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  have hq : 0 < (((a*a-a*b+b*b : ℤ) : ℝ)) := by
    exact_mod_cast coordinate_norm_pos_of_nonzero a b hc
  let u := EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  let v := EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  have h := EisensteinAbelFiber.scaled_shifted_gaussian_mass
    (((a*a-a*b+b*b : ℤ) : ℝ)) hq u v
  convert h using 1
  funext η
  congr 1
  apply tsum_congr
  intro z
  exact actual_fiber_gaussian_eq_shifted a b x y z.1 z.2 hc η
end OAI.ActualEisensteinCubic
