-- Prove2me | solution 2 for OAI.ArnoldCounterexample.Forms.normSq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:57:44.1958+00:00
-- url     : https://prove2.me/submissions/b934856c-64f8-4b48-94d5-be4f481a7232

import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic

open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped BigOperators ContDiff
theorem solution (n : ℕ) (z v : CSpace n) :
    fderiv ℝ (normSq n) z v = -symplectic n (Complex.I • z) v := by
  have hfun : normSq n = fun w => ∑ i, ((reCoord n i w) * (reCoord n i w) +
      (imCoord n i w) * (imCoord n i w)) := by
    funext w; simp [normSq, Complex.normSq_apply]
  have hd : HasFDerivAt (normSq n) (∑ i : Fin n,
      ((reCoord n i z) • reCoord n i + (reCoord n i z) • reCoord n i +
       ((imCoord n i z) • imCoord n i + (imCoord n i z) • imCoord n i))) z := by
    rw [hfun]
    apply HasFDerivAt.fun_sum
    intro i _
    have h1 := (reCoord n i).hasFDerivAt (x := z)
    have h2 := (imCoord n i).hasFDerivAt (x := z)
    exact (h1.mul h1).add (h2.mul h2)
  rw [hd.fderiv]
  simp only [symplectic, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply',
    reCoord_apply, imCoord_apply, smul_eq_mul, Complex.smul_re, Complex.smul_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [two_nsmul]
  ring
