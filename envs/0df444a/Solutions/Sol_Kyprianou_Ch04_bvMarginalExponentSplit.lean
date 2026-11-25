-- Prove2me | solution 1 for Kyprianou.Ch04.bvMarginalExponentSplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:26:35.626713+00:00
-- url     : https://prove2.me/submissions/308242a4-63ca-4236-91fa-83f23e99b472

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Recombine the large and small jump integrals and the BV drift correction. -/
theorem solution
    (T : LevyKhintchineTriple)
    (hBV : (∫⁻ x in Ioo (-1 : Real) 1, ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (b : Real) (hJump : Integrable (fun x : Real => Real.exp (b*x)-1) T.levyMeasure) :
    (∫ x in {x : Real | 1 ≤ |x|}, (Real.exp (b*x)-1) ∂T.levyMeasure) +
      (T.drift*b + ∫ x in Ioo (-1 : Real) 1,
        (Real.exp (b*x)-1-b*x) ∂T.levyMeasure) =
      (T.drift - ∫ x in Ioo (-1 : Real) 1, x ∂T.levyMeasure)*b +
        ∫ x, (Real.exp (b*x)-1) ∂T.levyMeasure := by
  let S := Ioo (-1 : ℝ) 1
  let f (x : ℝ) := Real.exp (b*x)-1
  have hi : Integrable (fun x : ℝ => x) (T.levyMeasure.restrict S) :=
    ⟨continuous_id.aestronglyMeasurable,
      by simpa [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using hBV⟩
  have hcomp : {x : ℝ | 1 ≤ |x|} = Sᶜ := by
    ext x
    change 1 ≤ |x| ↔ ¬ x ∈ S
    rw [← not_lt, abs_lt]
    rfl
  change (∫ x in _, f x ∂T.levyMeasure) +
    (T.drift*b + ∫ x in S, (f x-b*x) ∂T.levyMeasure) = _
  rw [hcomp, integral_sub hJump.integrableOn (hi.const_mul b), integral_const_mul]
  have hs := integral_add_compl (s := S) measurableSet_Ioo hJump
  linarith only [hs]
