-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_reflected_exp_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T11:29:18.744161+00:00
-- url     : https://prove2.me/submissions/eea1778d-8cff-4a90-b97d-b936443aa660

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha) (t : NNReal) (w : Omega) :
    0 ≤ Real.exp (-alpha * (runningSup L t w - L.X t w)) ∧
    Real.exp (-alpha * (runningSup L t w - L.X t w)) ≤ 1 := by 
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hAlpha)
    (sub_nonneg.mpr ((runningSup_monotone_and_path_le L w).2 t))
