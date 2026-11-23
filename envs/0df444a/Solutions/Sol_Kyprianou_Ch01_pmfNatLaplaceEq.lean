-- Prove2me | solution 1 for Kyprianou.Ch01.pmfNatLaplaceEq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:33:48.861262+00:00
-- url     : https://prove2.me/submissions/adababc1-52bc-48da-b3c1-74c8f6b36d83

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_summablePowerSeriesZeroCoefficientsOfSmallPositiveValues
import Theorems.Thm_Kyprianou_Ch01_pmfNatLaplaceDifferenceHasSumZero
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (p r : PMF ℕ)
    (hLaplace : ∀ (q : ℝ), 0 < q →
      (∑' n : ℕ, (p n).toReal * Real.exp (-q * (n : ℝ))) =
      (∑' n : ℕ, (r n).toReal * Real.exp (-q * (n : ℝ)))) :
    p = r := by
  have hp : Summable (fun n : ℕ => (p n).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hr : Summable (fun n : ℕ => (r n).toReal) :=
    ENNReal.summable_toReal r.tsum_coe_ne_top
  have hd : Summable (fun n : ℕ =>
      (p n).toReal - (r n).toReal) := hp.sub hr
  have hzero :=
    Kyprianou.Ch01.summablePowerSeriesZeroCoefficientsOfSmallPositiveValues
      (fun n : ℕ => (p n).toReal - (r n).toReal)
      hd (Kyprianou.Ch01.pmfNatLaplaceDifferenceHasSumZero p r hLaplace)
  apply PMF.ext
  intro n
  have hn : (p n).toReal = (r n).toReal :=
    sub_eq_zero.mp (hzero n)
  exact (ENNReal.toReal_eq_toReal_iff'
    (p.apply_ne_top n) (r.apply_ne_top n)).mp hn
