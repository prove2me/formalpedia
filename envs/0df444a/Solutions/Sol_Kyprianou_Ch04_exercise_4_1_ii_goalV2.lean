-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_1_ii_goalV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:21:20.826824+00:00
-- url     : https://prove2.me/submissions/b39cfbfa-d86f-4797-9a14-55c035ab0fd1

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_1CertificationV2
import Theorems.Thm_Kyprianou_Ch04_exercise41ContinuousLedgerV7
import Theorems.Thm_Kyprianou_Ch04_exercise41BoundaryLedgersV7
import Theorems.Thm_Kyprianou_Ch04_exercise41FinalAssemblyV7
open MeasureTheory Filter Set AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Combine the continuous and boundary ledgers on their common full-measure set. -/
theorem solution : certificate_ex4_1_ii_v2 := by
  classical
  unfold certificate_ex4_1_ii_v2
  intro Ω m P F L hBV hd Xleft hLeft f fLeft fRight
    hC1Left hC1Right hPieceLeft hPieceRight
  filter_upwards [
    exercise41ContinuousLedgerV7 P F L hBV hd Xleft hLeft
      fLeft fRight hC1Left hC1Right,
    exercise41BoundaryLedgersV7 P F L hBV hd Xleft hLeft
  ] with w hc hb
  intro hVisits t
  exact exercise41FinalAssemblyV7 _ f fLeft fRight hPieceLeft hPieceRight
    (L.X 0 w) (L.X t w) _ (fun z : ℝ × ℝ => Xleft z.1.toNNReal w)
    (fun z : ℝ × ℝ => Xleft z.1.toNNReal w + z.2) (fun s => Xleft s w)
    t (hVisits t).toFinset (hc t) (hb hVisits t)
