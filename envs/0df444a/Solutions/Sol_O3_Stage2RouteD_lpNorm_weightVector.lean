-- Prove2me | solution 1 for O3.Stage2RouteD.lpNorm_weightVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:28.250898+00:00
-- url     : https://prove2.me/submissions/5c1259bf-18a2-426f-b2e1-cbfd036b9262

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {q : ℝ} (hq : 2 < q) {d : ℕ} (z : Point d) :
    lpNorm (q / (q - 2)) (weightVector q z) =
      (lpNorm q z) ^ (q - 2) := by
  have hq0 : q ≠ 0 := by linarith
  have hqm : q - 2 ≠ 0 := by linarith
  unfold lpNorm lpPower weightVector
  have hsum :
      (∑ i, |(|z i| ^ (q - 2))| ^ (q / (q - 2))) =
        ∑ i, |z i| ^ q := by
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (z i)) _)]
    rw [← Real.rpow_mul (abs_nonneg (z i))]
    congr 1
    field_simp
  rw [hsum]
  have hS : 0 ≤ ∑ i, |z i| ^ q :=
    Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (z i)) q
  rw [← Real.rpow_mul hS]
  congr 1
  field_simp
end O3.Stage2RouteD
