-- Prove2me | solution 1 for O3.Stage2RouteD.lpNorm_squareVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:32.992048+00:00
-- url     : https://prove2.me/submissions/076d9f65-5bd4-4975-b812-f168d8ce1699

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {q : ℝ} (hq : 0 < q) {d : ℕ} (h : Point d) :
    lpNorm (q / 2) (squareVector h) = (lpNorm q h) ^ (2 : ℕ) := by
  have hq0 : q ≠ 0 := hq.ne'
  unfold lpNorm lpPower squareVector
  have hsum :
      (∑ i, |(h i) ^ (2 : ℕ)| ^ (q / 2)) = ∑ i, |h i| ^ q := by
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_pow, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (abs_nonneg (h i))]
    congr 1
    ring
  rw [hsum, ← Real.rpow_two]
  have hS : 0 ≤ ∑ i, |h i| ^ q :=
    Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (h i)) q
  rw [← Real.rpow_mul hS]
  congr 1
  field_simp
end O3.Stage2RouteD
