-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Quadratic.combine_quadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T18:47:12.70217+00:00
-- url     : https://prove2.me/submissions/a7b6297a-4580-41fe-ab67-88c5e67199ff

import Mathlib

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates00
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite matrix certificates for the quadratic coupling estimate. -/

namespace PositiveEinsteinFour.Quadratic

noncomputable section

private theorem combine_quadratic_sums (L : List (ℝ × ℝ × ℝ × ℝ)) (x y : ℝ) :
    (L.map (fun a => a.1 * a.2.2.2)).sum * x ^ 2 +
      2 * (L.map (fun a => a.2.2.1 * a.2.2.2)).sum * x * y +
      (L.map (fun a => a.2.1 * a.2.2.2)).sum * y ^ 2 =
      (L.map (fun a => (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rcases a with ⟨r, h, q, w⟩
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    ring

private theorem combine_quadratic_nonneg_oai (L : List (ℝ × ℝ × ℝ × ℝ)) (x y : ℝ)
    (h : L.Forall (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2)) :
    0 ≤ (L.map (fun a => a.1 * a.2.2.2)).sum * x ^ 2 +
      2 * (L.map (fun a => a.2.2.1 * a.2.2.2)).sum * x * y +
      (L.map (fun a => a.2.1 * a.2.2.2)).sum * y ^ 2 := by
  rw [combine_quadratic_sums]
  apply List.sum_nonneg
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact (List.forall_iff_forall_mem.mp h) a ha

end

end PositiveEinsteinFour.Quadratic
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Quadratic.combine_quadratic_nonneg_oai := @OAI.PositiveEinsteinFour.Quadratic.combine_quadratic_nonneg_oai
