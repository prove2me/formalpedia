-- Prove2me | solution 1 for O3.Stage2RouteA.exists_hasDerivAt_line_duality_pair_le_above_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:37:51.166526+00:00
-- url     : https://prove2.me/submissions/9e82f834-d3c3-4551-be45-024a9f0c877e

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_line_duality_pair_at_zero
import Theorems.Thm_O3_Stage2RouteA_lineGradientFormula_eq_duality_pair
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_lineGradientFormula_above_two_of_ne_zero
import Theorems.Thm_O3_Stage2RouteA_lineGradientFormula_deriv_le_above_two

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution
    {q : ℝ} (hq : 2 < q) {d : ℕ} (x h : Point d) (t : ℝ) :
    ∃ v : ℝ,
      HasDerivAt (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h) v t ∧
        v ≤ (q - 1) * (lpNorm q h) ^ (2 : ℕ) := by
  by_cases hz : x + t • h = 0
  · refine ⟨(lpNorm q h) ^ (2 : ℕ),
      hasDerivAt_line_duality_pair_at_zero (by linarith : 1 < q) x h t hz, ?_⟩
    have hn : 0 ≤ (lpNorm q h) ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  · let v : ℝ :=
      (2 - q) * linePower q x h t ^ (2 / q - 2) *
          linePowerPair q x h t ^ (2 : ℕ) +
        (q - 1) * linePower q x h t ^ (2 / q - 1) *
          weightedSquareSum q x h t
    have hformula : HasDerivAt (lineGradientFormula q x h) v t := by
      exact hasDerivAt_lineGradientFormula_above_two_of_ne_zero hq x h t hz
    have hcont : ContinuousAt (fun s : ℝ ↦ x + s • h) t := by fun_prop
    have hne : ∀ᶠ s in nhds t, x + s • h ≠ 0 := hcont.eventually_ne hz
    have heq :
        (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h) =ᶠ[nhds t]
          lineGradientFormula q x h := by
      filter_upwards [hne] with s hs
      exact (lineGradientFormula_eq_duality_pair (by linarith : q ≠ 0)
        x h s hs).symm
    refine ⟨v, hformula.congr_of_eventuallyEq heq, ?_⟩
    exact lineGradientFormula_deriv_le_above_two hq x h t hz
end O3.Stage2RouteA
