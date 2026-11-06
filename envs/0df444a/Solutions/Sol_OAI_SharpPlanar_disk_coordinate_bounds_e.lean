-- Prove2me | solution 1 for OAI.SharpPlanar.disk_coordinate_bounds_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:35:43.120473+00:00
-- url     : https://prove2.me/submissions/08d3feb8-00a6-4865-b7ef-0307410fc006

import Mathlib
import Definitions.Def_OAIQ098E018

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open Complex

lemma disk_coordinate_bounds_e_oai {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖t‖ ≤ 13/12 ∧ -(1/6:ℝ) ≤ t.im ∧ t.im ≤ 1/6 := by
  have hc0 : 0 ≤ diskCenter j := by unfold diskCenter; positivity
  have hc1 : diskCenter j ≤ 11/12 := by
    unfold diskCenter
    have : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
    linarith
  have hi := (Complex.abs_im_le_norm (t-(diskCenter j:ℂ))).trans ht
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,abs_le] at hi
  refine ⟨?_, hi⟩
  have hn := norm_add_le (t-(diskCenter j:ℂ)) (diskCenter j:ℂ)
  rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0] at hn
  linarith

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.disk_coordinate_bounds_e_oai := @OAI.SharpPlanar.disk_coordinate_bounds_e_oai
