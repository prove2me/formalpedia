-- Prove2me | solution 1 for OAI.SharpPlanar.disk_coordinate_bounds_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:15:04.629198+00:00
-- url     : https://prove2.me/submissions/6a8fbfab-2bdd-42c6-9fc4-7ec725cf1d2d

import Mathlib
import Definitions.Def_OAIQ098G072

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

lemma disk_coordinate_bounds_g_oai {j : ℕ} (hj : j < 6) {t : ℂ}
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

theorem solution : type_of% @OAI.SharpPlanar.disk_coordinate_bounds_g_oai := @OAI.SharpPlanar.disk_coordinate_bounds_g_oai
