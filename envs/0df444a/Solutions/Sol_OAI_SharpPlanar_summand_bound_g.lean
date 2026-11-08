-- Prove2me | solution 1 for OAI.SharpPlanar.summand_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:26:35.961207+00:00
-- url     : https://prove2.me/submissions/f090bade-4f70-4ead-8689-127c93a131df

import Mathlib
import Definitions.Def_OAIQ098G002
import Theorems.Thm_OAI_SharpPlanar_u_bound_g
import Theorems.Thm_OAI_SharpPlanar_v_bound_g

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

lemma v_bound' (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ densityBound := by
  apply (v_bound_g n j ht).trans
  unfold densityBound
  nlinarith [Real.pi_gt_three]

lemma summand_bound_g_oai (x : X) (n : Node) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(x (n, false) : ℂ) * u n.val j t + (x (n, true) : ℂ) * v n.val j t‖ ≤
      densityBound * (|x (n, false)| + |x (n, true)|) := by
  calc
    _ ≤ ‖(x (n, false) : ℂ) * u n.val j t‖ + ‖(x (n, true) : ℂ) * v n.val j t‖ := norm_add_le _ _
    _ = |x (n, false)| * ‖u n.val j t‖ + |x (n, true)| * ‖v n.val j t‖ := by
      simp [Complex.norm_real]
    _ ≤ |x (n, false)| * densityBound + |x (n, true)| * densityBound := by
      gcongr
      exacts [u_bound_g _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.summand_bound_g_oai := @OAI.SharpPlanar.summand_bound_g_oai
