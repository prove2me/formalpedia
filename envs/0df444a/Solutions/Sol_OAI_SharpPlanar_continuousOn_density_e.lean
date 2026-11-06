-- Prove2me | solution 1 for OAI.SharpPlanar.continuousOn_density_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:34:57.888663+00:00
-- url     : https://prove2.me/submissions/7a164f87-481b-4fac-beeb-6db2fdd584fa

import Mathlib
import Definitions.Def_OAIQ098E002
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_e
import Theorems.Thm_OAI_SharpPlanar_summand_bound_e

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


lemma continuous_u (n j : ℕ) : Continuous (u n j) := by
  unfold u
  fun_prop

lemma continuous_v (n j : ℕ) : Continuous (v n j) := by
  unfold v
  fun_prop

lemma continuousOn_density_e_oai (p : CardinalData) (j : ℕ) :
    ContinuousOn (density p j) (Set.Icc (0 : ℝ) 1) := by
  unfold density
  refine ((continuous_const.mul (continuous_u 0 j)).add
    (continuous_const.mul (continuous_v 0 j))).continuousOn.add ?_
  apply continuousOn_tsum (u := fun n : Node =>
    densityBound * (|p.x (n, false)| + |p.x (n, true)|))
  · intro n
    exact ((continuous_const.mul (continuous_u n.val j)).add
      (continuous_const.mul (continuous_v n.val j))).continuousOn
  · exact (X_summable_pairs_e p.x).mul_left densityBound
  · intro n t ht
    exact summand_bound_e p.x n j ht

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.continuousOn_density_e_oai := @OAI.SharpPlanar.continuousOn_density_e_oai
