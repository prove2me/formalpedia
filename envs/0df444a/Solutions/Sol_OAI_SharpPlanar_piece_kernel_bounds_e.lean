-- Prove2me | solution 1 for OAI.SharpPlanar.piece_kernel_bounds_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T20:23:20.536148+00:00
-- url     : https://prove2.me/submissions/95da754e-1a90-465e-ba49-c8fb6ec1ab96

import Mathlib
import Definitions.Def_OAIQ098E125
import Theorems.Thm_OAI_SharpPlanar_endpoint_kernel_bounds_e
import Theorems.Thm_OAI_SharpPlanar_lambda_sq_antitone_e
import Theorems.Thm_OAI_SharpPlanar_piece_damping_bound_e
import Theorems.Thm_OAI_SharpPlanar_z_sq_antitone_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma piece_kernel_bounds_e_oai (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖lambda t‖ ≤ lambdaCap ⟨j.val,by omega⟩ ∧
    ‖z t‖ ≤ zCap ⟨j.val,by omega⟩ ∧
    dampingCap ⟨j.val+1,by omega⟩+slopeCap j*(((j.val:ℝ)+1)/6-t) ≤ (z t).im := by
  have hs : 0 ≤ (j.val:ℝ)/6 := by positivity
  have hb := (endpoint_kernel_bounds_e ⟨j.val,by omega⟩).1
  have ha := (endpoint_kernel_bounds_e ⟨j.val,by omega⟩).2.1
  refine ⟨?_,?_,piece_damping_bound_e j ht⟩
  · exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (lambda_sq_antitone_e hs ht.1)).trans hb
  · exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (z_sq_antitone_e hs ht.1)).trans ha

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.piece_kernel_bounds_e_oai := @OAI.SharpPlanar.piece_kernel_bounds_e_oai
