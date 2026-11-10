-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:11:56.757767+00:00
-- url     : https://prove2.me/submissions/01775d32-91de-473d-9f24-dbc6dd445343

import Mathlib
import Definitions.Def_OAIQ098G322
import Definitions.Def_OAIQ098G364
import Definitions.Def_OAIQ098G365
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aLookup_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bLookup_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_density_check_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_uAmplitudeBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_vAmplitudeBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_norm_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma amplitude_endpoints_g_oai (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) :
    ‖uAmplitude n j.val ((j.val:ℝ)/6)‖ ≤ densityCap j ∧
    ‖uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ ≤ densityCap j ∧
    ‖vAmplitude n j.val‖ ≤ densityCap j := by
  obtain ⟨hc0,hc1,hcv⟩ := density_check_g n hn j
  have ha := aLookup_contains_g n j
  have hb := bLookup_contains_g n j
  refine ⟨?_,?_,CBox.norm_le_rat_g (vAmplitudeBox_contains_g ha) hcv⟩
  · exact CBox.norm_le_rat_g
      (uAmplitudeBox_contains_g (by simpa using RBox.contains_rat_g j.val 6 (by norm_num)) ha hb) hc0
  · exact CBox.norm_le_rat_g
      (uAmplitudeBox_contains_g (by simpa using RBox.contains_rat_g (j.val+1) 6 (by norm_num)) ha hb) hc1

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_g_oai := @OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_g_oai
