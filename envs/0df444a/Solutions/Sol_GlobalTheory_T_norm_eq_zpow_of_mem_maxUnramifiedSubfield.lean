-- Prove2me | solution 1 for GlobalTheory.T.norm_eq_zpow_of_mem_maxUnramifiedSubfield
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:36.793214+00:00
-- url     : https://prove2.me/submissions/a9bd6ee1-a9ce-48bb-856c-df9450887abd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
import Theorems.Thm_GlobalTheory_UnramValue_norm_of_mem_unramified_subfield


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : Om l), x ∈ K0 K → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by
  first | exact @GlobalTheory.UnramValue.norm_of_mem_unramified_subfield | exact GlobalTheory.UnramValue.norm_of_mem_unramified_subfield | (intros; apply GlobalTheory.UnramValue.norm_of_mem_unramified_subfield <;> assumption)
end _root_.GlobalTheory.T
