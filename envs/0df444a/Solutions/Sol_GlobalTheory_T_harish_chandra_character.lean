-- Prove2me | solution 1 for GlobalTheory.T.harish_chandra_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:21.569603+00:00
-- url     : https://prove2.me/submissions/afd18158-e74b-44e1-b6d3-b4254885c99a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FinGLChar_hcChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.HCChar := by
  first | exact @GlobalTheory.CompanionTheory.FinGLChar.hcChar | exact GlobalTheory.CompanionTheory.FinGLChar.hcChar | (intros; apply GlobalTheory.CompanionTheory.FinGLChar.hcChar <;> assumption)
end _root_.GlobalTheory.T
