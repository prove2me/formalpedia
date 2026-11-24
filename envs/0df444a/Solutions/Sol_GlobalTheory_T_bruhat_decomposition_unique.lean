-- Prove2me | solution 1 for GlobalTheory.T.bruhat_decomposition_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:04:09.752745+00:00
-- url     : https://prove2.me/submissions/171f228b-1fa7-48fa-9abe-1045cc4cf3a5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUniqueStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_bruhatUniq


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.BruhatUniq := by
  first | exact @GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq | exact GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq | (intros; apply GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq <;> assumption)
end _root_.GlobalTheory.T
