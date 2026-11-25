-- Prove2me | solution 1 for GlobalTheory.T.separable_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:39.443139+00:00
-- url     : https://prove2.me/submissions/8c4ec98a-8467-42c0-9da2-f207c8c4f1fd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducibleStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FinRep_sepIrr


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  first | exact @GlobalTheory.CompanionTheory.FinRep.sepIrr | exact GlobalTheory.CompanionTheory.FinRep.sepIrr | (intros; apply GlobalTheory.CompanionTheory.FinRep.sepIrr <;> assumption)
end _root_.GlobalTheory.T
