-- Prove2me | solution 1 for GlobalTheory.T.harish_chandra_dimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:12:23.06809+00:00
-- url     : https://prove2.me/submissions/280f2372-c79f-4e8b-8bb7-33079d124abc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimension
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimensionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_hcDim


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.HCDim := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.hcDim | exact GlobalTheory.CompanionTheory.TyFin.hcDim | (intros; apply GlobalTheory.CompanionTheory.TyFin.hcDim <;> assumption)
end _root_.GlobalTheory.T
