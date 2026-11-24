-- Prove2me | solution 1 for GlobalTheory.T.pattern_set_card_column_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:15.396323+00:00
-- url     : https://prove2.me/submissions/03f94ade-fcce-42cb-b565-b4f38a3c8c5d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStep
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStepStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_ncard_patSet_colGe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j < d →
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe | exact GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe <;> assumption)
end _root_.GlobalTheory.T
