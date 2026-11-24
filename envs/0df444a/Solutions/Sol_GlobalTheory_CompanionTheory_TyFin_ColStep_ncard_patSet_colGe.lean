-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:29:03.217825+00:00
-- url     : https://prove2.me/submissions/f6ffd30a-1e86-4a2a-8e48-69d76460e82c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStep
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_isPat_colGe
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_natCard_colGe
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_card_patSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep
namespace GlobalTheory.CompanionTheory.TyFin.ColStep
theorem _root_.solution (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (hj : j < d) :
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by
  rw [GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d j), GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d (j + 1)),
    natCard_colGe d j hj, pow_add]
end GlobalTheory.CompanionTheory.TyFin.ColStep
