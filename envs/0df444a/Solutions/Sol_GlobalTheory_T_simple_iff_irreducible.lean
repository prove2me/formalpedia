-- Prove2me | solution 1 for GlobalTheory.T.simple_iff_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:02:34.466352+00:00
-- url     : https://prove2.me/submissions/60efc0ca-70b8-41e8-9670-6d3089be2f8b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_simpleIffIrr


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | exact GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | (intros; apply GlobalTheory.CompanionTheory.TyFin.simpleIffIrr <;> assumption)
end _root_.GlobalTheory.T
