-- Prove2me | solution 1 for GlobalTheory.T.squarefree_dimension_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:17.72037+00:00
-- url     : https://prove2.me/submissions/57f4cf80-1a1c-47e0-b404-864eab66d834

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquarefreeDimensionFormula
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquarefreeDimensionFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_sqfreeDimAll


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SqfreeDimAll := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll | exact GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll | (intros; apply GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll <;> assumption)
end _root_.GlobalTheory.T
