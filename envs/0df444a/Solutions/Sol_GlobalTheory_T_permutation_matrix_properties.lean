-- Prove2me | solution 1 for GlobalTheory.T.permutation_matrix_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:05:33.391465+00:00
-- url     : https://prove2.me/submissions/60c38e29-57cb-4695-85af-fa79bd645380

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_pmFacts


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.PmFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts | exact GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts <;> assumption)
end _root_.GlobalTheory.T
