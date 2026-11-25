-- Prove2me | solution 1 for GlobalTheory.T.cuspidal_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:31.131973+00:00
-- url     : https://prove2.me/submissions/a02c4a59-93ed-484f-85bf-29627e7575ff

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_cuspVanish


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.CuspVanish := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish | exact GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish <;> assumption)
end _root_.GlobalTheory.T
