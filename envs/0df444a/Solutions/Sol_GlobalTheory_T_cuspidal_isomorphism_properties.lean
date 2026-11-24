-- Prove2me | solution 1 for GlobalTheory.T.cuspidal_isomorphism_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:28:57.670729+00:00
-- url     : https://prove2.me/submissions/406e1d01-8fa2-4685-a380-6792684e8c08

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismPropertiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_cuspIsoFacts


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts | exact GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts <;> assumption)
end _root_.GlobalTheory.T
