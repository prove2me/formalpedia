-- Prove2me | solution 1 for GlobalTheory.T.central_idempotent_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:29:21.780201+00:00
-- url     : https://prove2.me/submissions/b6e42d7c-dcd5-49c9-8bae-12dc3d5cf6dc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentProperties
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentPropertiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_zIdemFacts


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.zIdemFacts | exact GlobalTheory.CompanionTheory.TyFin.zIdemFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.zIdemFacts <;> assumption)
end _root_.GlobalTheory.T
