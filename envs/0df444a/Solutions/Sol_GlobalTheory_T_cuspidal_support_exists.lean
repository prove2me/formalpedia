-- Prove2me | solution 1 for GlobalTheory.T.cuspidal_support_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:57:14.972455+00:00
-- url     : https://prove2.me/submissions/32b28f74-58fe-4e10-a278-8781e6f38fa7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalSupportExists
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalSupportExistsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSupport_supportExistsAll


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SupportExistsAll := by
  first | exact @GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll | exact GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll | (intros; apply GlobalTheory.CompanionTheory.TyFinSupport.supportExistsAll <;> assumption)
end _root_.GlobalTheory.T
