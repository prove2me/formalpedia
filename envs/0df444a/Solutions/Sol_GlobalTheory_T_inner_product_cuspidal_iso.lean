-- Prove2me | solution 1 for GlobalTheory.T.inner_product_cuspidal_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:30.462856+00:00
-- url     : https://prove2.me/submissions/13e74d76-94e5-41cf-8bdd-fbc3e677a5c9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIsoStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_main


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.IpCuspIso := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.IpIso.main | exact GlobalTheory.CompanionTheory.TyFin.IpIso.main | (intros; apply GlobalTheory.CompanionTheory.TyFin.IpIso.main <;> assumption)
end _root_.GlobalTheory.T
