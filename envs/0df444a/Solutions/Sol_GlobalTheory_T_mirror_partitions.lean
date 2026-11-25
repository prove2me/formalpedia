-- Prove2me | solution 1 for GlobalTheory.T.mirror_partitions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:27.302502+00:00
-- url     : https://prove2.me/submissions/f47455d6-3bc6-418c-aca6-1e939bc07f65

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitions
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MirrorPartitionsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_main
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Mirrors_main


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.MirrorsOf := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Mirrors.main | exact GlobalTheory.CompanionTheory.TyFin.Mirrors.main | (intros; apply GlobalTheory.CompanionTheory.TyFin.Mirrors.main <;> assumption)
end _root_.GlobalTheory.T
