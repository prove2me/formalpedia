-- Prove2me | solution 1 for GlobalTheory.T.intertwiner_inner_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:15:06.732235+00:00
-- url     : https://prove2.me/submissions/9cc17eca-eb51-48df-b5d9-f7093b7a45ca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProduct
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProductStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_intwIp


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.IntwIp := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.intwIp | exact GlobalTheory.CompanionTheory.TyFin.intwIp | (intros; apply GlobalTheory.CompanionTheory.TyFin.intwIp <;> assumption)
end _root_.GlobalTheory.T
