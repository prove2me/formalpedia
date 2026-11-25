-- Prove2me | solution 1 for GlobalTheory.T.product_simple_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:36.096015+00:00
-- url     : https://prove2.me/submissions/878f7da7-a89e-4c1c-8dd8-c001181acfb4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_prodSimpleAll


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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.ProdSimpleAll := by
  first | exact @GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll | exact GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll | (intros; apply GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll <;> assumption)
end _root_.GlobalTheory.T
