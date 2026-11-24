-- Prove2me | solution 1 for GlobalTheory.FockAdj.fockQ_word_rowAct_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:41.945468+00:00
-- url     : https://prove2.me/submissions/b512f4b9-ba57-44e5-8ab9-58196c9d4ffb

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FockQWordRowActAdj
import Theorems.Thm_GlobalTheory_FockAdj_fockQ_applyWord
import Theorems.Thm_GlobalTheory_FockAdj_fockQ_rowAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open GlobalTheory GlobalTheory.FockAdj
namespace GlobalTheory.FockAdj
theorem _root_.solution : Formalism.GradedWeylDivisibility.FockQWordAdj ∧ Formalism.GradedWeylDivisibility.FockQRowAct :=
  ⟨fockQ_applyWord, fockQ_rowAct⟩
end GlobalTheory.FockAdj
