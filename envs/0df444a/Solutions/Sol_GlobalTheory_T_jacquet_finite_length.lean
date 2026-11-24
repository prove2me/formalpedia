-- Prove2me | solution 1 for GlobalTheory.T.jacquet_finite_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:17:10.668051+00:00
-- url     : https://prove2.me/submissions/7d528634-7900-4ace-9090-057465b1e49b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLengthStatement
import Theorems.Thm_GlobalTheory_JacquetBlocks_jacquetFiniteLength_of_standard


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard | exact GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard | (intros; apply GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard <;> assumption)
end _root_.GlobalTheory.T
