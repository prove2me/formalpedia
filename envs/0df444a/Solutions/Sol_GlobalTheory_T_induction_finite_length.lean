-- Prove2me | solution 1 for GlobalTheory.T.induction_finite_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:32.872946+00:00
-- url     : https://prove2.me/submissions/bfeb1bca-5e63-4327-b502-cafcf9f86862

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLengthStatement
import Theorems.Thm_GlobalTheory_inductionFiniteLength_of_standard


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
theorem _root_.solution : GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionFiniteLength k := by
  first | exact @GlobalTheory.inductionFiniteLength_of_standard | exact GlobalTheory.inductionFiniteLength_of_standard | (intros; apply GlobalTheory.inductionFiniteLength_of_standard <;> assumption)
end _root_.GlobalTheory.T
