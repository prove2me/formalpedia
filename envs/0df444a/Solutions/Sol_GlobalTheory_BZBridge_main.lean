-- Prove2me | solution 1 for GlobalTheory.BZBridge.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:27.746803+00:00
-- url     : https://prove2.me/submissions/3df56d28-d953-473d-88ea-8b6b1fe4a12b

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLengthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleAdmissible
import Theorems.Thm_GlobalTheory_BZBridge_irreducibleAdmissible
import Theorems.Thm_GlobalTheory_SmGL_IndDual_inductionContragredient
import Theorems.Thm_GlobalTheory_T_induction_finite_length
import Theorems.Thm_GlobalTheory_T_jacquet_finite_length


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BZBridge
namespace GlobalTheory.BZBridge
theorem _root_.solution : GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength →
    GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  intro hA hS k _ _ _ _
  exact ⟨irreducibleAdmissible hA k, GlobalTheory.T.jacquet_finite_length hS k, GlobalTheory.T.induction_finite_length hS k,
    GlobalTheory.SmGL.IndDual.inductionContragredient k⟩
end GlobalTheory.BZBridge
