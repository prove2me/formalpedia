-- Prove2me | solution 1 for GlobalTheory.SmGL.FinitenessModel.hasFiniteLength_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:01.493424+00:00
-- url     : https://prove2.me/submissions/8d6b0436-c480-41fe-b8ce-64337a2a3438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional
import Theorems.Thm_GlobalTheory_SmGL_FinitenessModel_hasFiniteLength_of_finiteDimensional

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
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.FinitenessModel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.FinitenessModel
theorem _root_.solution (e : (Σ a, m a) ≃ n) {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ (GL n k) V) : HasFiniteLength (jac e π) :=
  hasFiniteLength_of_finiteDimensional _
end GlobalTheory.SmGL.FinitenessModel
