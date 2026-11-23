-- Prove2me | solution 1 for GlobalTheory.SmGL.FinitenessModel.hasFiniteLength_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:13.680133+00:00
-- url     : https://prove2.me/submissions/c70cb3db-a0d4-465e-84ef-feaab6227e79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional

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
namespace GlobalTheory.SmGL.FinitenessModel
theorem _root_.solution {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ G V) : HasFiniteLength π := by
  let φ : Subrepresentation π ↪o Submodule ℂ V :=
    ⟨⟨Subrepresentation.toSubmodule, Subrepresentation.toSubmodule_injective⟩, Iff.rfl⟩
  exact (hasFiniteLength_iff_wellFounded π).2 ⟨φ.wellFoundedGT, φ.wellFoundedLT⟩
end GlobalTheory.SmGL.FinitenessModel
