-- Prove2me | solution 1 for GlobalTheory.SmGL.FinitenessModel.not_hasFiniteLength_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:11:59.681918+00:00
-- url     : https://prove2.me/submissions/bb923400-8098-4a83-b807-b1e66dbafacb

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.FinitenessModel
theorem _root_.solution :
    IsSmooth (Representation.trivial ℂ (GL n k) (ℕ →₀ ℂ)) ∧
      ¬ HasFiniteLength (Representation.trivial ℂ (GL n k) (ℕ →₀ ℂ)) := by
  refine ⟨fun v => by simp, fun h => ?_⟩
  have h1 := ((hasFiniteLength_iff_wellFounded _).1 h).1
  let φ : Submodule ℂ (ℕ →₀ ℂ) ↪o Subrepresentation (Representation.trivial ℂ (GL n k) (ℕ →₀ ℂ)) :=
    ⟨⟨fun S => ⟨S, fun g v hv => by simpa using hv⟩,
      fun a b hab => congrArg Subrepresentation.toSubmodule hab⟩, Iff.rfl⟩
  haveI : IsNoetherian ℂ (ℕ →₀ ℂ) := isNoetherian_iff'.2 φ.wellFoundedGT
  exact Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (R := ℂ) (ι := ℕ))
    inferInstance
end GlobalTheory.SmGL.FinitenessModel
