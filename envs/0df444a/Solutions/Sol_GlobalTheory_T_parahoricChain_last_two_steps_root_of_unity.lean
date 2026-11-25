-- Prove2me | solution 1 for GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:32.258471+00:00
-- url     : https://prove2.me/submissions/5d1f4016-48bb-40ee-b09e-a967ac6adc5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ParahoricChainLastTwoStepsRootOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ParahoricChainLastTwoStepsRootOfUnityStatement
import Theorems.Thm_GlobalTheory_LevelLaw_last_steps_law


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → ∀ g : GL (XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : XIx κ t (s + 1) → k) x, (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  first | exact @GlobalTheory.LevelLaw.last_steps_law | exact GlobalTheory.LevelLaw.last_steps_law | (intros; apply GlobalTheory.LevelLaw.last_steps_law <;> assumption)
end _root_.GlobalTheory.T
