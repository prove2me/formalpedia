-- Prove2me | solution 1 for GlobalTheory.T.finiteDimensional_fixed_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:20:54.339401+00:00
-- url     : https://prove2.me/submissions/cb21d648-b4a8-4075-b213-62a4fb2e7045

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalFixedTensor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalFixedTensorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ExtTensorFixed_finiteDimensional_fixed_extTensor


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
theorem _root_.solution : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (K₁ : Subgroup G) (K₂ : Subgroup H), FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K₁) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K₂) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed (GlobalTheory.SmGL.extTensor ρ σ) (K₁.prod K₂)) := by
  first | exact @GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor | exact GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor | (intros; apply GlobalTheory.CompanionTheory.ExtTensorFixed.finiteDimensional_fixed_extTensor <;> assumption)
end _root_.GlobalTheory.T
