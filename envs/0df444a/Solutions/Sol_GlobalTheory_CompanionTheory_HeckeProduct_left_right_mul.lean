-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.left_right_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:40.891509+00:00
-- url     : https://prove2.me/submissions/841ed3bc-b34c-4bf6-a0fa-99dc7c3eb938

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeProduct
variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
namespace GlobalTheory.CompanionTheory.HeckeProduct
theorem _root_.solution (g : G₁) (h : G₂) (u : V) :
    ρ (g, h) u = left ρ g (right ρ h u) := by
  have : ((g, h) : G₁ × G₂) = (g, 1) * (1, h) := by simp
  rw [this, map_mul]; rfl
end GlobalTheory.CompanionTheory.HeckeProduct
