-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.left_right_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:37.973945+00:00
-- url     : https://prove2.me/submissions/48828968-4b28-4a3c-abd4-44a393fd324a

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
    left ρ g (right ρ h u) = right ρ h (left ρ g u) := by
  have e1 : left ρ g (right ρ h u) = ρ ((g, 1) * (1, h)) u := by
    rw [map_mul]; rfl
  have e2 : right ρ h (left ρ g u) = ρ ((1, h) * (g, 1)) u := by
    rw [map_mul]; rfl
  rw [e1, e2]; simp
end GlobalTheory.CompanionTheory.HeckeProduct
