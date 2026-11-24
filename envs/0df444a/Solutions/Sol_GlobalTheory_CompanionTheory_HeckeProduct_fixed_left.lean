-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.fixed_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:37:01.458961+00:00
-- url     : https://prove2.me/submissions/fba954b8-00ec-4926-a553-96865aaff295

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_map_heckeSum
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_heckeSum_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_left_right_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_left_right_mul

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
variable {f : G₁ → ℂ} {f' : G₂ → ℂ}
namespace GlobalTheory.CompanionTheory.HeckeProduct
theorem _root_.solution (hf : (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite)
    (hl : ∀ k ∈ K₁, ∀ g, f (k * g) = f g) (hr : ∀ k ∈ K₁, ∀ g, f (g * k) = f g)
    (u : V) (hu : ∀ k ∈ K₁.prod K₂, ρ k u = u) :
    ∀ c ∈ K₁.prod K₂, ρ c (heckeSum (left ρ) K₁ f u) = heckeSum (left ρ) K₁ f u := by
  rintro ⟨c₁, c₂⟩ hc
  have hc' := Subgroup.mem_prod.1 hc
  have hu₁ : ∀ k ∈ K₁, left ρ k u = u := fun k hk =>
    hu (k, 1) (Subgroup.mem_prod.2 ⟨hk, K₂.one_mem⟩)
  have hu₂ : right ρ c₂ u = u := hu (1, c₂) (Subgroup.mem_prod.2 ⟨K₁.one_mem, hc'.2⟩)
  rw [left_right_mul, map_heckeSum (left ρ) K₁ hf (right ρ c₂)
    (fun g w => (left_right_comm ρ g c₂ w).symm), hu₂]
  exact heckeSum_fixed (left ρ) K₁ hf hl hr u hu₁ c₁ hc'.1
end GlobalTheory.CompanionTheory.HeckeProduct
