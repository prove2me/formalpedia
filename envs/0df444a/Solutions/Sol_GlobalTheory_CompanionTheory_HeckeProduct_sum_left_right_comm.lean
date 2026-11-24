-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeProduct.sum_left_right_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:39.266+00:00
-- url     : https://prove2.me/submissions/2c6b3635-06a5-439c-b19c-d493788d4c8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_map_heckeSum
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_heckeLin_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_left_right_comm

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
    (hf' : (Function.support fun q : G₂ ⧸ K₂ => f' q.out).Finite) (u : V) :
    heckeSum (left ρ) K₁ f (heckeSum (right ρ) K₂ f' u)
      = heckeSum (right ρ) K₂ f' (heckeSum (left ρ) K₁ f u) := by
  rw [← heckeLin_apply (left ρ) K₁ hf, ← heckeLin_apply (left ρ) K₁ hf]
  refine map_heckeSum (right ρ) K₂ hf' _ (fun h w => ?_) u
  rw [heckeLin_apply (left ρ) K₁ hf, heckeLin_apply (left ρ) K₁ hf]
  exact map_heckeSum (left ρ) K₁ hf (right ρ h) (fun g w => (left_right_comm ρ g h w).symm) w |>.symm
end GlobalTheory.CompanionTheory.HeckeProduct
