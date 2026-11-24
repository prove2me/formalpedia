-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:56.515795+00:00
-- url     : https://prove2.me/submissions/59a4b0f6-a63e-4afe-b971-df009ebe66a3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdRelIndexNeZero
import Theorems.Thm_GlobalTheory_CompanionTheory_GroupIndex_RelProd_relIndex_prod_eq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GroupIndex GlobalTheory.CompanionTheory.GroupIndex.RelProd
namespace GlobalTheory.CompanionTheory.GroupIndex.RelProd
theorem _root_.solution :
    ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂),
      I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  intro G₁ G₂ _ _ I₁ K₁ I₂ K₂ h₁ h₂
  rw [relIndex_prod_eq_mul]
  exact mul_ne_zero h₁ h₂
end GlobalTheory.CompanionTheory.GroupIndex.RelProd
