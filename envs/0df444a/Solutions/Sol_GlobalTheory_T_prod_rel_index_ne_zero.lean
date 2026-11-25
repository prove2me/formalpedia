-- Prove2me | solution 1 for GlobalTheory.T.prod_rel_index_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:06.698639+00:00
-- url     : https://prove2.me/submissions/1a073b93-1f1a-4e73-8f45-470ea419e4ea

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdRelIndexNeZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdRelIndexNeZeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_GroupIndex_RelProd_relIndex_prod_ne_zero_of_ne_zero


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
theorem _root_.solution : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂), I₁.relIndex K₁ ≠ 0 → I₂.relIndex K₂ ≠ 0 → (I₁.prod I₂).relIndex (K₁.prod K₂) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | exact GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero | (intros; apply GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_ne_zero_of_ne_zero <;> assumption)
end _root_.GlobalTheory.T
