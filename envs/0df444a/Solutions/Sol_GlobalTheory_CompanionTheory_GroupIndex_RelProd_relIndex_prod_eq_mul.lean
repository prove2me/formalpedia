-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:21.537956+00:00
-- url     : https://prove2.me/submissions/4652d0b2-63db-413e-867e-1a291a9ada51

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdRelIndexNeZero

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
theorem _root_.solution {G₁ G₂ : Type} [Group G₁] [Group G₂]
    (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂) :
    (I₁.prod I₂).relIndex (K₁.prod K₂) = I₁.relIndex K₁ * I₂.relIndex K₂ := by
  have hmap : ((I₁.prod I₂).subgroupOf (K₁.prod K₂)) =
      ((I₁.subgroupOf K₁).prod (I₂.subgroupOf K₂)).comap
        (Subgroup.prodEquiv K₁ K₂).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod, Subgroup.mem_comap]
    exact Iff.rfl
  unfold Subgroup.relIndex
  rw [hmap, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv K₁ K₂).surjective,
    Subgroup.index_prod]
end GlobalTheory.CompanionTheory.GroupIndex.RelProd
