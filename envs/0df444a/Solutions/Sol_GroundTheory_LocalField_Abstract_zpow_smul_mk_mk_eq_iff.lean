-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.zpow_smul_mk_mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:46:19.851937+00:00
-- url     : https://prove2.me/submissions/efab6f32-fddf-49df-8f23-426020d12c46

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Theorems.Thm_GroundTheory_LocalField_Abstract_mk_mk_eq_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger MulAction
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]
omit [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hLK' : L ≤ K') (hK'K : K' ≤ K) (σ x : (K : Subgroup G)) (k : ℤ) :
    ((σ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ k) •
        ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
          _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (x : G)⁻¹ * (σ : G) ^ k * x ∈ (K' : Subgroup G) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
    mk_mk_eq_iff hLK' hK'K]
  have e : (((σ ^ k * x : (K : Subgroup G)) : G))⁻¹ * x = ((x : G)⁻¹ * (σ : G) ^ k * x)⁻¹ := by
    simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
    group
  rw [e, Subgroup.inv_mem_iff]
end GroundTheory.LocalField.Abstract
