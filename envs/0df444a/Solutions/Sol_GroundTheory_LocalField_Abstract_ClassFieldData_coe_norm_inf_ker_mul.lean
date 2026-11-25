-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_inf_ker_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:31.026797+00:00
-- url     : https://prove2.me/submissions/4b49b4d1-b31a-44e5-9bf7-5cf01d51e7cc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution {y z : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hz : z ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨y * z, Subgroup.mul_mem _ hy hz⟩ : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨y, hy⟩ : A) *
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨z, hz⟩ := by
  have h : (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
      ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
  rw [h, map_mul]
  rfl
end GroundTheory.LocalField.Abstract.ClassFieldData
