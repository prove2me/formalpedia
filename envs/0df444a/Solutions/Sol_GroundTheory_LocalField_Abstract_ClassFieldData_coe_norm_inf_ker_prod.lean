-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_inf_ker_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:01.044832+00:00
-- url     : https://prove2.me/submissions/b8d98210-e27d-49ac-8bd4-23e8bd4204be

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
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
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i, f i ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ : A) =
      ∏ i ∈ s, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨f i, hf i⟩ : A) := by
  have h : (⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ :
      fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ∏ i ∈ s, ⟨f i, hf i⟩ := by
    ext
    simp
  rw [h, map_prod]
  simp
end GroundTheory.LocalField.Abstract.ClassFieldData
