-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.mk_mem_range_galRestrict_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:29.049966+00:00
-- url     : https://prove2.me/submissions/f0db1c2d-aa6d-4ec1-854a-3f46727c202a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_galRestrict_mk
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
theorem _root_.solution (hLK' : L ≤ K') (hK'K : K' ≤ K) (k : (K : Subgroup G)) :
    (k : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
      (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range ↔
      (k : G) ∈ (K' : Subgroup G) := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H k' =>
      rw [galRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      have h := (K' : Subgroup G).mul_mem k'.2 (hLK' hq)
      simpa using h
  · intro hk
    exact ⟨((⟨k, hk⟩ : (K' : Subgroup G)) : _ ⧸ _), rfl⟩
end GroundTheory.LocalField.Abstract
