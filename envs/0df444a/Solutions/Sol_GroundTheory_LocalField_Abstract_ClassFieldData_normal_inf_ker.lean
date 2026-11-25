-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.normal_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:34.083417+00:00
-- url     : https://prove2.me/submissions/693a1ea4-c2c5-4596-96e6-e4e1e77c955e

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
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((L : Subgroup G) ⊓ D.deg.ker).subgroupOf ((K : Subgroup G) ⊓ D.deg.ker)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := (Subgroup.mem_normalizer_iff.1 (FrobeniusLift.mem_normalizer (D := D) hLK g.2.1) n).1 hn
  simpa using h
end GroundTheory.LocalField.Abstract.ClassFieldData
