-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.toAdd_deg_mem_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:39:31.644884+00:00
-- url     : https://prove2.me/submissions/84ea2447-6279-4098-8a88-bd32adba9272

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples


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
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
open GroundTheory.LocalField.Abstract.ClassFieldData
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (K : OpenSubgroup G) {k : G} (hk : k ∈ (K : Subgroup G)) :
    Multiplicative.toAdd (D.deg k) ∈ multiples (inertiaDegree D.deg K) := by
  obtain ⟨y, hy⟩ := (D.mem_map_deg_iff K).1 ⟨k, hk, rfl⟩
  refine mem_multiples.2 ⟨Multiplicative.toAdd y, ?_⟩
  rw [← hy, toAdd_pow]
end GroundTheory.LocalField.Abstract.ClassFieldData
