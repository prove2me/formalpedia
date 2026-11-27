-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.continuous_relDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:57.483832+00:00
-- url     : https://prove2.me/submissions/8fef3f6f-1282-4619-9642-4258d0d65976

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_pow

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
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (K : OpenSubgroup G) : Continuous (D.relDeg K) := by
  have hp : Topology.IsClosedEmbedding (fun x : Multiplicative ℤ̂ => x ^ inertiaDegree D.deg K) :=
    (continuous_pow _).isClosedEmbedding (ProfiniteInteger.pow_left_injective (D.inertiaDegree_ne_zero K))
  rw [hp.isEmbedding.continuous_iff]
  have h : ((fun x : Multiplicative ℤ̂ => x ^ inertiaDegree D.deg K) ∘ D.relDeg K) =
      D.deg ∘ Subtype.val := funext (D.relDeg_pow K)
  rw [h]
  exact D.continuous_deg.comp continuous_subtype_val
end GroundTheory.LocalField.Abstract.ClassFieldData
