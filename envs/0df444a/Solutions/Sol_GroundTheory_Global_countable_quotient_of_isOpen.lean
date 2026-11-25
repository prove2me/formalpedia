-- Prove2me | solution 1 for GroundTheory.Global.countable_quotient_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:25.696815+00:00
-- url     : https://prove2.me/submissions/beb5385a-9ba3-4719-a8fc-824022816ad3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Countable (G ⧸ W) := by
  have : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW
  have h : IsLindelof (Set.univ : Set (G ⧸ W)) := by
    rw [← Set.image_univ_of_surjective (QuotientGroup.mk_surjective (s := W))]
    exact isLindelof_univ.image QuotientGroup.continuous_mk
  exact Set.countable_univ_iff.1 h.countable_of_discrete
end GroundTheory.Global
