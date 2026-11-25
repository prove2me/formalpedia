-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_addVal_lt_of_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:54.516269+00:00
-- url     : https://prove2.me/submissions/6a16ad2c-d630-452f-b195-450cc73e96b0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GroundTheory.LocalField
theorem _root_.solution {ι : Type*} [DecidableEq ι] {s : Finset ι} {t : ι → R}
    (hs : ∑ i ∈ s, t i = 0) {j : ι} (hj : j ∈ s)
    (hlt : ∀ i ∈ s, i ≠ j → addVal R (t j) < addVal R (t i)) : t j = 0 := by
  by_contra h0
  have htop : addVal R (t j) ≠ ⊤ := fun h => h0 (addVal_eq_top_iff.mp h)
  have hrest : addVal R (t j) < addVal R (∑ i ∈ s.erase j, t i) :=
    (addVal R).map_lt_sum htop fun i hi => hlt i (Finset.mem_of_mem_erase hi)
      (Finset.ne_of_mem_erase hi)
  have := (addVal R).map_add_eq_of_lt_left hrest
  rw [Finset.add_sum_erase s t hj, hs, AddValuation.map_zero] at this
  exact htop this.symm
end GroundTheory.LocalField
