-- Prove2me | solution 1 for GroundTheory.LocalField.continuous_of_vle_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:10.260798+00:00
-- url     : https://prove2.me/submissions/df821409-94b3-48ea-a62d-fd6c598eaaef

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries
namespace GroundTheory.LocalField
theorem _root_.solution {R S : Type*} [Field R] [ValuativeRel R] [TopologicalSpace R]
    [IsValuativeTopology R] [Field S] [ValuativeRel S] [TopologicalSpace S]
    [IsValuativeTopology S] (f : R →+* S) (hf : ∀ x y, f x ≤ᵥ f y ↔ x ≤ᵥ y)
    (hs : Function.Surjective f) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  refine ((IsValuativeTopology.hasBasis_nhds_zero' R).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' S)).mpr fun γ hγ => ?_
  obtain ⟨z, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨t, rfl⟩ := hs z
  refine ⟨valuation R t, fun h => hγ ?_, fun x hx => ?_⟩
  · rw [map_eq_zero] at h
    simp [h]
  · exact ((valuation S).vlt_iff_lt.symm.trans
      ((not_congr (hf t x)).trans (valuation R).vlt_iff_lt)).mpr hx
end GroundTheory.LocalField
