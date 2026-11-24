-- Prove2me | solution 1 for Kyprianou.Ch02.variationOfMonotoneApproximantsTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:34:24.910799+00:00
-- url     : https://prove2.me/submissions/e5edbbab-3d84-49e6-8a41-d3d29f30bcd1

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (s : Set ℝ≥0)
    (r : ℕ → ℝ≥0 → ℝ≥0)
    (hm : ∀ n, MonotoneOn (r n) s)
    (hmem : ∀ n, MapsTo (r n) s s)
    (hlim : ∀ x ∈ s, Tendsto (fun n => f (r n x)) atTop (nhds (f x))) :
    Tendsto (fun n => eVariationOn f (r n '' s)) atTop
      (nhds (eVariationOn f s)) := by
  apply tendsto_order.2
  constructor
  · intro v hv
    have h := eVariationOn.lowerSemicontinuous_aux
      (F := fun n => f ∘ r n) (p := atTop) (s := s) hlim hv
    exact h.mono (fun n hn => by
      rwa [eVariationOn.comp_eq_of_monotoneOn f (r n) (hm n)] at hn)
  · intro v hv
    exact Eventually.of_forall (fun n =>
      (eVariationOn.mono f (image_subset_iff.mpr (hmem n))).trans_lt hv)
