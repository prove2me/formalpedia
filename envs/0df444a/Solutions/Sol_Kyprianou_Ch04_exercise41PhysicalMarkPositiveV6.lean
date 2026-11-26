-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41PhysicalMarkPositiveV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:31:39.074395+00:00
-- url     : https://prove2.me/submissions/e9635665-6dc3-4ec8-b871-844a6025ee5e

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (l : NNReal → ℝ)
    (hx : Measurable x) (hl : Measurable l)
    (A : Set (NNReal × ℝ)) (hA : MeasurableSet A)
    (s : NNReal) (hs : 0 < s) (hj : x s - l s ≠ 0)
    (hm : (s, x s - l s) ∈ A) :
    1 ≤ ((Measure.count.restrict {u : NNReal | 0 < u ∧ x u - l u ≠ 0}).map
      (fun u => (u,x u - l u))) A := by
  let J : Set NNReal := {u | 0 < u ∧ x u - l u ≠ 0}
  let f : NNReal → NNReal × ℝ := fun u => (u,x u - l u)
  have hf : Measurable f := measurable_id.prodMk (hx.sub hl)
  change 1 ≤ ((Measure.count.restrict J).map f) A
  rw [Measure.map_apply hf hA, Measure.restrict_apply (hf hA)]
  rw [← Measure.count_singleton s]
  apply measure_mono
  intro u hu
  have he : u = s := Set.mem_singleton_iff.mp hu
  subst u
  exact ⟨hm, hs, hj⟩
