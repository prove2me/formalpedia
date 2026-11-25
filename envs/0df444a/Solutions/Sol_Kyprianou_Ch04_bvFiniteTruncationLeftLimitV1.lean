-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteTruncationLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:28:40.777243+00:00
-- url     : https://prove2.me/submissions/897607aa-93d2-4834-9d48-64418ebb05e0

import Mathlib
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I : Type} (τ : I → NNReal) (j : I → ℝ) (a c : ℝ)
    (S : Finset I) (u : NNReal) (hu : 0 < u) :
    Tendsto (fun v : NNReal => a + c * (v : ℝ) +
      ∑ s ∈ S, if τ s ≤ v then j s else 0)
      (nhdsWithin u (Set.Iio u))
      (nhds (a + c * (u : ℝ) + ∑ s ∈ S, if τ s < u then j s else 0)) := by
  classical
  let L := nhdsWithin u (Set.Iio u)
  have hsum : Tendsto (fun v : NNReal => ∑ s ∈ S, if τ s ≤ v then j s else 0)
      L (nhds (∑ s ∈ S, if τ s < u then j s else 0)) := by
    apply tendsto_finset_sum
    intro s hs
    apply tendsto_const_nhds.congr'
    by_cases hsu : τ s < u
    · have he : ∀ᶠ v : NNReal in L, τ s < v :=
        (nhdsWithin_le_nhds : L ≤ nhds u) (Ioi_mem_nhds hsu)
      filter_upwards [he] with v hv
      simp [hsu, hv.le]
    · have he : ∀ᶠ v : NNReal in L, v < u := self_mem_nhdsWithin
      filter_upwards [he] with v hv
      have hnv : ¬ τ s ≤ v := fun h => hsu (h.trans_lt hv)
      simp [hsu, hnv]
  have hc : Tendsto (fun v : NNReal => (v : ℝ)) L (nhds (u : ℝ)) :=
    (continuous_subtype_val.tendsto u).mono_left nhdsWithin_le_nhds
  exact (tendsto_const_nhds.add (tendsto_const_nhds.mul hc)).add hsum
