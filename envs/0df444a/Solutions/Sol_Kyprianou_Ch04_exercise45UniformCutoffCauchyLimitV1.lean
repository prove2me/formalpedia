-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45UniformCutoffCauchyLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:36:37.666305+00:00
-- url     : https://prove2.me/submissions/a22e8b03-1ebd-4d43-b9d5-d5a6d59f9494

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Use completeness at each time along a positive sequence converging to zero. Pass the uniform Cauchy inequality to that limit, then use the within-neighbourhood criterion. -/
theorem solution
    (A : ℝ → NNReal → ℝ) (e : ℕ → ℝ)
    (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (nhds 0))
    (hC : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
      ∀ r q : ℝ, 0 < r → r < a → 0 < q → q < a →
        ∀ t ≤ T, |A r t - A q t| < δ) :
    ∃ Z : NNReal → ℝ,
      (∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
        ∀ r : ℝ, 0 < r → r < a → ∀ t ≤ T, |A r t - Z t| ≤ δ) ∧
      (∀ t : NNReal, Tendsto (fun r : ℝ => A r t)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Z t))) := by
  classical
  have hseq (t : NNReal) : ∃ z : ℝ, Tendsto (fun n => A (e n) t) atTop (nhds z) := by
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    obtain ⟨a,ha,h⟩ := hC t δ hδ
    have hev : ∀ᶠ n in atTop, e n < a := he0 (Iio_mem_nhds ha)
    obtain ⟨n₀,hn₀⟩ := eventually_atTop.1 hev
    refine ⟨n₀,?_⟩
    intro m hm n hn
    rw [Real.dist_eq]
    exact h (e m) (e n) (he m) (hn₀ m hm) (he n) (hn₀ n hn) t le_rfl
  choose Z hZ using hseq
  have hu : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
      ∀ r : ℝ, 0 < r → r < a → ∀ t ≤ T, |A r t-Z t| ≤ δ := by
    intro T δ hδ
    obtain ⟨a,ha,h⟩ := hC T δ hδ
    refine ⟨a,ha,?_⟩
    intro r hr hra t ht
    have hev : ∀ᶠ n in atTop, e n < a := he0 (Iio_mem_nhds ha)
    have hl : Tendsto (fun n => |A r t-A (e n) t|) atTop (nhds |A r t-Z t|) :=
      (tendsto_const_nhds.sub (hZ t)).abs
    apply le_of_tendsto hl
    filter_upwards [hev] with n hn
    exact (h r (e n) hr hra (he n) hn t ht).le
  refine ⟨Z,hu,?_⟩
  intro t
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨a,ha,h⟩ := hu t (δ/2) (by positivity)
  have hev : ∀ᶠ r in nhdsWithin (0:ℝ) (Ioi 0), r < a :=
    nhdsWithin_le_nhds (Iio_mem_nhds ha)
  have hpos : ∀ᶠ r in nhdsWithin (0:ℝ) (Ioi 0), 0 < r := self_mem_nhdsWithin
  filter_upwards [hev,hpos] with r hra hr
  rw [Real.dist_eq]
  exact (h r hr hra t le_rfl).trans_lt (by linarith)
