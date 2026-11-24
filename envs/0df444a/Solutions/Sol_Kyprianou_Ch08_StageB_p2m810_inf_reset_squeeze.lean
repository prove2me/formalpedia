-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_inf_reset_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:15:30.989975+00:00
-- url     : https://prove2.me/submissions/edb68c45-4414-4d72-bcbd-906c20bb1f80


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Reflected exit reduction. -/
theorem solution :
    ∀ (R : ℝ → ℝ → ℝ) (F L x a : ℝ),
      0 < a → x ≤ a → F ≤ 1 → (x = a → L = 1) →
      (∀ ε : ℝ, 0 < ε → ε < a →
        R ε a ≤ F ∧ (x ≤ a-ε → F ≤ R ε (a-ε))) →
      Tendsto (fun ε => R ε a) (nhdsWithin 0 (Ioi 0)) (nhds L) →
      Tendsto (fun ε => R ε (a-ε)) (nhdsWithin 0 (Ioi 0)) (nhds L) →
      F = L := by
  intro R F L x a ha hxa hF hx hs h1 h2
  have hp : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), 0 < ε := self_mem_nhdsWithin
  have ht : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < a :=
    nhdsWithin_le_nhds (Iio_mem_nhds ha)
  apply le_antisymm _ (le_of_tendsto h1 (by
    filter_upwards [hp, ht] with ε he hε
    exact (hs ε he hε).1))
  rcases eq_or_lt_of_le hxa with he | hlt
  · rw [hx he]
    exact hF
  · have hu : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < a-x :=
      nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr hlt))
    apply ge_of_tendsto h2
    filter_upwards [hp, ht, hu] with ε he hε hε'
    exact (hs ε he hε).2 (by linarith)
