-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_uniform_lower_bound_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:40:17.650899+00:00
-- url     : https://prove2.me/submissions/3ba67e33-0e66-4bce-99f1-16ff394edf6e

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_negative_indicator_integral_zero_ae
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_levy_negative_grid_product
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_negative_grid_impossible
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecificLimits.Basic
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
/-- Independent increment reduction. -/
theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ),
      ProbabilityTheory.IsLevyProcess X P →
      ∀ (a c : ℝ) (t : ℝ≥0), c < 0 →
      (∀ s : ℝ≥0, ∀ᵐ ω ∂P, -a ≤ X s ω) →
      ∀ᵐ ω ∂P, c ≤ X t ω := by
  intro Ω mΩ P hP X hX a c t hc hb
  obtain ⟨n,hn⟩ := exists_nat_gt (a/(-c))
  have hn' : (n:ℝ)*c < -a := by
    have h := (div_lt_iff₀ (neg_pos.mpr hc)).1 hn
    linarith
  have hzero : (∫ ω, if X t ω<c then (1:ℝ) else 0 ∂P)^n = 0 := by
    rw [← p2m810_levy_negative_grid_product Ω P X hX t c n]
    have h : (fun ω => ∏ i : Fin n, (if X (((i.val+1 : ℕ):ℝ≥0)*t) ω -
        X ((i.val:ℝ≥0)*t) ω < c then (1:ℝ) else 0)) =ᵐ[P] 0 := by
      filter_upwards [hb ((n:ℝ≥0)*t)] with ω hw
      exact p2m810_negative_grid_impossible Ω X ω t a c n (congrFun hX.start_zero ω) hw hn'
    rw [integral_congr_ae h]
    change (∫ _ : Ω, (0 : ℝ) ∂P) = 0
    exact integral_zero _ _
  apply p2m810_negative_indicator_integral_zero_ae Ω P (X t) c
    (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t)
  by_contra h
  exact pow_ne_zero n h hzero
