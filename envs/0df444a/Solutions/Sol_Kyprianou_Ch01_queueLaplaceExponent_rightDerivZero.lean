-- Prove2me | solution 1 for Kyprianou.Ch01.queueLaplaceExponent_rightDerivZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T12:17:08.376947+00:00
-- url     : https://prove2.me/submissions/edec18f9-2994-4a3d-ac65-05faed61d50b

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_zero
import Theorems.Thm_Kyprianou_Ch01_queueExpDeficit_div_tendsto_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    HasDerivWithinAt (queueLaplaceExponent rate F)
      (1 - (rate : ℝ) * mu) (Set.Ici (0 : ℝ)) 0 := by
  have hlim := Kyprianou.Ch01.queueExpDeficit_div_tendsto_mean
    F hpositive hfiniteMean mu hmean
  have hlim' : Tendsto (fun theta : ℝ =>
      1 - (rate : ℝ) *
        ((∫ x : ℝ, (1 - Real.exp (-theta * x)) ∂F) / theta))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 - (rate : ℝ) * mu)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)
  apply (hasDerivWithinAt_iff_tendsto_slope).2
  have hset : (Set.Ici (0 : ℝ)) \ {0} = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨hx, hn⟩
      rcases eq_or_lt_of_le hx with heq | hh
      · exact (hn heq.symm).elim
      · exact hh
    · intro hx
      exact ⟨le_of_lt hx, ne_of_gt hx⟩
  rw [hset]
  have hevent :
      (slope (queueLaplaceExponent rate F) 0) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun theta : ℝ =>
          1 - (rate : ℝ) *
            ((∫ x : ℝ, (1 - Real.exp (-theta * x)) ∂F) / theta)) := by
    filter_upwards [self_mem_nhdsWithin] with theta ht
    have hne : theta ≠ 0 := ne_of_gt ht
    rw [slope_def_field, Kyprianou.Ch01.queueLaplaceExponent_zero rate F]
    dsimp [queueLaplaceExponent]
    simp only [sub_zero]
    field_simp
  exact (tendsto_congr' hevent).2 hlim'
