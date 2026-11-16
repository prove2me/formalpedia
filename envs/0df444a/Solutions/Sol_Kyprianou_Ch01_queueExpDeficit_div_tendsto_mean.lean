-- Prove2me | solution 1 for Kyprianou.Ch01.queueExpDeficit_div_tendsto_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T12:16:03.559957+00:00
-- url     : https://prove2.me/submissions/1aab7d45-3b89-4354-97f7-78d86363b871

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_expDeficitQuotient_tendsto
import Theorems.Thm_Kyprianou_Ch01_expDeficitQuotient_norm_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem solution
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmean : (∫ x, x ∂F) = mu) :
    Tendsto (fun theta : ℝ =>
      (∫ x : ℝ, (1 - Real.exp (-theta * x)) ∂F) / theta)
      (𝓝[>] (0 : ℝ)) (𝓝 mu) := by
  let g : ℝ → ℝ → ℝ :=
    fun theta x => (1 - Real.exp (-theta * x)) / theta
  have hae : ∀ᵐ x ∂F, 0 ≤ x := by
    apply (ae_iff).2
    have hz : F {z : ℝ | z ≤ 0} = 0 := hpositive
    have hstrict : ∀ᵐ x ∂F, 0 < x := by
      apply (ae_iff).2
      simpa only [not_lt] using hz
    exact hstrict.mono (fun x hx => hx.le)
  have hm : ∀ᶠ theta in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (g theta) F := by
    exact Filter.Eventually.of_forall (fun theta => by
      dsimp [g]
      fun_prop)
  have hb : ∀ᶠ theta in 𝓝[>] (0 : ℝ),
      ∀ᵐ x ∂F, ‖g theta x‖ ≤ x := by
    filter_upwards [self_mem_nhdsWithin] with theta ht
    filter_upwards [hae] with x hx
    exact Kyprianou.Ch01.expDeficitQuotient_norm_le theta x ht hx
  have hl : ∀ᵐ x ∂F, Tendsto (fun theta => g theta x)
      (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    exact Filter.Eventually.of_forall (fun x =>
      Kyprianou.Ch01.expDeficitQuotient_tendsto x)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => x) hm hb hfiniteMean hl
  dsimp [g] at hDCT
  simpa only [integral_div, hmean] using hDCT
