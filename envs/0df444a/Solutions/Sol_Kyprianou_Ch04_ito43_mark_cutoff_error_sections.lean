-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_mark_cutoff_error_sections
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:23:25.668475+00:00
-- url     : https://prove2.me/submissions/79ce3ab0-4ee3-4cf2-9fc3-032a16e07c3a

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_mark_integral_series
import Theorems.Thm_Kyprianou_Ch04_ito43_cadlag_stopped_cutoff_kernel_uniform
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (r : ℝ → ℝ) (hr : Continuous r) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ z, |z| ≤ δ → r z = 0) (T : NNReal) :
    let E : ℕ → NNReal → Ω → ℝ := fun n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X L w)) -
        ∑ k ∈ Finset.range n, r (X (v (k+1)) w-X (v k) w)
    ∀ n t, AEMeasurable (E n t) P := by
  intro E n t
  let J : Ω → ℝ := fun w =>
    ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X L w)
  let G : NNReal → ℕ → Ω → ℝ := fun H j w =>
    ∑ k ∈ Finset.range j,
      r (X (min t (H*((k+1:ℕ):NNReal)/(j:NNReal))) w-
        X (min t (H*(k:NNReal)/(j:NNReal))) w)
  have hG (H : NNReal) (j : ℕ) : AEMeasurable (G H j) P := by
    have hx := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
    apply Finset.aemeasurable_fun_sum
    intro k hk
    exact hr.measurable.comp_aemeasurable
      ((hx _).sub (hx _))
  have hJ : AEMeasurable J P := by
    refine aemeasurable_of_tendsto_metrizable_ae atTop (fun j => hG t j) ?_
    filter_upwards [hX.cadlag_ae,hL] with w hc hl
    have h := Kyprianou.Ch04.ito43_cadlag_stopped_cutoff_kernel_uniform
      (fun s => X s w) (fun s => L s w) hc hl (fun _ _ z => r z)
      (hr.comp (continuous_snd.comp continuous_snd)) δ hδ (fun _ _ z hz => hzero z hz) t
    have h0 := hzero 0 (by simpa using hδ.le)
    rw [show J w = _ from Kyprianou.Ch04.ito43_mark_integral_series X L w hc hl r h0 t]
    apply Metric.tendsto_atTop.mpr
    intro e he
    obtain ⟨N,hN⟩ := eventually_atTop.mp (h e he)
    exact ⟨N,fun j hj => by
      rw [Real.dist_eq]
      exact hN j hj t le_rfl⟩
  exact hJ.sub (hG T n)
