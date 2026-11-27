-- Prove2me | solution 1 for Kyprianou.Ch04.compensatedBandPathRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:52:32.782695+00:00
-- url     : https://prove2.me/submissions/4d2eb51b-dcdc-4f2b-a64e-e1034c4dba4f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_weightedRawIntegralRightV1
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite-band compensated Poisson paths are almost surely right continuous. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (N : PoissonRandomMeasure.{0,0,0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (hz : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (Y : NNReal → Ω → ℝ)
    (hY : ∀ t w, Y t w = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N w)) -
      (t : ℝ) * (∫ x in B,x ∂ν)) :
    ∀ᵐ w ∂P, ∀ t, Tendsto (fun s => Y s w) (𝓝[>] t) (𝓝 (Y t w)) := by
  filter_upwards [Kyprianou.Ch04.weightedRawIntegralRightV1 P ν N B hB hfin
    (fun z _ => z.2) hz] with w hw
  intro t
  simp only [hY]
  exact (hw t).sub ((NNReal.continuous_coe.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).mul tendsto_const_nhds)
