-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_mark_integral_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:23:22.526804+00:00
-- url     : https://prove2.me/submissions/6e10d1d4-c56b-479c-a6c7-baf72991e88e

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_exercise41CadlagPhysicalJumpsCountableV17
import Theorems.Thm_Kyprianou_Ch04_bvPathJumpMeasureAtomicV1
import Theorems.Thm_Kyprianou_Ch04_bvRestrictedDiracIntegralV1
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun t => X t w))
    (hl : ∀ t : NNReal, 0 < t → Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (r : ℝ → ℝ) (h0 : r 0 = 0) (t : NNReal) :
    (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X L w)) =
      ∑' s : Ioc (0:NNReal) t, r (X s w-L s w) := by
  classical
  let J : Set NNReal := {s | 0 < s ∧ X s w ≠ L s w}
  let φ : J → ℝ × ℝ := fun s => ((s.1 : ℝ),X s.1 w-L s.1 w)
  let B : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ univ
  let g : ℝ × ℝ → ℝ := fun z => r z.2
  have hJ := Kyprianou.Ch04.exercise41CadlagPhysicalJumpsCountableV17
    (fun s => X s w) (fun s => L s w) (fun s => (hc s).1) hl
  letI : Countable J := hJ.to_subtype
  change (∫ z in B, g z ∂(pathJumpMeasure X L w)) = _
  rw [Kyprianou.Ch04.bvPathJumpMeasureAtomicV1 X L w hJ]
  rw [Kyprianou.Ch04.bvRestrictedDiracIntegralV1 φ B (measurableSet_Icc.prod MeasurableSet.univ) g]
  let F : NNReal → ℝ := fun s => B.indicator g ((s:ℝ),X s w-L s w)
  let G : NNReal → ℝ := fun s => r (X s w-L s w)
  change (∑' s : J, F s) = ∑' s : Ioc (0:NNReal) t, G s
  rw [tsum_subtype J F,tsum_subtype (Ioc (0:NNReal) t) G]
  apply tsum_congr
  intro s
  by_cases h : X s w = L s w
  · simp [J,F,G,Set.indicator_apply,h,h0]
  · by_cases hs : 0 < s
    · have hm : ((s:ℝ),X s w-L s w) ∈ B ↔ s ≤ t := by
        change ((0:ℝ) ≤ (s:ℝ) ∧ (s:ℝ) ≤ (t:ℝ)) ∧
          X s w-L s w ∈ (univ : Set ℝ) ↔ s ≤ t
        simp
      simp [J,F,G,Set.indicator_apply,h,hs,hm,g]
    · simp [J,F,G,Set.indicator_apply,hs]
