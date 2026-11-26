-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_levy_no_fixed_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:37:50.055674+00:00
-- url     : https://prove2.me/submissions/06a7e810-36c4-4f5d-806a-f88cdf58264e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_matching_limits
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A real Levy process has no jump at any deterministic positive time. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (hLeft : ∀ᵐ w ∂P, Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Y t w))) :
    ∀ᵐ w ∂P, X t w = Y t w := by
  let l := nhdsWithin t (Iio t)
  let D : Ω → ℝ := fun w => X t w - Y t w
  let U : NNReal → Ω → ℝ := fun s w => X t w - X (min s t) w
  let V : NNReal → Ω → ℝ := fun s w => X (t - min s t) w - X 0 w
  haveI : l.NeBot := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
  have hm (s : NNReal) := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX s
  have hUm (s : NNReal) : AEMeasurable (U s) P := (hm t).sub (hm (min s t))
  have hVm (s : NNReal) : AEMeasurable (V s) P := (hm (t-min s t)).sub (hm 0)
  have hUL : ∀ᵐ w ∂P, Tendsto (fun s => U s w) l (nhds (D w)) := by
    filter_upwards [hLeft] with w hw
    have H : (fun s : NNReal => X t w - X s w) =ᶠ[l] (fun s => U s w) := by
      filter_upwards [self_mem_nhdsWithin (a := t) (s := Iio t)] with s hs
      simp [U,min_eq_left (le_of_lt (mem_Iio.mp hs))]
    exact (tendsto_const_nhds.sub hw).congr' H
  have htime : Tendsto (fun s : NNReal => t-min s t) l (nhds 0) := by
    have H := ((continuous_const.sub (continuous_id.min continuous_const) :
      Continuous (fun s : NNReal => t-min s t)).tendsto t).mono_left (show l ≤ nhds t from nhdsWithin_le_nhds)
    change Tendsto (fun s : NNReal => t-min s t) l (nhds (t-min t t)) at H
    simpa only [min_self,tsub_self] using H
  have hVL : ∀ᵐ w ∂P, Tendsto (fun s => V s w) l (nhds (0 : ℝ)) := by
    filter_upwards [hX.cadlag_ae] with w hw
    have hrc : Tendsto (fun u => X u w) (nhds (0 : NNReal)) (nhds (X 0 w)) := by
      simpa only [Ici_zero_eq_univ,nhdsWithin_univ] using (hw 0).1.tendsto
    simpa only [V,Function.comp_apply,sub_self] using (hrc.comp htime).sub (tendsto_const_nhds (x := X 0 w))
  have hLaw (s : NNReal) : P.map (U s) = P.map (V s) := by
    have H := (hX.stationary_increments (min s t) (t-min s t)).map_eq
    rwa [add_tsub_cancel_of_le (min_le_right s t)] at H
  exact (Kyprianou.Ch04.ito43_levy_matching_limits P l U V D hUm hVm hUL hVL hLaw).mono
    (fun w hw => sub_eq_zero.mp hw)
