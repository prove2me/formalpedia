-- Prove2me | solution 1 for Kyprianou.Ch05.positiveTimeLeftLimitRealNNRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:23:43.952787+00:00
-- url     : https://prove2.me/submissions/49e8472f-da18-42a8-b8fa-f98366250d0b

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (Q : Measure Omega)
    (g : ℝ → Omega → ℝ) (V : NNReal → Omega → ℝ)
    (hm : ∀ᵐ w ∂Q, Monotone (fun t : NNReal => g t w))
    (hl : ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      V t w = Function.leftLim (fun s : ℝ => g s w) (t : ℝ)) :
    ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      V t w = Function.leftLim (fun s : NNReal => g s w) t := by
  filter_upwards [hm,hl] with w hw hv
  intro t ht
  rw [hv t ht]
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have htend : Tendsto Real.toNNReal (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
      (nhdsWithin t (Iio t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · have hi : Tendsto (id : ℝ → ℝ) (nhdsWithin (t : ℝ) (Iio (t : ℝ)))
          (nhds (t : ℝ)) := nhdsWithin_le_nhds
      simpa only [Real.toNNReal_coe,id_eq] using tendsto_real_toNNReal hi
    · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds ht')] with s hs hp
      exact (Real.toNNReal_lt_iff_lt_coe hp.le).mpr hs
  have htend' := (hw.tendsto_leftLim t).comp htend
  have he : (fun s : ℝ => g (s.toNNReal : ℝ) w) =ᶠ[nhdsWithin (t : ℝ) (Iio (t : ℝ))]
      (fun s => g s w) := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht')] with s hs
    rw [Real.coe_toNNReal _ hs.le]
  exact leftLim_eq_of_tendsto (htend'.congr' he)
