-- Prove2me | solution 1 for Kyprianou.Ch04.actualCutoffStateRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:14:20.712606+00:00
-- url     : https://prove2.me/submissions/363b240c-9bf6-47f0-9d0b-429887c71168

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagAEV1
import Theorems.Thm_Kyprianou_Ch04_zeroTimeRestrictionIccIocV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite retained-band state is right continuous on the same physical sample
space, without a first-moment assumption on its large marks. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (Y X2 : NNReal → Ω → ℝ) (b a : ℝ) (ha : 0 < a)
    (hz : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0)
    (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hY : ∀ t w, Y t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) - (t : ℝ) * ∫ x in {x : ℝ | a < |x| ∧ |x| < 1}, x ∂ν) :
    ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t := by
  let B : Set ℝ := {x | 1 ≤ |x|}
  let C : Set ℝ := {x | a < |x| ∧ |x| < 1}
  have hB : MeasurableSet B := measurableSet_le measurable_const measurable_id.abs
  have hC : MeasurableSet C := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_lt measurable_id.abs measurable_const)
  have hfB : ν B < ⊤ := hν.measure_setOf_abs_ge_lt_top (by norm_num)
  have hfC : ν C < ⊤ := (measure_mono (show C ⊆ {x | a ≤ |x|} from
    fun x hx => hx.1.le)).trans_lt (hν.measure_setOf_abs_ge_lt_top ha)
  filter_upwards [hz,Kyprianou.Ch02.prmFiniteRegionCadlagAEV1 P ν N B hB hfB,
    Kyprianou.Ch02.prmFiniteRegionCadlagAEV1 P ν N C hC hfC] with w hw hB' hC'
  have he : (fun t => Y t w) = fun t : NNReal => b * (t : ℝ) +
      (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N w)) +
      (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ C, z.2 ∂(N.N w)) -
      (t : ℝ) * ∫ x in C, x ∂ν := by
    funext t
    rw [hY t w,h2 t w]
    change _ + (∫ z, z.2 ∂((N.N w).restrict (Icc 0 (t : ℝ) ×ˢ B))) +
      (∫ z, z.2 ∂((N.N w).restrict (Icc 0 (t : ℝ) ×ˢ C))) - _ = _
    rw [Kyprianou.Ch04.zeroTimeRestrictionIccIocV1 (N.N w) hw t B,
      Kyprianou.Ch04.zeroTimeRestrictionIccIocV1 (N.N w) hw t C]
  rw [he]
  intro t
  have hc : Continuous (fun s : NNReal => (s : ℝ)) := continuous_subtype_val
  exact (((continuous_const.mul hc).continuousWithinAt.add (hB' t).1).add
    (hC' t).1).sub ((hc.mul continuous_const).continuousWithinAt)
