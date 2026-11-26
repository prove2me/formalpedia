-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_deficit_law_equal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:21:18.118814+00:00
-- url     : https://prove2.me/submissions/f468db0c-e2d3-4c5b-9e5a-20a889e72326

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_actual_deficit_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_tail_law_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_passage_position_meas
import Theorems.Thm_Kyprianou_Ch04_cor412_zero_exp_law
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exp_law_unique
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The actual stopped-position measure equals the reflected integrated-tail density. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (hm : 0 < derivWithin L.ψ (Ici 0) 0)
    (finiteTime : Ω → NNReal)
    (hfin : ∀ w, Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (finiteTime w : WithTop NNReal)) :
    let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}
    let κ := (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal (1/L.drift) * L.ν (Iio (-y)))
    (P.restrict A).map (fun w => L.X (finiteTime w) w) = κ.map (fun y => -y) := by
  intro A κ
  let μ := (P.restrict A).map (fun w => L.X (finiteTime w) w)
  let ν := κ.map (fun y => -y)
  have hme := Kyprianou.Ch04.cor412_passage_position_meas L finiteTime hfin
  have hμ (s : ℝ) (hs : 0 < s) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂μ) =
        ENNReal.ofReal (1 - L.ψ s / (L.drift*s)) := by
    change (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂
      (P.restrict A).map (fun w => L.X (finiteTime w) w)) = _
    rw [lintegral_map' (by fun_prop) hme]
    exact Kyprianou.Ch04.cor412_actual_deficit_transform L hBV hd hm s hs finiteTime hfin
  have hν (s : ℝ) (hs : 0 < s) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂ν) =
        ENNReal.ofReal (1 - L.ψ s / (L.drift*s)) :=
    Kyprianou.Ch04.cor412_tail_law_transform L hBV hd s hs
  have he (s : ℝ) (hs : 0 < s) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (Real.exp (s*x)) ∂ν :=
    (hμ s hs).trans (hν s hs).symm
  change μ = ν
  by_cases hz : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂μ) = 0
  · have hzν : (∫⁻ x, ENNReal.ofReal (Real.exp x) ∂ν) = 0 := by
      simpa using (he 1 (by norm_num)).symm.trans (by simpa using hz)
    rw [Kyprianou.Ch04.cor412_zero_exp_law μ hz, Kyprianou.Ch04.cor412_zero_exp_law ν hzν]
  · apply Kyprianou.Ch04.cor412_positive_exp_law_unique μ ν _ he hz
    intro s hs
    rw [hμ s hs]
    exact ENNReal.ofReal_ne_top
