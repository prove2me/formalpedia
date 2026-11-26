-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonStripExponentProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:35:59.901126+00:00
-- url     : https://prove2.me/submissions/73ad7599-8dec-458b-8674-dfd9c725bc32

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
    (Pi : Measure ℝ) [SigmaFinite Pi] (s t u : ℝ) (hst : s ≤ t) :
    (∫ z : ℝ × ℝ, Complex.exp (Complex.I *
      ((u * (Ioc s t ×ˢ Ioi (0 : ℝ)).indicator Prod.snd z : ℝ) : ℂ)) - 1
        ∂((volume : Measure ℝ).prod Pi)) =
      ((t-s : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ),
        (Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1) ∂Pi := by
  classical
  let R := Ioc s t ×ˢ Ioi (0 : ℝ)
  let g : ℝ → ℂ := fun y => Complex.exp (Complex.I * ((u*y : ℝ) : ℂ)) - 1
  have he : (fun z : ℝ × ℝ => Complex.exp (Complex.I *
      ((u * R.indicator Prod.snd z : ℝ) : ℂ)) - 1) =
      R.indicator (fun z => (1 : ℂ) * g z.2) := by
    funext z
    by_cases hz : z ∈ R <;> simp [R,g,Set.indicator,hz] at *
  change (∫ z, Complex.exp (Complex.I * ((u * R.indicator Prod.snd z : ℝ) : ℂ)) - 1
    ∂((volume : Measure ℝ).prod Pi)) = _
  rw [he,integral_indicator (measurableSet_Ioc.prod measurableSet_Ioi),
    setIntegral_prod_mul (fun _ : ℝ => (1 : ℂ)) g (Ioc s t) (Ioi (0 : ℝ))]
  simp [measureReal_def,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hst),g]
