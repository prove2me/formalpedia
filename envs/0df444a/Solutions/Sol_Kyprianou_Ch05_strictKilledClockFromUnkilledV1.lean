-- Prove2me | solution 1 for Kyprianou.Ch05.strictKilledClockFromUnkilledV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:32:09.016445+00:00
-- url     : https://prove2.me/submissions/88345c1e-7756-4e52-a6d0-cbe78c882897

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_killedClockInfRestrictionV1
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
    {Omega : Type} (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (x : ℝ) (w : Omega) (T : ENNReal)
    (hT : T = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < Y t w})) :
    (strictUpcrossing Y death x w : ENNReal) =
      if T < (death w : ENNReal) then T else ⊤ := by
  classical
  let S : Set ENNReal := (fun t : NNReal => (t : ENNReal)) ''
    {t : NNReal | 0 < t ∧ x < Y t w}
  have he : ((fun t : NNReal => (t : ENNReal)) ''
      {t : NNReal | 0 < t ∧ (t : WithTop NNReal) < death w ∧ x < Y t w}) =
      S ∩ Iio (death w : ENNReal) := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,⟨ht.1,ht.2.2⟩,rfl⟩,ht.2.1⟩
    · rintro ⟨⟨t,ht,rfl⟩,he⟩
      exact ⟨t,⟨ht.1,he,ht.2⟩,rfl⟩
  change sInf ((fun t : NNReal => (t : ENNReal)) ''
      {t : NNReal | 0 < t ∧ (t : WithTop NNReal) < death w ∧ x < Y t w}) = _
  rw [he]
  let e : ENNReal := death w
  change T = sInf S at hT
  calc
    _ = if sInf S < e then sInf S else ⊤ := killedClockInfRestrictionV1 S e
    _ = _ := by
      rw [← hT]
      exact if_congr Iff.rfl rfl rfl
