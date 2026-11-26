-- Prove2me | solution 1 for Kyprianou.Ch05.activePositivePoissonMarkIsJumpV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:37:33.275072+00:00
-- url     : https://prove2.me/submissions/f457612f-410c-46cd-a243-9f5859575faa

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_pointFamilyPositiveFibreMassV1
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
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega) (f : NNReal → ℝ)
    (hinj : ∀ i j : ℕ × ℕ, i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j)
    (hj : ∀ t : NNReal, 0 < t → f t - Function.leftLim f t =
      (∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
        ∂(poissonRandomMeasure K Z w)).toReal)
    (i : ℕ × ℕ) (hi : i.2 < K i.1 w)
    (ht : 0 < (Z i.1 i.2 w).1) (hz : 0 < (Z i.1 i.2 w).2) :
    f (Z i.1 i.2 w).1.toNNReal - Function.leftLim f (Z i.1 i.2 w).1.toNNReal =
      (Z i.1 i.2 w).2 := by
  have h := hj (Z i.1 i.2 w).1.toNNReal (Real.toNNReal_pos.mpr ht)
  rw [Real.coe_toNNReal _ ht.le,pointFamilyPositiveFibreMassV1 K Z w hinj i hi hz,
    ENNReal.toReal_ofReal hz.le] at h
  exact h
