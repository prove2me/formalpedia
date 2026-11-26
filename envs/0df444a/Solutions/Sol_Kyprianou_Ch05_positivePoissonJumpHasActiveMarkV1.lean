-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonJumpHasActiveMarkV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:37:33.215687+00:00
-- url     : https://prove2.me/submissions/266ebb05-77e9-4261-84d1-94ad74ab1937

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_pointFamilyPositiveFibreExistsV1
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
    (t : NNReal) (ht : 0 < t) (hp : 0 < f t - Function.leftLim f t) :
    ∃ i : ℕ × ℕ, i.2 < K i.1 w ∧ (Z i.1 i.2 w).1 = (t : ℝ) ∧
      (Z i.1 i.2 w).2 = f t - Function.leftLim f t := by
  have h := hj t ht
  obtain ⟨i,hi,hit,hz⟩ := pointFamilyPositiveFibreExistsV1 K Z w (t : ℝ)
    (h ▸ hp)
  refine ⟨i,hi,hit,?_⟩
  rw [← hit,pointFamilyPositiveFibreMassV1 K Z w hinj i hi hz,
    ENNReal.toReal_ofReal hz.le] at h
  exact h.symm
