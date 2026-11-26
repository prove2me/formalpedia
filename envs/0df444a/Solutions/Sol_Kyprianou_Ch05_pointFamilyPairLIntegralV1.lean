-- Prove2me | solution 1 for Kyprianou.Ch05.pointFamilyPairLIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:26:49.250665+00:00
-- url     : https://prove2.me/submissions/20506721-905b-475b-8ee5-f6fb6c4ae005

import Mathlib
import Theorems.Thm_ProbabilityTheory_lintegral_poissonRandomMeasure
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
    {Omega E : Type} [MeasurableSpace E]
    (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → E)
    (w : Omega) (g : E → ENNReal) (hg : Measurable g) :
    (∫⁻ z, g z ∂(poissonRandomMeasure K Z w)) =
      ∑' i : ℕ × ℕ, if i.2 < K i.1 w then g (Z i.1 i.2 w) else 0 := by
  rw [lintegral_poissonRandomMeasure hg,ENNReal.tsum_prod']
  apply tsum_congr
  intro k
  rw [tsum_eq_sum (s := Finset.range (K k w))
    (fun n hn => if_neg (by simpa only [Finset.mem_range] using hn))]
  exact Finset.sum_congr rfl (fun n hn => (if_pos (by simpa only [Finset.mem_range] using hn)).symm)
