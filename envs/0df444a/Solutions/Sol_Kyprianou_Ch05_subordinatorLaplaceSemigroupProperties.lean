-- Prove2me | solution 1 for Kyprianou.Ch05.subordinatorLaplaceSemigroupProperties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:16:25.503641+00:00
-- url     : https://prove2.me/submissions/78b99ee4-6e1b-4cdc-ac7d-1b12a18579d4

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_subordinatorLaplacePositiveBound
import Theorems.Thm_Kyprianou_Ch05_subordinatorLaplaceAntitone
import Theorems.Thm_Kyprianou_Ch05_subordinatorLaplaceMultiplicative
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05


/-- Combine the three marginal Laplace properties. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) :
    let g : NNReal → ENNReal := fun t => (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P)
    (∀ t, 0 < g t ∧ g t ≤ 1) ∧ Antitone g ∧
      (∀ s t, g (s+t) = g s * g t) := by
  exact ⟨subordinatorLaplacePositiveBound P Y hY theta htheta,
    subordinatorLaplaceAntitone P Y hY theta htheta,
    subordinatorLaplaceMultiplicative P Y hY theta htheta⟩
