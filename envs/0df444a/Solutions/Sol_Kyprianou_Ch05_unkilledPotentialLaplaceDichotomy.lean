-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPotentialLaplaceDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:40.291629+00:00
-- url     : https://prove2.me/submissions/be7f7f3d-246d-4381-9b9f-6968c44a9ffa

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_subordinatorLaplaceSemigroupProperties
import Theorems.Thm_Kyprianou_Ch05_positiveAntitoneMultiplicativeExponential
import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialLaplaceFromSemigroup
import Theorems.Thm_Kyprianou_Ch05_subordinatorLaplaceOneForcesZero
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The potential transform dichotomy, derived from monotonicity and independent increments. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    (∀ t : NNReal, ∀ᵐ w ∂P, Y t w = 0) ∨
      (∀ theta : Real, 0 < theta → ∃ a : Real, 0 < a ∧
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 1)) =
          (ENNReal.ofReal (1 + a))⁻¹ ∧
        (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 0)) =
          (ENNReal.ofReal a)⁻¹) := by
  by_cases hz : ∀ t : NNReal, ∀ᵐ w ∂P, Y t w = 0
  · exact Or.inl hz
  · right
    intro theta htheta
    let g : NNReal → ENNReal :=
      fun t => ∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P
    obtain ⟨hb, hm, hmul⟩ := subordinatorLaplaceSemigroupProperties P Y hKilled.1 theta htheta
    obtain ⟨a, ha, hsem⟩ := positiveAntitoneMultiplicativeExponential g hb hm hmul
    have hpos : 0 < a := by
      by_contra! hn
      have he : a = 0 := le_antisymm hn ha
      apply hz
      intro t
      apply subordinatorLaplaceOneForcesZero P Y hKilled.1 theta htheta t
      change g t = 1
      simp [hsem t, he]
    refine ⟨a, hpos, ?_, ?_⟩
    · exact unkilledPotentialLaplaceFromSemigroup P Y hKilled.1 death
        (hKilled.2.2.2.1 rfl) U hPotential theta a ha hsem 1 (by norm_num)
    · simpa using unkilledPotentialLaplaceFromSemigroup P Y hKilled.1 death
        (hKilled.2.2.2.1 rfl) U hPotential theta a ha hsem 0 (by norm_num)
