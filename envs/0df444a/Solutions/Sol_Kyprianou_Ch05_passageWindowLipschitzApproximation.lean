-- Prove2me | solution 1 for Kyprianou.Ch05.passageWindowLipschitzApproximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:57:48.338172+00:00
-- url     : https://prove2.me/submissions/7ae23f82-a50e-4190-82c2-dcc4a0dcf714
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_lipschitzTestDensity
import Theorems.Thm_Kyprianou_Ch05_passageWindowStability
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (hNonLattice : NonLatticeMeasure (U 0)) :
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
    ∀ ε : Real, 0 < ε → ∃ g : Real × Real → Real,
      IsBoundedContinuousTest g ∧ g (0, 0) = 0 ∧
      (∃ C : Real, ∀ p q : Real × Real, |g p - g q| ≤ C * (|p.1 - q.1| + |p.2 - q.2|)) ∧
      ∀ᶠ x : Real in atTop,
        |passageTestExpectation P Y Yleft death x f - passageTestExpectation P Y Yleft death x g| ≤ ε ∧
        |(1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, g (z - y, y) ∂Pi ∂volume)| ≤ ε := by
  intro f hf hf0 ε hε
  have hμ : 0 < (∫ omega, Y 1 omega ∂P) := hPositiveMean
  have hK : 0 ≤ (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    exact ENNReal.toReal_nonneg
  have hKμ : 0 ≤ (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P) :=
    div_nonneg hK (le_of_lt hμ)
  set η : Real := ε / (2 * (1 + (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P))) with hηdef
  have hden : (0 : Real) < 2 * (1 + (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P)) := by linarith
  have hη : 0 < η := div_pos hε hden
  obtain ⟨g, hg, hg0, hCg, hsup⟩ := Kyprianou.Ch05.lipschitzTestDensity
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice f hf hf0 η hη
  have hstab := Kyprianou.Ch05.passageWindowStability
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice f g hf hg hf0 hg0 η hη hsup
  have he : η * (1 + (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P)) = ε / 2 := by
    rw [hηdef]
    field_simp
  have hηε : η ≤ ε := by
    have h1 : η ≤ η * (1 + (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P)) := by
      have h2 : (1 : Real) ≤ 1 + (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P) := by linarith
      calc η = η * 1 := (mul_one η).symm
        _ ≤ η * (1 + (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P)) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt hη)
    linarith
  have hbound : η * ((∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P)) ≤ ε := by
    have h1 : η * ((∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P))
        ≤ η * (1 + (∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P)) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hη)
    linarith
  exact ⟨g, hg, hg0, hCg, hstab.mono fun x hx => ⟨le_trans hx.1 hηε, le_trans hx.2 hbound⟩⟩
