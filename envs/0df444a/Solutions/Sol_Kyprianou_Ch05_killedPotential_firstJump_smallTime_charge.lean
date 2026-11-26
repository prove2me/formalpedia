-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_firstJump_smallTime_charge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T04:25:29.209479+00:00
-- url     : https://prove2.me/submissions/3c84e2ae-2ad7-42ba-86df-9fd9a6e87f17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_offLattice_chunk
import Theorems.Thm_Kyprianou_Ch05_killedPotential_oneJump_charge_on_chunk
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
    ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≠ 0 →
      ∃ c : ℝ≥0∞, 0 < c ∧ ∃ δ : Real, 0 < δ ∧
        c ≤ ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume) := by
  intro hfin h hh hne
  obtain ⟨a, b, ha, hab, hchunk, hPi⟩ :=
    Kyprianou.Ch05.killedPotential_offLattice_chunk P Y death eta d Pi Phi
      hKilled hTriplet hLaplaceLaw U hPotential hfin h hh hne
  obtain ⟨δ, hδ, hcharge⟩ :=
    Kyprianou.Ch05.killedPotential_oneJump_charge_on_chunk P Y death eta d Pi Phi
      hKilled hTriplet hLaplaceLaw U hPotential hfin h hh a b ha hab hchunk
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : Real) :=
    fun z hz => lt_of_lt_of_le ha hz.1
  have hPiTop : Pi (Set.Icc a b) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsub) hfin)
  have hfactor : ENNReal.ofReal (δ ^ 2 / 4) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (by positivity)
  have hfactorTop : ENNReal.ofReal (δ ^ 2 / 4) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : 0 < ENNReal.ofReal (δ ^ 2 / 4) * Pi (Set.Icc a b) :=
    ENNReal.mul_pos hfactor hPi.ne'
  exact ⟨ENNReal.ofReal (δ ^ 2 / 4) * Pi (Set.Icc a b), hc, δ, hδ, hcharge⟩
