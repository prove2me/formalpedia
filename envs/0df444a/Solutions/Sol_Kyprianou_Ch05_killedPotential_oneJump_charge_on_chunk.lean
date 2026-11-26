-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_oneJump_charge_on_chunk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T09:25:52.668055+00:00
-- url     : https://prove2.me/submissions/20a0259d-4075-4848-a06b-f6d728076e7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_oneJump_shiftedChunk_charge
import Theorems.Thm_Kyprianou_Ch05_killedPotential_shiftedChunk_le_offLattice_integral
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
    ∀ h : Real, 0 < h → ∀ a b : Real, 0 < a → a ≤ b →
      (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) →
      ∃ δ : Real, 0 < δ ∧ ENNReal.ofReal (δ^2 / 4) * Pi (Set.Icc a b) ≤
        ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume) := by
  intro hfin h hh a b ha hab hoff
  obtain ⟨δ, hδ, hJ1⟩ := Kyprianou.Ch05.killedPotential_oneJump_shiftedChunk_charge
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential
    hfin h hh a b ha hab hoff
  have hJ2 := Kyprianou.Ch05.killedPotential_shiftedChunk_le_offLattice_integral
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential
    h hh a b ha hab hoff δ
  refine ⟨δ, hδ, ?_⟩
  have hle : ENNReal.ofReal (δ^2 / 4) ≤ ENNReal.ofReal (δ^2 / 3) :=
    ENNReal.ofReal_le_ofReal (by have h2 : (0 : Real) ≤ δ^2 := sq_nonneg δ; linarith)
  have hconst : ENNReal.ofReal (δ^2 / 4) * Pi (Set.Icc a b) ≤
      ENNReal.ofReal (δ^2 / 3) * Pi (Set.Icc a b) :=
    mul_le_mul hle le_rfl bot_le bot_le
  exact hconst.trans (hJ1.trans hJ2)
