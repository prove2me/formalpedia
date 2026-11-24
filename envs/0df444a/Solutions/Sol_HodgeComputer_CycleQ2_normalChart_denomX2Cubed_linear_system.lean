-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_denomX2Cubed_linear_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:32:05.660523+00:00
-- url     : https://prove2.me/submissions/4146f15b-2c4d-4d5a-88b1-f81b0b2ce203
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Definitions.Def_HodgeComputerCycleQ2Character
import Definitions.Def_HodgeComputerCycleQ2NumeratorCharacter
import Definitions.Def_HodgeComputerCycleQ2DenomX2Cubed
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_denomX2Cubed_carrier_system
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

/-- Converse of `carrier_of_system`: carrier form implies the graded linear equation. -/
lemma graded_of_carrier (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n)
    (h : divergenceCarrier S W = F ^ 2 * Q) :
    gradedLinear S W Q = gradedInhomogeneous S := by
  let S5 : AmbientPoly 5 := S
  let Q5 : AmbientPoly 5 := Q
  let F5 : AmbientPoly 5 := F
  let div : AmbientPoly 5 := chartDivergence S W
  let src : AmbientPoly 5 := sparseSource
  have hL : gradedLinear S W Q = div - F5 ^ 2 * Q5 := by
    unfold gradedLinear
    rfl
  have hI : gradedInhomogeneous S = (-1 : AmbientPoly 5) * (S5 ^ 2 * src) := by
    unfold gradedInhomogeneous
    rfl
  have hC : divergenceCarrier S W = div + S5 ^ 2 * src := by
    unfold divergenceCarrier
    rfl
  have hCar : divergenceCarrier S W = F5 ^ 2 * Q5 := by
    convert h
    rfl
  have h5 : div + S5 ^ 2 * src = F5 ^ 2 * Q5 := hC.symm.trans hCar
  have h5' : div - F5 ^ 2 * Q5 = - (S5 ^ 2 * src) := by
    rw [← sub_eq_zero]
    calc
      div - F5 ^ 2 * Q5 - (-(S5 ^ 2 * src))
          = (div - F5 ^ 2 * Q5) + S5 ^ 2 * src := by abel
      _ = (div + S5 ^ 2 * src) - F5 ^ 2 * Q5 := by abel
      _ = F5 ^ 2 * Q5 - F5 ^ 2 * Q5 := by rw [h5]
      _ = 0 := by abel
  have h6 : div - F5 ^ 2 * Q5 = (-1 : AmbientPoly 5) * (S5 ^ 2 * src) := by
    refine h5'.trans ?_
    ring
  exact (hL.trans h6).trans hI.symm

theorem solution :
    ∃ (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      (∀ j, (W j).IsHomogeneous (3 + 7)) ∧
      Q.IsHomogeneous (2 * 3 + 4) ∧
      IsCharacter 1 (Q : AmbientPoly 5) ∧
      (∀ j, IsCharacter (numeratorCharacter j) (W j : AmbientPoly 5)) ∧
      gradedLinear denomX2Cubed W Q = gradedInhomogeneous denomX2Cubed := by
  obtain ⟨W, Q, hW, hQhom, hQ1, hWn, hcar⟩ :=
    HodgeComputer.CycleQ2.normalChart_denomX2Cubed_carrier_system
  -- Child states `= (F : AmbientPoly n) ^ 2 * Q`; convert to bare `F ^ 2 * Q`.
  have hcar' : divergenceCarrier denomX2Cubed W = F ^ 2 * Q := by
    simpa using hcar
  exact ⟨W, Q, hW, hQhom, hQ1, hWn, graded_of_carrier denomX2Cubed W Q hcar'⟩
