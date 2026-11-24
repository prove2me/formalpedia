-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_homogeneous_quotient_membership
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:55:59.223115+00:00
-- url     : https://prove2.me/submissions/f10864a7-446e-4ccd-801d-d783c2d7d0f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2ChartDivergence
import Definitions.Def_HodgeComputerCycleQ2GradedLinear
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_graded_linear_system
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

lemma carrier_of_system (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n)
    (h : gradedLinear S W Q = gradedInhomogeneous S) :
    divergenceCarrier S W = F ^ 2 * Q := by
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
  have h5 : div - F5 ^ 2 * Q5 = (-1 : AmbientPoly 5) * (S5 ^ 2 * src) :=
    (hL.symm.trans h).trans hI
  have h5' : div - F5 ^ 2 * Q5 = - (S5 ^ 2 * src) := by
    refine h5.trans ?_
    ring
  have h6 : div + S5 ^ 2 * src = F5 ^ 2 * Q5 := by
    rw [← sub_eq_zero]
    calc
      div + S5 ^ 2 * src - F5 ^ 2 * Q5
          = (div - F5 ^ 2 * Q5) + S5 ^ 2 * src := by abel
      _ = - (S5 ^ 2 * src) + S5 ^ 2 * src := by rw [h5']
      _ = 0 := by abel
  rw [hC]
  exact h6

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      Q.IsHomogeneous (2 * S.totalDegree + 4) ∧
      divergenceCarrier S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hQhom, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_graded_linear_system
  exact ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hQhom, carrier_of_system S W Q hchild⟩
