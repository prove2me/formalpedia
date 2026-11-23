-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_degree_at_least_two_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T21:19:51.230042+00:00
-- url     : https://prove2.me/submissions/69fe4a81-17e5-4a57-9c8b-1cfbdc055080
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2ExplicitSource
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_explicit_source_witness
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

lemma pderiv0_X0 : pderiv (0 : Fin 6) (X 0 : AmbientPoly 5) = 1 := by simp [pderiv_X_self]
lemma pderiv0_X1 : pderiv (0 : Fin 6) (X (1 : Fin 6) : AmbientPoly 5) = 0 := by simp [pderiv_X_of_ne]
lemma pderiv0_X2 : pderiv (0 : Fin 6) (X (2 : Fin 6) : AmbientPoly 5) = 0 := by simp [pderiv_X_of_ne]
lemma pderiv0_X3 : pderiv (0 : Fin 6) (X (3 : Fin 6) : AmbientPoly 5) = 0 := by simp [pderiv_X_of_ne]
lemma pderiv0_X4 : pderiv (0 : Fin 6) (X (4 : Fin 6) : AmbientPoly 5) = 0 := by simp [pderiv_X_of_ne]
lemma pderiv0_X5 : pderiv (0 : Fin 6) (X (5 : Fin 6) : AmbientPoly 5) = 0 := by simp [pderiv_X_of_ne]

lemma d0F :
    pderiv (0 : Fin 6) (F : AmbientPoly 5) =
      X 0 ^ 2 * X 1 * X 3 * X 4 * C (1 / 2 : ℂ) * 3 + X 0 ^ 5 * 6 +
        X 3 * C (1 / 2 : ℂ) * X 2 ^ 3 * X 5 := by
  simp only [F, n, Derivation.map_add, pderiv_mul, pderiv_pow, pderiv_C_mul, pderiv_C,
    pderiv0_X0, pderiv0_X1, pderiv0_X2, pderiv0_X3, pderiv0_X4, pderiv0_X5, mul_zero, zero_mul,
    add_zero, zero_add, mul_one, one_mul, Nat.cast_ofNat,
    show (6 : ℕ) - 1 = 5 from by decide, show (3 : ℕ) - 1 = 2 from by decide]
  ring

lemma pderiv0_three : pderiv (0 : Fin 6) (3 : AmbientPoly 5) = 0 := by
  have : (3 : AmbientPoly 5) = 1 + 1 + 1 := by norm_num
  rw [this, Derivation.map_add, Derivation.map_add, pderiv_one]
  simp

lemma pderiv0_six : pderiv (0 : Fin 6) (6 : AmbientPoly 5) = 0 := by
  have : (6 : AmbientPoly 5) = 3 + 3 := by norm_num
  rw [this, Derivation.map_add, pderiv0_three]
  simp

lemma d00F :
    pderiv (0 : Fin 6) (pderiv (0 : Fin 6) (F : AmbientPoly 5)) =
      X 0 * X 1 * X 3 * X 4 * C (1 / 2 : ℂ) * 3 * 2 + X 0 ^ 4 * 6 * 5 := by
  rw [d0F]
  simp only [Derivation.map_add, pderiv_mul, pderiv_pow, pderiv_C_mul, pderiv_C, pderiv0_three,
    pderiv0_X0, pderiv0_X1, pderiv0_X2, pderiv0_X3, pderiv0_X4, pderiv0_X5, pderiv0_three,
    pderiv0_six,
    mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, Nat.cast_ofNat,
    show (2 : ℕ) - 1 = 1 from by decide, show (5 : ℕ) - 1 = 4 from by decide]
  ring

def PF0 : AmbientPoly 5 := NormalChart.normal (F : AmbientPoly 5)

def dBGoal : AmbientPoly 5 :=
  C (2⁻¹ : ℂ) * (X 0 * X 1 ^ 2 * X 2 ^ 3 * X 3 ^ 2 * X 4 ^ 2 * X 5 * 2)

def PGoal : AmbientPoly 5 :=
  X 0 ^ 2 * X 1 * X 3 * X 4 * C (1 / 2 : ℂ) * 3 + X 0 ^ 5 * 6 +
    X 3 * C (1 / 2 : ℂ) * X 2 ^ 3 * X 5

def P00Goal : AmbientPoly 5 :=
  X 0 * X 1 * X 3 * X 4 * C (1 / 2 : ℂ) * 3 * 2 + X 0 ^ 4 * 6 * 5

lemma d0B_ann :
    pderiv (0 : Fin 6)
        (C (2⁻¹ : ℂ) * (X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 3 * X 3 ^ 2 * X 4 ^ 2 * X 5 : AmbientPoly 5)) =
      dBGoal := by
  unfold dBGoal
  rw [pderiv_C_mul]
  simp only [Derivation.map_add, pderiv_mul, pderiv_pow, pderiv_C, pderiv0_X0, pderiv0_X1,
    pderiv0_X2, pderiv0_X3, pderiv0_X4, pderiv0_X5, mul_zero, zero_mul, add_zero, zero_add,
    mul_one, one_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from by decide]
  ring

lemma PF_eq : PF0 = PGoal := by
  unfold PF0 NormalChart.normal PGoal
  exact d0F

lemma P00_eq : pderiv (0 : Fin 6) PF0 = P00Goal := by
  unfold PF0 NormalChart.normal P00Goal
  exact d00F

lemma dB_eq : pderiv (0 : Fin 6) chartPole = dBGoal := by
  unfold chartPole A n
  exact d0B_ann

lemma source_eq_probe : PF0 * pderiv (0 : Fin 6) chartPole - chartPole * pderiv (0 : Fin 6) PF0 = explicitSource := by
  rw [dB_eq, P00_eq, PF_eq]
  unfold PGoal dBGoal P00Goal explicitSource chartPole A n
  ring

lemma residue_explicit (S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5) :
    NormalChart.residue (F : AmbientPoly 5) chartPole S W =
      S ^ 2 * explicitSource +
        (NormalChart.residue (F : AmbientPoly 5) chartPole S W -
          S ^ 2 *
            (NormalChart.normal (F : AmbientPoly 5) * pderiv (0 : Fin 6) chartPole -
              chartPole * pderiv (0 : Fin 6) (NormalChart.normal (F : AmbientPoly 5)))) := by
  have hsrc :
      NormalChart.normal (F : AmbientPoly 5) * pderiv (0 : Fin 6) chartPole -
        chartPole * pderiv (0 : Fin 6) (NormalChart.normal (F : AmbientPoly 5)) = explicitSource := by
    simpa only [PF0] using source_eq_probe
  rw [← hsrc]
  ring

/-- The degree-at-least-two witness is the same existence with the source factor
`∂₀F · ∂₀B − B · ∂₀∂₀F` replaced by the expanded polynomial `explicitSource`. -/
theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      NormalChart.residue F (MvPolynomial.C ((2 : ℂ)⁻¹) * A) S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_explicit_source_witness
  refine ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, ?_⟩
  have eqv := residue_explicit (S : AmbientPoly 5) (W : Fin 5 → AmbientPoly 5)
  exact eqv.trans hchild
