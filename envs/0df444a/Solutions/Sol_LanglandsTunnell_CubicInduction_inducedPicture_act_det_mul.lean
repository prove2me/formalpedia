-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.inducedPicture_act_det_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bedbc9a5-213b-5936-8c22-b729bd07cffe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul

set_option autoImplicit false

namespace WsC
namespace DC

open MvPolynomial

noncomputable section

abbrev R9 := MvPolynomial (Fin 3 × Fin 3) ℂ

def act (ν : Fin 3 → ℂ) (c d : Fin 3) (p : R9) : R9 :=
  (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
      (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
  ∑ i : Fin 3, ∑ j : Fin 3,
    (∑ m : Fin 3,
      (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
        else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
        else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
      MvPolynomial.pderiv (i, j) p

def D : R9 := (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : R9)).det

theorem D_eq : D = X (0, 0) * X (1, 1) * X (2, 2) - X (0, 0) * X (1, 2) * X (2, 1)
    - X (0, 1) * X (1, 0) * X (2, 2) + X (0, 1) * X (1, 2) * X (2, 0)
    + X (0, 2) * X (1, 0) * X (2, 1) - X (0, 2) * X (1, 1) * X (2, 0) := by
  rw [D, Matrix.det_fin_three]
  simp only [Matrix.of_apply]

theorem pdX (i j a b : Fin 3) :
    pderiv (i, j) (X (a, b) : R9) = if a = i ∧ b = j then 1 else 0 := by
  classical
  rw [pderiv_X, Pi.single_apply]
  simp only [Prod.mk.injEq]

theorem lt01 : (0 : Fin 3) < 1 := by decide
theorem lt02 : (0 : Fin 3) < 2 := by decide
theorem lt12 : (1 : Fin 3) < 2 := by decide
theorem nlt10 : ¬ (1 : Fin 3) < 0 := by decide
theorem nlt20 : ¬ (2 : Fin 3) < 0 := by decide
theorem nlt21 : ¬ (2 : Fin 3) < 1 := by decide
theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
theorem ne12 : (1 : Fin 3) ≠ 2 := by decide
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide

set_option maxHeartbeats 1600000 in
theorem key (ν : Fin 3 → ℂ) (c d : Fin 3) (P : R9) : act ν c d (D * P) = D * act ν c d P := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
  have hd : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
  · simp only [act, D_eq, Fin.sum_univ_three, lt01, lt02, lt12, nlt10, nlt20, nlt21, lt_self_iff_false,
      if_true, if_false, pderiv_mul, map_add, map_sub, pdX, ne01, ne10, ne02, ne20, ne12, ne21,
      and_true, and_false, true_and, false_and, if_true, if_false, mul_one, mul_zero, zero_mul,
      add_zero, zero_add, sub_zero, zero_sub]
    ring

theorem main
    (ν : Fin 3 → ℂ) (c d : Fin 3) (P : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    act ν c d ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * P) =
      (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * act ν c d P := by
  exact key ν c d P

end

end WsC.DC

theorem solution
    (ν : Fin 3 → ℂ) (c d : Fin 3) (P : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    act ν c d ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * P) =
      (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * act ν c d P := by
  exact WsC.DC.main ν c d P

end S_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul (solution)
