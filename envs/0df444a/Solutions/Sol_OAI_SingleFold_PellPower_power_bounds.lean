-- Prove2me | solution 1 for OAI.SingleFold.PellPower.power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:14:22.849783+00:00
-- url     : https://prove2.me/submissions/7f8dcaa7-31e0-467c-bce0-be7f4954e222

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell

open OAI OAI.SingleFold OAI.SingleFold.PellPower
variable {a : ℕ} (ha : 1 < a)


theorem solution (n : ℕ) :
    (2*a-1)^n ≤ Pell.yn ha (n+1) ∧ Pell.yn ha (n+1) ≤ (2*a)^n := by
  induction n with
  | zero => simp [Pell.yn_one]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hs := Pell.yn_succ_succ ha n
    have hm : Pell.yn ha n ≤ Pell.yn ha (n+1) := (Pell.strictMono_y ha (Nat.lt_succ_self n)).le
    have ha1 : 1 ≤ 2 * a := by omega
    constructor
    · rw [pow_succ]
      have : (2*a-1) * Pell.yn ha (n+1) ≤ Pell.yn ha (n+2) := by
        have e : (2*a-1) * Pell.yn ha (n+1) + Pell.yn ha (n+1) = 2*a*Pell.yn ha (n+1) := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel ha1]
        omega
      calc (2*a-1)^n * (2*a-1) ≤ Pell.yn ha (n+1) * (2*a-1) := Nat.mul_le_mul_right _ ih1
        _ = (2*a-1) * Pell.yn ha (n+1) := mul_comm _ _
        _ ≤ _ := this
    · rw [pow_succ]
      calc Pell.yn ha (n+2) ≤ 2*a*Pell.yn ha (n+1) := by omega
        _ = Pell.yn ha (n+1) * (2*a) := mul_comm _ _
        _ ≤ (2*a)^n * (2*a) := Nat.mul_le_mul_right _ ih2

