-- Prove2me | solution 1 for OAI.NCHitting.formal_residue_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:33:49.751198+00:00
-- url     : https://prove2.me/submissions/17e4e4d1-c54b-44e7-b26e-65437bca6687

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Independence.lean:L100-L147
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.formal_residue_obstruction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula
import Definitions.Def_OAI_Algebra_FormulaHitting_Representation
import Definitions.Def_OAI_Algebra_FormulaHitting_Series
import Definitions.Def_OAI_Algebra_FormulaHitting_System
import Definitions.Def_OAI_Algebra_FormulaHitting_Evaluation
import Definitions.Def_OAI_Algebra_FormulaHitting_FormulaSeries
import Definitions.Def_OAI_Algebra_FormulaHitting_Independence

-- ---- from OAI.Algebra.FormulaHitting.Independence ----
namespace OAI

noncomputable section
open Polynomial
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F]

section FormalResidue
open PowerSeries

theorem coeff_X_mul_derivative (v : PowerSeries F) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.X * PowerSeries.derivative (R := F) v) =
      (k : F) * PowerSeries.coeff k v := by
  cases k with
  | zero => simp
  | succ k =>
    have hs := PowerSeries.coeff_X_pow_mul (PowerSeries.derivative (R := F) v) 1 k
    simp only [pow_one] at hs
    rw [hs, PowerSeries.coeff_derivative]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem X_mul_derivative_X_pow (k : ℕ) :
    PowerSeries.X * PowerSeries.derivative (R := F) ((PowerSeries.X : PowerSeries F)^k) =
      PowerSeries.C (k : F) * PowerSeries.X^k := by
  ext r
  rw [coeff_X_mul_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs with hr
  · subst r; rfl
  · simp

private theorem formal_wronskian_factor (A v Q S : PowerSeries F) (k : ℕ) :
    (PowerSeries.X * Q) *
        ((PowerSeries.X^k * A) * PowerSeries.derivative (R := F) (A*v) -
          PowerSeries.derivative (R := F) (PowerSeries.X^k * A) * (A*v)) +
        (PowerSeries.X^k * A)^2 * S =
      PowerSeries.X^k * A^2 *
        (Q * (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) +
          PowerSeries.X^k * S) := by
  simp only [Derivation.leibniz, smul_eq_mul]
  calc
    _ = PowerSeries.X^k * A^2 * (Q * (PowerSeries.X * PowerSeries.derivative (R := F) v) +
          PowerSeries.X^k * S) -
        (PowerSeries.X * PowerSeries.derivative (R := F) (PowerSeries.X^k)) * A^2 * Q * v := by
          ring
    _ = _ := by rw [X_mul_derivative_X_pow]; ring

theorem formal_residue_obstruction (p0 p Q S : PowerSeries F)
    (hp0 : p0 ≠ 0) (hQ : PowerSeries.constantCoeff Q ≠ 0)
    (h : (PowerSeries.X * Q) *
        (p0 * PowerSeries.derivative (R := F) p - PowerSeries.derivative (R := F) p0 * p) +
        p0^2 * S = 0) : PowerSeries.constantCoeff S = 0 := by
  let k := p0.order.toNat
  let A := p0.divXPowOrder
  let v := A⁻¹ * p
  have hA : PowerSeries.constantCoeff A ≠ 0 := by
    exact mt PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp hp0
  have hA0 : A ≠ 0 := by
    intro he
    exact hA (by simp [he])
  have hpa : PowerSeries.X^k * A = p0 := PowerSeries.X_pow_order_mul_divXPowOrder
  have hav : A*v = p := by
    dsimp [v]
    rw [← mul_assoc, MvPowerSeries.mul_inv_cancel A hA, one_mul]
  have hf : PowerSeries.X^k * A^2 *
      (Q * (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) +
        PowerSeries.X^k * S) = 0 := by
    rw [← formal_wronskian_factor]
    simpa only [hpa, hav] using h
  have hn : PowerSeries.X^k * A^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hA0)
  have he := (mul_eq_zero.mp hf).resolve_left hn
  have he' :
      (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) +
        PowerSeries.X^k * (Q⁻¹*S) = 0 := by
    calc
      _ = Q⁻¹ *
          (Q * (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) +
            PowerSeries.X^k * S) := by
        simp only [mul_add, ← mul_assoc, MvPowerSeries.inv_mul_cancel Q hQ, one_mul]
        ring
      _ = 0 := by rw [he, mul_zero]
  have hk := congrArg (PowerSeries.coeff k) he'
  have heuler : PowerSeries.coeff k
      (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) = 0 := by
    rw [map_sub, coeff_X_mul_derivative, PowerSeries.coeff_C_mul, sub_self]
  have hshift : PowerSeries.coeff k (PowerSeries.X^k * (Q⁻¹*S)) =
      PowerSeries.constantCoeff (Q⁻¹*S) := by
    simpa only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff] using
      PowerSeries.coeff_X_pow_mul (Q⁻¹*S) k 0
  rw [map_add, heuler, zero_add, hshift, map_zero] at hk
  rw [map_mul] at hk
  change (MvPowerSeries.constantCoeff Q⁻¹) * PowerSeries.constantCoeff S = 0 at hk
  rw [MvPowerSeries.constantCoeff_inv] at hk
  exact (mul_eq_zero.mp hk).resolve_left (inv_ne_zero hQ)

end FormalResidue

section DistinctPoles
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end DistinctPoles

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open Polynomial
open PowerSeries


theorem solution : type_of% @_root_.OAI.NCHitting.formal_residue_obstruction := @_root_.OAI.NCHitting.formal_residue_obstruction
