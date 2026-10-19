-- Prove2me | solution 1 for OAI.NCHitting.scaled_derivative_row
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:19:39.723271+00:00
-- url     : https://prove2.me/submissions/58c74e52-54d8-419f-b05c-741d75ef995c

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/ScaledDerivatives.lean:L67-L91
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.scaled_derivative_row. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.ScaledDerivatives ----
namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Polynomial Matrix

variable {F : Type*} [Field F]
variable {I : Type*} [Fintype I]

theorem derivative_scaled_power (q f : PowerSeries F) (j : ℕ) :
    q * PowerSeries.derivative (R := F) (q^j * f) =
      (j : PowerSeries F) * PowerSeries.derivative (R := F) q * (q^j * f) +
        q^(j+1) * PowerSeries.derivative (R := F) f := by
  rw [Derivation.leibniz]
  cases j with
  | zero => simp
  | succ j =>
    rw [PowerSeries.derivative_pow]
    simp only [Nat.add_sub_cancel, smul_eq_mul, pow_succ]
    ring

theorem coePolynomial_sum (Z : I → F[X]) :
    ((∑ t : I, Z t : F[X]) : PowerSeries F) = ∑ t : I, (Z t : PowerSeries F) :=
  map_sum Polynomial.coeToPowerSeries.ringHom Z Finset.univ

theorem coePolynomial_sub (p q : F[X]) :
    ((p - q : F[X]) : PowerSeries F) = (p : PowerSeries F) - (q : PowerSeries F) :=
  map_sub Polynomial.coeToPowerSeries.ringHom p q

theorem coePolynomial_natCast (k : ℕ) :
    ((k : F[X]) : PowerSeries F) = (k : PowerSeries F) :=
  map_natCast Polynomial.coeToPowerSeries.ringHom k

theorem derivative_polynomial_row (q : F[X]) (P : Matrix I I F[X])
    (G : Matrix I I (PowerSeries F))
    (hG : ∀ t l, (q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l) =
      ∑ a : I, (P t a : PowerSeries F) * G a l)
    (Z : I → F[X]) (l : I) :
    (q : PowerSeries F) * PowerSeries.derivative (R := F)
        (∑ t : I, (Z t : PowerSeries F) * G t l) =
      ∑ t : I, ((q * (Z t).derivative + ∑ a : I, Z a * P a t : F[X]) :
        PowerSeries F) * G t l := by
  classical
  calc
    _ = ∑ t : I, (((q : PowerSeries F) * ((Z t).derivative : PowerSeries F)) * G t l +
          (Z t : PowerSeries F) * ((q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l))) := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Derivation.leibniz, PowerSeries.derivative_coe]
      simp only [smul_eq_mul]
      ring
    _ = ∑ t : I, (((q : PowerSeries F) * ((Z t).derivative : PowerSeries F)) * G t l +
          ∑ a : I, (Z t : PowerSeries F) * (P t a : PowerSeries F) * G a l) := by
      simp_rw [hG, Finset.mul_sum, mul_assoc]
    _ = _ := by
      simp only [Polynomial.coe_add, Polynomial.coe_mul, coePolynomial_sum,
        add_mul, Finset.sum_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]

theorem scaled_derivative_row (q : F[X]) (P : Matrix I I F[X]) (u : I → F)
    (G : Matrix I I (PowerSeries F))
    (hG : ∀ t l, (q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l) =
      ∑ a : I, (P t a : PowerSeries F) * G a l)
    (j : ℕ) (l : I) :
    (q : PowerSeries F)^j * derivativeIter j
        (∑ t : I, PowerSeries.C (u t) * G t l) =
      ∑ t : I, (numeratorRow q P u j t : PowerSeries F) * G t l := by
  classical
  induction j with
  | zero => simp [derivativeIter, numeratorRow]
  | succ j ih =>
    have hd := congrArg (fun f : PowerSeries F =>
      (q : PowerSeries F) * PowerSeries.derivative (R := F) f) ih
    rw [derivative_scaled_power, derivative_polynomial_row q P G hG] at hd
    have he := eq_sub_of_add_eq' hd
    change (q : PowerSeries F)^(j+1) * PowerSeries.derivative (R := F)
      (derivativeIter j (∑ t : I, PowerSeries.C (u t) * G t l)) = _
    rw [he, ih]
    simp only [numeratorRow, Polynomial.coe_add, coePolynomial_sub,
      Polynomial.coe_mul, coePolynomial_sum,
      PowerSeries.derivative_coe, Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, add_mul, sub_mul, map_natCast, coePolynomial_natCast]
    simp only [mul_comm, mul_left_comm, mul_assoc]
    ring

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open PowerSeries Polynomial Matrix


theorem solution : type_of% @_root_.OAI.NCHitting.scaled_derivative_row := @_root_.OAI.NCHitting.scaled_derivative_row
