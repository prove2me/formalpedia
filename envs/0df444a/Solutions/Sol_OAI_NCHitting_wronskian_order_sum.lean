-- Prove2me | solution 1 for OAI.NCHitting.wronskian_order_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:18:01.764182+00:00
-- url     : https://prove2.me/submissions/dc9cf5fb-4f29-4829-8607-6ea976c9b681

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Wronskian.lean:L163-L190
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.wronskian_order_sum. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.Wronskian ----
namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Matrix

variable {F : Type*} [Field F]

theorem coeff_derivativeIter (j r : ℕ) (f : PowerSeries F) :
    PowerSeries.coeff r (derivativeIter j f) =
      PowerSeries.coeff (r+j) f * ((r+j).descFactorial j : F) := by
  induction j generalizing r with
  | zero => simp [derivativeIter]
  | succ j ih =>
    rw [derivativeIter, PowerSeries.coeff_derivative, ih]
    have he : r + 1 + j = r + (j + 1) := by omega
    have hs : r + (j + 1) - j = r + 1 := by omega
    rw [he, Nat.descFactorial_succ, hs, Nat.cast_mul]
    push_cast
    ring

theorem coeff_X_pow_derivativeIter (j r : ℕ) (f : PowerSeries F) :
    PowerSeries.coeff r (PowerSeries.X ^ j * derivativeIter j f) =
      PowerSeries.coeff r f * (r.descFactorial j : F) := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_derivativeIter, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega), Nat.cast_zero, mul_zero]

theorem X_pow_derivativeIter_eq (f : PowerSeries F) (a j : ℕ)
    (h : ∀ r < a, PowerSeries.coeff r f = 0) :
    PowerSeries.X ^ j * derivativeIter j f =
      PowerSeries.X ^ a * derivativeTail f a j := by
  ext r
  rw [coeff_X_pow_derivativeIter, PowerSeries.coeff_X_pow_mul']
  split_ifs with ha
  · rw [coeff_derivativeTail, Nat.sub_add_cancel ha]
  · rw [h r (by omega), zero_mul]

theorem wronskianMatrix_scaling {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (h : ∀ l r, r < a l → PowerSeries.coeff r (b l) = 0) :
    Matrix.diagonal (fun j : Fin k => (PowerSeries.X : PowerSeries F)^j.val) *
      wronskianMatrix b =
    normalizedWronskianMatrix b a *
      Matrix.diagonal (fun l => (PowerSeries.X : PowerSeries F)^(a l)) := by
  ext j l
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, wronskianMatrix,
    normalizedWronskianMatrix]
  rw [X_pow_derivativeIter_eq (b l) (a l) j.val (h l), mul_comm]

theorem wronskian_det_scaling {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (h : ∀ l r, r < a l → PowerSeries.coeff r (b l) = 0) :
    ((∏ j : Fin k, (PowerSeries.X : PowerSeries F)^j.val) * wronskian b) =
      (normalizedWronskianMatrix b a).det *
        ∏ l : Fin k, (PowerSeries.X : PowerSeries F)^(a l) := by
  have hd := congrArg Matrix.det (wronskianMatrix_scaling b a h)
  simpa only [Matrix.det_mul, Matrix.det_diagonal, wronskian] using hd

theorem det_descFactorial {k : ℕ} (a : Fin k → ℕ) :
    (Matrix.of fun j l : Fin k => ((a l).descFactorial j.val : F)).det =
      (Matrix.vandermonde fun l => (a l : F)).det := by
  have hh := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun l : Fin k => (a l : F)) (fun j : Fin k => descPochhammer F j.val)
    (fun j => descPochhammer_natDegree F j.val)
    (fun j => monic_descPochhammer F j.val)
  rw [← Matrix.det_transpose]
  change (Matrix.of fun i j : Fin k => ((a i).descFactorial j.val : F)).det = _
  simpa only [descPochhammer_eval_eq_descFactorial] using hh.symm

theorem det_descFactorial_ne_zero [CharZero F] {k : ℕ} (a : Fin k → ℕ)
    (ha : Function.Injective a) :
    (Matrix.of fun j l : Fin k => ((a l).descFactorial j.val : F)).det ≠ 0 := by
  rw [det_descFactorial]
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  exact (Nat.cast_injective (R := F)).comp ha

theorem normalizedWronskian_constant_ne_zero [CharZero F] {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (ha : Function.Injective a)
    (hb : ∀ l, PowerSeries.coeff (a l) (b l) ≠ 0) :
    PowerSeries.constantCoeff (normalizedWronskianMatrix b a).det ≠ 0 := by
  have he : (PowerSeries.constantCoeff : PowerSeries F →+* F).mapMatrix
      (normalizedWronskianMatrix b a) =
      (Matrix.of fun j l : Fin k => ((a l).descFactorial j.val : F)) *
        Matrix.diagonal (fun l => PowerSeries.coeff (a l) (b l)) := by
    funext j l
    rw [Matrix.mul_diagonal]
    change PowerSeries.constantCoeff (derivativeTail (b l) (a l) j.val) =
      ((a l).descFactorial j.val : F) * PowerSeries.coeff (a l) (b l)
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_derivativeTail, Nat.zero_add]
    exact mul_comm _ _
  rw [RingHom.map_det, he, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (det_descFactorial_ne_zero a ha) (Finset.prod_ne_zero_iff.mpr (fun l _ => hb l))

theorem wronskian_order_sum [CharZero F] {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (ha : Function.Injective a)
    (hb : ∀ l, PowerSeries.coeff (a l) (b l) ≠ 0)
    (hz : ∀ l r, r < a l → PowerSeries.coeff r (b l) = 0) :
    wronskian b ≠ 0 ∧
      (wronskian b).order.toNat + (∑ j : Fin k, j.val) = ∑ l : Fin k, a l := by
  have hc := normalizedWronskian_constant_ne_zero b a ha hb
  have hn : (normalizedWronskianMatrix b a).det ≠ 0 := by
    intro h
    exact hc (by rw [h, map_zero])
  have ho : (normalizedWronskianMatrix b a).det.order = 0 := by
    apply PowerSeries.order_eq_nat.mpr
    exact ⟨by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hc,
      fun r hr => (Nat.not_lt_zero r hr).elim⟩
  have he := wronskian_det_scaling b a hz
  simp only [Finset.prod_pow_eq_pow_sum] at he
  have hw : wronskian b ≠ 0 := by
    intro h
    rw [h, mul_zero] at he
    exact (mul_ne_zero hn (pow_ne_zero _ PowerSeries.X_ne_zero)) he.symm
  refine ⟨hw, ?_⟩
  have hord := congrArg PowerSeries.order he
  rw [PowerSeries.order_mul, PowerSeries.order_mul, ho, zero_add,
    PowerSeries.order_X_pow, PowerSeries.order_X_pow,
    ← PowerSeries.coe_toNat_order hw] at hord
  have heq : (∑ j : Fin k, j.val) + (wronskian b).order.toNat = ∑ l : Fin k, a l := by
    exact_mod_cast hord
  omega

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open PowerSeries Matrix


theorem solution : type_of% @_root_.OAI.NCHitting.wronskian_order_sum := @_root_.OAI.NCHitting.wronskian_order_sum
