-- Prove2me | solution 1 for OAI.NCHitting.no_polynomial_log_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:34:46.077128+00:00
-- url     : https://prove2.me/submissions/4f1353a1-931c-4c66-83c9-cda143f6d207

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Independence.lean:L207-L225
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.no_polynomial_log_primitive. The node keeps its source
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
import Theorems.Thm_OAI_NCHitting_formal_residue_obstruction

-- ---- from OAI.Algebra.FormulaHitting.Independence ----
namespace OAI

noncomputable section
open Polynomial
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F]

section FormalResidue
open PowerSeries

theorem polynomial_residue_obstruction (a : F) (p0 p Q S : F[X])
    (hp0 : p0 ≠ 0) (hQ : Q.eval a ≠ 0)
    (h : ((Polynomial.X - Polynomial.C a) * Q) *
        (p0 * p.derivative - p0.derivative * p) + p0^2 * S = 0) : S.eval a = 0 := by
  let shift := Polynomial.X + Polynomial.C a
  have hzero : (p0.comp shift : PowerSeries F) ≠ 0 := by
    simpa [shift, Polynomial.comp_X_add_C_eq_zero_iff] using hp0
  have hQzero : PowerSeries.constantCoeff (Q.comp shift : PowerSeries F) ≠ 0 := by
    simpa [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
      shift, Polynomial.eval_comp] using hQ
  have heq : (PowerSeries.X * (Q.comp shift : PowerSeries F)) *
      ((p0.comp shift : PowerSeries F) * PowerSeries.derivative (R := F) (p.comp shift : PowerSeries F) -
        PowerSeries.derivative (R := F) (p0.comp shift : PowerSeries F) * (p.comp shift : PowerSeries F)) +
      (p0.comp shift : PowerSeries F)^2 * (S.comp shift : PowerSeries F) = 0 := by
    have hh := congrArg (fun r : F[X] => (r.comp shift : PowerSeries F)) h
    simpa [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.pow_comp,
      PowerSeries.derivative_coe, Polynomial.derivative_comp, shift] using hh
  have hs := formal_residue_obstruction _ _ _ _ hzero hQzero heq
  simpa [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    shift, Polynomial.eval_comp] using hs

end FormalResidue

section DistinctPoles
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharZero F] in
theorem poleProduct_eq (a : ι → F) (i : ι) :
    poleProduct a = (Polynomial.X - Polynomial.C (a i)) * puncturedPoleProduct a i := by
  exact (Finset.mul_prod_erase Finset.univ (fun j => Polynomial.X - Polynomial.C (a j))
    (Finset.mem_univ i)).symm

omit [CharZero F] in
theorem eval_puncturedPoleProduct_self_ne_zero (a : ι → F) (ha : Function.Injective a) (i : ι) :
    (puncturedPoleProduct a i).eval (a i) ≠ 0 := by
  simp only [puncturedPoleProduct, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  have hji := (Finset.mem_erase.mp hj).1
  exact hji (ha he).symm

omit [CharZero F] in
theorem eval_puncturedPoleProduct_other (a : ι → F) (i j : ι) (hij : i ≠ j) :
    (puncturedPoleProduct a j).eval (a i) = 0 := by
  simp only [puncturedPoleProduct, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_eq_zero (i := i)
  · simp [hij]
  · simp

theorem no_polynomial_log_primitive (a : ι → F) (ha : Function.Injective a)
    (p0 p : F[X]) (hp0 : p0 ≠ 0) (c : ι → F)
    (h : poleProduct a * (p0 * p.derivative - p0.derivative * p) +
      p0^2 * (∑ i, Polynomial.C (c i) * puncturedPoleProduct a i) = 0) :
    ∀ i, c i = 0 := by
  intro i
  have hr := polynomial_residue_obstruction (a i) p0 p (puncturedPoleProduct a i)
    (∑ j, Polynomial.C (c j) * puncturedPoleProduct a j) hp0
    (eval_puncturedPoleProduct_self_ne_zero a ha i) (by simpa [poleProduct_eq a i] using h)
  have heval : (∑ j, Polynomial.C (c j) * puncturedPoleProduct a j).eval (a i) =
      c i * (puncturedPoleProduct a i).eval (a i) := by
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    apply Finset.sum_eq_single i
    · intro j hj hji
      simp [eval_puncturedPoleProduct_other a i j (Ne.symm hji)]
    · simp
  rw [heval] at hr
  exact (mul_eq_zero.mp hr).resolve_right (eval_puncturedPoleProduct_self_ne_zero a ha i)

end DistinctPoles

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open Polynomial


theorem solution : type_of% @_root_.OAI.NCHitting.no_polynomial_log_primitive := @_root_.OAI.NCHitting.no_polynomial_log_primitive
