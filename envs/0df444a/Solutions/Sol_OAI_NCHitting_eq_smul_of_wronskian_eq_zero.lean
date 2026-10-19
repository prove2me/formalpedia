-- Prove2me | solution 1 for OAI.NCHitting.eq_smul_of_wronskian_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:32:44.950649+00:00
-- url     : https://prove2.me/submissions/329a20e1-103e-4d67-ae66-5c0128cddef9

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Independence.lean:L22-L58
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.eq_smul_of_wronskian_eq_zero. The node keeps its source
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

omit [CharZero F] in
theorem wronskian_mul_common (g p q : F[X]) :
    Polynomial.wronskian (g*p) (g*q) = g^2 * Polynomial.wronskian p q := by
  simp only [Polynomial.wronskian, Polynomial.derivative_mul]
  ring

theorem eq_smul_of_wronskian_eq_zero (p q : F[X]) (hp : p ≠ 0)
    (hw : Polynomial.wronskian p q = 0) : ∃ c : F, q = c • p := by
  classical
  let : GCDMonoid F[X] := IsBezout.toGCDDomain _
  obtain ⟨a, b, ha, hb, hab⟩ := extract_gcd p q
  let g := gcd p q
  change p = g * a at ha
  change q = g * b at hb
  have hg : g ≠ 0 := by
    intro h
    apply hp
    simpa [h] using ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hp
    simpa [h] using ha
  have hwab : Polynomial.wronskian a b = 0 := by
    have hfactor : Polynomial.wronskian p q = g^2 * Polynomial.wronskian a b :=
      (congrArg₂ Polynomial.wronskian ha hb).trans (wronskian_mul_common g a b)
    rw [hfactor] at hw
    exact (mul_eq_zero.mp hw).resolve_left (pow_ne_zero _ hg)
  have hcop : IsCoprime a b := (gcd_isUnit_iff a b).mp hab
  obtain ⟨had, hbd⟩ := hcop.wronskian_eq_zero_iff.mp hwab
  have hac : a = C (a.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero had
  have hbc : b = C (b.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hbd
  have hac0 : a.coeff 0 ≠ 0 := by
    intro h
    apply ha0
    simpa [h] using hac
  refine ⟨b.coeff 0 / a.coeff 0, ?_⟩
  rw [Polynomial.smul_eq_C_mul]
  calc
    q = g * C (b.coeff 0) := hb.trans (congrArg (g * ·) hbc)
    _ = C (b.coeff 0 / a.coeff 0) * (g * C (a.coeff 0)) := by
      rw [mul_left_comm, ← C_mul, div_mul_cancel₀ _ hac0]
    _ = C (b.coeff 0 / a.coeff 0) * p :=
      congrArg (C (b.coeff 0 / a.coeff 0) * ·) (ha.trans (congrArg (g * ·) hac)).symm

section FormalResidue
open PowerSeries

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


theorem solution : type_of% @_root_.OAI.NCHitting.eq_smul_of_wronskian_eq_zero := @_root_.OAI.NCHitting.eq_smul_of_wronskian_eq_zero
