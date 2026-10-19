-- Prove2me | solution 1 for OAI.NCHitting.coeff_J
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:30:18.499609+00:00
-- url     : https://prove2.me/submissions/75b17908-ed4c-4d3e-ac66-20f0866f5ac5

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Series.lean:L107-L123
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.coeff_J. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.Series ----
namespace OAI

noncomputable section
open PowerSeries
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem coeff_J (i r : ℕ) (a : PowerSeries F) :
    PowerSeries.coeff r (J i a) =
      ∑ q ∈ Finset.range r,
        ((-1 : F)^(r-q-1) / ((r : F) * (i : F)^(r-q))) * PowerSeries.coeff q a := by
  cases r with
  | zero => simp [J]
  | succ r =>
    rw [J, coeff_integral_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    have hqr : q ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hsub' : r+1-q = r-q+1 := by omega
    simp only [coeff_kernel, hsub', Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

section Map
variable {K : Type*} [Field K] [CharZero K]

end Map

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open PowerSeries


theorem solution : type_of% @_root_.OAI.NCHitting.coeff_J := @_root_.OAI.NCHitting.coeff_J
