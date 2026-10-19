-- Prove2me | solution 1 for OAI.NCHitting.kernel_mul_linear
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:31:09.424698+00:00
-- url     : https://prove2.me/submissions/6303cfad-e8de-4533-b021-fc2a850acdd5

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Series.lean:L134-L149
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.kernel_mul_linear. The node keeps its source
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

theorem kernel_mul_linear (i : ℕ) (hi : i ≠ 0) :
    kernel (F := F) i * (PowerSeries.X + PowerSeries.C (i : F)) = 1 := by
  have hiF : (i : F) ≠ 0 := Nat.cast_ne_zero.mpr hi
  ext r
  cases r with
  | zero => simp [mul_add, kernel, hiF]
  | succ r =>
    rw [mul_add, map_add, PowerSeries.coeff_mul_C]
    have hx : PowerSeries.coeff (r+1) (kernel (F := F) i * PowerSeries.X) =
        PowerSeries.coeff r (kernel (F := F) i) := by
      simp
    rw [hx]
    simp only [coeff_kernel, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false,
      pow_succ]
    field_simp
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


theorem solution : type_of% @_root_.OAI.NCHitting.kernel_mul_linear := @_root_.OAI.NCHitting.kernel_mul_linear
