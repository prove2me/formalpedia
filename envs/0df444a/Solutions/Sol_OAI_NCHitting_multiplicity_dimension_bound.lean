-- Prove2me | solution 1 for OAI.NCHitting.multiplicity_dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:24:39.913533+00:00
-- url     : https://prove2.me/submissions/04ff6e66-3b59-4ab0-b7d8-b851d8db15e2

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/DimensionBound.lean:L19-L39
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.multiplicity_dimension_bound. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.DimensionBound ----
namespace OAI

namespace NCHitting

theorem choose_twice_add {s : ℕ} (hs : 0 < s) :
    (2*s).choose 2 + s = 2*s^2 := by
  rw [Nat.choose_two_right]
  have he : (2*s)*(2*s-1) = (s*(2*s-1))*2 := by ring
  rw [he, Nat.mul_div_left _ (by decide)]
  calc
    s*(2*s-1)+s = s*((2*s-1)+1) := by ring
    _ = s*(2*s) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ 2*s)]
    _ = 2*s^2 := by ring

theorem multiplicity_dimension_bound {n s m : ℕ}
    (hn : 0 < n) (hs : 0 < s) (hm : m ≤ 2*s) :
    (n-1)*m.choose 2 + m ≤ 2*n*s^2 := by
  by_cases h1 : n = 1
  · subst n
    simp only [Nat.sub_self, zero_mul, zero_add, mul_one]
    have hsq : s ≤ s*s := Nat.le_mul_of_pos_right s hs
    calc
      m ≤ 2*s := hm
      _ ≤ 2*(s*s) := Nat.mul_le_mul_left 2 hsq
      _ = 2*s^2 := by ring
  · have hn2 : 2 ≤ n := by omega
    have hc : m.choose 2 ≤ (2*s).choose 2 := Nat.choose_le_choose 2 hm
    calc
      (n-1)*m.choose 2 + m ≤ n*((2*s).choose 2)+2*s :=
        Nat.add_le_add (Nat.mul_le_mul (Nat.sub_le _ _) hc) hm
      _ ≤ n*((2*s).choose 2)+n*s :=
        Nat.add_le_add_left (Nat.mul_le_mul_right s hn2) _
      _ = n*((2*s).choose 2+s) := by ring
      _ = n*(2*s^2) := by rw [choose_twice_add hs]
      _ = 2*n*s^2 := by ring

end NCHitting

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting


theorem solution : type_of% @_root_.OAI.NCHitting.multiplicity_dimension_bound := @_root_.OAI.NCHitting.multiplicity_dimension_bound
