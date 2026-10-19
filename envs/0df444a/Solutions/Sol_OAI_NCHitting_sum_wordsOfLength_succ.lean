-- Prove2me | solution 1 for OAI.NCHitting.sum_wordsOfLength_succ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:28:01.9865+00:00
-- url     : https://prove2.me/submissions/cf9a8a83-35da-483c-adf9-0b8de56e15e4

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Formula.lean:L109-L124
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.sum_wordsOfLength_succ. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.Formula ----
namespace OAI

namespace NCHitting

namespace Formula

end Formula

theorem sum_wordsOfLength_succ {M : Type*} [AddCommMonoid M]
    {n : ℕ} (k : ℕ) (f : Word n → M) :
    (∑ w ∈ wordsOfLength n (k + 1), f w) =
      ∑ i : Fin n, ∑ w ∈ wordsOfLength n k, f (i :: w) := by
  rw [wordsOfLength, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_image (by
      intro a _ b _ h
      exact (List.cons.inj h).2)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    rcases Finset.mem_image.mp hi with ⟨v, _, hv⟩
    rcases Finset.mem_image.mp hj with ⟨v', _, hv'⟩
    exact hij (List.cons.inj (hv.trans hv'.symm)).1

end NCHitting

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting


theorem solution : type_of% @_root_.OAI.NCHitting.sum_wordsOfLength_succ := @_root_.OAI.NCHitting.sum_wordsOfLength_succ
