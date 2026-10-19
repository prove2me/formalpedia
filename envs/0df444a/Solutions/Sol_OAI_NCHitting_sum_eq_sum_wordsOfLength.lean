-- Prove2me | solution 1 for OAI.NCHitting.sum_eq_sum_wordsOfLength
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:31:59.232593+00:00
-- url     : https://prove2.me/submissions/2ea5dad7-a01a-4752-8eee-33e9bff83d84

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Evaluation.lean:L56-L76
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.sum_eq_sum_wordsOfLength. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.Evaluation ----
namespace OAI

namespace NCHitting

attribute [local instance] OAI.NCHitting.instDecidableEqFreeMonoidFin_oAI
theorem sum_eq_sum_wordsOfLength {F M : Type*} {n d : ℕ}
    [Zero F] [AddCommMonoid M] (p : Word n →₀ F)
    (hcut : ∀ w, d ≤ w.length → p w = 0)
    (h : Word n → F → M) (hzero : ∀ w, h w 0 = 0) :
    p.sum h = ∑ k ∈ Finset.range d, ∑ w ∈ wordsOfLength n k, h w (p w) := by
  classical
  let S := (Finset.range d).biUnion (wordsOfLength n)
  have hsupport : p.support ⊆ S := by
    intro w hw
    have hne : p w ≠ 0 := Finsupp.mem_support_iff.mp hw
    have hlen : w.length < d := by
      by_contra hn
      exact hne (hcut w (by omega))
    exact Finset.mem_biUnion.mpr ⟨w.length, Finset.mem_range.mpr hlen,
      (mem_wordsOfLength w).mpr rfl⟩
  rw [Finsupp.sum_of_support_subset p hsupport h (fun w _ => hzero w)]
  apply Finset.sum_biUnion
  intro k hk l hl hkl
  apply Finset.disjoint_left.mpr
  intro w hwk hwl
  exact hkl (((mem_wordsOfLength w).mp hwk).symm.trans ((mem_wordsOfLength w).mp hwl))

namespace Formula

end Formula
end NCHitting

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
attribute [local instance] OAI.NCHitting.instDecidableEqFreeMonoidFin_oAI


theorem solution : type_of% @_root_.OAI.NCHitting.sum_eq_sum_wordsOfLength := @_root_.OAI.NCHitting.sum_eq_sum_wordsOfLength
