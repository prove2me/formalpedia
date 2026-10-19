-- Prove2me | solution 1 for OAI.NCHitting.numeratorRow_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:18:56.847777+00:00
-- url     : https://prove2.me/submissions/a2c95228-1ff8-4177-9f4e-65aa0e23837b

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/NumeratorRows.lean:L34-L63
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.numeratorRow_degree. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.NumeratorRows ----
namespace OAI

noncomputable section

namespace NCHitting

open Polynomial

variable {F : Type*} [Field F]

private theorem degree_q_derivative {q p : F[X]} {n b : ℕ}
    (hn : 0 < n) (hq : q.natDegree ≤ n) (hp : p.natDegree ≤ b) :
    (q * p.derivative).natDegree ≤ b + (n-1) := by
  by_cases hzero : p.natDegree = 0
  · simp [Polynomial.derivative_of_natDegree_zero hzero]
  · have hb : 0 < b := by omega
    have hd := p.natDegree_derivative_le
    have hm : (q * p.derivative).natDegree ≤ q.natDegree + p.derivative.natDegree :=
      Polynomial.natDegree_mul_le
    omega

theorem numeratorRow_degree {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    (q : F[X]) (P : Matrix I I F[X]) (u : I → F)
    (hq : q.natDegree ≤ n) (hP : ∀ t l, (P t l).natDegree ≤ n-1)
    (j : ℕ) (l : I) :
    (numeratorRow q P u j l).natDegree ≤ j * (n-1) := by
  induction j generalizing l with
  | zero => simp [numeratorRow]
  | succ j ih =>
    have ihall : ∀ l, (numeratorRow q P u j l).natDegree ≤ j * (n-1) := by
      intro l'
      exact ih l'
    have ha := degree_q_derivative hn hq (ihall l)
    have hb : (C (j : F) * q.derivative * numeratorRow q P u j l).natDegree ≤
        j * (n-1) + (n-1) := by
      have hq' : q.derivative.natDegree ≤ n-1 :=
        q.natDegree_derivative_le.trans (Nat.sub_le_sub_right hq 1)
      have hC := Polynomial.natDegree_C_mul_le (j : F) q.derivative
      have hmul : (C (j : F) * q.derivative * numeratorRow q P u j l).natDegree ≤
          (C (j : F) * q.derivative).natDegree + (numeratorRow q P u j l).natDegree :=
        Polynomial.natDegree_mul_le
      have hp := ihall l
      omega
    have hc : (∑ t : I, numeratorRow q P u j t * P t l).natDegree ≤
        j * (n-1) + (n-1) := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro t _
      exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (ihall t) (hP t l))
    rw [numeratorRow, Nat.add_mul, one_mul]
    apply Polynomial.natDegree_add_le_of_degree_le _ hc
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le ha hb)

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open Polynomial


theorem solution : type_of% @_root_.OAI.NCHitting.numeratorRow_degree := @_root_.OAI.NCHitting.numeratorRow_degree
