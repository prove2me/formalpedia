-- Prove2me | solution 1 for OAI.NCHitting.natDegree_det_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:21:31.931803+00:00
-- url     : https://prove2.me/submissions/7cca7513-cd8c-4344-8b05-f343dfa77413

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Minors.lean:L54-L69
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.natDegree_det_le_sum. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.Minors ----
namespace OAI

noncomputable section

namespace NCHitting

open Matrix Finset Polynomial

variable {R : Type*} [CommRing R]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

theorem natDegree_det_le_sum {F : Type*} [Field F]
    (A : Matrix I I F[X]) (d : I → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ d i) :
    A.det.natDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  apply (Polynomial.natDegree_mul_le).trans
  have hsign : (↑(Equiv.Perm.sign σ) : F[X]).natDegree = 0 := by
    exact Polynomial.natDegree_intCast _
  rw [hsign, zero_add]
  calc
    (∏ i, A (σ i) i).natDegree ≤ ∑ i, d (σ i) :=
      (Polynomial.natDegree_prod_le Finset.univ (fun i => A (σ i) i)).trans (Finset.sum_le_sum (fun i _ => h (σ i) i))
    _ = ∑ i, d i := Equiv.sum_comp σ d

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open Matrix Finset Polynomial


theorem solution : type_of% @_root_.OAI.NCHitting.natDegree_det_le_sum := @_root_.OAI.NCHitting.natDegree_det_le_sum
