-- Prove2me | solution 1 for OAI.NCHitting.Formula.representation_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:28:36.265045+00:00
-- url     : https://prove2.me/submissions/4f885507-b11a-43e2-ad4a-08b561d8bde8

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Representation.lean:L305-L319
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.Formula.representation_card_le. The node keeps its source
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

-- ---- from OAI.Algebra.FormulaHitting.Representation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace NCHitting

open Matrix

attribute [instance] AcyclicRepresentation.fintype AcyclicRepresentation.decidableEq

namespace AcyclicRepresentation

variable {F : Type*} {n : ℕ} [CommSemiring F]

end AcyclicRepresentation

theorem Formula.representation_card_le {F : Type*} {n : ℕ} [CommSemiring F]
    (f : Formula F n) : Fintype.card f.representation.State ≤ 2 * f.size := by
  induction f with
  | scalar a => change 1 ≤ 2 * 1; decide
  | var i => change 2 ≤ 2 * 1; decide
  | add f g ihf ihg =>
    change Fintype.card (f.representation.State ⊕ g.representation.State) ≤
      2 * (f.size + g.size + 1)
    rw [Fintype.card_sum]
    omega
  | mul f g ihf ihg =>
    change Fintype.card (f.representation.State ⊕ g.representation.State) ≤
      2 * (f.size + g.size + 1)
    rw [Fintype.card_sum]
    omega

end NCHitting

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open Matrix


theorem solution : type_of% @_root_.OAI.NCHitting.Formula.representation_card_le := @_root_.OAI.NCHitting.Formula.representation_card_le
