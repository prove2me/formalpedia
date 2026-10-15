-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.projection_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:04:18.477148+00:00
-- url     : https://prove2.me/submissions/e95d8a52-9f3f-4eb3-838e-19feee483826

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/ProjectionBlocks.lean:L78-L92
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.projection_commutator. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks

-- ---- from OAI.Combinatorics.GotsmanLinial.ProjectionBlocks ----
namespace OAI

/-!
# Matrix blocks of a finite orthogonal projection family

The Hilbert--Schmidt quantity below is the explicit sum of squared entry norms
rather than an ambient matrix norm instance.
-/

open scoped BigOperators ComplexConjugate
open Module

noncomputable section

namespace LeanBlast.GotsmanLinial

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

namespace OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)

include hP

theorem mul_eq_ite [DecidableEq κ] (r s : κ) :
    P r * P s = if r = s then P r else 0 := by
  by_cases hrs : r = s
  · subst s
    simp [hP.idempotent]
  · simp [hrs, hP.orthogonal r s hrs]

end OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ}

theorem projection_mul_matrixGrading (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (s : κ) : P s * matrixGrading P weight = (weight s : ℂ) • P s := by
  classical
  simp only [matrixGrading, Matrix.mul_sum, Matrix.mul_smul, hP.mul_eq_ite]
  simp

theorem matrixGrading_mul_projection (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (r : κ) : matrixGrading P weight * P r = (weight r : ℂ) • P r := by
  classical
  simp only [matrixGrading, Matrix.sum_mul, Matrix.smul_mul, hP.mul_eq_ite]
  simp

theorem projection_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B - B * matrixGrading P weight) * P r =
      ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  calc
    P s * (matrixGrading P weight * B) * P r -
        P s * (B * matrixGrading P weight) * P r =
      (P s * matrixGrading P weight) * B * P r -
        P s * B * (matrixGrading P weight * P r) := by simp only [Matrix.mul_assoc]
    _ = ((weight s : ℂ) • P s) * B * P r -
        P s * B * ((weight r : ℂ) • P r) := by
      rw [projection_mul_matrixGrading hP, matrixGrading_mul_projection hP]
    _ = ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Complex.ofReal_sub, sub_smul]

section OperatorTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

attribute [local instance] OAI.LeanBlast.GotsmanLinial.instCompleteSpace_oAI
end OperatorTransport

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators ComplexConjugate
open Module


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.projection_commutator := @_root_.OAI.LeanBlast.GotsmanLinial.projection_commutator
