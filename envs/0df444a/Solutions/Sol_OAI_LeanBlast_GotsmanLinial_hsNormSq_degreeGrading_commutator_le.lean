-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.hsNormSq_degreeGrading_commutator_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:06:49.280379+00:00
-- url     : https://prove2.me/submissions/d675c2c9-f348-4022-b6ed-375713fcd1af

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Commutator.lean:L205-L225
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.hsNormSq_degreeGrading_commutator_le. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_projection_commutator

-- ---- from OAI.Combinatorics.GotsmanLinial.HilbertSchmidt ----
namespace OAI

open scoped BigOperators ComplexConjugate

namespace LeanBlast.GotsmanLinial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem hsNormSq_nonneg (A : Matrix ι κ ℂ) : 0 ≤ hsNormSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem hsNormSq_smul (c : ℂ) (A : Matrix ι κ ℂ) :
    hsNormSq (c • A) = ‖c‖ ^ 2 * hsNormSq A := by
  simp [hsNormSq, mul_pow, Finset.mul_sum]

theorem hsNormSq_real_smul (c : ℝ) (A : Matrix ι κ ℂ) :
    hsNormSq ((c : ℂ) • A) = c ^ 2 * hsNormSq A := by
  rw [hsNormSq_smul]
  simp

end LeanBlast.GotsmanLinial

end OAI

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

theorem conjTranspose_eq (k : κ) : (P k).conjTranspose = P k := by
  simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using hP.selfAdjoint k

end OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ}

omit [DecidableEq ι] in
theorem trace_projection_sandwich (Q A : Matrix ι ι ℂ) (hQ : Q * Q = Q) :
    Matrix.trace (Q * A * Q) = Matrix.trace (Q * A) := by
  rw [Matrix.trace_mul_cycle, hQ]

theorem hsNormSq_projection_mul (hP : OrthogonalProjectionFamily P)
    (s : κ) (B : Matrix ι ι ℂ) :
    hsNormSq (P s * B) = (Matrix.trace (B.conjTranspose * P s * B)).re := by
  rw [hsNormSq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  congr 2
  calc
    (B.conjTranspose * P s) * (P s * B) =
        B.conjTranspose * (P s * P s) * B := by simp only [Matrix.mul_assoc]
    _ = B.conjTranspose * P s * B := by rw [hP.idempotent]

theorem hsNormSq_mul_projection (hP : OrthogonalProjectionFamily P)
    (r : κ) (B : Matrix ι ι ℂ) :
    hsNormSq (B * P r) = (Matrix.trace (P r * (B.conjTranspose * B))).re := by
  rw [hsNormSq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  have heq : (P r * B.conjTranspose) * (B * P r) =
      P r * (B.conjTranspose * B) * P r := by simp only [Matrix.mul_assoc]
  rw [heq, trace_projection_sandwich _ _ (hP.idempotent r)]

theorem hsNormSq_left_projection_decomposition (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) : hsNormSq B = ∑ s, hsNormSq (P s * B) := by
  simp_rw [hsNormSq_projection_mul hP]
  rw [← Complex.re_sum, ← Matrix.trace_sum]
  simp_rw [← Matrix.sum_mul]
  rw [← Matrix.mul_sum, hP.sum_eq_one, Matrix.mul_one, hsNormSq_eq_re_trace]

theorem hsNormSq_right_projection_decomposition (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) : hsNormSq B = ∑ r, hsNormSq (B * P r) := by
  simp_rw [hsNormSq_mul_projection hP]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    hP.sum_eq_one, Matrix.one_mul, hsNormSq_eq_re_trace]

theorem hsNormSq_block_parseval (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) :
    hsNormSq B = ∑ r, ∑ s, hsNormSq (P s * B * P r) := by
  rw [hsNormSq_right_projection_decomposition hP B]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [Matrix.mul_assoc] using hsNormSq_left_projection_decomposition hP (B * P r)

theorem hsNormSq_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) :
    hsNormSq (matrixGrading P weight * B - B * matrixGrading P weight) =
      ∑ r, ∑ s, (weight s - weight r) ^ 2 * hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_commutator hP, hsNormSq_real_smul]

section OperatorTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

attribute [local instance] OAI.LeanBlast.GotsmanLinial.instCompleteSpace_oAI
end OperatorTransport

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.Commutator ----
namespace OAI

/-!
# Entry bounds for a tridiagonal grading commutator

All norms here are norms of individual complex entries.  No default
norm on a matrix is used.  A complete orthogonal family defines a phase
unitary with eigenvalues `I^k`.  For a tridiagonal operator the commutator is
the difference of two unitary conjugates divided by `2 I`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace LeanBlast.GotsmanLinial

section SpectralMultiplier

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

variable (P : κ → Matrix ι ι ℂ)
variable (hmul : ∀ r s, P r * P s = if r = s then P r else 0)
include hmul

end SpectralMultiplier

section GradingCommutator

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Fin (n + 1) → Matrix ι ι ℂ}

/-- The Hilbert--Schmidt commutator bound is a consequence of block Parseval
and the fact that each nonzero block has grading distance at most one. -/
theorem hsNormSq_degreeGrading_commutator_le
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) :
    hsNormSq (degreeGrading P * Z - Z * degreeGrading P) ≤ hsNormSq Z := by
  rw [degreeGrading, hsNormSq_commutator hP, hsNormSq_block_parseval hP Z]
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro s _
  by_cases hfar : r.val + 1 < s.val ∨ s.val + 1 < r.val
  · simp only [htri r s hfar, hsNormSq_zero, mul_zero, le_refl]
  · have hsr : (s.val : ℝ) ≤ (r.val : ℝ) + 1 := by
      exact_mod_cast (show s.val ≤ r.val + 1 by omega)
    have hrs : (r.val : ℝ) ≤ (s.val : ℝ) + 1 := by
      exact_mod_cast (show r.val ≤ s.val + 1 by omega)
    have hsq : ((s.val : ℝ) - (r.val : ℝ)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    exact (mul_le_mul_of_nonneg_right hsq (hsNormSq_nonneg _)).trans_eq (one_mul _)

end GradingCommutator

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators Matrix


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.hsNormSq_degreeGrading_commutator_le := @_root_.OAI.LeanBlast.GotsmanLinial.hsNormSq_degreeGrading_commutator_le
