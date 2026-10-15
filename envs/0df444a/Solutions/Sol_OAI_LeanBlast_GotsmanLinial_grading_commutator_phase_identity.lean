-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.grading_commutator_phase_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:06:03.890264+00:00
-- url     : https://prove2.me/submissions/d9d73d2e-86d9-4654-a0f7-85551bebe049

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Commutator.lean:L170-L189
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.grading_commutator_phase_identity. The node keeps its source
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

theorem sum_projection_blocks (hP : OrthogonalProjectionFamily P) (B : Matrix ι ι ℂ) :
    (∑ r, ∑ s, P s * B * P r) = B := by
  simp_rw [← Matrix.sum_mul, hP.sum_eq_one, Matrix.one_mul]
  rw [← Matrix.mul_sum, hP.sum_eq_one, Matrix.mul_one]

theorem projection_block_ext (hP : OrthogonalProjectionFamily P)
    {A B : Matrix ι ι ℂ} (h : ∀ r s, P s * A * P r = P s * B * P r) : A = B := by
  rw [← sum_projection_blocks hP A, ← sum_projection_blocks hP B]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => h r s

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

theorem spectralMultiplier_mul_projection (a : κ → ℂ) (r : κ) :
    spectralMultiplier P a * P r = a r • P r := by
  classical
  simp [spectralMultiplier, Finset.sum_mul, hmul]

theorem projection_mul_spectralMultiplier (a : κ → ℂ) (r : κ) :
    P r * spectralMultiplier P a = a r • P r := by
  classical
  simp [spectralMultiplier, Finset.mul_sum, hmul]

omit hmul [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
theorem star_spectralMultiplier (hstar : ∀ k, star (P k) = P k) (a : κ → ℂ) :
    star (spectralMultiplier P a) = spectralMultiplier P (fun k => star (a k)) := by
  simp only [spectralMultiplier, star_sum, star_smul, hstar]

theorem spectralMultiplier_sandwich_block (a b : κ → ℂ)
    (Z : Matrix ι ι ℂ) (r s : κ) :
    P s * (spectralMultiplier P a * Z * spectralMultiplier P b) * P r =
      (a s * b r) • (P s * Z * P r) := by
  calc
    _ = ((P s * spectralMultiplier P a) * Z) *
        (spectralMultiplier P b * P r) := by simp only [mul_assoc]
    _ = ((a s • P s) * Z) * (b r • P r) := by
      rw [projection_mul_spectralMultiplier P hmul,
        spectralMultiplier_mul_projection P hmul]
    _ = _ := by simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

end SpectralMultiplier

theorem I_pow_mul_star (k : ℕ) : Complex.I ^ k * star (Complex.I ^ k) = 1 := by
  rw [Complex.star_def, Complex.mul_conj']
  simp

theorem phase_coeff_adjacent (r s : ℕ) (h₁ : s ≤ r + 1) (h₂ : r ≤ s + 1) :
    Complex.I ^ s * star (Complex.I ^ r) - star (Complex.I ^ s) * Complex.I ^ r =
      (2 * Complex.I) * ((s : ℂ) - (r : ℂ)) := by
  have hcases : s = r ∨ s = r + 1 ∨ r = s + 1 := by omega
  rcases hcases with h | h | h
  · subst s
    simp [mul_comm]
  · subst s
    simp only [pow_succ, star_mul, Complex.star_def, Complex.conj_I, Nat.cast_add,
      Nat.cast_one]
    calc
      _ = (2 * Complex.I) * (Complex.I ^ r * star (Complex.I ^ r)) := by
        simp only [Complex.star_def]
        ring
      _ = _ := by rw [I_pow_mul_star]; ring
  · subst r
    simp only [pow_succ, star_mul, Complex.star_def, Complex.conj_I, Nat.cast_add,
      Nat.cast_one]
    calc
      _ = -(2 * Complex.I) * (Complex.I ^ s * star (Complex.I ^ s)) := by
        simp only [Complex.star_def]
        ring
      _ = _ := by rw [I_pow_mul_star]; ring

section GradingCommutator

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Fin (n + 1) → Matrix ι ι ℂ}

/-- Two opposite phase conjugations differ by `2 I` times the grading commutator. -/
theorem grading_commutator_phase_identity (hP : OrthogonalProjectionFamily P)
    (Z : Matrix ι ι ℂ) (htri : BlockTridiagonal P Z) :
    (2 * Complex.I) • (degreeGrading P * Z - Z * degreeGrading P) =
      gradingPhase P * Z * star (gradingPhase P) -
        star (gradingPhase P) * Z * gradingPhase P := by
  apply projection_block_ext hP
  intro r s
  rw [Matrix.mul_smul, Matrix.smul_mul, degreeGrading, projection_commutator hP,
    Matrix.mul_sub, Matrix.sub_mul]
  simp only [gradingPhase,
    star_spectralMultiplier P (fun k => (hP.selfAdjoint k).star_eq)]
  rw [spectralMultiplier_sandwich_block P hP.mul_eq_ite,
    spectralMultiplier_sandwich_block P hP.mul_eq_ite]
  by_cases hfar : r.val + 1 < s.val ∨ s.val + 1 < r.val
  · simp only [htri r s hfar, smul_zero, sub_self]
  · have hsr : s.val ≤ r.val + 1 := by omega
    have hrs : r.val ≤ s.val + 1 := by omega
    rw [← sub_smul, smul_smul, phase_coeff_adjacent r.val s.val hsr hrs]
    simp

end GradingCommutator

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators Matrix


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.grading_commutator_phase_identity := @_root_.OAI.LeanBlast.GotsmanLinial.grading_commutator_phase_identity
