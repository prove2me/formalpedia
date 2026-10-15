-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.sensitivity_bound_of_cube_grading
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:20:14.596306+00:00
-- url     : https://prove2.me/submissions/76e86215-a1cf-489e-a725-1321ff6d3d7e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Main.lean:L47-L90
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.sensitivity_bound_of_cube_grading. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WalshDimensions
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WeightedGrading
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_GradingShift
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_adjacent_iff_hammingDist_eq_one
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_binomial_block_coupling_bound
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_edge_recovery
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_grading_commutator_phase_identity
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_hsNormSq_degreeGrading_commutator_le
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sum_choose_centered_sq_range
import Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sum_hsNormSq_coordinate_commutator

-- ---- from OAI.Combinatorics.GotsmanLinial.Statement ----
namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

theorem averageSensitivity_eq_count {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f = (sensitiveEdgeCount f : ℝ) / (2 : ℝ) ^ n := by
  simp [averageSensitivity, sensitiveEdgeCount, Finset.sum_div]

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.BinomialMoments ----
namespace OAI

/-!
Exact finite moments of the symmetric binomial weights. These identities provide
the grading multiplicities and the variance used in the finite coupling estimate.
No probabilistic assumptions or measures enter the statements.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

theorem sum_choose_centered_sq (n : ℕ) :
    (∑ k : Fin (n + 1),
      (n.choose k.val : ℝ) * ((k.val : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (n.choose k : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2)]
  exact sum_choose_centered_sq_range n

end LeanBlast.GotsmanLinial

end OAI

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

omit [Fintype κ] in
theorem sum_sq_norm_column_eq_re (A : Matrix ι κ ℂ) (j : κ) :
    ∑ i, ‖A i j‖ ^ 2 = ((A.conjTranspose * A) j j).re := by
  exact congrArg Complex.re (ofReal_sum_sq_norm_column A j)

theorem hsNormSq_mul_left_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (A : Matrix ι κ ℂ) (hU : U.conjTranspose * U = 1) :
    hsNormSq (U * A) = hsNormSq A := by
  rw [hsNormSq_eq_re_trace, hsNormSq_eq_re_trace]
  congr 2
  calc
    (U * A).conjTranspose * (U * A) = A.conjTranspose *
        (U.conjTranspose * U) * A := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = A.conjTranspose * A := by rw [hU, Matrix.mul_one]

theorem hsNormSq_mul_right_of_unitary [DecidableEq κ]
    (A : Matrix ι κ ℂ) (U : Matrix κ κ ℂ) (hU : U * U.conjTranspose = 1) :
    hsNormSq (A * U) = hsNormSq A := by
  rw [← hsNormSq_conjTranspose (A * U), Matrix.conjTranspose_mul]
  rw [hsNormSq_mul_left_of_unitary U.conjTranspose A.conjTranspose]
  · exact hsNormSq_conjTranspose A
  · simpa using hU

theorem hsNormSq_projection (P : Matrix ι ι ℂ)
    (hself : P.conjTranspose = P) (hidem : P * P = P) :
    hsNormSq P = (Matrix.trace P).re := by
  rw [hsNormSq_eq_re_trace, hself, hidem]

theorem sum_sq_norm_column_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) (j : ι) :
    ∑ i, ‖U i j‖ ^ 2 = 1 := by
  rw [sum_sq_norm_column_eq_re, hU]
  simp

theorem sq_norm_entry_le_one_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) (i j : ι) :
    ‖U i j‖ ^ 2 ≤ 1 := by
  rw [← sum_sq_norm_column_of_unitary U hU j]
  exact Finset.single_le_sum (fun k _ => sq_nonneg ‖U k j‖) (Finset.mem_univ i)

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

theorem projection_anticommutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B + B * matrixGrading P weight) * P r =
      ((weight s + weight r : ℝ) : ℂ) • (P s * B * P r) := by
  rw [Matrix.mul_add, Matrix.add_mul]
  calc
    P s * (matrixGrading P weight * B) * P r +
        P s * (B * matrixGrading P weight) * P r =
      (P s * matrixGrading P weight) * B * P r +
        P s * B * (matrixGrading P weight * P r) := by simp only [Matrix.mul_assoc]
    _ = ((weight s : ℂ) • P s) * B * P r +
        P s * B * ((weight r : ℂ) • P r) := by
      rw [projection_mul_matrixGrading hP, matrixGrading_mul_projection hP]
    _ = ((weight s + weight r : ℝ) : ℂ) • (P s * B * P r) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Complex.ofReal_add, add_smul]

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

theorem hsNormSq_matrixGrading (hP : OrthogonalProjectionFamily P) (weight : κ → ℝ) :
    hsNormSq (matrixGrading P weight) = ∑ r, weight r ^ 2 * hsNormSq (P r) := by
  classical
  rw [hsNormSq_block_parseval hP]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single r]
  · rw [projection_mul_matrixGrading hP, Matrix.smul_mul, hP.idempotent,
      hsNormSq_real_smul]
  · intro s _ hsr
    rw [projection_mul_matrixGrading hP, Matrix.smul_mul,
      hP.orthogonal s r hsr, smul_zero, hsNormSq_zero]
  · simp

theorem hsNormSq_matrixGrading_trace (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) :
    hsNormSq (matrixGrading P weight) = ∑ r, weight r ^ 2 * (Matrix.trace (P r)).re := by
  rw [hsNormSq_matrixGrading hP]
  apply Finset.sum_congr rfl
  intro r _
  rw [hsNormSq_projection (P r) (hP.conjTranspose_eq r) (hP.idempotent r)]

theorem sum_hsNormSq_blocks_column (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r : κ) (hB : B.conjTranspose * B = 1) :
    (∑ s, hsNormSq (P s * B * P r)) = hsNormSq (P r) := by
  calc
    (∑ s, hsNormSq (P s * B * P r)) = hsNormSq (B * P r) := by
      simpa only [Matrix.mul_assoc] using
        (hsNormSq_left_projection_decomposition hP (B * P r)).symm
    _ = hsNormSq (P r) := hsNormSq_mul_left_of_unitary B (P r) hB

theorem sum_hsNormSq_blocks_row (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (s : κ) (hB : B * B.conjTranspose = 1) :
    (∑ r, hsNormSq (P s * B * P r)) = hsNormSq (P s) := by
  rw [← hsNormSq_right_projection_decomposition hP (P s * B)]
  exact hsNormSq_mul_right_of_unitary (P s) B hB

theorem hsNormSq_centeredGrading_trace {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    hsNormSq (centeredGrading P) =
      ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * (Matrix.trace (P k)).re :=
  hsNormSq_matrixGrading_trace hP _

theorem centeredGrading_eq {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    centeredGrading P = degreeGrading P - (((n : ℝ) / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  simp only [centeredGrading, degreeGrading, matrixGrading, Complex.ofReal_sub, sub_smul,
    Finset.sum_sub_distrib]
  rw [← Finset.smul_sum, hP.sum_eq_one]

theorem projection_centered_anticommutator {n : ℕ}
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r s : Fin (n + 1)) :
    P s * (centeredGrading P * B + B * centeredGrading P) * P r =
      (((s.val : ℝ) + (r.val : ℝ) - n : ℝ) : ℂ) • (P s * B * P r) := by
  rw [centeredGrading, projection_anticommutator hP]
  congr 2
  ring

theorem hsNormSq_centered_anticommutator {n : ℕ}
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) :
    hsNormSq (centeredGrading P * B + B * centeredGrading P) =
      ∑ r, ∑ s, ((s.val : ℝ) + (r.val : ℝ) - n) ^ 2 *
        hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_centered_anticommutator hP, hsNormSq_real_smul]

section OperatorTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

attribute [local instance] OAI.LeanBlast.GotsmanLinial.instCompleteSpace_oAI
end OperatorTransport

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.BlockCoupling ----
namespace OAI

/-!
# The finite block coupling

Normalize a nonnegative matrix of block masses, identify its two binomial
marginals, and reflect its first index.  The low-degree block vanishing gives
the one-sided displacement bound required by the finite coupling lemma.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

/-- The spectral block coupling bounds the actual centered grading
anticommutator.  Its hypotheses are the orthogonal grading, its binomial
multiplicities, unitarity, and the separately proved low-degree vanishing. -/
theorem hsNormSq_centeredGrading_anticommutator_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  rw [hsNormSq_centered_anticommutator hP H]
  apply binomial_block_coupling_bound n d (fun r s => hsNormSq (P s * H * P r))
  · intro r s
    exact hsNormSq_nonneg _
  · intro r
    rw [sum_hsNormSq_blocks_column hP H r hleft, hmult]
  · intro s
    rw [sum_hsNormSq_blocks_row hP H s hright, hmult]
  · intro r s hrs
    rw [hvanish r s hrs, hsNormSq_zero]

/-- Trace-multiplicity form, for direct use with finite-dimensional orthogonal
projections whose ranks have already been computed. -/
theorem hsNormSq_centeredGrading_anticommutator_le_of_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  apply hsNormSq_centeredGrading_anticommutator_le n d P hP H hleft hright _ hvanish
  intro k
  rw [hsNormSq_projection (P k) (hP.conjTranspose_eq k) (hP.idempotent k), htrace]

end LeanBlast.GotsmanLinial

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

theorem spectralMultiplier_mul (a b : κ → ℂ) :
    spectralMultiplier P a * spectralMultiplier P b =
      spectralMultiplier P (fun k => a k * b k) := by
  change spectralMultiplier P a * (∑ k, b k • P k) = _
  rw [Finset.mul_sum]
  simp only [mul_smul_comm, spectralMultiplier_mul_projection P hmul, smul_smul]
  simp only [spectralMultiplier, mul_comm]

omit hmul [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
theorem star_spectralMultiplier (hstar : ∀ k, star (P k) = P k) (a : κ → ℂ) :
    star (spectralMultiplier P a) = spectralMultiplier P (fun k => star (a k)) := by
  simp only [spectralMultiplier, star_sum, star_smul, hstar]

theorem spectralMultiplier_unitary
    (hstar : ∀ k, star (P k) = P k) (hsum : ∑ k, P k = 1)
    (a : κ → ℂ) (ha : ∀ k, a k * star (a k) = 1) :
    spectralMultiplier P a ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_spectralMultiplier P hstar,
    spectralMultiplier_mul P hmul]
  simpa only [spectralMultiplier, ha, one_smul] using hsum

end SpectralMultiplier

theorem I_pow_mul_star (k : ℕ) : Complex.I ^ k * star (Complex.I ^ k) = 1 := by
  rw [Complex.star_def, Complex.mul_conj']
  simp

/-- The difference of two unitary matrices, divided by `2 I`, has entries
of modulus at most one. -/
theorem entry_norm_le_one_of_two_unitaries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C U V : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (h : (2 * Complex.I) • C = U - V) (x y : ι) : ‖C x y‖ ≤ 1 := by
  have heq := congrArg (fun A : Matrix ι ι ℂ => A x y) h
  have hn : (2 : ℝ) * ‖C x y‖ = ‖U x y - V x y‖ := by
    simpa [norm_mul] using congrArg norm heq
  have htri := norm_sub_le (U x y) (V x y)
  have hu₂ := sq_norm_entry_le_one_of_unitary U hU.1 x y
  have hv₂ := sq_norm_entry_le_one_of_unitary V hV.1 x y
  have hu : ‖U x y‖ ≤ 1 := by nlinarith [norm_nonneg (U x y)]
  have hv : ‖V x y‖ ≤ 1 := by nlinarith [norm_nonneg (V x y)]
  linarith

section GradingCommutator

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Fin (n + 1) → Matrix ι ι ℂ}

theorem gradingPhase_unitary (hP : OrthogonalProjectionFamily P) :
    gradingPhase P ∈ Matrix.unitaryGroup ι ℂ := by
  exact spectralMultiplier_unitary P hP.mul_eq_ite (fun k => (hP.selfAdjoint k).star_eq)
    hP.sum_eq_one _ (fun k => I_pow_mul_star k.val)

/-- Every entry of the tridiagonal degree commutator has modulus at most one. -/
theorem norm_degreeGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(degreeGrading P * Z - Z * degreeGrading P) x y‖ ≤ 1 := by
  have hW := gradingPhase_unitary hP
  have hWstar := Unitary.star_mem hW
  have hU : gradingPhase P * Z * star (gradingPhase P) ∈ Matrix.unitaryGroup ι ℂ :=
    (Matrix.unitaryGroup ι ℂ).mul_mem ((Matrix.unitaryGroup ι ℂ).mul_mem hW hZ) hWstar
  have hV : star (gradingPhase P) * Z * gradingPhase P ∈ Matrix.unitaryGroup ι ℂ :=
    (Matrix.unitaryGroup ι ℂ).mul_mem ((Matrix.unitaryGroup ι ℂ).mul_mem hWstar hZ) hW
  exact entry_norm_le_one_of_two_unitaries _ _ _ hU hV
    (grading_commutator_phase_identity hP Z htri) x y

theorem hsNormSq_degreeGrading_commutator_le_card
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ) :
    hsNormSq (degreeGrading P * Z - Z * degreeGrading P) ≤ Fintype.card ι := by
  calc
    _ ≤ hsNormSq Z := hsNormSq_degreeGrading_commutator_le hP Z htri
    _ = _ := hsNormSq_of_unitary Z hZ.1

/-- Centering the grading does not change its commutator. -/
theorem centeredGrading_commutator_eq (hP : OrthogonalProjectionFamily P)
    (Z : Matrix ι ι ℂ) :
    centeredGrading P * Z - Z * centeredGrading P =
      degreeGrading P * Z - Z * degreeGrading P := by
  rw [centeredGrading_eq hP]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

theorem norm_centeredGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(centeredGrading P * Z - Z * centeredGrading P) x y‖ ≤ 1 := by
  rw [centeredGrading_commutator_eq hP]
  exact norm_degreeGrading_commutator_entry_le_one hP Z htri hZ x y

theorem sq_norm_centeredGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(centeredGrading P * Z - Z * centeredGrading P) x y‖ ^ 2 ≤ 1 := by
  rw [sq_le_one_iff₀ (norm_nonneg _)]
  exact norm_centeredGrading_commutator_entry_le_one hP Z htri hZ x y

theorem hsNormSq_centeredGrading_commutator_le_card
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ) :
    hsNormSq (centeredGrading P * Z - Z * centeredGrading P) ≤ Fintype.card ι := by
  rw [centeredGrading_commutator_eq hP]
  exact hsNormSq_degreeGrading_commutator_le_card hP Z htri hZ

end GradingCommutator

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.CoordinateMultipliers ----
namespace OAI

/-!
# Actual diagonal sign and coordinate operators on the cube

The matrices here act on the cube with its counting inner product.  Their
continuous linear maps act on `EuclideanSpace`, so all operator-norm statements
refer to the intended Euclidean norm.  The Hilbert--Schmidt statements use the
explicit squared-entry sum `hsNormSq`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace LeanBlast.GotsmanLinial

variable {n : ℕ}

theorem signMatrix_mul_conjTranspose (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    signMatrix h * (signMatrix h).conjTranspose = 1 := by
  rw [signMatrix_conjTranspose, signMatrix_mul_self h hh]

theorem signMatrix_unitary (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    signMatrix h ∈ Matrix.unitaryGroup (Cube n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, signMatrix_star]
  exact signMatrix_mul_self h hh

theorem coordinateSignMatrix_unitary (i : Fin n) :
    coordinateSignMatrix i ∈ Matrix.unitaryGroup (Cube n) ℂ :=
  signMatrix_unitary _ (fun x => cubeCoord_cases x i)

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.CubeOperators ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

/-!
# Coordinate commutators and Hamming-distance energy

The coordinate sign matrices are the actual diagonal operators of the Boolean
cube. The identities here turn their Hilbert--Schmidt and entry estimates into
the energy estimates used by the edge-recovery argument.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {n : ℕ}

/-- In the point basis, a coordinate commutator records the difference of the
two endpoint signs. -/
theorem coordinate_commutator_apply
    (M : Matrix (Cube n) (Cube n) ℂ) (i : Fin n) (x y : Cube n) :
    (M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y =
      (((cubeCoord y i - cubeCoord x i : ℝ) : ℂ)) * M x y := by
  simp only [coordinateSignMatrix, signMatrix, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.ofReal_sub]
  ring

/-- Squaring a coordinate difference gives four exactly on the coordinates
where the Boolean endpoints differ. -/
theorem coordinate_commutator_sq_norm
    (M : Matrix (Cube n) (Cube n) ℂ) (i : Fin n) (x y : Cube n) :
    ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 =
      (if x i ≠ y i then (4 : ℝ) else 0) * ‖M x y‖ ^ 2 := by
  rw [coordinate_commutator_apply, norm_mul, mul_pow]
  congr 1
  cases hx : x i <;> cases hy : y i <;> norm_num [cubeCoord, hx, hy]

/-- A uniform coordinate-commutator Hilbert--Schmidt bound gives the distance
energy inequality for the actual cube matrix. -/
theorem distance_energy_le_of_coordinate_commutator_bound
    (M : Matrix (Cube n) (Cube n) ℂ)
    (hbound : ∀ i : Fin n,
      hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M) ≤ (2 : ℝ) ^ n) :
    (∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hbound i)
  rw [sum_hsNormSq_coordinate_commutator] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- A coordinate at which distinct endpoints differ turns an entrywise
commutator estimate into the edge-entry cap `1/4`. -/
theorem off_diagonal_sq_norm_le_quarter_of_commutator_bound
    (M : Matrix (Cube n) (Cube n) ℂ)
    (hbound : ∀ (i : Fin n) (x y : Cube n),
      ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 ≤ 1)
    (x y : Cube n) (hxy : x ≠ y) : ‖M x y‖ ^ 2 ≤ (1 : ℝ) / 4 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    exact not_not.mp (not_exists.mp h i)
  have h := hbound i x y
  rw [coordinate_commutator_sq_norm, ite_eq_left hi] at h
  linarith

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.SignParity ----
namespace OAI

/-!
# Removing threshold zeros and turning sensitive edges into constant-sign edges

All graph pairs are ordered. The cube coordinates are the real
signs encoded by `Bool` in the public statement.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

theorem fullParity_cases {n : ℕ} (x : Cube n) :
    fullParity x = 1 ∨ fullParity x = -1 :=
  sq_eq_one_iff.mp (fullParity_sq x)

theorem orderedNeighborPairs_eq_map {n : ℕ} :
    orderedNeighborPairs n = Finset.univ.map (directedEdgeEmbedding n) := by
  classical
  ext e
  constructor
  · intro he
    have hd : hammingDist e.1 e.2 = 1 := (Finset.mem_filter.mp he).2
    obtain ⟨i, hi⟩ := (adjacent_iff_hammingDist_eq_one e.1 e.2).mpr hd
    exact Finset.mem_map.mpr ⟨(i, e.1), Finset.mem_univ _, Prod.ext rfl hi⟩
  · intro he
    obtain ⟨⟨i, x⟩, _, rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hammingDist_flip i x⟩

theorem card_orderedConstantEdges {n : ℕ} (h : Cube n → ℝ) :
    (orderedConstantEdges h).card =
      ∑ i : Fin n, (Finset.univ.filter fun x => h x = h (flip i x)).card := by
  classical
  unfold orderedConstantEdges
  rw [orderedNeighborPairs_eq_map, Finset.filter_map, Finset.card_map]
  change (Finset.univ.filter fun e : Fin n × Cube n => h e.2 = h (flip e.1 e.2)).card = _
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Fintype.sum_prod_type _

/-- Twisting a sign-valued function by parity changes sensitivity into
equality across a coordinate flip. -/
theorem parity_twist_eq_iff {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) (i : Fin n) (x : Cube n) :
    fullParity x * f x = fullParity (flip i x) * f (flip i x) ↔
      f x ≠ f (flip i x) := by
  rw [fullParity_flip]
  rcases fullParity_cases x with hp | hp <;>
    rcases hf x with hx | hx <;>
    rcases hf (flip i x) with hy | hy <;> norm_num [hp, hx, hy]

theorem parity_twist_cases {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) (x : Cube n) :
    fullParity x * f x = 1 ∨ fullParity x * f x = -1 := by
  rcases fullParity_cases x with hp | hp <;>
    rcases hf x with hx | hx <;> simp [hp, hx]

theorem card_orderedConstantEdges_parity {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    (orderedConstantEdges (fun x => fullParity x * f x)).card = sensitiveEdgeCount f := by
  classical
  rw [card_orderedConstantEdges]
  unfold sensitiveEdgeCount
  apply Finset.sum_congr rfl
  intro i _
  unfold sensitiveVertices
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  exact parity_twist_eq_iff hf i x

/-- Exact uniform normalization: both sides count each sensitive undirected
edge twice, once in each direction. -/
theorem averageSensitivity_eq_parity_edges {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    averageSensitivity f =
      ((orderedConstantEdges (fun x => fullParity x * f x)).card : ℝ) / (2 : ℝ) ^ n := by
  rw [averageSensitivity_eq_count, card_orderedConstantEdges_parity hf]

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.Combinatorics.GotsmanLinial.Main ----
namespace OAI

/-!
# Assembly of the Gotsman--Linial average-sensitivity bound

The first lemmas are explicitly conditional assembly bridges. The final
theorems discharge their matrix and counting hypotheses using the concrete
weighted Boolean-cube grading and a sign-preserving constant perturbation.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

/-- The two analytic constants combine to the constant `8` after
normalizing by the number of cube vertices. This is only a scalar bridge. -/
theorem normalized_edge_bound {N C T a : ℝ} (hN : 0 < N)
    (hedge : C ≤ 2 * T) (henergy : T ≤ 4 * a * N) :
    C / N ≤ 8 * a := by
  apply (div_le_iff₀ hN).mpr
  calc
    C ≤ 2 * T := hedge
    _ ≤ 2 * (4 * a * N) := mul_le_mul_of_nonneg_left henergy (by norm_num)
    _ = 8 * a * N := by ring

/-- Convert a counted-edge identity, edge recovery, and an anticommutator
energy estimate into the desired sensitivity inequality. The counting and energy premises are explicit. -/
theorem sensitivity_bound_of_counting_energy {n d : ℕ}
    (f : Cube n → ℝ) (C T : ℝ)
    (hcount : averageSensitivity f = C / (2 : ℝ) ^ n)
    (hedge : C ≤ 2 * T)
    (henergy : T ≤ 4 * ((d : ℝ) * Real.sqrt (n : ℝ)) * (2 : ℝ) ^ n) :
    averageSensitivity f ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  rw [hcount]
  simpa only [mul_assoc] using
    normalized_edge_bound (pow_pos (by norm_num : (0 : ℝ) < 2) n) hedge henergy

/-- The finite-matrix bound assuming an orthogonal projection family with
binomial multiplicities, coordinate tridiagonality, and low-block vanishing. -/
theorem sensitivity_bound_of_cube_grading {n d : ℕ}
    (f : Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (P : Fin (n + 1) → Matrix (Cube n) (Cube n) ℂ)
    (hP : OrthogonalProjectionFamily P)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (htri : ∀ i : Fin n, BlockTridiagonal P (coordinateSignMatrix i))
    (hvanish : ∀ r s : Fin (n + 1), r.val + s.val < n - d →
      P s * signMatrix (fun x => fullParity x * f x) * P r = 0) :
    averageSensitivity f ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  classical
  let h : Cube n → ℝ := fun x => fullParity x * f x
  let H : Matrix (Cube n) (Cube n) ℂ := signMatrix h
  let M : Matrix (Cube n) (Cube n) ℂ := centeredGrading P
  have hh (x : Cube n) : h x = 1 ∨ h x = -1 := parity_twist_cases hf x
  have htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4 := by
    change hsNormSq (centeredGrading P) = _
    rw [hsNormSq_centeredGrading_trace hP]
    simp_rw [htrace]
    simpa only [mul_comm] using sum_choose_centered_sq n
  have hcoordinate (i : Fin n) :
      hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M) ≤ (2 : ℝ) ^ n := by
    simpa only [M, card_cube, Nat.cast_pow, Nat.cast_ofNat] using
      hsNormSq_centeredGrading_commutator_le_card hP (coordinateSignMatrix i)
        (htri i) (coordinateSignMatrix_unitary i)
  have hdistance :
      (∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M := by
    rw [htotal]
    exact distance_energy_le_of_coordinate_commutator_bound M hcoordinate
  have hcap (x y : Cube n) (hxy : x ≠ y) : ‖M x y‖ ^ 2 ≤ (1 : ℝ) / 4 := by
    apply off_diagonal_sq_norm_le_quarter_of_commutator_bound M _ x y hxy
    intro i a b
    exact sq_norm_centeredGrading_commutator_entry_le_one hP (coordinateSignMatrix i)
      (htri i) (coordinateSignMatrix_unitary i) a b
  have hedge : ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * H + H * M) := edge_recovery M h hh htotal hdistance hcap
  have henergy : hsNormSq (M * H + H * M) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n :=
    hsNormSq_centeredGrading_anticommutator_le_of_trace n d P hP H
      (signMatrix_conjTranspose_mul h hh) (signMatrix_mul_conjTranspose h hh) htrace hvanish
  apply sensitivity_bound_of_counting_energy f ((orderedConstantEdges h).card : ℝ)
    (hsNormSq (M * H + H * M)) (averageSensitivity_eq_parity_edges hf) hedge
  simpa only [mul_assoc] using henergy

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.sensitivity_bound_of_cube_grading := @_root_.OAI.LeanBlast.GotsmanLinial.sensitivity_bound_of_cube_grading
