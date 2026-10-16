-- Prove2me | solution 1 for OAI.PermanentBorder.degree_affineMatrixPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:40:42.438984+00:00
-- url     : https://prove2.me/submissions/845a8376-aa86-4fb7-979b-bc9b2e831f4c

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Model.lean:L244-L258
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.degree_affineMatrixPolynomial. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model

-- ---- from OAI.Algebra.Determinantal.Model ----
namespace OAI

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

end PermanentBorder.Polar

namespace PermanentBorder

open Filter
open scoped Topology

end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

theorem degree_affine_form (b : ℂ) (a : σ → ℂ) :
    (C b + ∑ v : σ, C (a v) * X v : Poly σ).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro v _
    exact (totalDegree_mul _ _).trans (by simp)

theorem degree_affineMatrixPolynomial (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    (affineMatrixPolynomial n A₀ A).totalDegree ≤ n := by
  classical
  unfold affineMatrixPolynomial
  have he := Matrix.det_apply (show Matrix (Fin n) (Fin n) (Poly σ) from
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  rw [he]
  apply totalDegree_finsetSum_le
  intro s _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum fun i _ => degree_affine_form _ _
    _ = n := by simp
end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

end AffineSubstitution
end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section ScalarNormalization
variable {σ : Type*} [Fintype σ]

end ScalarNormalization
end PermanentBorder

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder
open MvPolynomial Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.degree_affineMatrixPolynomial := @_root_.OAI.PermanentBorder.degree_affineMatrixPolynomial
