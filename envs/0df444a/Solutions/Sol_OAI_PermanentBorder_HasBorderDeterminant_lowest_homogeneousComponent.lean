-- Prove2me | solution 1 for OAI.PermanentBorder.HasBorderDeterminant.lowest_homogeneousComponent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:46:18.19365+00:00
-- url     : https://prove2.me/submissions/7a070cdd-2e36-48a5-a837-53552238593d

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/InitialForm.lean:L107-L126
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.HasBorderDeterminant.lowest_homogeneousComponent. The node keeps its source
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
import Definitions.Def_OAI_Algebra_Determinantal_BorderPolars
import Definitions.Def_OAI_Algebra_Determinantal_InitialForm
import Theorems.Thm_OAI_PermanentBorder_HasBorderDeterminant_coefficientwise_limit
import Theorems.Thm_OAI_PermanentBorder_InitialHomogeneous_normalizedDilation_tendsto
import Theorems.Thm_OAI_PermanentBorder_degree_affineMatrixPolynomial
import Theorems.Thm_OAI_PermanentBorder_support_subset_cube_of_limit

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

theorem support_subset_exponentCube {P : Poly σ} {n : ℕ} (hP : P.totalDegree ≤ n) :
    P.support ⊆ exponentCube n := by
  intro d hd
  rw [mem_exponentCube]
  intro i
  exact (monomial_le_degreeOf i hd).trans ((degreeOf_le_totalDegree P i).trans hP)

theorem sum_over_exponentCube {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) :
    P = ∑ d ∈ exponentCube n, monomial d (P.coeff d) := by
  calc
    P = ∑ d ∈ P.support, monomial d (P.coeff d) := MvPolynomial.as_sum P
    _ = _ := ?_
  apply Finset.sum_subset hP
  intro d _ hd
  simp only [notMem_support_iff.mp hd, map_zero]

theorem coeff_linear_map_cube (F : Poly σ →ₗ[ℂ] Poly τ) {P : Poly σ} {n : ℕ}
    (hP : P.support ⊆ exponentCube n) (e : τ →₀ ℕ) :
    (F P).coeff e = ∑ d ∈ exponentCube n,
      P.coeff d * (F (monomial d 1)).coeff e := by
  conv_lhs => rw [sum_over_exponentCube hP]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [show monomial d (P.coeff d) = P.coeff d • monomial d (1 : ℂ) by simp [smul_monomial],
    map_smul, coeff_smul, smul_eq_mul]

theorem coefficientwise_linear_map_limit (F : Poly σ →ₗ[ℂ] Poly τ)
    {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    ∀ e, Tendsto (fun j => (F (P j)).coeff e) atTop (𝓝 ((F p).coeff e)) := by
  intro e
  have hc := support_subset_cube_of_limit hP hp
  have ht := tendsto_finsetSum (exponentCube (σ := σ) n)
    (fun d _ => (hp d).mul (tendsto_const_nhds (x := (F (monomial d 1)).coeff e)))
  convert ht using 1
  · funext j
    exact coeff_linear_map_cube F (hP j) e
  · congr 1
    exact coeff_linear_map_cube F hc e
end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem affineSubstitution_matrix (b : σ → ℂ) (B : σ → τ → ℂ)
    (n : ℕ) (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    affineSubstitution b B (affineMatrixPolynomial n A₀ A) =
      affineMatrixPolynomial n
        (fun i j => A₀ i j + ∑ v : σ, A v i j * b v)
        (fun w i j => ∑ v : σ, A v i j * B v w) := by
  classical
  unfold affineMatrixPolynomial
  have he := RingHom.map_det (affineSubstitution b B).toRingHom
    (show Matrix (Fin n) (Fin n) (Poly σ) from
      fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v)
  refine he.trans ?_
  apply congrArg Matrix.det
  funext i j
  change (affineSubstitution b B) (C (A₀ i j) + ∑ v, C (A v i j) * X v) =
    C (A₀ i j + ∑ v, A v i j * b v) + ∑ w, C (∑ v, A v i j * B v w) * X w
  simp only [affineSubstitution, map_add, map_sum, map_mul,
    aeval_C, aeval_X, algebraMap_eq]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, ← map_mul]
  rw [← add_assoc]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, map_mul, mul_assoc]

theorem HasBorderDeterminant.affineSubstitution {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (b : σ → ℂ) (B : σ → τ → ℂ) :
    HasBorderDeterminant n (affineSubstitution b B p) := by
  classical
  obtain ⟨hn, A₀, A, hlim⟩ := h
  refine ⟨hn,
    (fun l i j => A₀ l i j + ∑ v : σ, A l v i j * b v),
    (fun l w i j => ∑ v : σ, A l v i j * B v w), ?_⟩
  have hf := coefficientwise_linear_map_limit (PermanentBorder.affineSubstitution b B).toLinearMap
    (fun l => support_subset_exponentCube (degree_affineMatrixPolynomial n (A₀ l) (A l))) hlim
  intro e
  simpa only [AlgHom.toLinearMap_apply, affineSubstitution_matrix] using hf e
end AffineSubstitution
end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section ScalarNormalization
variable {σ : Type*} [Fintype σ]

theorem affineMatrixPolynomial_scaleRow (n : ℕ) (i₀ : Fin n) (a : ℂ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    affineMatrixPolynomial n (A₀.updateRow i₀ (a • A₀ i₀))
      (fun v => (A v).updateRow i₀ (a • A v i₀)) =
    a • affineMatrixPolynomial n A₀ A := by
  classical
  let M : Matrix (Fin n) (Fin n) (Poly σ) :=
    fun i j => C (A₀ i j) + ∑ v, C (A v i j) * X v
  let M' : Matrix (Fin n) (Fin n) (Poly σ) := fun i j =>
    C ((A₀.updateRow i₀ (a • A₀ i₀)) i j) +
      ∑ v, C (((A v).updateRow i₀ (a • A v i₀)) i j) * X v
  have hM : M' = M.updateRow i₀ ((C a : Poly σ) • M i₀) := by
    funext i j
    change C ((A₀.updateRow i₀ (a • A₀ i₀)) i j) + (∑ v,
      C (((A v).updateRow i₀ (a • A v i₀)) i j) * X v) = _
    by_cases hi : i = i₀
    · subst i
      rw [Matrix.updateRow_self, Matrix.updateRow_self]
      simp only [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, map_mul]
      change _ = C a * (C (A₀ i₀ j) + ∑ v, C (A v i₀ j) * X v)
      simp only [mul_add, Finset.mul_sum, mul_assoc]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi]
      simp only [Matrix.updateRow_ne hi]
      rfl
  change M'.det = a • M.det
  rw [hM]
  rw [Matrix.det_updateRow_smul]
  rw [Matrix.updateRow_eq_self]
  exact (MvPolynomial.smul_eq_C_mul M.det a).symm

theorem HasBorderDeterminant.smul {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (a : ℂ) : HasBorderDeterminant n (a • p) := by
  classical
  obtain ⟨hn, A₀, A, hlim⟩ := h
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨hn, (fun l => (A₀ l).updateRow i₀ (a • A₀ l i₀)),
    (fun l v => (A l v).updateRow i₀ (a • A l v i₀)), ?_⟩
  intro e
  simp only [affineMatrixPolynomial_scaleRow, coeff_smul, smul_eq_mul]
  exact tendsto_const_nhds.mul (hlim e)

theorem HasBorderDeterminant.affineSubstitution_smul
    {τ : Type*} [Fintype τ] {n : ℕ} {p : Poly σ}
    (h : HasBorderDeterminant n p) (b : σ → ℂ) (B : σ → τ → ℂ) (a : ℂ) :
    HasBorderDeterminant n (a • PermanentBorder.affineSubstitution b B p) :=
  (h.affineSubstitution b B).smul a
end ScalarNormalization
end PermanentBorder

end OAI

-- ---- from OAI.Algebra.Determinantal.InitialForm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

namespace InitialHomogeneous
variable {σ : Type*} [Fintype σ]

end InitialHomogeneous

/-- The lowest homogeneous component inherits the fixed border determinant size
by degeneration along a geometric sequence of nonzero scales. -/
theorem HasBorderDeterminant.lowest_homogeneousComponent
    {σ : Type*} [Fintype σ] {n r : ℕ} {q : Poly σ}
    (hb : HasBorderDeterminant n q)
    (hlow : ∀ j < r, homogeneousComponent j q = 0) :
    HasBorderDeterminant n (homogeneousComponent r q) := by
  classical
  let t : ℕ → ℂ := fun j => (1 / 2 : ℂ) ^ j
  have ht : Tendsto t atTop (𝓝 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    norm_num
  have hne : ∀ j, t j ≠ 0 := fun j => pow_ne_zero j (by norm_num)
  apply HasBorderDeterminant.coefficientwise_limit
    (P := fun j => InitialHomogeneous.normalizedDilation r q (t j))
  · intro j
    exact hb.affineSubstitution_smul (fun _ => 0)
      (fun i k => if i = k then t j else 0) ((t j ^ r)⁻¹)
  · exact InitialHomogeneous.normalizedDilation_tendsto hlow ht
      (Filter.Eventually.of_forall hne)

end PermanentBorder

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder
open MvPolynomial Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.HasBorderDeterminant.lowest_homogeneousComponent := @_root_.OAI.PermanentBorder.HasBorderDeterminant.lowest_homogeneousComponent
