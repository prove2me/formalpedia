-- Prove2me | solution 1 for OAI.AffineBernstein.balanced_global_directional_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:12:27.579243+00:00
-- url     : https://prove2.me/submissions/ad6a70f3-fbf0-4c59-99b6-7b7f642946e2

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_balanced_affineMaximal_constant_det
import Theorems.Thm_OAI_AffineBernstein_normalized_balanced_det_bounds
import Theorems.Thm_OAI_AffineBernstein_normalized_critical_density

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PiolaAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expand one determinant row in the coordinate vectors. -/
theorem det_updateRow_sum (A : Matrix ι ι ℝ) (l : ι) (v : ι → ℝ) :
    (A.updateRow l v).det = ∑ m, v m * (A.updateRow l (Pi.single m 1)).det := by
  have hv : v = ∑ m, v m • Pi.single m (1 : ℝ) := by
    ext k
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    (A.updateRow l v).det =
        ∑ m, (A.updateRow l (v m • Pi.single m 1)).det := by
      conv_lhs => rw [hv]
      exact (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).map_update_sum
        Finset.univ l (fun m => v m • Pi.single m (1 : ℝ)) (fun k => A k)
    _ = _ := Finset.sum_congr rfl fun m _ => Matrix.det_updateRow_smul A l (v m) _

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_HessianDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- For an invertible Hessian, the manuscript's definition is exactly the adjugate. -/
theorem cofactorHessian_eq_adjugate {n : ℕ} (u : Space n → ℝ) (x : Space n)
    (hdet : (hessian u x).det ≠ 0) : cofactorHessian u x = (hessian u x).adjugate := by
  unfold cofactorHessian
  rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hdet, one_smul]

/-- The Hessian cofactor is symmetric under the standing positivity hypothesis. -/
theorem cofactorHessian_isSymm {n : ℕ} (u : Space n → ℝ) (x : Space n)
    (hpos : (hessian u x).PosDef) : (cofactorHessian u x).IsSymm := by
  rw [cofactorHessian_eq_adjugate u x (ne_of_gt hpos.det_pos)]
  exact (Matrix.isHermitian_iff_isSymm.mp hpos.isHermitian).adjugate

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The frozen coordinate Hessian has smooth entries at every interior smooth point. -/
theorem contDiffAt_hessian_entry {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => hessian u y i j) x := by
  exact (((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiffAt_const

/-- Determinants of the actual Hessian are smooth, by row multilinearity. -/
theorem contDiffAt_det_hessian {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : ContDiffAt ℝ ∞ (fun y => (hessian u y).det) x := by
  have hH : ContDiffAt ℝ ∞ (fun y i j => hessian u y i j) x :=
    contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu i j
  exact continuousDetRows.contDiff.contDiffAt.comp x hH

/-- The real determinant weight has its original exponent throughout the proof. -/
theorem contDiffAt_affineWeight {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef) :
    ContDiffAt ℝ ∞ (affineWeight u) x :=
  (contDiffAt_det_hessian hu).rpow_const_of_ne (ne_of_gt hpos.det_pos)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section WeightedDivergence

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem contDiffAt_dirDeriv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (dirDeriv v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem dirDeriv_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    dirDeriv v (fun y => f y * g y) x = dirDeriv v f x * g x + f x * dirDeriv v g x := by
  simp only [dirDeriv, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

theorem dirDeriv_sum (f : ι → E → ℝ) {x : E}
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) (v : E) :
    dirDeriv v (fun y => ∑ i, f i y) x = ∑ i, dirDeriv v (f i) x := by
  simp only [dirDeriv, fderiv_fun_sum (fun i _ => hf i), sum_apply]

end WeightedDivergence

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CompactIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section CompactIntegration

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Global smoothness of a fixed-direction derivative. -/
theorem contDiff_dirDeriv {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (dirDeriv v f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

end CompactIntegration

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DeterminantVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section RadialCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Commuting fixed-direction differentiation with evaluation of a derivative. -/
theorem dirDeriv_eq_second {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v z : E) :
    dirDeriv v (dirDeriv z f) x = fderiv ℝ (fderiv ℝ f) x v z := by
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const z x)
  change fderiv ℝ (fun y => fderiv ℝ f y z) x v = _
  rw [he.fderiv]
  simp

/-- Symmetry of the second derivative in fixed directions. -/
theorem dirDeriv_comm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v z : E) :
    dirDeriv v (dirDeriv z f) x = dirDeriv z (dirDeriv v f) x := by
  rw [dirDeriv_eq_second hf, dirDeriv_eq_second hf]
  exact hf.isSymmSndFDerivAt (by simp) v z

end RadialCalculus

/-- Jacobi's formula in arbitrary fixed directions, for the actual entries. -/
theorem dirDeriv_det {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] (A : E → Matrix ι ι ℝ) {x : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E) :
    dirDeriv v (fun y => (A y).det) x =
      ∑ i, ∑ j, (A x).adjugate j i * dirDeriv v (fun y => A y i j) x := by
  let D : E →L[ℝ] (ι → ι → ℝ) := ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.pi fun j => fderiv ℝ (fun y => A y i j) x
  have hD : HasFDerivAt (fun y i j => A y i j) D x :=
    hasFDerivAt_pi.mpr fun i => hasFDerivAt_pi.mpr fun j => (hA i j).hasFDerivAt
  have hc := (continuousDetRows.hasFDerivAt (fun i j => A x i j)).comp x hD
  change fderiv ℝ (continuousDetRows ∘ (fun y i j => A y i j)) x v = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change ((A x).updateRow i (fun j => dirDeriv v (fun y => A y i j) x)).det = _
  rw [det_updateRow_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.adjugate_apply, mul_comm]

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

/-- Linear functionals are recovered exactly by coordinates. -/
theorem clm_coordinate_sum {n : ℕ} (L : Space n →L[ℝ] ℝ) (v : Space n) :
    L v = ∑ i, v i * L (coordinateVector n i) := by
  conv_lhs => rw [← sum_coordinateVector v]
  simp

/-- The radial vector derivative is the sum of its coordinate derivatives. -/
theorem dirDeriv_coordinate_sum {n : ℕ} (f : Space n → ℝ) (x v : Space n) :
    dirDeriv v f x = ∑ i, v i * dirDeriv (coordinateVector n i) f x :=
  clm_coordinate_sum (fderiv ℝ f x) v

theorem dirDeriv_graphAffineFunction {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ u x) (a : Space n →L[ℝ] ℝ) (b d : ℝ) (v : Space n) :
    dirDeriv v (graphAffineFunction u a b d) x = a v + b * dirDeriv v u x := by
  unfold dirDeriv graphAffineFunction
  rw [fderiv_add_const, fderiv_fun_add a.differentiableAt (hu.const_mul b),
    fderiv_const_mul hu]
  simp

theorem hessian_graphAffineFunction {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) (i j : Fin n) :
    hessian (graphAffineFunction u a b d) x i j = b * hessian u x i j := by
  have he : dirDeriv (coordinateVector n j) (graphAffineFunction u a b d) =ᶠ[nhds x]
      (fun y => a (coordinateVector n j) + b * dirDeriv (coordinateVector n j) u y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_graphAffineFunction
      ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) a b d _
  change fderiv ℝ (dirDeriv (coordinateVector n j) (graphAffineFunction u a b d)) x
    (coordinateVector n i) = _
  rw [he.fderiv_eq, fderiv_const_add,
    fderiv_const_mul ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx))
      (coordinateVector n j)).differentiableAt (by simp))]
  rfl

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

theorem hessian_isSymm {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : (hessian u x).IsSymm := by
  ext i j
  exact dirDeriv_comm hu (coordinateVector n j) (coordinateVector n i)

theorem matrix_trace_pair {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm) : (A * B).trace = ∑ i, ∑ j, A i j * B i j := by
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ j, A i j * B j i) = ∑ j, A i j * B i j
  apply Finset.sum_congr rfl
  intro j hj
  rw [hB.apply j i]

/-- First derivative of composition with an affine base change. -/
theorem dirDeriv_comp_affine {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n)
    {u : Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u (affineBaseMap B d x))
    (v : Space n) :
    dirDeriv v (fun y => u (affineBaseMap B d y)) x =
      dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B v) u (affineBaseMap B d x) := by
  have ht : HasFDerivAt (affineBaseMap B d) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B) x := by
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).hasFDerivAt.add_const d
  change fderiv ℝ (u ∘ affineBaseMap B d) x v = _
  rw [(hu.hasFDerivAt.comp x ht).fderiv]
  rfl

/-- The Hessian chain rule, retaining the exact order Bᵀ H B. -/
theorem hessian_comp_affine {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) {x : Space n}
    (hx : affineBaseMap B d x ∈ Ω) :
    hessian (fun y => u (affineBaseMap B d y)) x =
      B.transpose * hessian u (affineBaseMap B d x) * B := by
  have hT : Continuous (affineBaseMap B d) := by unfold affineBaseMap; fun_prop
  have hΩ' : IsOpen (affineBaseMap B d ⁻¹' Ω) := hΩ.preimage hT
  ext i j
  have he : dirDeriv (coordinateVector n j) (fun y => u (affineBaseMap B d y)) =ᶠ[nhds x]
      (fun y => dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j)) u (affineBaseMap B d y)) := by
    filter_upwards [hΩ'.mem_nhds hx] with y hy
    exact dirDeriv_comp_affine B d ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) _
  change fderiv ℝ (dirDeriv (coordinateVector n j) (fun y => u (affineBaseMap B d y))) x (coordinateVector n i) =
    (B.transpose * hessian u (affineBaseMap B d x) * B) i j
  rw [he.fderiv_eq]
  change dirDeriv (coordinateVector n i) (fun y =>
    dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j)) u (affineBaseMap B d y)) x = _
  rw [dirDeriv_comp_affine B d
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) _).differentiableAt (by simp))]
  rw [dirDeriv_eq_second (hu.contDiffAt (hΩ.mem_nhds hx))]
  rw [← sum_coordinateVector (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n i)),
      ← sum_coordinateVector (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j))]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, euclideanCLM_coordinateVector, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hd : fderiv ℝ (fderiv ℝ u) (affineBaseMap B d x) (coordinateVector n l) (coordinateVector n k) =
      hessian u (affineBaseMap B d x) l k :=
    (dirDeriv_eq_second (hu.contDiffAt (hΩ.mem_nhds hx)) _ _).symm
  rw [hd]
  ring

/-- Multiplying heights by a scalar multiplies the actual Hessian by it. -/
theorem hessian_const_mul {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (c : ℝ) {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => c * u y) x = c • hessian u x := by
  ext i j
  have he : (fun y => fderiv ℝ (fun z => c * u z) y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => c * dirDeriv (coordinateVector n j) u y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [fderiv_const_mul ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) c]
    rfl
  change fderiv ℝ _ x (coordinateVector n i) = c * _
  rw [he.fderiv_eq, fderiv_const_mul
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) _).differentiableAt (by simp)) c]
  rfl

/-- Nonsingular congruence and positive scalar multiplication preserve strict
ellipticity. The condition on B is exactly invertibility, not orthogonality. -/
theorem posDef_affine_congruence {n : ℕ} {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c) :
    (c • (B.transpose * H * B)).PosDef := by
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB)
  have hBt : B.conjTranspose = B.transpose := by ext i j; simp
  simpa only [hBt] using
    (hH.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hBu)).smul hc

/-- Exact determinant normalization used for rescaled sections. -/
theorem det_affine_congruence {n : ℕ} (H B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (c • (B.transpose * H * B)).det = (c ^ n * B.det ^ 2) * H.det := by
  simp only [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The trace contraction is invariant under simultaneous congruence, with the
exact scalar ratio. This is the algebra behind covariance of the affine PDE. -/
theorem trace_inverse_congruence {n : ℕ} {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c)
    (K : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ((c • (B.transpose * H * B))⁻¹ * (t • (B.transpose * K * B))).trace =
    (c⁻¹ * t) * (H⁻¹ * K).trace := by
  let : Invertible c := invertibleOfNonzero (ne_of_gt hc)
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBt : IsUnit B.transpose.det := by simpa using hBu
  have hPu : IsUnit (B.transpose * H * B).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hB (ne_of_gt hH.det_pos)) hB
  rw [Matrix.inv_smul _ c hPu, invOf_eq_inv, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  suffices hs : (((B.transpose * H * B)⁻¹) * (B.transpose * K * B)).trace =
      (H⁻¹ * K).trace by rw [hs]; ring
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have he : (B⁻¹ * (H⁻¹ * B.transpose⁻¹)) * (B.transpose * K * B) =
      B⁻¹ * (H⁻¹ * K) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B.transpose⁻¹ B.transpose, Matrix.nonsing_inv_mul _ hBt, one_mul]
  rw [he, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hBu, one_mul]

/-- The classical PDE is equivalent to the inverse-Hessian trace formulation
wherever its coefficients are the actual positive-definite Hessian. -/
theorem affineMaximalOn_iff_trace {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) :
    AffineMaximalOn Ω u ↔ ∀ x ∈ Ω,
      ((hessian u x)⁻¹ * hessian (affineWeight u) x).trace = 0 := by
  apply forall₂_congr
  intro x hx
  have hw := hessian_isSymm (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hx)) (hpos x hx))
  rw [matrix_trace_pair _ _ hw]
  change (∑ i, ∑ j, (hessian u x).det * (hessian u x)⁻¹ i j * hessian (affineWeight u) x i j) = 0 ↔ _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  exact mul_eq_zero_iff_left (ne_of_gt (hpos x hx).det_pos)

theorem contDiff_affineBaseMap {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) :
    ContDiff ℝ ∞ (affineBaseMap B d) := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).contDiff.add contDiff_const

theorem contDiffOn_affineGraphPullback {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) :
    ContDiffOn ℝ ∞ (affineGraphPullback u B d a c e) (affineBaseMap B d ⁻¹' Ω) := by
  have hut := hu.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  exact (a.contDiff.contDiffOn.add (contDiffOn_const.mul hut)).add contDiffOn_const

theorem hessian_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    hessian (affineGraphPullback u B d a c e) x =
      c • (B.transpose * hessian u (affineBaseMap B d x) * B) := by
  have hΩ' := hΩ.preimage (contDiff_affineBaseMap B d).continuous
  have hut := hu.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  have hh : hessian (affineGraphPullback u B d a c e) x =
      c • hessian (fun y => u (affineBaseMap B d y)) x := by
    ext i j
    exact hessian_graphAffineFunction hΩ' hut hx a c e i j
  rw [hh, hessian_comp_affine hΩ hu B d hx]

theorem posDef_hessian_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    (hessian (affineGraphPullback u B d a c e) x).PosDef := by
  rw [hessian_affineGraphPullback hΩ hu B d a c e hx]
  exact posDef_affine_congruence (hpos _ hx) hB hc

/-- The actual determinant weight transforms by its exact positive constant. -/
theorem affineWeight_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    affineWeight (affineGraphPullback u B d a c e) x =
      Real.rpow (c ^ n * B.det ^ 2) (-(((n : ℝ) + 1) / ((n : ℝ) + 2))) *
        affineWeight u (affineBaseMap B d x) := by
  unfold affineWeight
  rw [hessian_affineGraphPullback hΩ hu B d a c e hx, det_affine_congruence]
  exact Real.mul_rpow (mul_nonneg (pow_nonneg hc.le _) (sq_pos_of_ne_zero hB).le)
    (hpos _ hx).det_pos.le

/-- Hessians are local, including their inner derivative. -/
theorem hessian_congr_nhds {n : ℕ} {u v : Space n → ℝ} {x : Space n}
    (he : u =ᶠ[nhds x] v) : hessian u x = hessian v x := by
  ext i j
  have hd : (fun y => fderiv ℝ u y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ v y (coordinateVector n j)) :=
    he.fderiv.mono (fun _ hy => congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n j)) hy)
  exact congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n i)) hd.fderiv_eq

/-- Exact, classical affine-maximal PDE covariance for section normalization.
No transformed PDE is assumed: it follows from the original one by the actual
Hessian and determinant chain rules. -/
theorem affineMaximalOn_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ) :
    AffineMaximalOn (affineBaseMap B d ⁻¹' Ω) (affineGraphPullback u B d a c e) := by
  have hΩ' := hΩ.preimage (contDiff_affineBaseMap B d).continuous
  have hv := contDiffOn_affineGraphPullback hu B d a c e
  have hpv : ∀ x ∈ affineBaseMap B d ⁻¹' Ω,
      (hessian (affineGraphPullback u B d a c e) x).PosDef :=
    fun _ hx => posDef_hessian_affineGraphPullback hΩ hu hpos hB d a hc e hx
  apply (affineMaximalOn_iff_trace hΩ' hv hpv).mpr
  intro x hx
  let t := Real.rpow (c ^ n * B.det ^ 2) (-(((n : ℝ) + 1) / ((n : ℝ) + 2)))
  have hw : ContDiffOn ℝ ∞ (affineWeight u) Ω := by
    intro y hy
    exact (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hy)) (hpos y hy)).contDiffWithinAt
  have hwt : ContDiffOn ℝ ∞ (fun y => affineWeight u (affineBaseMap B d y))
      (affineBaseMap B d ⁻¹' Ω) :=
    hw.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  have hew : affineWeight (affineGraphPullback u B d a c e) =ᶠ[nhds x]
      (fun y => t * affineWeight u (affineBaseMap B d y)) := by
    filter_upwards [hΩ'.mem_nhds hx] with y hy
    exact affineWeight_affineGraphPullback hΩ hu hpos hB d a hc e hy
  rw [hessian_congr_nhds hew, hessian_const_mul hΩ' hwt t hx,
    hessian_comp_affine hΩ hw B d hx, hessian_affineGraphPullback hΩ hu B d a c e hx,
    trace_inverse_congruence (hpos _ hx) hB hc,
    (affineMaximalOn_iff_trace hΩ hu hpos).mp hmax _ hx, mul_zero]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

theorem hessian_eq_second {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    hessian u x i j =
      fderiv ℝ (fderiv ℝ u) x (coordinateVector n i) (coordinateVector n j) := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (coordinateVector n j) x)
  unfold hessian
  rw [he.fderiv]
  simp

theorem second_fderiv_eq_sum {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (v : Space n) :
    fderiv ℝ (fderiv ℝ u) x v v =
    ∑ i, ∑ j, v i * hessian u x i j * v j := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x (∑ i, v i • coordinateVector n i)
        (∑ j, v j • coordinateVector n j) := by rw [sum_coordinateVector]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hessian_eq_second hu,
        hu.isSymmSndFDerivAt (by simp)
          (coordinateVector n j) (coordinateVector n i)]
      ring

theorem second_fderiv_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosSemidef) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_nonneg (fun i => v i)

theorem second_fderiv_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  have hv' : (fun i => v i) ≠ 0 := fun he => hv (by ext i; exact congrFun he i)
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_pos hv'

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem contDiffAt_gradient {H : E → ℝ} {e : E} (hh : ContDiffAt ℝ ∞ H e) :
    ContDiffAt ℝ ∞ (gradient H) e :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
    e (hh.fderiv_right (by simp))

theorem inner_fderiv_gradient {H : E → ℝ} {e : E} (hh : ContDiffAt ℝ ∞ H e)
    (v w : E) : inner ℝ (fderiv ℝ (gradient H) e v) w =
      fderiv ℝ (fderiv ℝ H) e v w := by
  have hd := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt.comp
    e ((hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  change inner ℝ (fderiv ℝ (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ H x)) e v) w = _
  change HasFDerivAt (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ H x)) _ e at hd
  rw [hd.fderiv]
  simp

end
section PositiveDerivative
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive-definiteness of the derivative makes a map injective on a convex
set, by strict monotonicity along every segment. -/
lemma injOn_of_positive_derivative {S : Set E} (hS : Convex ℝ S) {G : E → E}
    (hG : ∀ x ∈ S, DifferentiableAt ℝ G x)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < inner ℝ (fderiv ℝ G x v) v) :
    Set.InjOn G S := by
  intro x hx y hy he
  by_contra hxy
  let v := y-x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  let γ := fun t : ℝ => x+t • v
  let f := fun t : ℝ => inner ℝ (G (γ t)) v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const v).const_add x
  have hγS (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : γ t ∈ S :=
    hS.add_smul_sub_mem hx hy ht
  have hf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt f (inner ℝ (fderiv ℝ G (γ t) v) v) t := by
    simpa [f] using ((hG (γ t) (hγS t ht)).hasFDerivAt.comp_hasDerivAt t (hγ t)).inner ℝ
      (hasDerivAt_const t v)
  have hmono : StrictMonoOn f (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · intro t ht
      exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hf t ht').deriv]
      exact hpos (γ t) (hγS t ht') v hv
  have hh := hmono (show (0:ℝ) ∈ Icc 0 1 by norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0:ℝ)<1)
  have h0 : f 0 = inner ℝ (G x) v := by simp [f,γ]
  have h1 : f 1 = inner ℝ (G y) v := by simp [f,γ,v]
  rw [h0,h1,he] at hh
  exact lt_irrefl _ hh
end PositiveDerivative

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ConvexGradientBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_fderiv_support {Ω : Set E} {f : E → ℝ} (hc : ConvexOn ℝ Ω f)
    {x y : E} (hx : x ∈ Ω) (hy : y ∈ Ω) (hd : DifferentiableAt ℝ f x) :
    fderiv ℝ f x (y-x) ≤ f y-f x := by
  have hh := hc.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have hγ : HasDerivAt (fun t : ℝ => t • (y-x)+x) (y-x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y-x)).add_const x
  have hdf : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x y) (fderiv ℝ f x (y-x)) 0 := by
    have hd' : HasFDerivAt f (fderiv ℝ f x) ((0:ℝ) • (y-x)+x) := by
      simpa using hd.hasFDerivAt
    simpa only [AffineMap.lineMap_apply_module',Function.comp_def] using
      hd'.comp_hasDerivAt 0 hγ
  have h0 : (0:ℝ) ∈ AffineMap.lineMap (k := ℝ) x y ⁻¹' Ω := by simpa
  have h1 : (1:ℝ) ∈ AffineMap.lineMap (k := ℝ) x y ⁻¹' Ω := by simpa
  have hs := hh.le_slope_of_hasDerivAt h0 h1 (by norm_num) hdf
  simpa only [slope_def_field,sub_zero,div_one,Function.comp_apply,
    AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hs

end ConvexGradientBound

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphPatchArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem convexOn_of_hessian_posSemidef {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    ConvexOn ℝ Ω u := by
  refine ⟨hcv, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (u ∘ γ) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hf hdf hdd
      (fun t ht => second_fderiv_nonneg
        (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
        (hp _ (hseg t (interior_subset ht))) (y - x))
  have he := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have heq : γ b = a • x + b • y := by
    dsimp [γ]
    rw [smul_sub]
    have ha' : a = 1 - b := by linarith
    rw [ha', sub_smul, one_smul]
    abel
  simpa [Function.comp_def, γ, heq, smul_eq_mul] using he

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JetCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem second_fderiv_comp {f : F → G} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) +
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hdf := hf.differentiableAt (by simp)
  have hdg := hg.differentiableAt (by simp)
  have hddf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hddg := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hdfg := (((hf.comp x hg).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
  have hleft := hdfg.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hright := (hddf.hasFDerivAt.comp x hdg.hasFDerivAt).clm_apply
    (hddg.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have heq : (fun q => fderiv ℝ (f ∘ g) q w) =ᶠ[𝓝 x]
      (fun q => fderiv ℝ f (g q) (fderiv ℝ g q w)) := by
    have hfg : ∀ᶠ q in 𝓝 x, ContDiffAt ℝ 1 f (g q) := hg.continuousAt.eventually
      ((hf.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp))
    filter_upwards [hfg,
      (hg.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqf hqg
    rw [fderiv_comp q (hqf.differentiableAt (by norm_num)) (hqg.differentiableAt (by norm_num))]
    rfl
  have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hh := congrArg (fun L : E →L[ℝ] G => L v) he
  simpa [add_comm] using hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeDensityVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

lemma second_fderiv_affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} (L : S →L[ℝ] F) (a : F)
    {x : S} (hf : ContDiffAt ℝ ∞ f (a + L x)) (v w : S) :
    fderiv ℝ (fderiv ℝ (fun z => f (a + L z))) x v w =
      fderiv ℝ (fderiv ℝ f) (a + L x) (L v) (L w) := by
  have hd (z : S) : fderiv ℝ (fun z => a + L z) z = L := by
    exact ((L.hasFDerivAt).const_add a).fderiv
  have hdd : fderiv ℝ (fderiv ℝ (fun z => a + L z)) x = 0 := by
    rw [show fderiv ℝ (fun z => a + L z) = (fun _ => L) from funext hd]
    simp
  change fderiv ℝ (fderiv ℝ (f ∘ (fun z => a + L z))) x v w = _
  rw [second_fderiv_comp (g := fun z => a + L z) hf (contDiffAt_const.add L.contDiff.contDiffAt), hd, hdd]
  simp

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportAnnulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

variable {n : ℕ}

lemma toMatrix_fderiv_gradient_eq_hessian_transpose {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fderiv ℝ (gradient u) x).toLinearMap =
      (hessian u x).transpose := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (OrthonormalBasis.repr (EuclideanSpace.basisFun (Fin n) ℝ)
    (fderiv ℝ (gradient u) x ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i = _
  rw [OrthonormalBasis.repr_apply_apply,real_inner_comm,
    inner_fderiv_gradient hu,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_apply]
  exact (hessian_eq_second hu j i).symm

lemma det_fderiv_shiftedGradient {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) :
    (fderiv ℝ (fun x => gradient u x + x) x).det = (hessian u x + 1).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have he : (fderiv ℝ (fun x => gradient u x + x) x).toLinearMap =
      (fderiv ℝ (gradient u) x).toLinearMap + LinearMap.id := by
    change (fderiv ℝ (fun y => gradient u y + id y) x).toLinearMap = _
    rw [fderiv_fun_add ((contDiffAt_gradient hu).differentiableAt (by simp)) differentiableAt_id,
      fderiv_id]
    rfl
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,he,map_add,
    toMatrix_fderiv_gradient_eq_hessian_transpose hu,LinearMap.toMatrix_id]
  have ht : (hessian u x).transpose + (1 : Matrix (Fin n) (Fin n) ℝ) =
      (hessian u x + 1).transpose := by
    ext i j
    simp only [Matrix.add_apply,Matrix.transpose_apply,Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij,Ne.symm]
  rw [ht,Matrix.det_transpose]

/- On any bounded measurable annular set, the cofactor trace of the literal
support Hessian has a bound depending only on the radius of the convex fiber.
The proof uses the injective shifted Gauss map and genuine change of variables. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_HessianMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

variable {n : ℕ}

lemma shiftedGradient_injOn_of_hessian_posSemidef {Ω : Set (Space n)}
    (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ∀ x ∈ Ω, ContDiffAt ℝ ∞ u x)
    (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    Set.InjOn (fun x => gradient u x + x) Ω := by
  apply injOn_of_positive_derivative hcv
  · intro x hx
    exact ((contDiffAt_gradient (hu x hx)).differentiableAt (by simp)).add differentiableAt_id
  · intro x hx v hv
    change 0 < inner ℝ (fderiv ℝ (fun y => gradient u y + id y) x v) v
    rw [fderiv_fun_add ((contDiffAt_gradient (hu x hx)).differentiableAt (by simp))
      differentiableAt_id,fderiv_id]
    simp only [add_apply,ContinuousLinearMap.id_apply,inner_add_left,
      inner_fderiv_gradient (hu x hx)]
    exact add_pos_of_nonneg_of_pos (second_fderiv_nonneg (hu x hx) (hp x hx) v)
      (real_inner_self_pos.mpr hv)

/- One genuine change of variables for the shifted convex gradient bounds
all the large principal minors at once. This is an alternative proof of the
source principal-minor estimate, with every quantity the actual Hessian.
It does not posit any Hessian or determinant bound. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualBaseMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

section ConvexGradientBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- A bounded convex function on a full larger ball has bounded actual
Euclidean gradient at its center. No derivative estimate is assumed. -/
lemma norm_gradient_le_of_convex_bounded {Ω : Set E} {f : E → ℝ}
    (hc : ConvexOn ℝ Ω f) {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ f x)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : Metric.closedBall x r ⊆ Ω) (hb : ∀ y ∈ Ω, |f y| ≤ M) :
    ‖gradient f x‖ ≤ 2*M/r := by
  by_cases hg : gradient f x = 0
  · simp only [hg,norm_zero]
    positivity
  have hgp : 0 < ‖gradient f x‖ := norm_pos_iff.mpr hg
  let y := x + (r/‖gradient f x‖) • gradient f x
  have hdist : dist y x = r := by
    rw [dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hgp),
      div_mul_cancel₀ _ hgp.ne']
  have hy : y ∈ Ω := hball (by rw [Metric.mem_closedBall,hdist])
  have hs := convex_fderiv_support hc hx hy hd
  have he : fderiv ℝ f x (y-x) = r*‖gradient f x‖ := by
    dsimp [y]
    rw [add_sub_cancel_left,map_smul,smul_eq_mul,← inner_gradient_left,
      real_inner_self_eq_norm_sq]
    field_simp
  rw [he] at hs
  have hfx := (abs_le.mp (hb x hx)).1
  have hfy := (abs_le.mp (hb y hy)).2
  apply (le_div_iff₀ hr).mpr
  nlinarith

end ConvexGradientBound

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/
theorem matrixLinearEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (x : Space n) (i : Fin n) :
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis A hA x i =
      A.mulVec x i := by
  simp [Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
    EuclideanSpace.basisFun_apply, Pi.single_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      Matrix.mulVec, dotProduct]

/- A convex combination allowing unused mass at the origin. -/
theorem convex_sum_mem_le_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] {K : Set E} (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (c : ι → ℝ) (v : ι → E) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ i, c i ≤ 1) (hv : ∀ i, v i ∈ K) : (∑ i, c i • v i) ∈ K := by
  classical
  have hn : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  by_cases hz : ∑ i, c i = 0
  · have hc0 : ∀ i, c i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hz i (Finset.mem_univ i)
    simpa [hc0] using h0
  · have hp : 0 < ∑ i, c i := lt_of_le_of_ne hn (Ne.symm hz)
    have hm := hK.centerMass_mem (t := Finset.univ) (w := c) (z := v)
      (fun i _ => hc i) hp (fun i _ => hv i)
    have he := hK.smul_mem_of_zero_mem h0 hm ⟨hn, hsum⟩
    simpa [Finset.centerMass, smul_smul, hz] using he

/- The cross-polytope spanned by any points of a symmetric convex body lies
in that body. This is the inner-inclusion half of max-determinant normalization. -/
theorem symmetric_convex_sum_mem {n : ℕ} {K : Set (Space n)}
    (hK : Convex ℝ K) (h0 : (0 : Space n) ∈ K)
    (hneg : ∀ x ∈ K, -x ∈ K) (v : Fin n → Space n)
    (hv : ∀ i, v i ∈ K) (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) :
    (∑ i, c i • v i) ∈ K := by
  classical
  let w : Fin n → Space n := fun i => if 0 ≤ c i then v i else -v i
  have hw (i : Fin n) : w i ∈ K := by
    dsimp [w]; split_ifs <;> first | exact hv i | exact hneg _ (hv i)
  have he (i : Fin n) : |c i| • w i = c i • v i := by
    dsimp [w]; split_ifs with hi
    · rw [abs_of_nonneg hi]
    · rw [abs_of_neg (lt_of_not_ge hi), neg_smul, smul_neg, neg_neg]
  simpa only [he] using convex_sum_mem_le_one hK h0 (fun i => |c i|) w
    (fun i => abs_nonneg _) hc hw

/- The exact ℓ¹/Euclidean comparison used for the inner ball. -/
theorem sum_abs_coordinate_le {n : ℕ} (x : Space n) :
    ∑ i, |x i| ≤ Real.sqrt n * ‖x‖ := by
  have he := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin n => |x i|)
    (fun _ => (1 : ℝ))
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul, ← Real.norm_eq_abs, ← hn, Real.sqrt_sq (norm_nonneg _),
    mul_comm] using he

/- The exact ℓ∞/Euclidean comparison used for the outer ball. -/
theorem norm_le_sqrt_card_of_coordinate_le {n : ℕ} (x : Space n)
    (hx : ∀ i, |x i| ≤ 1) : ‖x‖ ≤ Real.sqrt n := by
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  have hs : ‖x‖ ^ 2 ≤ (n : ℝ) := by
    rw [hn]
    calc
      _ ≤ ∑ i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        have := hx i
        rw [Real.norm_eq_abs]
        nlinarith [sq_nonneg (|x i| - 1), abs_nonneg (x i)]
      _ = n := by simp
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (by rwa [Real.sq_sqrt (Nat.cast_nonneg n)])

/- A compact body's column determinant has a maximizer, with nonzero value
whenever the body contains a ball about zero. -/
theorem exists_max_det_columns {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0 : Space n) r ⊆ K) :
    ∃ v : Fin n → Space n, (∀ i, v i ∈ K) ∧
      (Matrix.det (fun i j => v j i) ≠ 0) ∧
      ∀ w : Fin n → Space n, (∀ i, w i ∈ K) →
        |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)| := by
  classical
  let S : Set (Fin n → Space n) := {v | ∀ i, v i ∈ K}
  have hS : IsCompact S := isCompact_pi_infinite (fun _ => hK)
  let w : Fin n → Space n := fun j => r • EuclideanSpace.single j 1
  have hw : w ∈ S := by
    intro i
    apply hball
    simp [w, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
  have hM : (fun i j => w j i) = (r : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [w, Matrix.one_apply]
  have hd : Matrix.det (fun i j => w j i) ≠ 0 := by rw [hM]; simp [hr.ne']
  obtain ⟨v, hv, hmax⟩ := hS.exists_isMaxOn ⟨w, hw⟩
    (show Continuous (fun v : Fin n → Space n => |Matrix.det (fun i j => v j i)|) by
      fun_prop).continuousOn
  refine ⟨v, hv, ?_, fun w hw => hmax hw⟩
  intro hz
  have hh := hmax hw
  change |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)| at hh
  rw [hz, abs_zero] at hh
  exact hd (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

/- Maximal determinant makes each inverse coordinate of a body point at most
one. The proof is the literal one-column replacement identity. -/
theorem maxdet_coordinate_bound {n : ℕ} {K : Set (Space n)}
    (v : Fin n → Space n) (hv : ∀ i, v i ∈ K)
    (hd : Matrix.det (fun i j => v j i) ≠ 0)
    (hmax : ∀ w : Fin n → Space n, (∀ i, w i ∈ K) →
      |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)|) :
    ∃ q : Space n ≃ₗ[ℝ] Space n,
      (∀ x : Space n, q x = ∑ i, x i • v i) ∧
      ∀ x ∈ K, ∀ i, |q.symm x i| ≤ 1 := by
  classical
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => v j i
  let q : Space n ≃ₗ[ℝ] Space n :=
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis M
      (isUnit_iff_ne_zero.mpr hd)
  have hq (x : Space n) : q x = ∑ i, x i • v i := by
    ext j
    rw [show q x j = M.mulVec x j from matrixLinearEquiv_apply M _ x j]
    simp [Matrix.mulVec, dotProduct, M, mul_comm]
  refine ⟨q, hq, ?_⟩
  intro x hx j
  have hw : ∀ i, Function.update v j x i ∈ K := by
    intro i
    by_cases h : i = j
    · simpa [h] using hx
    · simpa [Function.update_of_ne h] using hv i
  have hm := hmax (Function.update v j x) hw
  have hcol : (fun i k => Function.update v j x k i) = M.updateCol j x := by
    ext i k
    simp [Matrix.updateCol, M, Function.update_apply]
    split_ifs <;> rfl
  have hsum : (fun k => ∑ i, (q.symm x i) • M k i) = (fun k => x k) := by
    funext k
    have he := congrArg (fun p : Space n => p k) (hq (q.symm x))
    simpa [M, mul_comm] using he.symm
  rw [hcol] at hm
  change |(M.updateCol j (fun k => x k)).det| ≤ |M.det| at hm
  rw [← hsum, Matrix.det_updateCol_sum, smul_eq_mul, abs_mul] at hm
  have hdpos : 0 < |M.det| := abs_pos.mpr hd
  change |q.symm x j| * |M.det| ≤ |M.det| at hm
  exact (mul_le_mul_iff_left₀ hdpos).mp (by simpa using hm)

/- The symmetric max-determinant normalization, with the exact weaker radius
n sufficient for all centered normalizations used in the source. -/
theorem symmetric_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (h0 : (0 : Space n) ∈ K) (hneg : ∀ x ∈ K, -x ∈ K)
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall (0 : Space n) r ⊆ K) :
    ∃ A : Space n ≃L[ℝ] Space n,
      Metric.closedBall 0 1 ⊆ A '' K ∧ A '' K ⊆ Metric.closedBall 0 n := by
  obtain ⟨v, hv, hd, hmax⟩ := exists_max_det_columns hK hr hball
  obtain ⟨q, hq, hh⟩ := maxdet_coordinate_bound v hv hd hmax
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  let S := LinearEquiv.smulOfNeZero ℝ (Space n) (Real.sqrt n) hspos.ne'
  let A := (q.symm.trans S).toContinuousLinearEquiv
  have hA (x : Space n) : A x = Real.sqrt n • q.symm x := rfl
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hxn : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    let y : Space n := (Real.sqrt n)⁻¹ • x
    have hy : ∑ i, |y i| ≤ 1 := by
      calc
        _ ≤ Real.sqrt n * ‖y‖ := sum_abs_coordinate_le y
        _ = ‖x‖ := by simp [y, norm_smul, Real.norm_eq_abs, abs_of_pos hspos,
          hspos.ne']
        _ ≤ 1 := hxn
    have hmem : q y ∈ K := hq y ▸ symmetric_convex_sum_mem hconv h0 hneg v hv
      (fun i => y i) hy
    refine ⟨q y, hmem, ?_⟩
    rw [hA, LinearEquiv.symm_apply_apply]
    simp [y, smul_smul, hspos.ne']
  · rintro x ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul,
      Real.norm_eq_abs, abs_of_pos hspos]
    calc
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left
        (norm_le_sqrt_card_of_coordinate_le _ (hh y hy)) hspos.le
      _ = n := Real.mul_self_sqrt hnpos.le

open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/
theorem centered_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (h0 : (0 : Space n) ∈ K)
    {C : ℝ} (hC : 1 ≤ C) (hbal : -K ⊆ C • K) :
    ∃ A : Space n ≃L[ℝ] Space n,
      Metric.closedBall 0 (2 / (C + 1)) ⊆ A '' K ∧
      A '' K ⊆ Metric.closedBall 0 (2 * n) := by
  let D := K - K
  have hDeq : D = (fun p : Space n × Space n => p.1 - p.2) '' (K ×ˢ K) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hDc : IsCompact D := by
    rw [hDeq]
    exact (hK.prod hK).image (continuous_fst.sub continuous_snd)
  have hDv : Convex ℝ D := hconv.sub hconv
  have hD0 : (0 : Space n) ∈ D := ⟨0, h0, 0, h0, sub_self _⟩
  have hDneg : ∀ x ∈ D, -x ∈ D := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, (neg_sub _ _).symm⟩
  obtain ⟨p, hp⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hp)
  have hDb : Metric.closedBall (0 : Space n) r ⊆ D := by
    intro x hx
    have hpx : p + x ∈ K := hball (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
    exact ⟨p + x, hpx, p, interior_subset hp, by abel_nf⟩
  obtain ⟨L, hLin, hLout⟩ := symmetric_body_normalization hn hDc hDv hD0 hDneg hr hDb
  have hCp : 0 < C + 1 := by linarith
  have hscale : ∀ d ∈ D, (C + 1)⁻¹ • d ∈ K := by
    rintro d ⟨a, ha, b, hb, rfl⟩
    have hnb : -b ∈ -K := by simpa using hb
    obtain ⟨z, hz, hzb⟩ := Set.mem_smul_set.mp (hbal hnb)
    have h := hconv ha hz (inv_nonneg.mpr hCp.le)
      (div_nonneg (by linarith : 0 ≤ C) hCp.le)
      (show (C + 1)⁻¹ + C / (C + 1) = 1 by field_simp; ring)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_sub, sub_eq_add_neg, ← smul_neg, ← hzb, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  let A := (L.toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (Space n) 2 (by norm_num))).toContinuousLinearEquiv
  have hA (x : Space n) : A x = (2 : ℝ) • L x := rfl
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hn : ‖x‖ ≤ 2 / (C + 1) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hy : ((C + 1) / 2) • x ∈ Metric.closedBall (0 : Space n) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < (C + 1) / 2)]
      have := mul_le_mul_of_nonneg_left hn (show 0 ≤ (C + 1) / 2 by positivity)
      have he : (C + 1) / 2 * (2 / (C + 1)) = 1 := by field_simp
      simpa [he] using this
    obtain ⟨d, hd, he⟩ := hLin hy
    refine ⟨(C + 1)⁻¹ • d, hscale d hd, ?_⟩
    rw [hA, map_smul, he, smul_smul, smul_smul]
    have heq : 2 * ((C + 1)⁻¹ * ((C + 1) / 2)) = 1 := by field_simp
    rw [mul_assoc, heq, one_smul]
  · rintro x ⟨y, hy, rfl⟩
    have hyd : y ∈ D := ⟨y, hy, 0, h0, sub_zero _⟩
    have hn : ‖L y‖ ≤ n := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hLout ⟨y, hyd, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith

/- A dimension-only inscribed ball in the standard simplex. This allows
noncentered model fibers to be normalized without importing John's theorem. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatLogCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dirDeriv_const_mul {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (c : ℝ) (v : E) : dirDeriv v (fun y => c * f y) x = c * dirDeriv v f x := by
  simp [dirDeriv,fderiv_const_mul hf]

lemma dirDeriv_expMul {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (c : ℝ) (v : E) : dirDeriv v (fun y => Real.exp (c*f y)) x =
      Real.exp (c*f x) * c * dirDeriv v f x := by
  simp [dirDeriv,fderiv_exp (hf.const_mul c),fderiv_const_mul hf,mul_assoc]

lemma second_dirDeriv_const_mul {W : Set E} (hW : IsOpen W) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) {x : E} (hx : x ∈ W) (c : ℝ) (v w : E) :
    dirDeriv v (dirDeriv w (fun y => c*f y)) x = c * dirDeriv v (dirDeriv w f) x := by
  have he : dirDeriv w (fun y => c*f y) =ᶠ[𝓝 x] (fun y => c*dirDeriv w f y) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact dirDeriv_const_mul ((hf.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) c w
  change fderiv ℝ (dirDeriv w (fun y => c*f y)) x v = _
  rw [he.fderiv_eq]
  exact dirDeriv_const_mul ((contDiffAt_dirDeriv (hf.contDiffAt (hW.mem_nhds hx)) w).differentiableAt (by simp)) c v

lemma second_dirDeriv_expMul {W : Set E} (hW : IsOpen W) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) {x : E} (hx : x ∈ W) (c : ℝ) (v w : E) :
    dirDeriv v (dirDeriv w (fun y => Real.exp (c*f y))) x =
      Real.exp (c*f x) * (c * dirDeriv v (dirDeriv w f) x +
        c^2 * dirDeriv v f x * dirDeriv w f x) := by
  have hd := (hf.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have hdw := (contDiffAt_dirDeriv (hf.contDiffAt (hW.mem_nhds hx)) w).differentiableAt (by simp)
  have he : dirDeriv w (fun y => Real.exp (c*f y)) =ᶠ[𝓝 x]
      (fun y => Real.exp (c*f y) * (c*dirDeriv w f y)) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    simpa only [mul_assoc] using dirDeriv_expMul
      ((hf.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) c w
  change fderiv ℝ (dirDeriv w (fun y => Real.exp (c*f y))) x v = _
  rw [he.fderiv_eq]
  change dirDeriv v (fun y => Real.exp (c*f y) * (c*dirDeriv w f y)) x = _
  rw [dirDeriv_mul ((hd.const_mul c).exp) (hdw.const_mul c),dirDeriv_expMul hd,
    dirDeriv_const_mul hdw]
  ring

lemma second_dirDeriv_congr {f g : E → ℝ} {x : E} (he : f =ᶠ[𝓝 x] g) (v w : E) :
    dirDeriv v (dirDeriv w f) x = dirDeriv v (dirDeriv w g) x := by
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fun y => fderiv ℝ g y w) x v
  have hh : (fun y => fderiv ℝ f y w) =ᶠ[𝓝 x] (fun y => fderiv ℝ g y w) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun y hy => congrArg (fun l : E →L[ℝ] ℝ => l w) hy)
  exact congrArg (fun l : E →L[ℝ] ℝ => l v) hh.fderiv_eq

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricVariationAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiff_adjugate_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j) := by
  simp only [Matrix.adjugate_apply]
  change ContDiff ℝ ∞ (continuousDetRows ∘ fun A : ι → ι → ℝ =>
    fun l m => Matrix.updateRow (Matrix.of A) j (Pi.single i 1) l m)
  apply (continuousDetRows (ι := ι)).contDiff.comp
  apply contDiff_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hl, Matrix.of_apply]
    fun_prop

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricGraphJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- The actual first derivative of the horizontal component, in graph coordinates. -/

lemma third_dirDeriv_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : E} (hx : x ∈ Ω) (v w z : E) :
    dirDeriv v (dirDeriv w (dirDeriv z u)) x =
      dirDeriv z (dirDeriv v (dirDeriv w u)) x := by
  have he : dirDeriv w (dirDeriv z u) =ᶠ[nhds x] dirDeriv z (dirDeriv w u) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_comm (hu.contDiffAt (hΩ.mem_nhds hy)) w z
  calc
    _ = dirDeriv v (dirDeriv z (dirDeriv w u)) x :=
      congrArg (fun L : E →L[ℝ] ℝ => L v) he.fderiv_eq
    _ = _ := dirDeriv_comm (contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) w) v z

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricSmoothness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma contDiffAt_inverse_matrix_entry_param {P ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι] [DecidableEq ι]
    {A : P → Matrix ι ι ℝ} {p : P}
    (hA : ContDiffAt ℝ ∞ (fun q i j => A q i j) p) (hd : (A p).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ ∞ (fun q => (A q)⁻¹ i j) p := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp p hA).inv hd).mul
    ((contDiff_adjugate_entry i j).contDiffAt.comp p hA)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatFCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma log_second_identity {W : Set E} (hW : IsOpen W) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ W) (hpos : ∀ y ∈ W, 0 < φ y)
    {x : E} (hx : x ∈ W) (v w : E) :
    dirDeriv v (dirDeriv w φ) x = φ x *
      (dirDeriv v (dirDeriv w (fun y => Real.log (φ y))) x +
        dirDeriv v (fun y => Real.log (φ y)) x * dirDeriv w (fun y => Real.log (φ y)) x) := by
  have hp : ContDiffOn ℝ ∞ (fun y => Real.log (φ y)) W :=
    hφ.log (fun y hy => ne_of_gt (hpos y hy))
  have he : (fun y => Real.exp (Real.log (φ y))) =ᶠ[𝓝 x] φ := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact Real.exp_log (hpos y hy)
  rw [← second_dirDeriv_congr he]
  have hh := second_dirDeriv_expMul hW hp hx 1 v w
  simpa only [one_mul,one_pow,Real.exp_log (hpos x hx)] using hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformSphericalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open intervalIntegral
open scoped Pointwise

open Filter
open scoped Topology
/- Every admissible graph path has at least the Euclidean length of its
base displacement. This uses the literal C¹-path definition of completeness. -/
theorem enorm_sub_le_graphEDist {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (x y : Space n) : ‖y - x‖ₑ ≤ graphEDist Ω u x y := by
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  apply le_iInf
  intro hγΩ
  apply le_iInf
  intro hγ0
  apply le_iInf
  intro hγ1
  have hl := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hγ (show (0 : ℝ) ≤ 1 by norm_num)
  rw [hγ1, hγ0] at hl
  apply hl.trans
  apply lintegral_mono
  intro t
  dsimp only
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (le_add_of_nonneg_right (sq_nonneg _))

/- A straight base segment has constant velocity, including its endpoints
for the closed-interval derivative used in the metric. -/
theorem derivWithin_baseSegment {n : ℕ} (x v : Space n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (fun s : ℝ => x + s • v) (Icc (0 : ℝ) 1) t = v := by
  have hd := ((hasDerivAt_id t).smul_const v).const_add x
  simpa using hd.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num) t ht)

/- Length estimate on a segment on which the graph height is nondecreasing. -/
theorem graphEDist_le_of_segment_deriv_nonneg {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ fderiv ℝ u (x + t • (y - x)) (y - x)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + (u y - u x)) := by
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hdu (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (u ∘ γ) (d t) t :=
    ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)
  have hd : ContinuousOn d (Icc (0 : ℝ) 1) := by
    intro t ht
    have hc : ContinuousAt (fderiv ℝ u) (γ t) :=
      ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).fderiv_right
        (m := ∞) (by simp)).continuousAt
    have hc' : ContinuousAt (fun t => fderiv ℝ u (γ t)) t :=
      hc.comp hγ.continuous.continuousAt
    exact (hc'.clm_apply continuousAt_const).continuousWithinAt
  have hid : IntegrableOn d (Icc (0 : ℝ) 1) := hd.integrableOn_Icc
  have hic : IntegrableOn (fun _ : ℝ => ‖y - x‖) (Icc (0 : ℝ) 1) :=
    continuousOn_const.integrableOn_Icc
  have hi : IntegrableOn (fun t => ‖y - x‖ + d t) (Icc (0 : ℝ) 1) :=
    hic.add hid
  have hftc : ∫ t in Icc (0 : ℝ) 1, d t = u y - u x := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hdu t (by simpa using ht))
      ((by simpa using hd : ContinuousOn d (uIcc (0 : ℝ) 1)).intervalIntegrable)
    simpa [γ, Function.comp_def] using he
  have hl : graphPathLength u γ ≤ ENNReal.ofReal (‖y - x‖ + (u y - u x)) := by
    unfold graphPathLength
    calc
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (‖y - x‖ + d t) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [show derivWithin γ (Icc (0 : ℝ) 1) t = y - x from derivWithin_baseSegment x (y - x) ht]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [d, γ]
        apply Real.sqrt_le_iff.mpr
        constructor
        · exact add_nonneg (norm_nonneg _) (hp t ht)
        · nlinarith [norm_nonneg (y - x), hp t ht]
      _ = ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, (‖y - x‖ + d t)) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal hi
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact add_nonneg (norm_nonneg _) (hp t ht)
      _ = _ := by
        rw [integral_add hic hid,
          setIntegral_const, hftc]
        simp
  have hdist : graphEDist Ω u x y ≤ graphPathLength u γ := by
    unfold graphEDist
    exact iInf_le_of_le γ (iInf_le_of_le (hγ.of_le (by simp)).contDiffOn
      (iInf_le_of_le hseg (iInf_le_of_le (by simp [γ])
        (iInf_le_of_le (by simp [γ]) le_rfl))))
  exact hdist.trans hl

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem graphEDist_le_segment_monotone {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (x + t • (y - x))) (Icc (0 : ℝ) 1)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + |u y - u x|) := by
  apply (graphEDist_le_of_segment_deriv_nonneg hΩ hu x y hseg ?_).trans
  · exact ENNReal.ofReal_le_ofReal (add_le_add_right (le_abs_self _) _)
  · intro t ht
    have hd : HasDerivAt (fun t : ℝ => u (x + t • (y - x)))
        (fderiv ℝ u (x + t • (y - x)) (y - x)) t := by
      have hγ : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
        simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
      exact ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hγ
    rw [← hd.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) t ht)]
    exact hm.derivWithin_nonneg

theorem graphEDist_le_segment_antitone {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hm : AntitoneOn (fun t : ℝ => u (x + t • (y - x))) (Icc (0 : ℝ) 1)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + |u y - u x|) := by
  have he := graphEDist_le_segment_monotone hΩ hu.neg x y hseg hm.neg
  change graphEDist Ω (-u) x y ≤ ENNReal.ofReal
    (‖y - x‖ + |(-u) y - (-u) x|) at he
  simpa only [graphEDist_neg, Pi.neg_apply, neg_sub_neg, abs_sub_comm] using he

open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
theorem tendsto_of_graphEDist {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {x : ℕ → Space n} {a : Space n}
    (ha : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N,
      graphEDist Ω u (x i) a < ENNReal.ofReal ε) :
    Tendsto x atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, fun i hi => ?_⟩
  have h := (enorm_sub_le_graphEDist Ω u (x i) a).trans_lt (hN i hi)
  rw [← ofReal_norm] at h
  have h' := (ENNReal.ofReal_lt_ofReal_iff hε).mp h
  simpa [dist_eq_norm, norm_sub_rev] using h'

/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
theorem mem_of_complete_graph_cauchy {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : EuclideanGraphComplete Ω u) {x : ℕ → Space n} {a : Space n}
    (hx : ∀ i, x i ∈ Ω) (ha : Tendsto x atTop (𝓝 a))
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε) : a ∈ Ω := by
  obtain ⟨b, hb, hxb⟩ := hc x hx hC
  exact (tendsto_nhds_unique ha (tendsto_of_graphEDist hxb)) ▸ hb

/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
theorem graph_cauchy_of_segment_bound {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {x : ℕ → Space n} (hx : CauchySeq x) (hu : CauchySeq (u ∘ x))
    (hbound : ∀ i j, graphEDist Ω u (x i) (x j) ≤
      ENNReal.ofReal (‖x j - x i‖ + |u (x j) - u (x i)|)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hx (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨max N M, fun i hi j hj => (hbound i j).trans_lt ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  have hx' : ‖x j - x i‖ < ε / 2 := by
    simpa [dist_eq_norm] using hN j (le_trans (le_max_left _ _) hj) i
      (le_trans (le_max_left _ _) hi)
  have hu' : |u (x j) - u (x i)| < ε / 2 := by
    simpa [Function.comp_def, Real.dist_eq] using hM j
      (le_trans (le_max_right _ _) hj) i (le_trans (le_max_right _ _) hi)
  linarith

/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
theorem graphEDist_le_on_monotone_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (a v : Space n) (q : ℝ)
    (hseg : ∀ t ∈ Ico q 1, a + t • v ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (a + t • v)) (Ico q 1) ∨
      AntitoneOn (fun t : ℝ => u (a + t • v)) (Ico q 1))
    {s r : ℝ} (hs : s ∈ Ico q 1) (hr : r ∈ Ico q 1) :
    graphEDist Ω u (a + s • v) (a + r • v) ≤
      ENNReal.ofReal (‖(a + r • v) - (a + s • v)‖ +
        |u (a + r • v) - u (a + s • v)|) := by
  have heq (t : ℝ) : (a + s • v) + t • ((a + r • v) - (a + s • v)) =
      a + (s + t * (r - s)) • v := by module
  have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : s + t * (r - s) ∈ Ico q 1 := by
    simpa [smul_eq_mul] using (convex_Ico q (1 : ℝ)).add_smul_mem hs
      (by simpa using hr) ht
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (a + s • v) + t • ((a + r • v) - (a + s • v)) ∈ Ω := by
    rw [heq]
    exact hseg _ (hmap t ht)
  rcases hm with hm | hm
  · by_cases hsr : s ≤ r
    · apply graphEDist_le_segment_monotone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap t ht) (hmap w hw)
      nlinarith
    · apply graphEDist_le_segment_antitone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap w hw) (hmap t ht)
      nlinarith
  · by_cases hsr : s ≤ r
    · apply graphEDist_le_segment_antitone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap t ht) (hmap w hw)
      nlinarith
    · apply graphEDist_le_segment_monotone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap w hw) (hmap t ht)
      nlinarith

/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
theorem endpoint_mem_of_bounded_monotone_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hc : EuclideanGraphComplete Ω u) (a b : Space n) {q : ℝ} (hq : q < 1)
    (hseg : ∀ t ∈ Ico q 1, a + t • (b - a) ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (a + t • (b - a))) (Ico q 1) ∨
      AntitoneOn (fun t : ℝ => u (a + t • (b - a))) (Ico q 1))
    (hbdd : ∃ C : ℝ, ∀ t ∈ Ico q 1, |u (a + t • (b - a))| ≤ C) : b ∈ Ω := by
  obtain ⟨t, htm, htmem, htlim⟩ := exists_seq_strictMono_tendsto' hq
  have ht (i : ℕ) : t i ∈ Ico q 1 := ⟨(htmem i).1.le, (htmem i).2⟩
  let x : ℕ → Space n := fun i => a + t i • (b - a)
  have hx (i : ℕ) : x i ∈ Ω := hseg _ (ht i)
  have hxlim : Tendsto x atTop (𝓝 b) := by
    have he := (tendsto_const_nhds (x := a)).add (htlim.smul_const (b - a))
    simpa [x] using he
  obtain ⟨C, hC⟩ := hbdd
  have hxheight : CauchySeq (u ∘ x) := by
    rcases hm with hm | hm
    · have hmono : Monotone (u ∘ x) := fun i j hij => hm (ht i) (ht j) (htm.monotone hij)
      have hbounded : BddAbove (range (u ∘ x)) := by
        refine ⟨C, ?_⟩
        rintro v ⟨i, rfl⟩
        exact (le_abs_self _).trans (hC _ (ht i))
      exact (tendsto_atTop_ciSup hmono hbounded).cauchySeq
    · have hanti : Antitone (u ∘ x) := fun i j hij => hm (ht i) (ht j) (htm.monotone hij)
      have hbounded : BddBelow (range (u ∘ x)) := by
        refine ⟨-C, ?_⟩
        rintro v ⟨i, rfl⟩
        exact (neg_le_neg (hC _ (ht i))).trans (neg_abs_le _)
      exact (tendsto_atTop_ciInf hanti hbounded).cauchySeq
  apply mem_of_complete_graph_cauchy hc hx hxlim
  apply graph_cauchy_of_segment_bound hxlim.cauchySeq hxheight
  intro i j
  exact graphEDist_le_on_monotone_ray hΩ hu a (b - a) q hseg hm (ht i) (ht j)

/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
theorem convexOn_monotone_tail {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ico (0 : ℝ) 1) f)
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ f t) :
    ∃ q ∈ Ico (0 : ℝ) 1, MonotoneOn f (Ico q 1) ∨ AntitoneOn f (Ico q 1) := by
  by_cases hex : ∃ q ∈ Ico (0 : ℝ) 1, 0 ≤ deriv f q
  · obtain ⟨q, hq, hqp⟩ := hex
    refine ⟨q, hq, Or.inl ?_⟩
    have hsub : Ico q 1 ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨hq.1.trans ht.1, ht.2⟩
    apply monotoneOn_of_deriv_nonneg (convex_Ico _ _)
      (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (hsub (interior_subset ht))).differentiableWithinAt)
    intro t ht
    exact hqp.trans (hf.monotoneOn_deriv hd hq (hsub (interior_subset ht))
      (interior_subset ht).1)
  · refine ⟨0, by norm_num, Or.inr ?_⟩
    apply antitoneOn_of_deriv_nonpos (convex_Ico _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableWithinAt)
    intro t ht
    exact le_of_lt (lt_of_not_ge (fun h => hex ⟨t, interior_subset ht, h⟩))

/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
theorem convexOn_bounded_ray {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ico (0 : ℝ) 1) f)
    (hd : DifferentiableAt ℝ f 0) {A : ℝ} (hA : ∀ t ∈ Ico (0 : ℝ) 1, f t ≤ A) :
    ∃ C : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, |f t| ≤ C := by
  refine ⟨|A| + |f 0| + |deriv f 0|, ?_⟩
  intro t ht
  have hs : f 0 + t * deriv f 0 ≤ f t := by
    rcases eq_or_lt_of_le ht.1 with he | he
    · subst t
      simp
    · have h := hf.le_slope_of_hasDerivAt (by norm_num) ht he hd.hasDerivAt
      simp only [slope_def_field, sub_zero] at h
      have h' := (le_div_iff₀ he).mp h
      linarith
  have hp : -|deriv f 0| ≤ t * deriv f 0 := by
    calc
      _ ≤ t * (-|deriv f 0|) := by nlinarith [abs_nonneg (deriv f 0), ht.2]
      _ ≤ _ := mul_le_mul_of_nonneg_left (neg_abs_le _) ht.1
  apply abs_le.mpr
  constructor
  · have h0 := neg_abs_le (f 0)
    have hAA := abs_nonneg A
    linarith
  · exact (hA t ht).trans (by linarith [le_abs_self A, abs_nonneg (f 0), abs_nonneg (deriv f 0)])

/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
theorem endpoint_mem_of_bounded_convex_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hcv : ConvexOn ℝ Ω u) (hc : EuclideanGraphComplete Ω u) (a b : Space n)
    (hseg : ∀ t ∈ Ico (0 : ℝ) 1, a + t • (b - a) ∈ Ω)
    (hbounded : ∃ A : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, u (a + t • (b - a)) ≤ A) : b ∈ Ω := by
  let f : ℝ → ℝ := fun t => u (a + t • (b - a))
  have hfc : ConvexOn ℝ (Ico (0 : ℝ) 1) f := by
    have hh := (hcv.comp_affineMap (AffineMap.lineMap a b)).subset
      (s := Ico (0 : ℝ) 1) (fun t ht => ?_) (convex_Ico _ _)
    · simpa [f, Function.comp_def, AffineMap.lineMap_apply, add_comm] using hh
    · simpa [AffineMap.lineMap_apply, add_comm] using hseg t ht
  have hfd (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : DifferentiableAt ℝ f t := by
    have hγ : HasDerivAt (fun t : ℝ => a + t • (b - a)) (b - a) t := by
      simpa using ((hasDerivAt_id t).smul_const (b - a)).const_add a
    exact (((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hγ).differentiableAt
  obtain ⟨A, hA⟩ := hbounded
  obtain ⟨C, hC⟩ := convexOn_bounded_ray hfc (hfd 0 (by norm_num)) hA
  obtain ⟨q, hq, hm⟩ := convexOn_monotone_tail hfc hfd
  have hsub : Ico q 1 ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨hq.1.trans ht.1, ht.2⟩
  exact endpoint_mem_of_bounded_monotone_ray hΩ hu hc a b hq.2
    (fun t ht => hseg t (hsub ht)) hm ⟨C, fun t ht => hC t (hsub ht)⟩

/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
theorem mem_of_bounded_graph_sequence {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hcv : ConvexOn ℝ Ω u) (hc : EuclideanGraphComplete Ω u)
    {a : Space n} (ha : a ∈ Ω) {x : ℕ → Space n} {b : Space n}
    (hx : ∀ i, x i ∈ Ω) (hlim : Tendsto x atTop (𝓝 b))
    {A : ℝ} (hA : ∀ i, u (x i) ≤ A) : b ∈ Ω := by
  have hb : b ∈ closure Ω := mem_closure_iff_seq_limit.mpr ⟨x, hx, hlim⟩
  have hseg (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : a + t • (b - a) ∈ Ω := by
    have hh := hcv.1.combo_interior_closure_mem_interior
      (show a ∈ interior Ω by simpa [hΩ.interior_eq] using ha) hb
      (sub_pos.mpr ht.2) ht.1 (show (1 - t) + t = 1 by ring)
    have he : (1 - t) • a + t • b = a + t • (b - a) := by module
    rw [he, hΩ.interior_eq] at hh
    exact hh
  apply endpoint_mem_of_bounded_convex_ray hΩ hu hcv hc a b hseg
  refine ⟨max (u a) A, ?_⟩
  intro t ht
  have hzlim : Tendsto (fun i => a + t • (x i - a)) atTop
      (𝓝 (a + t • (b - a))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.smul (hlim.sub tendsto_const_nhds))
  have hulim := (hu.continuousOn.continuousAt (hΩ.mem_nhds (hseg t ht))).tendsto.comp hzlim
  apply le_of_tendsto' hulim
  intro i
  have hv := hcv.2 ha (hx i) (sub_nonneg.mpr ht.2.le) ht.1
    (show (1 - t) + t = 1 by ring)
  have he : (1 - t) • a + t • x i = a + t • (x i - a) := by module
  rw [he] at hv
  calc
    _ ≤ (1 - t) * u a + t * u (x i) := hv
    _ ≤ (1 - t) * max (u a) A + t * max (u a) A :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht.2.le))
        (mul_le_mul_of_nonneg_left ((hA i).trans (le_max_right _ _)) ht.1)
    _ = _ := by ring

/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
theorem isClosed_epigraph_of_complete {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hcv : ConvexOn ℝ Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    IsClosed {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2} := by
  apply isClosed_of_closure_subset
  intro p hp
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp hp
  obtain ⟨a, ha⟩ := hne
  obtain ⟨A, hA⟩ := hlim.snd_nhds.bddAbove_range
  have hpΩ : p.1 ∈ Ω := mem_of_bounded_graph_sequence hΩ hu hcv hc ha
    (fun i => (hz i).1) hlim.fst_nhds (fun i => (hz i).2.trans (hA (mem_range_self i)))
  refine ⟨hpΩ, ?_⟩
  apply le_of_tendsto_of_tendsto
    ((hu.continuousOn.continuousAt (hΩ.mem_nhds hpΩ)).tendsto.comp hlim.fst_nhds) hlim.snd_nhds
  exact Eventually.of_forall fun i => (hz i).2

-- END

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelCenteringFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
/- Finite boundary blow-up, derived from the manuscript's literal Euclidean
intrinsic completeness assumption. -/
/- The epigraph is genuinely closed in Rⁿ × R. Completeness was not
silently replaced by properness of the graph embedding. -/
/- Strict version of the second-derivative test, with specified derivatives. -/
theorem strictConvexOn_of_hasDerivWithinAt2_pos {D : Set ℝ} (hD : Convex ℝ D)
    {f f' f'' : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, 0 < f'' x) : StrictConvexOn ℝ D f := by
  have he : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine strictConvexOn_of_deriv2_pos hD hf fun x hx => ?_
  convert hf''₀ x hx using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  rw [deriv_eqOn isOpen_interior (fun y hy => ?_) hx]
  exact (hf'' _ hy).congr he (by rw [he hy])

/- The standing Hessian hypothesis gives strict convexity on every nonconstant
base segment, with the literal coordinate Hessian, not an abstract Hessian. -/
theorem strictConvexOn_segment {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {x y : Space n} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : y ≠ x) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => u (x + t • (y - x))) := by
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  exact strictConvexOn_of_hasDerivWithinAt2_pos (convex_Icc _ _) hf hdf hdd
    (fun t ht => second_fderiv_pos
      (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
      (hp _ (hseg t (interior_subset ht))) (sub_ne_zero.mpr hxy))

/- The tangent-plane height used in all source sections. -/

theorem tangentHeight_pos {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) (hxa : x ≠ a) :
    0 < tangentHeight u a x := by
  have hc := strictConvexOn_segment hΩ hcv hu hp ha hx hxa
  have hd : HasDerivAt (fun t : ℝ => u (a + t • (x - a)))
      (fderiv ℝ u a (x - a)) 0 := by
    have hγ : HasDerivAt (fun t : ℝ => a + t • (x - a)) (x - a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x - a)).const_add a
    have hdu : HasFDerivAt u (fderiv ℝ u a) (a + (0 : ℝ) • (x - a)) := by
      simpa using ((hu.contDiffAt (hΩ.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt
    exact hdu.comp_hasDerivAt 0 hγ
  have hs := hc.lt_slope_of_hasDerivAt (x := 0) (y := 1)
    (by norm_num) (by norm_num) (by norm_num) hd
  simp only [slope_def_field, sub_zero, div_one, zero_smul, add_zero, one_smul,
    add_sub_cancel] at hs
  exact sub_pos.mpr hs

theorem convexOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hcv : ConvexOn ℝ Ω u) (a : Space n) :
    ConvexOn ℝ Ω (tangentHeight u a) := by
  refine ⟨hcv.1, ?_⟩
  intro x hx y hy s t hs ht hst
  have he := hcv.2 hx hy hs ht hst
  have hv : s • x + t • y - a = s • (x - a) + t • (y - a) := by
    rw [smul_sub, smul_sub]
    have heq : s • a + t • a = a := by rw [← add_smul, hst, one_smul]
    calc
      _ = s • x + t • y - (s • a + t • a) := by rw [heq]
      _ = _ := by module
  simp only [tangentHeight, hv, map_add, map_smul, smul_eq_mul]
  simp only [smul_eq_mul] at he
  have heq : s * u a + t * u a = u a := by rw [← add_mul, hst, one_mul]
  nlinarith

theorem continuousOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) (a : Space n) :
    ContinuousOn (tangentHeight u a) Ω := by
  exact (hu.sub continuousOn_const).sub
    ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const)).continuousOn

/- Tangent-plane sublevels are closed, by closedness of the actual epigraph.
No implicit completeness-invariance under a shear is needed. -/
theorem isClosed_tangent_sublevel {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hcv : ConvexOn ℝ Ω u)
    (hc : EuclideanGraphComplete Ω u) (a : Space n) (t : ℝ) :
    IsClosed {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have he := isClosed_epigraph_of_complete hΩ hne hu hcv hc
  have hf : Continuous (fun x : Space n => (x, u a + fderiv ℝ u a (x - a) + t)) :=
    continuous_id.prodMk ((continuous_const.add
      ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const))).add continuous_const)
  convert he.preimage hf using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq, mem_preimage, tangentHeight]
  constructor <;> rintro ⟨hx, hh⟩ <;> exact ⟨hx, by linarith⟩

/- A finite-radius positive support gap yields a linear coercivity bound.
This replaces only the choice of constants in geometry.tex:56–67, not any
standing hypothesis or conclusion. -/
theorem tangentHeight_coercive {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a : Space n} (ha : a ∈ Ω) :
    ∃ r > 0, ∃ m > 0, ∀ x ∈ Ω, r ≤ ‖x - a‖ →
      m * ‖x - a‖ ≤ r * tangentHeight u a x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds ha)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrΩ : Metric.closedBall a r ⊆ Ω :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hRΩ
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcg := convexOn_tangentHeight hcu a
  have hct := continuousOn_tangentHeight hu.continuousOn a
  have hsΩ : Metric.sphere a r ⊆ Ω := Metric.sphere_subset_closedBall.trans hrΩ
  obtain ⟨m, hm, hmlow⟩ : ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ Metric.sphere a r, m ≤ tangentHeight u a x := by
    by_cases hne : (Metric.sphere a r).Nonempty
    · obtain ⟨y, hy, hmin⟩ := (isCompact_sphere a r).exists_isMinOn hne (hct.mono hsΩ)
      refine ⟨tangentHeight u a y, tangentHeight_pos hΩ hcv hu hp ha (hsΩ hy) ?_, hmin⟩
      intro he
      subst y
      have hh : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hy
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  refine ⟨r, hr, m, hm, ?_⟩
  intro x hx hxr
  have hn : 0 < ‖x - a‖ := hr.trans_le hxr
  let q := r / ‖x - a‖
  have hq : 0 < q := div_pos hr hn
  have hq1 : q ≤ 1 := (div_le_one hn).mpr hxr
  let y := a + q • (x - a)
  have hyn : ‖y - a‖ = r := by
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    exact div_mul_cancel₀ r hn.ne'
  have hys : y ∈ Metric.sphere a r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hyn
  have hv : (1 - q) • a + q • x = y := by dsimp [y]; module
  have hineq := hcg.2 ha hx (sub_nonneg.mpr hq1) hq.le (show (1 - q) + q = 1 by ring)
  rw [hv, tangentHeight_self] at hineq
  simp only [smul_eq_mul, mul_zero, zero_add] at hineq
  have hmm : m ≤ r / ‖x - a‖ * tangentHeight u a x := (hmlow y hys).trans hineq
  have heq : r / ‖x - a‖ * tangentHeight u a x =
      (r * tangentHeight u a x) / ‖x - a‖ := by ring
  rw [heq] at hmm
  exact (le_div_iff₀ hn).mp hmm

/- The compact tangent sections required throughout the manuscript, proved
from PD Hessian, convexity of the open base, and intrinsic graph completeness. -/
theorem isCompact_tangent_sublevel {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) (t : ℝ) :
    IsCompact {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hclosed := isClosed_tangent_sublevel hΩ ⟨a, ha⟩ hu hcu hc a t
  obtain ⟨r, hr, m, hm, hbound⟩ := tangentHeight_coercive hΩ hcv hu hp ha
  apply (isCompact_closedBall a (max r (r * t / m))).of_isClosed_subset hclosed
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_cases hxr : r ≤ ‖x - a‖
  · apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hm).mpr
    have hb := (hbound x hx.1 hxr).trans (mul_le_mul_of_nonneg_left hx.2 hr.le)
    simpa [mul_comm] using hb
  · exact (le_of_not_ge hxr).trans (le_max_left _ _)

theorem tangentHeight_nonneg {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    0 ≤ tangentHeight u a x := by
  by_cases hxa : x = a
  · simp [hxa]
  · exact (tangentHeight_pos hΩ hcv hu hp ha hx hxa).le

/- Interior of the epigraph, including the correct restriction to the open
base domain. This is a local continuity fact and needs no completeness. -/
theorem closure_tangentSection {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω)
    {t : ℝ} (ht : 0 < t) :
    closure (tangentSection Ω u a t) = {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcg := convexOn_tangentHeight hcu a
  apply le_antisymm
  · refine closure_minimal ?_ (isClosed_tangent_sublevel hΩ ⟨a, ha⟩ hu hcu hc a t)
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  · intro x hx
    obtain ⟨q, hqm, hqmem, hqlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun i => a + q i • (x - a), ?_, ?_⟩
    · intro i
      have hqi : q i ∈ Ioo (0 : ℝ) 1 := hqmem i
      refine ⟨hcv.add_smul_mem ha (by simpa using hx.1) ⟨hqi.1.le, hqi.2.le⟩, ?_⟩
      have hv : (1 - q i) • a + q i • x = a + q i • (x - a) := by module
      have he := hcg.2 ha hx.1 (sub_nonneg.mpr hqi.2.le) hqi.1.le
        (show (1 - q i) + q i = 1 by ring)
      rw [hv, tangentHeight_self] at he
      simp only [smul_eq_mul, mul_zero, zero_add] at he
      exact lt_of_le_of_lt (he.trans (mul_le_mul_of_nonneg_left hx.2 hqi.1.le))
        (by nlinarith [ht, hqi.2])
    · have hh := (tendsto_const_nhds (x := a)).add (hqlim.smul_const (x - a))
      simpa using hh

/- Source equation uniform-section-balance, in unshifted coordinates;
equivalently, -ρ(closure S-a) ⊆ closure S-a. -/
theorem sectionBalance_reflection {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {ρ : ℝ} (hbal : SectionBalance Ω u ρ)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    a - ρ • (x - a) ∈ Ω ∧
    tangentHeight u a (a - ρ • (x - a)) ≤ tangentHeight u a x := by
  by_cases hxa : x = a
  · simp only [hxa, sub_self, smul_zero, sub_zero, le_refl, and_true]
    exact ha
  · have ht := tangentHeight_pos hΩ hcv hu hp ha hx hxa
    have he := hbal a ha _ ht x (by
      rw [closure_tangentSection hΩ hcv hu hp hc ha ht]
      exact ⟨hx, le_rfl⟩)
    rwa [closure_tangentSection hΩ hcv hu hp hc ha ht] at he

/- An open set containing a point and invariant under one dilation about it
of factor greater than one is the whole vector space. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EntireAndDoubling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology

/-- The differential of the log determinant is the literal inverse-Hessian
contraction of the differentiated Hessian. -/
lemma dirDeriv_logHessianDet {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (v : Space n) :
    dirDeriv v (logHessianDet u) x =
      ∑ i, ∑ j, (hessian u x)⁻¹ i j * dirDeriv v (fun y => hessian u y i j) x := by
  have hd := ((contDiffAt_det_hessian hu).differentiableAt (by simp)).hasFDerivAt
  have hr := hd.log (ne_of_gt hp.det_pos)
  have he : dirDeriv v (logHessianDet u) x =
      (hessian u x).det⁻¹ * dirDeriv v (fun y => (hessian u y).det) x := by
    unfold dirDeriv logHessianDet
    rw [hr.fderiv]
    simp only [smul_apply, smul_eq_mul]
  rw [he, dirDeriv_det (hessian u)
    (fun i j => (contDiffAt_hessian_entry hu i j).differentiableAt (by simp))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hc : (hessian u x).adjugate j i = (hessian u x).det * (hessian u x)⁻¹ i j := by
    rw [← cofactorHessian_eq_adjugate u x (ne_of_gt hp.det_pos)]
    rw [(cofactorHessian_isSymm u x hp).apply i j]
    rfl
  rw [hc]
  field_simp [ne_of_gt hp.det_pos]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogBarrierCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogBarrierCalculus
open Filter
open scoped Topology

lemma dirDeriv_real_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hne : f x ≠ 0) (v : E) :
    dirDeriv v (fun y => Real.log (f y)) x = dirDeriv v f x / f x := by
  unfold dirDeriv
  rw [(hf.hasFDerivAt.log hne).fderiv]
  simp only [smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

end LogBarrierCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveMatrixTraceBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section PositiveMatrixTraceBound
open scoped MatrixOrder

lemma posSemidef_quadratic_le_trace_mul_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (p : ι → ℝ) :
    p ⬝ᵥ A.mulVec p ≤ A.trace * ∑ i, (p i)^2 := by
  let S := CFC.sqrt A
  have hS : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp
    (show S.IsHermitian from (CFC.sqrt_nonneg A).isSelfAdjoint)
  have hSS : S*S = A := by
    simpa only [pow_two] using CFC.sq_sqrt A hA.nonneg
  have hvec : Matrix.vecMul p S = Matrix.mulVec S p := by
    rw [← Matrix.mulVec_transpose,hS.eq]
  have hm : p ⬝ᵥ A.mulVec p = ∑ i, (S.mulVec p i)^2 := by
    rw [← hSS, ← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,hvec]
    simp only [dotProduct,pow_two]
  have ht : A.trace = ∑ i, ∑ j, (S i j)^2 := by
    rw [← hSS]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hS.apply i j]
    ring
  rw [hm,ht,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [Matrix.mulVec, dotProduct] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => S i j) p

end PositiveMatrixTraceBound

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TangentShiftCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section TangentShiftCalculus
open Filter
open scoped Topology

lemma affineMaximalOn_add_affine {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hm : AffineMaximalOn Ω f)
    (L : Space n →L[ℝ] ℝ) (c : ℝ) : AffineMaximalOn Ω (graphAffineFunction f L 1 c) := by
  have he (x : Space n) (hx : x ∈ Ω) : hessian (graphAffineFunction f L 1 c) x = hessian f x := by
    ext i j
    simpa only [one_mul] using hessian_graphAffineFunction hΩ hf hx L 1 c i j
  intro x hx
  have hw : affineWeight (graphAffineFunction f L 1 c) =ᶠ[𝓝 x] affineWeight f := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    simp only [affineWeight,he y hy]
  rw [show cofactorHessian (graphAffineFunction f L 1 c) x = cofactorHessian f x by
    simp only [cofactorHessian,he x hx],hessian_congr_nhds hw]
  exact hm x hx

lemma tangentShift_eq_graphAffineFunction {n : ℕ} (f : Space n → ℝ) (a : Space n) (h : ℝ) :
    tangentShift f a h = graphAffineFunction f (-fderiv ℝ f a) 1
      (-f a + fderiv ℝ f a a - h) := by
  funext x
  simp only [tangentShift,tangentHeight,graphAffineFunction,neg_apply,map_sub,one_mul]
  ring

lemma contDiffOn_tangentShift {n : ℕ} {Ω : Set (Space n)} {f : Space n → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (a : Space n) (h : ℝ) :
    ContDiffOn ℝ ∞ (tangentShift f a h) Ω := by
  exact ((hf.sub contDiffOn_const).sub
    ((fderiv ℝ f a).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn).sub contDiffOn_const

lemma hessian_tangentShift {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (a : Space n) (h : ℝ)
    {x : Space n} (hx : x ∈ Ω) : hessian (tangentShift f a h) x = hessian f x := by
  rw [tangentShift_eq_graphAffineFunction]
  ext i j
  simpa only [one_mul] using hessian_graphAffineFunction hΩ hf hx (-fderiv ℝ f a) 1
    (-f a + fderiv ℝ f a a - h) i j

lemma affineMaximalOn_tangentShift {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hm : AffineMaximalOn Ω f) (a : Space n) (h : ℝ) :
    AffineMaximalOn Ω (tangentShift f a h) := by
  rw [tangentShift_eq_graphAffineFunction]
  exact affineMaximalOn_add_affine hΩ hf hm _ _

lemma fderiv_tangentShift {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : DifferentiableAt ℝ f x) (a : Space n) (h : ℝ) :
    fderiv ℝ (tangentShift f a h) x = fderiv ℝ f x - fderiv ℝ f a := by
  change fderiv ℝ (fun y => f y - f a - fderiv ℝ f a (y-a) - h) x = _
  have hh := ((hf.hasFDerivAt.sub_const (f a)).sub
    ((fderiv ℝ f a).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a))).sub_const h
  simpa only [tangentShift,tangentHeight,Pi.sub_apply,Function.comp_apply,id_eq,
    ContinuousLinearMap.comp_id] using hh.fderiv

lemma norm_fderiv_le_of_convex_bounded {n : ℕ} {Ω : Set (Space n)} {f : Space n → ℝ}
    (hc : ConvexOn ℝ Ω f) {x : Space n} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ f x)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : Metric.closedBall x r ⊆ Ω) (hb : ∀ y ∈ Ω, |f y| ≤ M) :
    ‖fderiv ℝ f x‖ ≤ 2*M/r := by
  have hh := norm_gradient_le_of_convex_bounded hc hx hd hr hM hball hb
  simpa only [gradient,LinearIsometryEquiv.norm_map] using hh

end TangentShiftCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EntireGraphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EntireGraphComplete
open Filter
open scoped Topology

lemma graphEDist_le_segment_fderiv_bound {n : ℕ} {O : Set (Space n)}
    (f : Space n → ℝ) (x y : Space n) {M : ℝ} (hM : 0 ≤ M)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x+t • (y-x) ∈ O)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ f (x+t • (y-x))‖ ≤ M) :
    graphEDist O f x y ≤ ENNReal.ofReal ((1+M)*‖y-x‖) := by
  let γ : ℝ → Space n := fun t => x+t • (y-x)
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hp : graphPathLength f γ ≤ ENNReal.ofReal ((1+M)*‖y-x‖) := by
    unfold graphPathLength
    calc
      _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ENNReal.ofReal ((1+M)*‖y-x‖) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [show derivWithin γ (Icc (0:ℝ) 1) t = y-x from derivWithin_baseSegment x (y-x) ht]
        apply ENNReal.ofReal_le_ofReal
        have H := (fderiv ℝ f (γ t)).le_opNorm (y-x)
        have H' : |fderiv ℝ f (γ t) (y-x)| ≤ M*‖y-x‖ := by
          simpa only [Real.norm_eq_abs] using H.trans (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _))
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity,?_⟩
        have Hsq := sq_le_sq₀ (abs_nonneg _) (mul_nonneg hM (norm_nonneg _)) |>.mpr H'
        rw [sq_abs] at Hsq
        nlinarith [mul_nonneg hM (sq_nonneg ‖y-x‖)]
      _ = _ := by simp
  apply le_trans _ hp
  unfold graphEDist
  exact iInf_le_of_le γ (iInf_le_of_le (hγ.of_le (by simp)).contDiffOn
    (iInf_le_of_le hseg (iInf_le_of_le (by simp [γ])
      (iInf_le_of_le (by simp [γ]) le_rfl))))

/-- An entire C∞ graph is complete for the literal induced Euclidean path
metric, not merely for the ambient chord metric. Straight segments and a
local derivative bound produce intrinsic convergence of every Cauchy sequence. -/
lemma euclideanGraphComplete_entire {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) : EuclideanGraphComplete univ f := by
  intro x _ hc
  have hcx : CauchySeq x := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hc ε hε
    refine ⟨N,fun i hi j hj => ?_⟩
    have H := (enorm_sub_le_graphEDist univ f (x i) (x j)).trans_lt (hN i hi j hj)
    rw [← ofReal_norm,ENNReal.ofReal_lt_ofReal_iff hε] at H
    simpa only [dist_eq_norm,norm_sub_rev] using H
  obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete hcx
  have hdf : ContinuousAt (fderiv ℝ f) a :=
    ((hf.contDiffAt.fderiv_right (m := ∞) (by simp))).continuousAt
  obtain ⟨δ,hδ,hδb⟩ := Metric.continuousAt_iff.mp hdf 1 zero_lt_one
  let M : ℝ := ‖fderiv ℝ f a‖+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbd : ∀ z ∈ Metric.ball a δ, ‖fderiv ℝ f z‖ ≤ M := by
    intro z hz
    have H := hδb hz
    have HT := norm_le_norm_add_norm_sub (fderiv ℝ f a) (fderiv ℝ f z)
    rw [dist_eq_norm] at H
    rw [norm_sub_rev] at HT
    dsimp [M]
    linarith
  refine ⟨a,mem_univ a,?_⟩
  intro ε hε
  have hp : 0 < 1+M := by positivity
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ha (min δ (ε/(1+M))) (lt_min hδ (div_pos hε hp))
  refine ⟨N,fun i hi => ?_⟩
  have Hi := hN i hi
  have hib : x i ∈ Metric.ball a δ := lt_of_lt_of_le Hi (min_le_left _ _)
  have hab : a ∈ Metric.ball a δ := Metric.mem_ball_self hδ
  have hs : ∀ t ∈ Icc (0:ℝ) 1, x i+t • (a-x i) ∈ Metric.ball a δ := by
    intro t ht
    have H := (convex_ball a δ) hib hab (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    module
  apply (graphEDist_le_segment_fderiv_bound f (x i) a hM (fun _ _ => mem_univ _) (fun t ht => hbd _ (hs t ht))).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  have Hnorm : ‖a-x i‖ < ε/(1+M) := by
    simpa only [dist_eq_norm,norm_sub_rev] using lt_of_lt_of_le Hi (min_le_right _ _)
  simpa only [mul_comm] using (lt_div_iff₀ hp).mp Hnorm

end EntireGraphComplete


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedFamilyDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedFamilyDet

lemma tangentHeight_tangentShift {n : ℕ} {v : Space n → ℝ}
    (hv : Differentiable ℝ v) (a x y : Space n) (h : ℝ) :
    tangentHeight (tangentShift v a h) x y = tangentHeight v x y := by
  simp only [tangentHeight, tangentShift, fderiv_tangentShift (hv x),
    sub_apply, map_sub]
  ring

end NormalizedFamilyDet


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedLogVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedLogVariance

lemma normalized_gradient_bound {n : ℕ} {ρ R : ℝ} {v : Space n → ℝ}
    (hv : BalancedNormalized ρ R v) {x : Space n}
    (hx : x ∈ Metric.closedBall (0:Space n) (1/4:ℝ)) :
    ‖fderiv ℝ v x‖ ≤ 4 := by
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ convex_univ hv.smooth.contDiffOn
    (fun y _ => (hv.posDef y).posSemidef)
  have hxn : ‖x‖ ≤ (1/4:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hbase : x ∈ Metric.ball (0:Space n) 1 := by
    rw [Metric.mem_ball,dist_zero_right]; linarith
  have hnb : Metric.closedBall x (1/2:ℝ) ⊆ Metric.ball 0 1 := by
    intro y hy
    have hyn : ‖y-x‖ ≤ (1/2:ℝ) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
    rw [Metric.mem_ball,dist_zero_right]
    have hh := norm_add_le (y-x) x
    rw [sub_add_cancel] at hh
    linarith
  have hb : ∀ y ∈ Metric.ball (0:Space n) 1, |v y| ≤ 1 := by
    intro y hy
    have h0 : 0 ≤ v y := by
      have H := tangentHeight_nonneg isOpen_univ convex_univ hv.smooth.contDiffOn
        (fun z _ => hv.posDef z) (mem_univ 0) (mem_univ y)
      simpa [tangentHeight,hv.zero,hv.deriv_zero] using H
    have h1 : v y < 1 := by
      have H := (hv.inner hy).2
      simpa [tangentHeight,hv.zero,hv.deriv_zero] using H
    rw [abs_of_nonneg h0]
    exact h1.le
  have H := norm_fderiv_le_of_convex_bounded
    (hcv.subset (subset_univ _) (convex_ball _ _)) hbase
    (hv.smooth.differentiable (by simp) x) (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (0:ℝ)≤1) hnb hb
  norm_num at H ⊢
  exact H

end NormalizedLogVariance


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LinearNormalizationCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LinearNormalizationCalculus

lemma cleMatrix_det_ne_zero {n : ℕ} (A : Space n ≃L[ℝ] Space n) : (cleMatrix A).det ≠ 0 := by
  have H : cleMatrix A * cleMatrix A.symm = 1 := by
    apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).injective
    simp only [map_mul,map_one]
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (cleMatrix A)) *
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (cleMatrix A.symm)) = 1
    rw [cleMatrix_apply,cleMatrix_apply]
    apply ContinuousLinearMap.ext
    intro x
    exact A.apply_symm_apply x
  have Hd : (cleMatrix A).det * (cleMatrix A.symm).det = 1 := by
    rw [← Matrix.det_mul,H,Matrix.det_one]
  exact left_ne_zero_of_mul_eq_one Hd

lemma normalizedFunction_eq_pullback {n : ℕ} (u : Space n → ℝ)
    (A : Space n ≃L[ℝ] Space n) (t : ℝ) :
    normalizedFunction u A t = affineGraphPullback u (cleMatrix A) 0 0 t⁻¹ 0 := by
  ext y
  simp [normalizedFunction,affineGraphPullback,graphAffineFunction,affineBaseMap]

lemma contDiff_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) :
    ContDiff ℝ ∞ (normalizedFunction u A t) := contDiff_const.mul (hu.comp A.contDiff)

lemma hessian_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x : Space n) :
    hessian (normalizedFunction u A t) x =
      t⁻¹ • ((cleMatrix A).transpose * hessian u (A x) * cleMatrix A) := by
  rw [normalizedFunction_eq_pullback,hessian_affineGraphPullback isOpen_univ hu.contDiffOn _ _ _ _ _ (mem_univ _)]
  simp only [affineBaseMap,cleMatrix_apply,ContinuousLinearEquiv.coe_coe,add_zero]

lemma posDef_hessian_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (A : Space n ≃L[ℝ] Space n) {t : ℝ} (ht : 0 < t) (x : Space n) :
    (hessian (normalizedFunction u A t) x).PosDef := by
  rw [hessian_normalizedFunction hu]
  exact posDef_affine_congruence (hp _) (cleMatrix_det_ne_zero A) (inv_pos.mpr ht)

lemma affineMaximalOn_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (A : Space n ≃L[ℝ] Space n) {t : ℝ} (ht : 0 < t) :
    AffineMaximalOn univ (normalizedFunction u A t) := by
  rw [normalizedFunction_eq_pullback]
  simpa only [preimage_univ] using affineMaximalOn_affineGraphPullback isOpen_univ hu.contDiffOn
    (fun x _ => hp x) hm (cleMatrix_det_ne_zero A) 0 0 (inv_pos.mpr ht) 0

lemma fderiv_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x : Space n) :
    fderiv ℝ (normalizedFunction u A t) x = t⁻¹ • ((fderiv ℝ u (A x)).comp A.toContinuousLinearMap) := by
  exact (((hu.differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt).const_mul t⁻¹).fderiv

lemma tangentHeight_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x y : Space n) :
    tangentHeight (normalizedFunction u A t) x y = t⁻¹ * tangentHeight u (A x) (A y) := by
  simp only [tangentHeight,fderiv_normalizedFunction hu,normalizedFunction,
    smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    map_sub,smul_eq_mul]
  ring

lemma sectionBalance_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    {ρ : ℝ} (hbal : SectionBalance univ u ρ) (A : Space n ≃L[ℝ] Space n)
    {t : ℝ} (ht : 0 < t) : SectionBalance univ (normalizedFunction u A t) ρ := by
  let v := normalizedFunction u A t
  have hv := contDiff_normalizedFunction hu A t
  have hpv := posDef_hessian_normalizedFunction hu hp A ht
  have hcv := euclideanGraphComplete_entire hu
  have hcvv := euclideanGraphComplete_entire hv
  intro x hx s hs y hy
  rw [closure_tangentSection isOpen_univ convex_univ hv.contDiffOn (fun z _ => hpv z) hcvv hx hs] at hy ⊢
  refine ⟨mem_univ _,?_⟩
  have H := (sectionBalance_reflection isOpen_univ convex_univ hu.contDiffOn (fun z _ => hp z)
    hcv hbal (mem_univ (A x)) (mem_univ (A y))).2
  have HH : tangentHeight v x (x-ρ • (y-x)) ≤ tangentHeight v x y := by
    dsimp only [v]
    rw [tangentHeight_normalizedFunction hu,tangentHeight_normalizedFunction hu]
    simp only [map_sub,map_smul]
    exact mul_le_mul_of_nonneg_left H (inv_nonneg.mpr ht.le)
  exact HH.trans hy.2

end LinearNormalizationCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SectionNormalizationFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SectionNormalizationFamily
open scoped Pointwise
open Filter
open scoped Topology

/-- The actual uniform, zero-preserving section normalizations in rigidity.tex.
The radius is fixed before height; the maps are produced from the compact
convex sections and their genuine balance inclusion. -/
theorem centered_section_normalization_family {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : ℝ, 0 < t → ∃ A : Space n ≃L[ℝ] Space n,
      Metric.ball 0 1 ⊆ tangentSection univ (normalizedFunction u A t) 0 1 ∧
      tangentSection univ (normalizedFunction u A t) 0 1 ⊆ Metric.ball 0 R := by
  let C := ρ⁻¹
  have hC : 1 ≤ C := (one_le_inv₀ hρ).mpr hρ1
  have hCp : 0 < C+1 := by linarith
  let R : ℝ := 2*(n:ℝ)*(C+1)+1
  have hR : 1 ≤ R := by
    have H : 0 ≤ 2*(n:ℝ)*(C+1) := by positivity
    dsimp [R]
    linarith
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ convex_univ hu.contDiffOn
    (fun x _ => (hp x).posSemidef)
  have hc := euclideanGraphComplete_entire hu
  have hg (x : Space n) : tangentHeight u 0 x = u x := by simp [tangentHeight,hzero,hdzero]
  refine ⟨R,hR,?_⟩
  intro t ht
  let K := closure (tangentSection univ u 0 t)
  have hKeq : K = {x | u x ≤ t} := by
    dsimp [K]
    rw [closure_tangentSection isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) ht]
    simp only [mem_univ,true_and,hg]
  have hK : IsCompact K := by
    dsimp [K]
    rw [closure_tangentSection isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) ht]
    exact isCompact_tangent_sublevel isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) t
  have hKcv : Convex ℝ K := by
    rw [hKeq]
    simpa only [mem_univ,true_and] using hcv.convex_le t
  have hK0 : (0:Space n) ∈ K := by rw [hKeq]; simpa only [mem_ofPred_eq,hzero] using ht.le
  have hKi : (interior K).Nonempty := by
    refine ⟨0,mem_interior_iff_mem_nhds.mpr ?_⟩
    have hopen : IsOpen {x | u x < t} := isOpen_lt hu.continuous continuous_const
    have hn := hopen.mem_nhds (show (0:Space n) ∈ {x | u x < t} by
      simpa only [mem_ofPred_eq,hzero] using ht)
    apply mem_of_superset hn
    intro x hx
    rw [hKeq]
    exact (show u x < t from hx).le
  have hKb : -K ⊆ C • K := by
    intro z hz
    have hz' : -z ∈ K := by simpa using hz
    have H := hbal 0 (mem_univ _) t ht (-z) hz'
    have Hz : ρ • z ∈ K := by simpa only [zero_sub,sub_zero,smul_neg,neg_neg] using H
    exact Set.mem_smul_set.mpr ⟨ρ • z,Hz,by simp [C,smul_smul,hρ.ne']⟩
  obtain ⟨L,hLin,hLout⟩ := centered_body_normalization hn hK hKcv hKi hK0 hC hKb
  let s : ℝ := (C+1)⁻¹
  have hs : 0 < s := inv_pos.mpr hCp
  let S : Space n ≃L[ℝ] Space n := (LinearEquiv.smulOfNeZero ℝ (Space n) s hs.ne').toContinuousLinearEquiv
  let A := S.trans L.symm
  have hLA (y : Space n) : L (A y) = s • y := by simp [A,S]
  let v := normalizedFunction u A t
  have hv := contDiff_normalizedFunction hu A t
  have hv0 : v 0=0 := by simp [v,normalizedFunction,hzero]
  have hdv0 : fderiv ℝ v 0=0 := by simp [v,fderiv_normalizedFunction hu,hdzero]
  have hgv (y : Space n) : tangentHeight v 0 y = v y := by simp [tangentHeight,hv0,hdv0]
  refine ⟨A,?_,?_⟩
  · intro y hy
    have hyn : ‖y‖ ≤ 1 := (mem_ball_zero_iff.mp hy).le
    have hzin : L ((2:ℝ) • A y) ∈ Metric.closedBall (0:Space n) (2/(C+1)) := by
      rw [Metric.mem_closedBall,dist_zero_right,map_smul,hLA,smul_smul,norm_smul,
        Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num) hs)]
      calc
        _ ≤ (2*s)*1 := mul_le_mul_of_nonneg_left hyn (by positivity)
        _ = 2/(C+1) := by simp [s,div_eq_mul_inv]
    obtain ⟨z,hz,hze⟩ := hLin hzin
    have hzk : (2:ℝ) • A y ∈ K := L.injective hze ▸ hz
    have hzu : u ((2:ℝ) • A y) ≤ t := by rwa [hKeq] at hzk
    have hconv := hcv.2 (mem_univ 0) (mem_univ ((2:ℝ) • A y))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
    have huAy : u (A y) ≤ t/2 := by
      simp only [smul_zero,zero_add,smul_smul,show (1:ℝ)/2*2=1 by norm_num,one_smul,
        hzero,smul_eq_mul,mul_zero,zero_add] at hconv
      linarith
    refine ⟨mem_univ y,?_⟩
    change tangentHeight v 0 y < 1
    rw [hgv]
    change t⁻¹*u (A y)<1
    have H := mul_le_mul_of_nonneg_left huAy (inv_nonneg.mpr ht.le)
    have He : t⁻¹*(t/2)=(1:ℝ)/2 := by field_simp
    rw [He] at H
    linarith
  · intro y hy
    have hyv : v y < 1 := by
      have H : tangentHeight v 0 y < 1 := hy.2
      rwa [hgv] at H
    have hyu : u (A y)<t := by
      change t⁻¹*u (A y)<1 at hyv
      rw [mul_comm,← div_eq_mul_inv] at hyv
      exact (div_lt_iff₀ ht).mp hyv |>.trans_eq (one_mul t)
    have hyK : A y ∈ K := by rw [hKeq]; exact hyu.le
    have HL := hLout ⟨A y,hyK,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,hLA,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at HL
    have HLy : ‖y‖ ≤ 2*(n:ℝ)*(C+1) := by
      have H := mul_le_mul_of_nonneg_right HL hCp.le
      have He : s*‖y‖*(C+1)=‖y‖ := by dsimp [s]; field_simp
      rwa [He] at H
    rw [Metric.mem_ball,dist_zero_right]
    dsimp [R]
    linarith

end SectionNormalizationFamily


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LinearizedNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LinearizedNormalization

lemma inverseHessianTrace_eq_matrixTrace {n : ℕ} {u s : Space n → ℝ}
    (hs : ContDiff ℝ ∞ s) (x : Space n) :
    inverseHessianTrace u s x = ((hessian u x)⁻¹*hessian s x).trace := by
  symm
  exact matrix_trace_pair _ _ (hessian_isSymm hs.contDiffAt)

lemma contDiff_comp_cle {n : ℕ} {s : Space n → ℝ} (hs : ContDiff ℝ ∞ s)
    (A : Space n ≃L[ℝ] Space n) : ContDiff ℝ ∞ (fun x => s (A x)) :=
  hs.comp A.contDiff

/-- The previously produced normalizations can put any finite collection
of fixed original points in the same small inner ball. -/
theorem centered_normalization_at_points {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ P : Finset (Space n),
      ∃ t : ℝ, 0 < t ∧ ∃ A : Space n ≃L[ℝ] Space n,
        BalancedNormalized ρ R (normalizedFunction u A t) ∧
        ∀ x ∈ P, A.symm x ∈ Metric.ball (0:Space n) (1/64:ℝ) := by
  obtain ⟨R,hR,H⟩ := centered_section_normalization_family hn hu hp hzero hdzero hρ hρ1 hbal
  refine ⟨R,hR,?_⟩
  intro P
  let t : ℝ := 1 + ∑ x ∈ P, |u ((64*R) • x)|
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨A,hin,hout⟩ := H t ht
  have hv0 : normalizedFunction u A t 0=0 := by simp [normalizedFunction,hzero]
  have hdz : fderiv ℝ (normalizedFunction u A t) 0=0 := by
    rw [fderiv_normalizedFunction hu]
    simp only [map_zero,hdzero,ContinuousLinearMap.zero_comp,smul_zero]
  refine ⟨t,ht,A,⟨contDiff_normalizedFunction hu A t,posDef_hessian_normalizedFunction hu hp A ht,
    affineMaximalOn_normalizedFunction hu hp hm A ht,hv0,hdz,
    sectionBalance_normalizedFunction hu hp hbal A ht,hin,hout⟩,?_⟩
  intro x hx
  have hxu : u ((64*R) • x) < t := by
    have HH := Finset.single_le_sum (fun point _ => abs_nonneg (u ((64*R) • point))) hx
    dsimp [t]
    linarith [le_abs_self (u ((64*R) • x))]
  have hsec : (64*R) • (A.symm x) ∈ tangentSection univ (normalizedFunction u A t) 0 1 := by
    refine ⟨mem_univ _,?_⟩
    rw [tangentHeight_normalizedFunction hu]
    simp only [map_zero,map_smul,ContinuousLinearEquiv.apply_symm_apply,tangentHeight,hzero,hdzero,
      sub_zero,zero_apply,smul_zero]
    rw [mul_comm,← div_eq_mul_inv]
    exact (div_lt_one ht).mpr hxu
  have hnorm := hout hsec
  rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_of_pos (show 0 < 64*R by linarith)] at hnorm
  rw [Metric.mem_ball,dist_zero_right]
  have hRp : 0 < R := by linarith
  nlinarith

end LinearizedNormalization


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConstantDetCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ConstantDetCalculus
open Filter Matrix
open scoped Topology

lemma dirDeriv_matrix_mul {n m : ℕ} {A B : Space n → Matrix (Fin m) (Fin m) ℝ}
    {x : Space n} (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) x) (v : Space n) :
    matrixDirDeriv v (fun y => A y*B y) x =
      matrixDirDeriv v A x*B x + A x*matrixDirDeriv v B x := by
  ext i j
  simp only [matrixDirDeriv,Matrix.mul_apply,Matrix.add_apply]
  rw [dirDeriv_sum (fun k y => A y i k*B y k j) (fun k => (hA i k).mul (hB k j))]
  simp only [dirDeriv_mul (hA _ _) (hB _ _),Finset.sum_add_distrib]

lemma dirDeriv_matrix_trace {n m : ℕ} {A : Space n → Matrix (Fin m) (Fin m) ℝ}
    {x : Space n} (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : Space n) :
    dirDeriv v (fun y => (A y).trace) x = (matrixDirDeriv v A x).trace := by
  exact dirDeriv_sum (fun i y => A y i i) (fun i => hA i i) v

lemma contDiff_inverseHessian_entry {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) (i j : Fin n) :
    ContDiff ℝ ∞ (fun y => (hessian u y)⁻¹ i j) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_inverse_matrix_entry_param
    (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu.contDiffAt i j)
    (hp x).det_pos.ne' i j

lemma contDiff_hessian_entry_global {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (i j : Fin n) : ContDiff ℝ ∞ (fun y => hessian u y i j) := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => contDiffAt_hessian_entry hu.contDiffAt i j

lemma matrixDirDeriv_inverseHessian {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) (v x : Space n) :
    matrixDirDeriv v (fun y => (hessian u y)⁻¹) x =
      -((hessian u x)⁻¹ * matrixDirDeriv v (hessian u) x * (hessian u x)⁻¹) := by
  have he : (fun y => (hessian u y)⁻¹*hessian u y) = (fun _ => (1:Matrix (Fin n) (Fin n) ℝ)) := by
    funext y
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hp y).det_pos.ne')
  have hd := dirDeriv_matrix_mul
    (fun i j => (contDiff_inverseHessian_entry hu hp i j).differentiable (by simp) x)
    (fun i j => (contDiff_hessian_entry_global hu i j).differentiable (by simp) x) v
  rw [he] at hd
  have hz : matrixDirDeriv v (fun _ : Space n => (1:Matrix (Fin n) (Fin n) ℝ)) x=0 := by
    ext i j
    simp [matrixDirDeriv,dirDeriv]
  rw [hz] at hd
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M*(hessian u x)⁻¹) hd
  rw [Matrix.zero_mul,Matrix.add_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (hp x).det_pos.ne'),Matrix.mul_one] at hh
  exact eq_neg_of_add_eq_zero_left hh.symm

lemma hessian_dirDeriv_vector {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (v x : Space n) : hessian (dirDeriv v u) x = matrixDirDeriv v (hessian u) x := by
  ext i j
  exact third_dirDeriv_comm isOpen_univ hu.contDiffOn (mem_univ x) _ _ _

lemma hessian_dirDeriv_twice {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (v x : Space n) : hessian (dirDeriv v (dirDeriv v u)) x =
      matrixDirDeriv v (hessian (dirDeriv v u)) x :=
  hessian_dirDeriv_vector (contDiff_dirDeriv hu v) v x

lemma constant_det_trace_diff_zero {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) (v x : Space n) :
    ((hessian u x)⁻¹ * hessian (dirDeriv v u) x).trace=0 := by
  have he : logHessianDet u = fun _ => Real.log (hessian u 0).det := by
    funext y
    exact congrArg Real.log (hD y 0)
  have hh := dirDeriv_logHessianDet hu.contDiffAt (hp x) v
  rw [he] at hh
  have hz : dirDeriv v (fun _ : Space n => Real.log (hessian u 0).det) x=0 := by simp [dirDeriv]
  rw [hz] at hh
  rw [matrix_trace_pair _ _ (hessian_isSymm (contDiff_dirDeriv hu v).contDiffAt),hessian_dirDeriv_vector hu]
  exact hh.symm

lemma constant_det_directional_equation {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) (v x : Space n) :
    inverseHessianTrace u (dirDeriv v (dirDeriv v u)) x =
      ((hessian u x)⁻¹ * hessian (dirDeriv v u) x *
       (hessian u x)⁻¹ * hessian (dirDeriv v u) x).trace := by
  let M := hessian (dirDeriv v u)
  have hM : ∀ i j, ContDiff ℝ ∞ (fun y => M y i j) :=
    contDiff_hessian_entry_global (contDiff_dirDeriv hu v)
  have hi := contDiff_inverseHessian_entry hu hp
  have he : (fun y => ((hessian u y)⁻¹*M y).trace) = fun _ => (0:ℝ) := by
    funext y
    exact constant_det_trace_diff_zero hu hp hD v y
  have hh := dirDeriv_matrix_trace (A := fun y => (hessian u y)⁻¹*M y)
    (fun i j => by
      simp only [Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun k _ => ((hi i k).differentiable (by simp) x).mul
        ((hM k j).differentiable (by simp) x)) v
  rw [he] at hh
  have hz : dirDeriv v (fun _ : Space n => (0:ℝ)) x=0 := by simp [dirDeriv]
  rw [hz,dirDeriv_matrix_mul (fun i j => (hi i j).differentiable (by simp) x)
    (fun i j => (hM i j).differentiable (by simp) x) v,
    matrixDirDeriv_inverseHessian hu hp,hessian_dirDeriv_vector hu v x |>.symm,
    ← hessian_dirDeriv_twice hu v x,Matrix.trace_add,Matrix.neg_mul,Matrix.trace_neg] at hh
  rw [inverseHessianTrace_eq_matrixTrace (contDiff_dirDeriv (contDiff_dirDeriv hu v) v)]
  dsimp only [M] at hh
  linarith

lemma directional_second_gradient {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (v x : Space n) (i : Fin n) :
    dirDeriv (coordinateVector n i) (dirDeriv v (dirDeriv v u)) x =
      (hessian (dirDeriv v u) x *ᵥ (fun j => v j)) i := by
  rw [dirDeriv_comm (contDiff_dirDeriv hu v).contDiffAt,
    dirDeriv_coordinate_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dirDeriv_comm (contDiff_dirDeriv hu v).contDiffAt]
  exact mul_comm _ _

end ConstantDetCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TracefreeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Matrix
open scoped MatrixOrder

lemma tracefree_sum_square_bound {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ)
    (ha : ∑ i, a i = 0) (i : Fin n) :
    ((n:ℝ)+1)*(a i)^2 ≤ (n:ℝ)*(∑ j, (a j)^2) := by
  have he := Finset.sum_erase_add (s := Finset.univ) a (Finset.mem_univ i)
  have he2 := Finset.sum_erase_add (s := Finset.univ) (fun j => (a j)^2) (Finset.mem_univ i)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase i) (f := a)
  have hcard : ((Finset.univ.erase i).card : ℝ) = (n:ℝ)-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,Nat.cast_sub hn]
    norm_num
  rw [hcard] at hcs
  rw [ha] at he
  have hsum : 0 ≤ ∑ j, (a j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hse : (∑ x ∈ Finset.univ.erase i, a x) = -a i := by linarith
  have hse2 : (∑ x ∈ Finset.univ.erase i, a x^2) = (∑ j, (a j)^2)-(a i)^2 := by linarith
  rw [hse,hse2,neg_sq] at hcs
  have hbase : (n:ℝ)*(a i)^2 ≤ ((n:ℝ)-1)*(∑ j, (a j)^2) := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hbase (show 0 ≤ (n:ℝ)+1 by positivity)
  apply (mul_le_mul_iff_left₀ (show (0:ℝ)<n by linarith)).mp
  nlinarith [ht]

lemma tracefree_matrix_gap {n : ℕ} (hn : 1 ≤ n)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsHermitian) (htr : B.trace=0) :
    (((n:ℝ)*(B*B).trace) • (1 : Matrix (Fin n) (Fin n) ℝ) - ((n:ℝ)+1) • (B*B)).PosSemidef := by
  let a := hB.eigenvalues
  have ha : ∑ i, a i=0 := by simpa [a,hB.trace_eq_sum_eigenvalues] using htr
  let U := hB.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal a
  have hBD : B = (U:Matrix (Fin n) (Fin n) ℝ) * D * (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose := by
    simpa [a,U,D,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using hB.spectral_theorem
  have hUU : (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose * (U:Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Unitary.coe_star_mul_self U
  have hUU' : (U:Matrix (Fin n) (Fin n) ℝ) * (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose = 1 :=
    Unitary.coe_mul_star_self U
  have hB2 : B*B = (U:Matrix (Fin n) (Fin n) ℝ) * (D*D) * (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose := by
    rw [hBD]
    simp only [Matrix.mul_assoc,← Matrix.mul_assoc (U:Matrix (Fin n) (Fin n) ℝ).conjTranspose, hUU,Matrix.one_mul]
  have ht : (B*B).trace = ∑ i, (a i)^2 := by
    rw [hB2,Matrix.trace_mul_cycle,hUU,Matrix.one_mul]
    simp [D,Matrix.diagonal_mul_diagonal,pow_two,Matrix.trace_diagonal]
  have hp : (((n:ℝ)*(∑ i, (a i)^2)) • (1 : Matrix (Fin n) (Fin n) ℝ) - ((n:ℝ)+1) • (D*D)).PosSemidef := by
    have hd : ((n:ℝ)*(∑ i, (a i)^2)) • (1 : Matrix (Fin n) (Fin n) ℝ) - ((n:ℝ)+1) • (D*D) =
        Matrix.diagonal (fun i => (n:ℝ)*(∑ j, (a j)^2)-((n:ℝ)+1)*(a i)^2) := by
      ext i j
      by_cases hij : i=j
      · subst j
        simp [D,Matrix.diagonal_mul_diagonal,pow_two]
      · simp [D,Matrix.diagonal_mul_diagonal,hij]
    rw [hd,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (tracefree_sum_square_bound hn a ha i)
  have hh := hp.mul_mul_conjTranspose_same (U:Matrix (Fin n) (Fin n) ℝ)
  simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hUU',← hB2,← ht] using hh

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedTracefreeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Matrix
open scoped MatrixOrder

lemma weighted_tracefree_matrix_gap {n : ℕ} (hn : 1 ≤ n)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.IsHermitian)
    (htr : (A⁻¹*B).trace=0) :
    (((n:ℝ)*(A⁻¹*B*A⁻¹*B).trace) • A - ((n:ℝ)+1) • (B*A⁻¹*B)).PosSemidef := by
  let S := CFC.sqrt A⁻¹
  have hS : S.conjTranspose=S := (CFC.sqrt_nonneg A⁻¹).isSelfAdjoint
  have hSS : S*S=A⁻¹ := by simpa only [S,pow_two] using CFC.sq_sqrt A⁻¹ hA.inv.posSemidef.nonneg
  let C := S*B*S
  have hC : C.IsHermitian := by
    change (S*B*S).conjTranspose=S*B*S
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hS,hB,Matrix.mul_assoc]
  have hc0 : C.trace=0 := by
    dsimp only [C]
    rw [Matrix.trace_mul_cycle,hSS,htr]
  have hc2 : C*C=S*(B*A⁻¹*B)*S := by
    dsimp [C]
    calc
      _ = S*(B*(S*S)*B)*S := by noncomm_ring
      _ = _ := by rw [hSS]
  have hct : (C*C).trace=(A⁻¹*B*A⁻¹*B).trace := by
    rw [hc2,Matrix.trace_mul_cycle,hSS]
    simp only [Matrix.mul_assoc]
  have haI : A*A⁻¹=1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hIa : A⁻¹*A=1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hT : (A*S).conjTranspose=S*A := by rw [Matrix.conjTranspose_mul,hS,hA.isHermitian.eq]
  have hT1 : (A*S)*1*(S*A)=A := by
    rw [Matrix.mul_one]
    calc
      _ = A*(S*S)*A := by noncomm_ring
      _ = A := by rw [hSS,haI,Matrix.one_mul]
  have hT2 : (A*S)*(C*C)*(S*A)=B*A⁻¹*B := by
    rw [hc2]
    calc
      _ = (A*(S*S))*(B*A⁻¹*B)*((S*S)*A) := by noncomm_ring
      _ = _ := by rw [hSS,haI,hIa,Matrix.one_mul,Matrix.mul_one]
  have hh := (tracefree_matrix_gap hn hC hc0).mul_mul_conjTranspose_same (A*S)
  simpa only [hT,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,hT1,hT2,hct] using hh

lemma weighted_tracefree_quadratic_gap {n : ℕ} (hn : 1 ≤ n)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.IsHermitian)
    (htr : (A⁻¹*B).trace=0) (e : Fin n → ℝ) :
    ((n:ℝ)+1)*(e ⬝ᵥ ((B*A⁻¹*B)*ᵥ e)) ≤
      (n:ℝ)*(e ⬝ᵥ (A*ᵥ e))*(A⁻¹*B*A⁻¹*B).trace := by
  have h := (weighted_tracefree_matrix_gap hn hA hB htr).dotProduct_mulVec_nonneg e
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul] at h
  nlinarith

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DirectionalJacobi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DirectionalJacobi
open Matrix

lemma constant_det_directional_jacobi {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) (e x : Space n) :
    ((n:ℝ)+1)*inverseHessianPair u (dirDeriv e (dirDeriv e u)) (dirDeriv e (dirDeriv e u)) x ≤
      (n:ℝ)*dirDeriv e (dirDeriv e u) x*inverseHessianTrace u (dirDeriv e (dirDeriv e u)) x := by
  let B := hessian (dirDeriv e u) x
  let A := hessian u x
  have hB : B.IsSymm := hessian_isSymm (contDiff_dirDeriv hu e).contDiffAt
  have hq : inverseHessianPair u (dirDeriv e (dirDeriv e u)) (dirDeriv e (dirDeriv e u)) x =
      (fun i => e i) ⬝ᵥ ((B*A⁻¹*B)*ᵥ (fun i => e i)) := by
    rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose,show B.transpose=B from hB]
    simp only [inverseHessianPair,directional_second_gradient hu,Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    apply Finset.sum_congr rfl
    intro otherCoordinate _
    dsimp only [B,A]
    simp only [← Finset.mul_sum]
    ring
  have hf : dirDeriv e (dirDeriv e u) x = (fun i => e i) ⬝ᵥ (A*ᵥ (fun i => e i)) := by
    rw [dirDeriv_eq_second hu.contDiffAt,second_fderiv_eq_sum hu.contDiffAt]
    simp only [A,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    apply Finset.sum_congr rfl
    intro otherCoordinate _
    ring
  rw [hq,hf,constant_det_directional_equation hu hp hD]
  exact weighted_tracefree_quadratic_gap hn (hp x) (Matrix.isHermitian_iff_isSymm.mpr hB)
    (constant_det_trace_diff_zero hu hp hD e x) (fun i => e i)

lemma inverseHessianTrace_expMul {n : ℕ} {u f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : Space n) :
    inverseHessianTrace u (fun y => Real.exp (c*f y)) x =
      Real.exp (c*f x)*(c*inverseHessianTrace u f x+c^2*inverseHessianPair u f f x) := by
  have he (i j : Fin n) : hessian (fun y => Real.exp (c*f y)) x i j =
      Real.exp (c*f x)*(c*hessian f x i j+c^2*dirDeriv (coordinateVector n i) f x*dirDeriv (coordinateVector n j) f x) :=
    second_dirDeriv_expMul isOpen_univ hf.contDiffOn (mem_univ x) c _ _
  simp only [inverseHessianTrace,inverseHessianPair,he,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro coordinate _ <;>
    apply Finset.sum_congr rfl <;> intro otherCoordinate _ <;> ring

lemma inverseHessianPair_log_positive {n : ℕ} {u f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x) (x : Space n) :
    inverseHessianPair u (fun y => Real.log (f y)) (fun y => Real.log (f y)) x =
      inverseHessianPair u f f x/(f x)^2 := by
  simp only [inverseHessianPair,dirDeriv_real_log (hf.differentiable (by simp) x) (hpos x).ne',
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro coordinate _
  apply Finset.sum_congr rfl
  intro otherCoordinate _
  ring

lemma inverseHessianTrace_log_positive {n : ℕ} {u f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x) (x : Space n) :
    inverseHessianTrace u (fun y => Real.log (f y)) x =
      inverseHessianTrace u f x/f x-inverseHessianPair u f f x/(f x)^2 := by
  have he : inverseHessianTrace u f x = f x *
      (inverseHessianTrace u (fun y => Real.log (f y)) x +
        inverseHessianPair u (fun y => Real.log (f y)) (fun y => Real.log (f y)) x) := by
    simp only [inverseHessianTrace,inverseHessianPair,mul_add,Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hh := log_second_identity isOpen_univ hf.contDiffOn (fun y _ => hpos y)
      (mem_univ x) (coordinateVector n i) (coordinateVector n j)
    change hessian f x i j = f x * (hessian (fun y => Real.log (f y)) x i j + _) at hh
    rw [hh]
    ring
  rw [inverseHessianPair_log_positive hf hpos] at he
  apply eq_sub_iff_add_eq.mpr
  apply (eq_div_iff (hpos x).ne').mpr
  simpa only [mul_comm] using he.symm

lemma inverseNthRoot_pos {n : ℕ} (f : Space n → ℝ) (x : Space n) : 0 < inverseNthRoot n f x :=
  Real.exp_pos _

lemma contDiff_inverseNthRoot {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (hpos : ∀ x, 0 < f x) : ContDiff ℝ ∞ (inverseNthRoot n f) :=
  (contDiff_const.mul (hf.log (fun x => (hpos x).ne'))).exp

lemma inverseNthRoot_pow {n : ℕ} (hn : 1 ≤ n) {f : Space n → ℝ}
    {x : Space n} (hf : 0 < f x) : (inverseNthRoot n f x)^n = (f x)⁻¹ := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n≠0)
  rw [inverseNthRoot,← Real.exp_nat_mul]
  have he : (n:ℝ)*(-((n:ℝ)⁻¹)*Real.log (f x)) = -Real.log (f x) := by field_simp
  rw [he,Real.exp_neg,Real.exp_log hf]

lemma inverseNthRoot_supersolution_of_jacobi {n : ℕ} (hn : 1 ≤ n) {u f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < f x)
    (hJ : ∀ x, ((n:ℝ)+1)*inverseHessianPair u f f x ≤ (n:ℝ)*f x*inverseHessianTrace u f x) :
    ∀ x, inverseHessianTrace u (inverseNthRoot n f) x ≤ 0 := by
  intro x
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  have hlog : ContDiff ℝ ∞ (fun y => Real.log (f y)) := hf.log (fun y => (hpos y).ne')
  change inverseHessianTrace u (fun y => Real.exp (-((n:ℝ)⁻¹)*Real.log (f y))) x ≤ 0
  rw [inverseHessianTrace_expMul hlog,inverseHessianTrace_log_positive hf hpos,
    inverseHessianPair_log_positive hf hpos]
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  have H := hJ x
  have hfx := hpos x
  apply (mul_le_mul_iff_right₀ (show 0 < (n:ℝ)^2*(f x)^2 by positivity)).mp
  rw [mul_zero]
  field_simp [hn0.ne',(hpos x).ne']
  nlinarith

lemma constant_det_directional_inverse_root_supersolution {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) {e : Space n} (he : e ≠ 0) :
    ∀ x, inverseHessianTrace u (inverseNthRoot n (dirDeriv e (dirDeriv e u))) x ≤ 0 := by
  apply inverseNthRoot_supersolution_of_jacobi hn (contDiff_dirDeriv (contDiff_dirDeriv hu e) e)
  · intro x
    rw [dirDeriv_eq_second hu.contDiffAt]
    exact second_fderiv_pos hu.contDiffAt (hp x) he
  · exact fun x => constant_det_directional_jacobi hn hu hp hD e x

end DirectionalJacobi


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EntireGlobalDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EntireGlobalDet

lemma sectionBalance_tangentShift {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) {ρ : ℝ} (hbal : SectionBalance univ u ρ)
    (a : Space n) (h : ℝ) : SectionBalance univ (tangentShift u a h) ρ := by
  have he (x : Space n) (t : ℝ) : tangentSection univ (tangentShift u a h) x t = tangentSection univ u x t := by
    ext y
    simp only [tangentSection,mem_ofPred_eq,tangentHeight_tangentShift (hu.differentiable (by simp))]
  intro x hx t ht y hy
  rw [he] at hy ⊢
  exact hbal x hx t ht y hy

end EntireGlobalDet



end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixUniformBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section MatrixUniformBounds
open Matrix
open scoped MatrixOrder

lemma posDef_lower_of_det_trace_bounds {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {c C : ℝ} (_hc : 0 < c) (hC : 0 ≤ C)
    (hdet : c ≤ A.det) (htr : A.trace ≤ C) :
    (A-(c/(C+1)^n) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  let a := hA.isHermitian.eigenvalues
  have ha (i : Fin n) : 0 < a i := hA.eigenvalues_pos i
  have hs : A.trace = ∑ i, a i := by simpa [a] using hA.isHermitian.trace_eq_sum_eigenvalues
  have hab (i : Fin n) : a i ≤ C :=
    (Finset.single_le_sum (fun j hj => (ha j).le) (Finset.mem_univ i)).trans (hs ▸ htr)
  have hd : A.det = ∏ i, a i := by simpa [a] using hA.isHermitian.det_eq_prod_eigenvalues
  have he (i : Fin n) : c/(C+1)^n ≤ a i := by
    have hp : (∏ j ∈ Finset.univ.erase i, a j) ≤ (C+1)^n := by
      calc
        _ ≤ ∏ j ∈ Finset.univ.erase i, (C+1) := Finset.prod_le_prod
          (fun j hj => (ha j).le) (fun j hj => by linarith [hab j])
        _ = (C+1)^(Finset.univ.erase i).card := by simp
        _ ≤ (C+1)^n := pow_le_pow_right₀ (by linarith) (by
          exact (Finset.card_le_card (Finset.erase_subset i Finset.univ)).trans_eq (by simp))
    have hmul := mul_le_mul_of_nonneg_left hp (ha i).le
    rw [Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i),← hd] at hmul
    exact (div_le_iff₀ (by positivity : 0 < (C+1)^n)).mpr (hdet.trans hmul)
  let U := hA.isHermitian.eigenvectorUnitary
  have hspec : A = (U:Matrix (Fin n) (Fin n) ℝ)*Matrix.diagonal a*(U:Matrix (Fin n) (Fin n) ℝ).conjTranspose := by
    simpa [U,a,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using hA.isHermitian.spectral_theorem
  have hUU : (U:Matrix (Fin n) (Fin n) ℝ)*(U:Matrix (Fin n) (Fin n) ℝ).conjTranspose=1 :=
    Unitary.coe_mul_star_self U
  have hdpos : (Matrix.diagonal a-(c/(C+1)^n) • (1:Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    have hh : Matrix.diagonal a-(c/(C+1)^n) • (1:Matrix (Fin n) (Fin n) ℝ) =
        Matrix.diagonal (fun i => a i-c/(C+1)^n) := by
      ext i j
      by_cases hij : i=j
      · subst j; simp
      · simp [Matrix.diagonal,hij]
    rw [hh,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (he i)
  have hh := hdpos.mul_mul_conjTranspose_same (U:Matrix (Fin n) (Fin n) ℝ)
  simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hUU,← hspec] using hh

lemma posDef_quadratic_bounds {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hdet : c ≤ A.det) (htr : A.trace ≤ C) (p : Fin n → ℝ) :
    (c/(C+1)^n)*(∑ i, (p i)^2) ≤ p ⬝ᵥ (A*ᵥ p) ∧
      p ⬝ᵥ (A*ᵥ p) ≤ C*(∑ i, (p i)^2) := by
  constructor
  · have H := (posDef_lower_of_det_trace_bounds hA hc hC hdet htr).dotProduct_mulVec_nonneg p
    have he : p ⬝ᵥ ((A-(c/(C+1)^n) • (1:Matrix (Fin n) (Fin n) ℝ))*ᵥ p) =
        p ⬝ᵥ (A*ᵥ p)-(c/(C+1)^n)*(∑ i, (p i)^2) := by
      simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct,
        Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [star_trivial,he] at H
    exact sub_nonneg.mp H
  · exact (posSemidef_quadratic_le_trace_mul_sq hA.posSemidef p).trans
      (mul_le_mul_of_nonneg_right htr (Finset.sum_nonneg fun i hi => sq_nonneg _))

end MatrixUniformBounds


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_VarianceSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section VarianceSeparation

lemma compact_sublevel_in_compact {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {f : Space n → ℝ} (hf : Continuous f) (t : ℝ) :
    IsCompact {x | x ∈ K ∧ f x ≤ t} :=
  hK.inter_right (isClosed_le hf continuous_const)

end VarianceSeparation


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_HessianTraceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section HessianTraceIntegral
open Matrix

lemma trace_le_card_mul_det_add_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    A.trace ≤ (Fintype.card ι:ℝ)*(A+1).det := by
  let Q : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  let d : ι → ℝ := hA.1.eigenvalues
  have hQ : Q*Qᵀ = 1 := by
    simpa only [Q,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Unitary.coe_mul_star_self hA.1.eigenvectorUnitary)
  have hspec : A = Q * Matrix.diagonal d * Qᵀ := by
    simpa [Q,d,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.1.spectral_theorem
  have hdetQ : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using hh
  have hsum : A+1 = Q * Matrix.diagonal (fun i => d i+1) * Qᵀ := by
    have he : Matrix.diagonal (fun i => d i+1) = Matrix.diagonal d+1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal,hij]
    rw [he,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,← hspec,hQ]
  have hdet : (A+1).det = ∏ i, (d i+1) := by
    rw [hsum,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal]
    calc
      _ = (Q.det*Q.det)*(∏ i, (d i+1)) := by ring
      _ = _ := by rw [hdetQ,one_mul]
  have hi (i : ι) : d i ≤ ∏ j, (d j+1) := by
    have hd (j : ι) : 0 ≤ d j := hA.eigenvalues_nonneg j
    have hp : 1 ≤ ∏ j ∈ Finset.univ.erase i, (d j+1) :=
      Finset.one_le_prod (fun j hj => by linarith [hd j])
    rw [← Finset.mul_prod_erase Finset.univ (fun j => d j+1) (Finset.mem_univ i)]
    nlinarith [hd i]
  rw [hdet,hA.isHermitian.trace_eq_sum_eigenvalues]
  simpa [d] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)

lemma continuous_hessian_trace {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (fun x => (hessian u x).trace) := by
  apply continuous_finsetSum
  intro i hi
  exact (contDiff_dirDeriv (contDiff_dirDeriv hu (coordinateVector n i)) (coordinateVector n i)).continuous

lemma integral_hessian_trace_le_ball {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    {D : Set (Space n)} (hD : IsCompact D) {G R : ℝ}
    (hG : ∀ x ∈ D, ‖gradient u x‖ ≤ G) (hR : ∀ x ∈ D, ‖x‖ ≤ R) :
    (∫ x in D, (hessian u x).trace) ≤
      (n:ℝ)*(volume (Metric.closedBall (0:Space n) (G+R))).toReal := by
  let F := fun x => gradient u x+x
  have hd (x : Space n) : DifferentiableAt ℝ F x :=
    ((contDiffAt_gradient hu.contDiffAt).differentiableAt (by simp)).add differentiableAt_id
  have hi : Set.InjOn F D :=
    (shiftedGradient_injOn_of_hessian_posSemidef convex_univ (fun x hx => hu.contDiffAt)
      (fun x hx => (hp x).posSemidef)).mono (subset_univ D)
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD.measurableSet
    (fun x hx => (hd x).hasFDerivAt.hasFDerivWithinAt) hi (fun _ : Space n => (1:ℝ≥0∞))
  simp only [lintegral_const,Measure.restrict_apply_univ,mul_one,one_mul] at hj
  have himage : F '' D ⊆ Metric.closedBall 0 (G+R) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add (hG x hx) (hR x hx))
  have hlin : (∫⁻ x in D, ENNReal.ofReal ((hessian u x).trace)) ≤
      (n:ℝ≥0∞)*volume (Metric.closedBall (0:Space n) (G+R)) := by
    calc
      _ ≤ ∫⁻ x in D, (n:ℝ≥0∞)*ENNReal.ofReal |(fderiv ℝ F x).det| := by
        apply setLIntegral_mono' hD.measurableSet
        intro x hx
        rw [show F = (fun y => gradient u y+y) from rfl,det_fderiv_shiftedGradient hu.contDiffAt,
          abs_of_nonneg ((hp x).posSemidef.add Matrix.PosSemidef.one).det_nonneg,
          ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        simpa only [Fintype.card_fin] using trace_le_card_mul_det_add_one (hp x).posSemidef
      _ = (n:ℝ≥0∞)*(∫⁻ x in D, ENNReal.ofReal |(fderiv ℝ F x).det|) := by
        rw [lintegral_const_mul']; simp
      _ ≤ _ := by rw [← hj]; exact mul_le_mul_right (measure_mono (μ := volume) himage) _
  have hiT : IntegrableOn (fun x => (hessian u x).trace) D volume :=
    ContinuousOn.integrableOn_compact hD (continuous_hessian_trace hu).continuousOn
  have hnon (x : Space n) : 0 ≤ (hessian u x).trace := (hp x).posSemidef.trace_nonneg
  have H := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
    (isCompact_closedBall (0:Space n) (G+R)).measure_lt_top.ne) hlin
  rw [← ofReal_integral_eq_lintegral_ofReal hiT (Filter.Eventually.of_forall hnon),
    ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg hnon),ENNReal.toReal_mul] at H
  simpa using H

end HessianTraceIntegral


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedHessianUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedHessianUpper

lemma inverseNthRoot_sublevel_second {n : ℕ} (hn : 1 ≤ n) {f : Space n → ℝ}
    (hf : ∀ x, 0 < f x) {a x : Space n}
    (h : inverseNthRoot n f x ≤ 2*inverseNthRoot n f a) : f a ≤ (2:ℝ)^n*f x := by
  have H := pow_le_pow_left₀ (inverseNthRoot_pos f x).le h n
  rw [mul_pow,inverseNthRoot_pow hn (hf x),inverseNthRoot_pow hn (hf a)] at H
  have H' := mul_le_mul_of_nonneg_left H (mul_pos (hf a) (hf x)).le
  have he : f a*f x*(f x)⁻¹ = f a  := by field_simp [(hf x).ne', (hf a).ne']
  have he' : f a*f x*((2:ℝ)^n*(f a)⁻¹)=(2:ℝ)^n*f x  := by field_simp [(hf x).ne', (hf a).ne']
  rwa [he,he'] at H'

lemma hessian_diagonal_le_trace {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (i : Fin n) : hessian u x i i ≤ (hessian u x).trace := by
  exact Finset.single_le_sum (f := fun j => hessian u x j j)
    (fun _ _ => hp.posSemidef.diag_nonneg) (Finset.mem_univ i)

/-- A genuine normalized Hessian upper bound made from the original equation:
the inverse-root Jacobi supersolution, ABP critical density, and the shifted
gradient area formula. No interior regularity theorem is postulated. -/
theorem normalized_hessian_diagonal_upper {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ), ∀ i : Fin n, hessian v a i i ≤ C := by
  obtain ⟨δ,hδ,Hδ⟩ := normalized_critical_density hn hρ hρ1 hR
  let J := (n:ℝ)*(volume (Metric.closedBall (0:Space n) (4+(1/16:ℝ)))).toReal
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨(2:ℝ)^n*J/δ+1,by positivity,?_⟩
  intro v hv a ha i
  let f := fun x => hessian v x i i
  let s := inverseNthRoot n f
  have hne : coordinateVector n i ≠ 0 := by
    intro H
    have HH := congrArg (fun e : Space n => e i) H
    simp [coordinateVector] at HH
  have hf : ContDiff ℝ ∞ f := contDiff_dirDeriv (contDiff_dirDeriv hv.smooth _) _
  have hfp (x : Space n) : 0 < f x := by
    change 0 < dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n i) v) x
    rw [dirDeriv_eq_second hv.smooth.contDiffAt]
    exact second_fderiv_pos hv.smooth.contDiffAt (hv.posDef x) hne
  have hs : ContDiff ℝ ∞ s := contDiff_inverseNthRoot hf hfp
  have hsp (x : Space n) : 0 < s x := inverseNthRoot_pos f x
  have hD := balanced_affineMaximal_constant_det hn hv.smooth hv.posDef hv.maximal hρ hρ1 hv.balance
  have hLs : ∀ x, inverseHessianTrace v s x ≤ 0 :=
    constant_det_directional_inverse_root_supersolution hn hv.smooth hv.posDef hD hne
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  let T := {x | x ∈ K ∧ s x ≤ 2*s a}
  have hK : IsCompact K := isCompact_closedBall _ _
  have hT : IsCompact T := compact_sublevel_in_compact hK hs.continuous (2*s a)
  have hTK : T ⊆ K := fun _ hx => hx.1
  have hlow : δ ≤ (volume T).toReal := Hδ v hv s hs (fun x => (hsp x).le) hLs a ha (s a) (hsp a) le_rfl
  have hpoint (x : Space n) (hx : x ∈ T) : f a ≤ (2:ℝ)^n*(hessian v x).trace := by
    exact (inverseNthRoot_sublevel_second hn hfp hx.2).trans
      (mul_le_mul_of_nonneg_left (hessian_diagonal_le_trace (hv.posDef x) i) (by positivity))
  let : IsFiniteMeasure (volume.restrict T) := ⟨by simpa using hT.measure_lt_top (μ := volume)⟩
  have hiT : IntegrableOn (fun x => (hessian v x).trace) T volume :=
    ContinuousOn.integrableOn_compact hT (continuous_hessian_trace hv.smooth).continuousOn
  have hiK : IntegrableOn (fun x => (hessian v x).trace) K volume :=
    ContinuousOn.integrableOn_compact hK (continuous_hessian_trace hv.smooth).continuousOn
  have hInt := setIntegral_mono_on (integrable_const (f a)) (hiT.const_mul ((2:ℝ)^n))
    hT.measurableSet hpoint
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,integral_const_mul] at hInt
  have hmon : (∫ x in T, (hessian v x).trace) ≤ ∫ x in K, (hessian v x).trace :=
    setIntegral_mono_set hiK (Filter.Eventually.of_forall fun x => (hv.posDef x).posSemidef.trace_nonneg)
      (Filter.Eventually.of_forall hTK)
  have hupper : (∫ x in K, (hessian v x).trace) ≤ J := by
    apply integral_hessian_trace_le_ball hv.smooth hv.posDef hK
    · intro x hx
      have hxq : x ∈ Metric.closedBall (0:Space n) (1/4:ℝ) :=
        Metric.closedBall_subset_closedBall (by norm_num) hx
      simpa only [gradient,LinearIsometryEquiv.norm_map] using normalized_gradient_bound hv hxq
    · intro x hx
      simpa only [K,Metric.mem_closedBall,dist_zero_right] using hx
  have Hmul := mul_le_mul_of_nonneg_left (hmon.trans hupper) (show 0 ≤ (2:ℝ)^n by positivity)
  have Hδ := mul_le_mul_of_nonneg_right hlow (hfp a).le
  have Hbound : f a ≤ (2:ℝ)^n*J/δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  change f a ≤ _
  linarith

theorem normalized_hessian_trace_upper {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ), (hessian v a).trace ≤ C := by
  obtain ⟨C,hC,H⟩ := normalized_hessian_diagonal_upper hn hρ hρ1 hR
  refine ⟨(n:ℝ)*C,mul_pos (by exact_mod_cast hn) hC,?_⟩
  intro v hv a ha
  simpa only [Matrix.trace,Matrix.diag_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
    Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => H v hv a ha i)

end NormalizedHessianUpper


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GlobalHessianBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GlobalHessianBound
open Matrix

lemma second_directional_eq_quadratic {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (e x : Space n) :
    dirDeriv e (dirDeriv e u) x = (fun i => e i) ⬝ᵥ ((hessian u x)*ᵥ (fun i => e i)) := by
  rw [dirDeriv_eq_second hu.contDiffAt,second_fderiv_eq_sum hu.contDiffAt]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

lemma second_directional_normalized {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (e x : Space n) :
    dirDeriv e (dirDeriv e (normalizedFunction u A t)) x =
      t⁻¹*dirDeriv (A e) (dirDeriv (A e) u) (A x) := by
  change dirDeriv e (dirDeriv e (fun y => t⁻¹*u (A y))) x = _
  rw [second_dirDeriv_const_mul isOpen_univ (contDiff_comp_cle hu A).contDiffOn
    (mem_univ x),dirDeriv_eq_second (contDiff_comp_cle hu A).contDiffAt,
    dirDeriv_eq_second hu.contDiffAt]
  have H := second_fderiv_affine_comp A.toContinuousLinearMap (0:Space n) (x := x) hu.contDiffAt e e
  simpa only [zero_add,ContinuousLinearEquiv.coe_coe] using congrArg (fun z : ℝ => t⁻¹*z) H

/-- The pointwise normalized estimate transfers through actual section maps
to a global upper bound for every directional second derivative. -/
theorem centered_balanced_global_directional_bound {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ e x : Space n,
      dirDeriv e (dirDeriv e u) x ≤ C*dirDeriv e (dirDeriv e u) 0 := by
  classical
  obtain ⟨R,hR,Hnorm⟩ := centered_normalization_at_points hn hu hp hm hzero hdzero hρ hρ1 hbal
  obtain ⟨c,D,hc,hD,Hdet⟩ := normalized_balanced_det_bounds hρ hρ1 hR (n := n)
  obtain ⟨C,hC,Htr⟩ := normalized_hessian_trace_upper hn hρ hρ1 hR
  let d := c/(C+1)^n
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨C/d,div_pos hC hd,?_⟩
  intro e x
  obtain ⟨t,ht,A,hv,Hpts⟩ := Hnorm {0,x}
  let v := normalizedFunction u A t
  let p := A.symm e
  have h0 : (0:Space n) ∈ Metric.ball 0 (1/64:ℝ) := by simp
  have hx : A.symm x ∈ Metric.ball (0:Space n) (1/64:ℝ) := Hpts x (by simp)
  have h0det : c ≤ (hessian v 0).det := (Hdet v hv.smooth hv.posDef hv.maximal hv.zero hv.deriv_zero
    hv.balance hv.inner hv.outer 0 (by simp)).1
  have hlo := (posDef_quadratic_bounds (hv.posDef 0) hc hC.le h0det (Htr v hv 0 h0)
    (fun i => p i)).1
  have hhi := (posSemidef_quadratic_le_trace_mul_sq (hv.posDef (A.symm x)).posSemidef (fun i => p i)).trans
    (mul_le_mul_of_nonneg_right (Htr v hv (A.symm x) hx)
      (Finset.sum_nonneg fun index _ => sq_nonneg (p index)))
  rw [← second_directional_eq_quadratic hv.smooth,second_directional_normalized hu] at hlo hhi
  simp only [p,ContinuousLinearEquiv.apply_symm_apply,map_zero] at hlo hhi
  change d*(∑ i, (p i)^2) ≤ t⁻¹*dirDeriv e (dirDeriv e u) 0 at hlo
  have Hscaled := mul_le_mul_of_nonneg_left hlo (div_pos hC hd).le
  have he : (C/d)*(d*(∑ i, (p i)^2)) = C*(∑ i, (p i)^2) := by field_simp
  rw [he] at Hscaled
  have H := hhi.trans Hscaled
  apply (mul_le_mul_iff_right₀ (inv_pos.mpr ht)).mp
  nlinarith [H]

theorem balanced_global_directional_bddAbove_oai {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbal : SectionBalance univ u ρ) (e : Space n) :
    BddAbove (range (dirDeriv e (dirDeriv e u))) := by
  let v := tangentShift u 0 0
  have hv : ContDiff ℝ ∞ v := contDiffOn_univ.mp (contDiffOn_tangentShift hu.contDiffOn 0 0)
  have hh (x : Space n) : hessian v x = hessian u x := hessian_tangentShift isOpen_univ hu.contDiffOn 0 0 (mem_univ x)
  have hvp (x : Space n) : (hessian v x).PosDef := hh x ▸ hp x
  have hvm := affineMaximalOn_tangentShift isOpen_univ hu.contDiffOn hm 0 0
  have hv0 : v 0=0 := by simp [v,tangentShift,tangentHeight]
  have hdv0 : fderiv ℝ v 0=0 := by
    dsimp [v]
    rw [fderiv_tangentShift (hu.differentiable (by simp) 0)]
    exact sub_self _
  obtain ⟨C,hC,HC⟩ := centered_balanced_global_directional_bound hn hv hvp hvm hv0 hdv0 hρ hρ1
    (sectionBalance_tangentShift hu hbal 0 0)
  have he (x : Space n) : dirDeriv e (dirDeriv e v) x = dirDeriv e (dirDeriv e u) x := by
    rw [second_directional_eq_quadratic hv,second_directional_eq_quadratic hu,hh]
  refine ⟨C*dirDeriv e (dirDeriv e u) 0,?_⟩
  rintro y ⟨x,rfl⟩
  simpa only [he] using HC e x

end GlobalHessianBound


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.balanced_global_directional_bddAbove_oai := @OAI.AffineBernstein.balanced_global_directional_bddAbove_oai
