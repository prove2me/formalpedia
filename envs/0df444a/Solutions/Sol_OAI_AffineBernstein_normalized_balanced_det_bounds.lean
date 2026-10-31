-- Prove2me | solution 1 for OAI.AffineBernstein.normalized_balanced_det_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:18:21.777726+00:00
-- url     : https://prove2.me/submissions/ddc1c874-4320-4252-acb3-3bdce122aed9

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineMaximal_det_upper_of_section_control

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

/-- A second derivative product rule on the actual open domain. -/
theorem second_dirDeriv_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    {x : E} (hx : x ∈ Ω) (v z : E) :
    dirDeriv z (dirDeriv v (fun y => f y * g y)) x =
      dirDeriv z (dirDeriv v f) x * g x + dirDeriv v f x * dirDeriv z g x +
      dirDeriv z f x * dirDeriv v g x + f x * dirDeriv z (dirDeriv v g) x := by
  have he : dirDeriv v (fun y => f y * g y) =ᶠ[nhds x]
      (fun y => dirDeriv v f y * g y + f y * dirDeriv v g y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_mul ((hf.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) v
  have hfx := hf.contDiffAt (hΩ.mem_nhds hx)
  have hgx := hg.contDiffAt (hΩ.mem_nhds hx)
  have hdf := hfx.differentiableAt (by simp)
  have hdg := hgx.differentiableAt (by simp)
  have hdfv := (contDiffAt_dirDeriv hfx v).differentiableAt (by simp)
  have hdgv := (contDiffAt_dirDeriv hgx v).differentiableAt (by simp)
  change fderiv ℝ _ x z = _
  have h1 : DifferentiableAt ℝ (fun y => dirDeriv v f y * g y) x := hdfv.mul hdg
  have h2 : DifferentiableAt ℝ (fun y => f y * dirDeriv v g y) x := hdf.mul hdgv
  rw [he.fderiv_eq, fderiv_fun_add h1 h2]
  simp only [add_apply]
  change dirDeriv z (fun y => dirDeriv v f y * g y) x +
    dirDeriv z (fun y => f y * dirDeriv v g y) x = _
  rw [dirDeriv_mul hdfv hdg, dirDeriv_mul hdf hdgv]
  ring

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

/-- Coordinate pairing equals the ordinary matrix-vector contraction. -/
theorem matrix_pair_eq_dot {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (p q : ι → ℝ) :
    (∑ i, ∑ j, A i j * p i * q j) = p ⬝ᵥ (A.mulVec q) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Symmetry of the covector contraction, with the literal matrix coefficients. -/
theorem matrix_pair_symm {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.IsSymm) (p q : ι → ℝ) :
    (∑ i, ∑ j, A i j * p i * q j) = ∑ i, ∑ j, A i j * q i * p j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.apply i j]
  ring

/-- Exact inverse contraction for a radial vector and a covector. -/
theorem inverse_radial_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (v p : ι → ℝ) :
    (∑ i, ∑ j, H⁻¹ i j * (∑ k, v k * H k i) * p j) = ∑ i, v i * p i := by
  rw [matrix_pair_eq_dot]
  change (Matrix.vecMul v H) ⬝ᵥ ((H⁻¹).mulVec p) = _
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos)), Matrix.vecMul_one]
  rfl

/-- Product trace in coordinates. -/
theorem hessian_product_trace {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f g : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    {x : Space n} (hx : x ∈ Ω) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (∑ i, ∑ j, A i j * hessian (fun y => f y * g y) x i j) =
      g x * (∑ i, ∑ j, A i j * hessian f x i j) +
      f x * (∑ i, ∑ j, A i j * hessian g x i j) +
      2 * (∑ i, ∑ j, A i j * dirDeriv (coordinateVector n i) f x *
        dirDeriv (coordinateVector n j) g x) := by
  have he (i j : Fin n) : hessian (fun y => f y * g y) x i j =
      hessian f x i j * g x + dirDeriv (coordinateVector n j) f x *
        dirDeriv (coordinateVector n i) g x +
      dirDeriv (coordinateVector n i) f x * dirDeriv (coordinateVector n j) g x +
      f x * hessian g x i j :=
    second_dirDeriv_mul hΩ hf hg hx (coordinateVector n j) (coordinateVector n i)
  simp_rw [he, mul_add, Finset.sum_add_distrib]
  have hswap := matrix_pair_symm hA
    (fun i => dirDeriv (coordinateVector n i) f x)
    (fun i => dirDeriv (coordinateVector n i) g x)
  have hterm1 : (∑ i, ∑ j, A i j * (hessian f x i j * g x)) =
      g x * (∑ i, ∑ j, A i j * hessian f x i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hterm2 : (∑ i, ∑ j, A i j * (f x * hessian g x i j)) =
      f x * (∑ i, ∑ j, A i j * hessian g x i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hterm3 : (∑ i, ∑ j, A i j *
      (dirDeriv (coordinateVector n j) f x * dirDeriv (coordinateVector n i) g x)) =
      ∑ i, ∑ j, A i j * dirDeriv (coordinateVector n i) f x *
        dirDeriv (coordinateVector n j) g x := by
    rw [hswap]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hterm1, hterm2, hterm3]
  simp only [← mul_assoc]
  ring

/-- Positivity fixes the inverse-Hessian symmetry employed in a cap test. -/
theorem inverseHessian_isSymm {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hpos : (hessian u x).PosDef) : ((hessian u x)⁻¹).IsSymm :=
  (Matrix.isHermitian_iff_isSymm.mp hpos.isHermitian).inv

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

/-- On an open set the Hessian is additive; no extension outside that set is used. -/
theorem hessian_add_on {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => u y + v y) x = hessian u x + hessian v x := by
  ext i j
  have he : (fun y => fderiv ℝ (fun z => u z + v z) y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ u y (coordinateVector n j) + fderiv ℝ v y (coordinateVector n j)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [fderiv_fun_add ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hv.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))]
    rfl
  change fderiv ℝ (fun y => fderiv ℝ (fun z => u z + v z) y (coordinateVector n j)) x (coordinateVector n i) =
    fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector n j)) x (coordinateVector n i) +
    fderiv ℝ (fun y => fderiv ℝ v y (coordinateVector n j)) x (coordinateVector n i)
  rw [he.fderiv_eq]
  change fderiv ℝ (fun y => dirDeriv (coordinateVector n j) u y + dirDeriv (coordinateVector n j) v y) x (coordinateVector n i) =
    fderiv ℝ (dirDeriv (coordinateVector n j) u) x (coordinateVector n i) +
    fderiv ℝ (dirDeriv (coordinateVector n j) v) x (coordinateVector n i)
  rw [fderiv_fun_add
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) (coordinateVector n j)).differentiableAt (by simp))
    ((contDiffAt_dirDeriv (hv.contDiffAt (hΩ.mem_nhds hx)) (coordinateVector n j)).differentiableAt (by simp))]
  rfl

theorem hessian_isSymm {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : (hessian u x).IsSymm := by
  ext i j
  exact dirDeriv_comm hu (coordinateVector n j) (coordinateVector n i)

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

/-- Hessians are local, including their inner derivative. -/
theorem hessian_congr_nhds {n : ℕ} {u v : Space n → ℝ} {x : Space n}
    (he : u =ᶠ[nhds x] v) : hessian u x = hessian v x := by
  ext i j
  have hd : (fun y => fderiv ℝ u y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ v y (coordinateVector n j)) :=
    he.fderiv.mono (fun _ hy => congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n j)) hy)
  exact congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n i)) hd.fderiv_eq

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexSmoothMax
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

lemma hessian_sub_on {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => u y-v y) x = hessian u x-hessian v x := by
  have h := hessian_add_on hΩ (hu.sub hv) hv hx
  have he : (fun y => (u y-v y)+v y) = u := by funext y; ring
  rw [he] at h
  exact eq_sub_iff_add_eq.mpr h.symm

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

lemma hessian_dirDeriv {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (k i j : Fin n) :
    hessian (dirDeriv (coordinateVector n k) u) x i j =
      dirDeriv (coordinateVector n k) (fun y => hessian u y i j) x :=
  third_dirDeriv_comm hΩ hu hx _ _ _

lemma hessian_sum_on {κ : Type*} [Fintype κ] {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {f : κ → Space n → ℝ} (hf : ∀ k, ContDiffOn ℝ ∞ (f k) Ω)
    {x : Space n} (hx : x ∈ Ω) (i j : Fin n) :
    hessian (fun y => ∑ k, f k y) x i j = ∑ k, hessian (f k) x i j := by
  have he : dirDeriv (coordinateVector n j) (fun y => ∑ k, f k y) =ᶠ[nhds x]
      (fun y => ∑ k, dirDeriv (coordinateVector n j) (f k) y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_sum f (fun k => ((hf k).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) _
  calc
    _ = dirDeriv (coordinateVector n i) (fun y => ∑ k, dirDeriv (coordinateVector n j) (f k) y) x :=
      congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinateVector n i)) he.fderiv_eq
    _ = _ := dirDeriv_sum (fun k => dirDeriv (coordinateVector n j) (f k))
      (fun k => (contDiffAt_dirDeriv ((hf k).contDiffAt (hΩ.mem_nhds hx)) _).differentiableAt (by simp)) _

lemma contDiffOn_dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (v : E) :
    ContDiffOn ℝ ∞ (dirDeriv v f) Ω := by
  intro x hx
  exact (contDiffAt_dirDeriv (hf.contDiffAt (hΩ.mem_nhds hx)) v).contDiffWithinAt

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

lemma dirDeriv_sub {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    dirDeriv v (fun y => f y-g y) x = dirDeriv v f x-dirDeriv v g x := by
  change (fderiv ℝ (f-g) x) v = _
  rw [fderiv_sub hf hg]
  rfl

lemma matrix_inverse_contraction_self {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) :
    (∑ j, ∑ i, A⁻¹ i j * A j i) = Fintype.card ι := by
  rw [Finset.sum_comm]
  have he := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  have ht := congrArg Matrix.trace he
  simpa [Matrix.trace,Matrix.diag,Matrix.mul_apply] using ht

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
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricAffineArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The augmented tangent frame, with its transverse column last. -/

lemma hessian_add_constant {n : ℕ} (f : Space n → ℝ) (r : ℝ) (x : Space n) :
    hessian (fun y => f y + r) x = hessian f x := by
  ext i j
  simp only [hessian, fderiv_add_const]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphParametricArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma hessian_coordinate {n : ℕ} (k : Fin n) (x : Space n) :
    hessian (fun y : Space n => y k) x = 0 := by
  change hessian (coordinateProjection n k) x = 0
  ext i j
  simp [hessian, (coordinateProjection n k).fderiv]

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
theorem gap_doubling_of_sectionBalance {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {ρ : ℝ} (hρ : 0 < ρ)
    (hbal : SectionBalance Ω u ρ) {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    a + (1 + ρ / 2) • (x - a) ∈ Ω ∧
    tangentHeight u a (a + (1 + ρ / 2) • (x - a)) ≤
      ((2 + ρ) * (1 + ρ) / ρ) * tangentHeight u a x := by
  let θ : ℝ := (2 + ρ) / (2 * (1 + ρ))
  let β : ℝ := 1 + ρ / 2
  let A : ℝ := (2 + ρ) * (1 + ρ) / ρ
  have hden : 0 < 2 * (1 + ρ) := by positivity
  have hθ : 0 < θ := div_pos (by linarith) hden
  have hθ1 : θ < 1 := (div_lt_one hden).mpr (by linarith)
  have hβ : β = (1 + ρ) * θ := by dsimp [β, θ]; field_simp
  have hA : A * (1 - θ) = β := by
    dsimp [A, θ, β]
    field_simp
    ring
  have hA0 : 0 < A := by dsimp [A]; positivity
  let v := x - a
  let y := a + θ • v
  let z := a + β • v
  have hy : y ∈ Ω := hcv.add_smul_mem ha (by simpa [v] using hx) ⟨hθ.le, hθ1.le⟩
  have hz : y - ρ • (a - y) = z := by
    dsimp [y, z]
    rw [hβ]
    module
  have hrfl := sectionBalance_reflection hΩ hcv hu hp hc hbal hy ha
  rw [hz] at hrfl
  refine ⟨hrfl.1, ?_⟩
  have hzy : z - y = (β - θ) • v := by dsimp [z, y]; module
  have hay : a - y = (-θ) • v := by dsimp [y]; module
  have hxy : x - y = (1 - θ) • v := by dsimp [y, v]; module
  have hza : z - a = β • v := by simp [z]
  have hya : y - a = θ • v := by simp [y]
  have hrefl := hrfl.2
  simp only [tangentHeight, hzy, hay, map_smul, smul_eq_mul] at hrefl
  have hsupport := tangentHeight_nonneg hΩ hcv hu hp hy hx
  simp only [tangentHeight, hxy, map_smul, smul_eq_mul] at hsupport
  have hbase := tangentHeight_nonneg hΩ hcv hu hp ha hy
  simp only [tangentHeight, hya, map_smul, smul_eq_mul] at hbase
  have hbound : (1 - θ) * (fderiv ℝ u y v - fderiv ℝ u a v) ≤ tangentHeight u a x := by
    dsimp [tangentHeight, v] at *
    nlinarith
  have hzbound : tangentHeight u a z ≤ β * (fderiv ℝ u y v - fderiv ℝ u a v) := by
    simp only [tangentHeight, hza, map_smul, smul_eq_mul]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbound hA0.le
  rw [← mul_assoc, hA] at hmul
  exact hzbound.trans hmul

/- Convexity of the actual support gap gives its monotonicity on every ray. -/
theorem tangentHeight_ray_mono {n : ℕ} {u : Space n → ℝ}
    (hu : ConvexOn ℝ univ u) (hmin : ∀ a x, 0 ≤ tangentHeight u a x)
    (a e : Space n) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    tangentHeight u a (a + r • e) ≤ tangentHeight u a (a + s • e) := by
  by_cases hs : s = 0
  · have : r = 0 := le_antisymm (by simpa [hs] using hrs) hr
    simp [this, hs]
  have hs0 : 0 < s := lt_of_le_of_ne (hr.trans hrs) (Ne.symm hs)
  have hq : 0 ≤ r / s := div_nonneg hr hs0.le
  have hq1 : r / s ≤ 1 := (div_le_one hs0).mpr hrs
  have he := (convexOn_tangentHeight hu a).2 (mem_univ a) (mem_univ (a + s • e))
    (sub_nonneg.mpr hq1) hq (show (1 - r / s) + r / s = 1 by ring)
  have hv : (1 - r / s) • a + (r / s) • (a + s • e) = a + r • e := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ hs]
    module
  rw [hv, tangentHeight_self] at he
  simp only [smul_eq_mul, mul_zero, zero_add] at he
  exact he.trans (mul_le_of_le_one_left (hmin _ _) hq1)

/- The normalization B₁⊆{v<1}, at a zero tangent, gives v≤1/4 on B₁/₄. -/
theorem normalized_value_le_quarter {n : ℕ} {v : Space n → ℝ}
    (hv : ConvexOn ℝ univ v) (hzero : v 0 = 0) (hdzero : fderiv ℝ v 0 = 0)
    (hinner : Metric.ball 0 1 ⊆ tangentSection univ v 0 1)
    {x : Space n} (hx : ‖x‖ < 1 / 4) : v x ≤ 1 / 4 := by
  have hmem : (4 : ℝ) • x ∈ Metric.ball 0 1 := by
    rw [mem_ball_zero_iff, norm_smul_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    linarith
  have hsmall := (hinner hmem).2
  simp only [tangentHeight, hzero, hdzero, sub_zero, zero_apply] at hsmall
  have he := hv.2 (mem_univ (0 : Space n)) (mem_univ ((4 : ℝ) • x))
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num)
  norm_num [smul_smul, hzero] at he
  linarith

/- Source fixed-radius-gap. The proof uses reflected closed sections directly,
rather than choosing the intersection with their radial boundary. -/
theorem fixed_radius_gap_of_sectionBalance {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hp : ∀ x, (hessian v x).PosDef)
    (hc : EuclideanGraphComplete univ v)
    (hzero : v 0 = 0) (hdzero : fderiv ℝ v 0 = 0)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R)
    (hbal : SectionBalance univ v ρ)
    (hinner : Metric.ball 0 1 ⊆ tangentSection univ v 0 1)
    (houter : tangentSection univ v 0 1 ⊆ Metric.ball 0 R)
    {x e : Space n} (hx : ‖x‖ < 1 / 4) (he : ‖e‖ = 1) :
    (1 / 4 : ℝ) ≤ tangentHeight v x (x + (2 * R / ρ) • e) := by
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ (convex_univ : Convex ℝ (univ : Set (Space n)))
    hv.contDiffOn (fun z _ => (hp z).posSemidef)
  have hvx := normalized_value_le_quarter hcv hzero hdzero hinner hx
  have hout (z : Space n) (hz : R ≤ ‖z‖) : 1 ≤ v z := by
    by_contra hh
    have hmem : z ∈ tangentSection univ v 0 1 := by
      refine ⟨mem_univ _, ?_⟩
      simpa [tangentHeight, hzero, hdzero] using lt_of_not_ge hh
    have hnorm := mem_ball_zero_iff.mp (houter hmem)
    linarith
  have hb : 0 < 2 * R / ρ := by positivity
  have hbet : 2 * R ≤ 2 * R / ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
  have hfar {s : ℝ} (hs : 2 * R ≤ |s|) : R ≤ ‖x + s • e‖ := by
    have hnorm := norm_add_le (x + s • e) (-x)
    have heq : x + s • e + -x = s • e := by abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, he, mul_one] at hnorm
    linarith
  by_cases hsgn : fderiv ℝ v x e ≤ 0
  · have hvz := hout _ (hfar (s := 2 * R / ρ) (by rwa [abs_of_pos hb]))
    simp only [tangentHeight, add_sub_cancel_left, map_smul, smul_eq_mul]
    have hneg := mul_nonpos_of_nonneg_of_nonpos hb.le hsgn
    linarith
  · have hvz := hout (x - (2 * R) • e) (by
      simpa only [neg_smul, sub_eq_add_neg] using
        hfar (s := -(2 * R)) (by rw [abs_neg, abs_of_pos (by positivity)]))
    have href := (sectionBalance_reflection isOpen_univ (convex_univ : Convex ℝ (univ : Set (Space n)))
      hv.contDiffOn (fun z _ => hp z) hc hbal (mem_univ x)
      (mem_univ (x + (2 * R / ρ) • e))).2
    have hreflect : x - ρ • (x + (2 * R / ρ) • e - x) = x - (2 * R) • e := by
      rw [add_sub_cancel_left, smul_smul, mul_div_cancel₀ _ hρ.ne']
    rw [hreflect] at href
    have hdisp : x - (2 * R) • e - x = -(2 * R) • e := by module
    simp only [tangentHeight, hdisp, map_smul, smul_eq_mul] at href
    have hprod : 0 ≤ (2 * R) * fderiv ℝ v x e := mul_nonneg (by positivity) (le_of_not_ge hsgn)
    unfold tangentHeight
    linarith

/- Exact integer in rigidity.tex: N(r)=max(0,ceil(log_beta(R*/r))).
The natural-number ceiling incorporates max with zero. -/

theorem normalizedModulus_pos {ρ R r : ℝ} (hρ : 0 < ρ) :
    0 < normalizedModulus ρ R r := by
  unfold normalizedModulus
  positivity

theorem modulusIterates_spec {ρ R r : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hr : 0 < r) :
    2 * R / ρ ≤ (1 + ρ / 2) ^ modulusIterates ρ R r * r := by
  have hb : 1 < 1 + ρ / 2 := by linarith
  have hb0 : 0 < 1 + ρ / 2 := zero_lt_one.trans hb
  have ht : 0 < (2 * R / ρ) / r := by positivity
  have he := Real.rpow_le_rpow_of_exponent_le hb.le
    (Nat.le_ceil (Real.logb (1 + ρ / 2) ((2 * R / ρ) / r)))
  rw [Real.rpow_logb hb0 (ne_of_gt hb) ht, Real.rpow_natCast] at he
  exact (div_le_iff₀ hr).mp he

/- Iterate the source's doubling inequality for the actual gap at a point. -/
theorem gap_doubling_iterate {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete univ u) {ρ : ℝ} (hρ : 0 < ρ)
    (hbal : SectionBalance univ u ρ) (a x : Space n) (k : ℕ) :
    tangentHeight u a (a + (1 + ρ / 2) ^ k • (x - a)) ≤
      ((2 + ρ) * (1 + ρ) / ρ) ^ k * tangentHeight u a x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := (gap_doubling_of_sectionBalance isOpen_univ
      (convex_univ : Convex ℝ (univ : Set (Space n))) hu.contDiffOn
      (fun z _ => hp z) hc hρ hbal (mem_univ a)
      (mem_univ (a + (1 + ρ / 2) ^ k • (x - a)))).2
    simp only [add_sub_cancel_left, smul_smul] at he
    have hA : 0 ≤ (2 + ρ) * (1 + ρ) / ρ := by positivity
    calc
      _ ≤ ((2 + ρ) * (1 + ρ) / ρ) *
          tangentHeight u a (a + (1 + ρ / 2) ^ k • (x - a)) := by
        simpa only [pow_succ, mul_comm] using he
      _ ≤ ((2 + ρ) * (1 + ρ) / ρ) *
          (((2 + ρ) * (1 + ρ) / ρ) ^ k * tangentHeight u a x) :=
        mul_le_mul_of_nonneg_left ih hA
      _ = _ := by rw [pow_succ]; ring

/- Uniform normalized modulus, rigidity.tex:118–175. Every quantifier is
uniform in the normalized function, point and direction; only rho and R occur
in the explicit modulus. The section balance producer remains separate. -/
theorem normalized_modulus_of_sectionBalance {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hp : ∀ x, (hessian v x).PosDef)
    (hc : EuclideanGraphComplete univ v)
    (hzero : v 0 = 0) (hdzero : fderiv ℝ v 0 = 0)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R)
    (hbal : SectionBalance univ v ρ)
    (hinner : Metric.ball 0 1 ⊆ tangentSection univ v 0 1)
    (houter : tangentSection univ v 0 1 ⊆ Metric.ball 0 R)
    {x : Space n} (hx : x ∈ Metric.ball 0 (1 / 4)) {r : ℝ} (hr : 0 < r) :
    tangentSection univ v x (normalizedModulus ρ R r) ⊆ Metric.ball x r := by
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ
    (convex_univ : Convex ℝ (univ : Set (Space n))) hv.contDiffOn (fun z _ => (hp z).posSemidef)
  have hmin (a z : Space n) : 0 ≤ tangentHeight v a z := tangentHeight_nonneg
    isOpen_univ (convex_univ : Convex ℝ (univ : Set (Space n))) hv.contDiffOn
    (fun z _ => hp z) (mem_univ _) (mem_univ _)
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm]
  by_contra hh
  have hdist : r ≤ ‖z - x‖ := le_of_not_gt hh
  have hd : 0 < ‖z - x‖ := hr.trans_le hdist
  let e : Space n := ‖z - x‖⁻¹ • (z - x)
  have he : ‖e‖ = 1 := by simp [e, norm_smul, hd.ne']
  have hzrep : x + ‖z - x‖ • e = z := by simp [e, smul_smul, hd.ne']
  let N := modulusIterates ρ R r
  let β : ℝ := 1 + ρ / 2
  let A : ℝ := (2 + ρ) * (1 + ρ) / ρ
  have hA : 0 < A := by dsimp [A]; positivity
  have hrad := modulusIterates_spec hρ (zero_lt_one.trans_le hR) hr
  have hfixed := fixed_radius_gap_of_sectionBalance hv hp hc hzero hdzero hρ hρ1 hR
    hbal hinner houter (mem_ball_zero_iff.mp hx) he
  have hmono := tangentHeight_ray_mono hcv hmin x e (by positivity : 0 ≤ 2 * R / ρ) hrad
  have hdouble := gap_doubling_iterate hv hp hc hρ hbal x (x + r • e) N
  simp only [add_sub_cancel_left, smul_smul] at hdouble
  have hsmall : tangentHeight v x (x + r • e) ≤ tangentHeight v x z := by
    have heq := tangentHeight_ray_mono hcv hmin x e hr.le hdist
    rwa [hzrep] at heq
  have hbound : (1 / 4 : ℝ) ≤ A ^ N * tangentHeight v x z :=
    (hfixed.trans hmono).trans (hdouble.trans (mul_le_mul_of_nonneg_left hsmall (pow_nonneg hA.le _)))
  have hscale : 0 < 8 * A ^ N := by positivity
  have hgap := hz.2
  change tangentHeight v x z < 1 / (8 * A ^ N) at hgap
  have hgap' := (lt_div_iff₀ hscale).mp hgap
  nlinarith

/- The manuscript's epigraph; the domain is not silently replaced by all of space. -/
/- Literal tangent affine coordinates, ordered as one base direction and n
transverse directions. -/

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

lemma contDiffAt_logHessianDet {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) :
    ContDiffAt ℝ ∞ (logHessianDet u) x :=
  (contDiffAt_det_hessian hu).log (ne_of_gt hp.det_pos)

lemma contDiffOn_logHessianDet {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) : ContDiffOn ℝ ∞ (logHessianDet u) Ω := by
  intro x hx
  exact (contDiffAt_logHessianDet (hu.contDiffAt (hΩ.mem_nhds hx)) (hp x hx)).contDiffWithinAt

lemma affineMaximal_inverseHessianTrace_zero {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hm : AffineMaximalOn Ω u)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (affineWeight u) x = 0 := by
  have hh := hm x hx
  have he : (∑ i, ∑ j, cofactorHessian u x i j * hessian (affineWeight u) x i j) =
      (hessian u x).det * inverseHessianTrace u (affineWeight u) x := by
    simp only [cofactorHessian, Matrix.smul_apply, smul_eq_mul, inverseHessianTrace,
      Finset.mul_sum, mul_assoc]
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hp.det_pos)

lemma affineWeight_eq_exp_logHessianDet {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) :
    affineWeight u x = Real.exp (-(((n : ℝ)+1)/((n : ℝ)+2)) * logHessianDet u x) := by
  rw [affineWeight, Real.rpow_eq_pow, Real.rpow_def_of_pos hp.det_pos]
  simp only [logHessianDet, mul_comm]

/-- The exact logarithmic form of the original affine maximal equation.
It is derived from the frozen determinant exponent, not a replacement PDE. -/
theorem affineMaximal_logHessianDet_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    {x : Space n} (hx : x ∈ Ω) :
    inverseHessianTrace u (logHessianDet u) x =
      (((n : ℝ)+1)/((n : ℝ)+2)) *
        inverseHessianPair u (logHessianDet u) (logHessianDet u) x := by
  let a : ℝ := ((n : ℝ)+1)/((n : ℝ)+2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hφ := contDiffOn_logHessianDet hΩ hu hp
  have he : affineWeight u =ᶠ[𝓝 x] (fun y => Real.exp (-a * logHessianDet u y)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact affineWeight_eq_exp_logHessianDet (hp y hy)
  have hentry (i j : Fin n) : hessian (affineWeight u) x i j =
      Real.exp (-a * logHessianDet u x) *
        (-a * hessian (logHessianDet u) x i j + a^2 *
          dirDeriv (coordinateVector n i) (logHessianDet u) x *
          dirDeriv (coordinateVector n j) (logHessianDet u) x) := by
    change dirDeriv _ (dirDeriv _ (affineWeight u)) x = _
    rw [second_dirDeriv_congr he, second_dirDeriv_expMul hΩ hφ hx]
    simp only [neg_sq]
    rfl
  have htrace : inverseHessianTrace u (affineWeight u) x =
      Real.exp (-a * logHessianDet u x) *
        (-a * inverseHessianTrace u (logHessianDet u) x + a^2 *
          inverseHessianPair u (logHessianDet u) (logHessianDet u) x) := by
    simp only [inverseHessianTrace, inverseHessianPair, hentry,
      Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
      apply Finset.sum_congr rfl <;> intro j hj <;> ring
  rw [affineMaximal_inverseHessianTrace_zero hm hx (hp x hx)] at htrace
  have hz := (mul_eq_zero.mp htrace.symm).resolve_left (Real.exp_ne_zero _)
  change inverseHessianTrace u (logHessianDet u) x = a * _
  nlinarith

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

lemma inverseHessianTrace_dirDeriv {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) (k : Fin n) :
    inverseHessianTrace u (dirDeriv (coordinateVector n k) u) x =
      dirDeriv (coordinateVector n k) (logHessianDet u) x := by
  rw [dirDeriv_logHessianDet (hu.contDiffAt (hΩ.mem_nhds hx)) hp]
  simp only [inverseHessianTrace, hessian_dirDeriv hΩ hu hx]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LocalMaximumSecond
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

/-- The second-order necessary condition, proved from the local Taylor
remainder. No elliptic estimate is hidden in the maximum principle step. -/
lemma localMax_second_deriv_nonpos {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hm : IsLocalMax f 0) : deriv (deriv f) 0 ≤ 0 := by
  obtain ⟨U,hU,hc⟩ := hf.contDiffOn le_rfl (by norm_num)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  let I : Set ℝ := Ioo (-r) r
  have h0 : (0:ℝ) ∈ I := ⟨by linarith,hr⟩
  have hIU : I ⊆ U := by
    intro t ht
    apply hrU
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt] using (show -r < t ∧ t < r from ht)
  have hI : IsOpen I := isOpen_Ioo
  have hcI : ContDiffOn ℝ 2 f I := hc.mono hIU
  have hid (k : ℕ) (hk : k ≤ 2) : iteratedDerivWithin k f I 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hI.uniqueDiffOn (hf.of_le (by exact_mod_cast hk)) h0
  have hz := hm.deriv_eq_zero
  have hpoly (t : ℝ) : taylorWithinEval f 2 I 0 t =
      f 0 + (deriv (deriv f) 0 / 2) * t^2 := by
    simp only [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hid 0 (by omega),hid 1 (by omega),hid 2 (by omega)]
    simp only [iteratedDeriv_zero, iteratedDeriv_succ, hz,
      Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one,
      Nat.cast_mul, sub_zero, pow_zero, pow_one, smul_eq_mul]
    ring
  have ht := Real.taylor_tendsto (show Convex ℝ I from convex_Ioo _ _) h0 hcI
  rw [nhdsWithin_eq_nhds.mpr (hI.mem_nhds h0)] at ht
  simp only [hpoly,sub_zero] at ht
  have ht' := ht.mono_left (show 𝓝[≠] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have hle : (0:ℝ) ≤ -(deriv (deriv f) 0 / 2) := by
    apply le_of_tendsto ht'
    filter_upwards [hm.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hne
    have htne : t ≠ 0 := hne
    apply (div_le_iff₀ (sq_pos_of_ne_zero htne)).mpr
    nlinarith
  linarith

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LocalMaximumHessian
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

section LocalMaximumHessian
open Filter
open scoped Topology MatrixOrder

lemma deriv_affineLine_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (x v : E) (t : ℝ) (hf : DifferentiableAt ℝ f (x+t • v)) :
    deriv (fun s : ℝ => f (x+s • v)) t = dirDeriv v f (x+t • v) := by
  have hd : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1 <;> simp
    rfl
  exact (hf.hasFDerivAt.comp_hasDerivAt t hd).deriv

lemma localMax_second_fderiv_nonpos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hm : IsLocalMax f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let α : ℝ → E := fun t => x+t • v
  have hα : ContDiff ℝ ∞ α := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hα0 : α 0 = x := by simp [α]
  have hc : ContDiffAt ℝ ∞ (fun t => f (α t)) 0 := by
    exact (hα0 ▸ hf).comp 0 hα.contDiffAt
  have hl : IsLocalMax (fun t => f (α t)) 0 := by
    apply IsLocalMax.comp_continuous (g := α) (hα0 ▸ hm) hα.continuous.continuousAt
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  have hn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (h1.eventually (by simp)).mono (fun y hy => hy.differentiableAt (by simp))
  have hnl : Tendsto α (𝓝 0) (𝓝 x) := hα0 ▸ hα.continuous.continuousAt
  have he : deriv (fun t => f (α t)) =ᶠ[𝓝 0] (fun t => dirDeriv v f (α t)) := by
    filter_upwards [hnl.eventually hn] with t ht
    exact deriv_affineLine_comp x v t ht
  have h2 := localMax_second_deriv_nonpos (hc.of_le (by decide)) hl
  rw [he.deriv_eq] at h2
  have hd := deriv_affineLine_comp (f := dirDeriv v f) x v 0
    (by simpa only [zero_smul,add_zero] using
      (contDiffAt_dirDeriv hf v).differentiableAt (by simp))
  simp only [zero_smul,add_zero] at hd
  have hh : dirDeriv v (dirDeriv v f) x = fderiv ℝ (fderiv ℝ f) x v v :=
    dirDeriv_eq_second hf v v
  change deriv (fun t : ℝ => dirDeriv v f (x+t • v)) 0 ≤ 0 at h2
  rwa [hd,hh] at h2

lemma hessian_neg_posSemidef_of_localMax {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ ∞ f x) (hm : IsLocalMax f x) : (- hessian f x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.isHermitian_iff_isSymm.mpr (hessian_isSymm hf)).neg
  intro p
  let v : Space n := (WithLp.equiv 2 (Fin n → ℝ)).symm p
  have hn := localMax_second_fderiv_nonpos hf hm v
  rw [second_fderiv_eq_sum hf] at hn
  simpa [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,v] using neg_nonneg.mpr hn

lemma trace_mul_posSemidef_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let S := CFC.sqrt A
  have hS : Matrix.conjTranspose S = S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : S*S = A := by
    simpa only [pow_two] using CFC.sq_sqrt A hA.nonneg
  have hh := (hB.mul_mul_conjTranspose_same S).trace_nonneg
  rw [hS,Matrix.trace_mul_cycle,hSS] at hh
  exact hh

/-- A local maximum of a smooth test has nonpositive actual linearized
Monge--Ampère trace at every positive Hessian point. -/
lemma inverseHessianTrace_nonpos_of_localMax {n : ℕ} {u f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ ∞ f x) (hp : (hessian u x).PosDef) (hm : IsLocalMax f x) :
    inverseHessianTrace u f x ≤ 0 := by
  have hh := trace_mul_posSemidef_nonneg hp.posSemidef.inv (hessian_neg_posSemidef_of_localMax hf hm)
  have hs := hessian_isSymm hf
  have he : ((hessian u x)⁻¹ * (-hessian f x)).trace = - inverseHessianTrace u f x := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.neg_apply,
      mul_neg,Finset.sum_neg_distrib,inverseHessianTrace]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs.apply i j]
  rw [he] at hh
  linarith

end LocalMaximumHessian


end
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

lemma second_dirDeriv_log_of_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (hneg : ∀ y ∈ Ω, f y < 0) {x : E} (hx : x ∈ Ω) (v w : E) :
    dirDeriv v (dirDeriv w (fun y => Real.log (f y))) x =
      dirDeriv v (dirDeriv w f) x / f x - dirDeriv v f x * dirDeriv w f x / (f x)^2 := by
  have hn : f x ≠ 0 := ne_of_lt (hneg x hx)
  have hfn : ContDiffOn ℝ ∞ (fun y => -1 * f y) Ω := contDiffOn_const.mul hf
  have hpn : ∀ y ∈ Ω, 0 < (-1:ℝ)*f y := by intro y hy; nlinarith [hneg y hy]
  have he : (fun y => Real.log ((-1:ℝ)*f y)) = (fun y => Real.log (f y)) := by
    funext y
    simp only [neg_one_mul,Real.log_neg_eq_log]
  have hh := log_second_identity hΩ hfn hpn hx v w
  rw [he,second_dirDeriv_const_mul hΩ hf hx,
    dirDeriv_real_log ((hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) hn,
    dirDeriv_real_log ((hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) hn] at hh
  linear_combination (norm := (field_simp [hn]; ring_nf)) ((f x)⁻¹) * hh

lemma inverseHessianTrace_self {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) : inverseHessianTrace u u x = n := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hp.isHermitian
  have hh := matrix_inverse_contraction_self (ne_of_gt hp.det_pos)
  rw [Finset.sum_comm] at hh
  simpa only [inverseHessianTrace,hs.apply,Fintype.card_fin] using hh

lemma inverseHessianTrace_add {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u f g : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    {x : Space n} (hx : x ∈ Ω) :
    inverseHessianTrace u (fun y => f y + g y) x =
      inverseHessianTrace u f x + inverseHessianTrace u g x := by
  simp only [inverseHessianTrace,hessian_add_on hΩ hf hg hx,Matrix.add_apply,
    mul_add,Finset.sum_add_distrib]

lemma inverseHessianTrace_const_mul {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) {x : Space n} (hx : x ∈ Ω) (c : ℝ) :
    inverseHessianTrace u (fun y => c * f y) x = c * inverseHessianTrace u f x := by
  simp only [inverseHessianTrace,hessian_const_mul hΩ hf c hx,Matrix.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma inverseHessianPair_symm {n : ℕ} {u f g : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) : inverseHessianPair u f g x = inverseHessianPair u g f x := by
  unfold inverseHessianPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [(inverseHessian_isSymm hp).apply i j]
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

lemma inverseHessianPair_grad_linear {n : ℕ} {u f g h : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (k l : ℝ)
    (he : ∀ i : Fin n, dirDeriv (coordinateVector n i) h x =
      k * dirDeriv (coordinateVector n i) f x + l * dirDeriv (coordinateVector n i) g x) :
    inverseHessianPair u h h x = k^2 * inverseHessianPair u f f x +
      2*k*l*inverseHessianPair u g f x + l^2 * inverseHessianPair u g g x := by
  have hh : inverseHessianPair u h h x = k^2 * inverseHessianPair u f f x +
      k*l*inverseHessianPair u f g x + k*l*inverseHessianPair u g f x +
      l^2 * inverseHessianPair u g g x := by
    unfold inverseHessianPair
    simp only [he,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [inverseHessianPair_symm hp (f := f) (g := g)] at hh
  rw [hh]
  ring

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DetBarrierPhase
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

section DetBarrierPhase

lemma posSemidef_det_le_trace_pow {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : A.det ≤ A.trace ^ n := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues,hA.isHermitian.trace_eq_sum_eigenvalues]
  calc
    _ ≤ ∏ _i : Fin n, (∑ j, hA.isHermitian.eigenvalues j) := by
      apply Finset.prod_le_prod
      · intro index _
        exact hA.eigenvalues_nonneg index
      · intro index hindex
        exact Finset.single_le_sum (fun entry _ => hA.eigenvalues_nonneg entry) hindex
    _ = _ := by simp

end DetBarrierPhase


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DualHeightCalculus
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

section DualHeightCalculus
open Filter
open scoped Topology

lemma dualHeight_expansion {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    dualHeight u x = (∑ k, x k * dirDeriv (coordinateVector n k) u x) + u 0 - u x := by
  simp only [dualHeight,tangentHeight,zero_sub,map_neg,sub_neg_eq_add]
  rw [clm_coordinate_sum]
  simp only [dirDeriv]
  ring

lemma contDiffOn_dualHeight {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) : ContDiffOn ℝ ∞ (dualHeight u) Ω := by
  have he : dualHeight u = fun x => (∑ k, x k * dirDeriv (coordinateVector n k) u x) + u 0 - u x :=
    funext (dualHeight_expansion u)
  rw [he]
  exact ((ContDiffOn.sum fun k _ => (coordinateProjection n k).contDiff.contDiffOn.mul
    (contDiffOn_dirDeriv hΩ hu _)).add contDiffOn_const).sub hu

lemma dirDeriv_coordinate {n : ℕ} (i k : Fin n) (x : Space n) :
    dirDeriv (coordinateVector n i) (fun y : Space n => y k) x = if i=k then 1 else 0 := by
  change (fderiv ℝ (coordinateProjection n k) x) _ = _
  rw [ContinuousLinearMap.fderiv]
  simp [coordinateVector,eq_comm]

lemma dirDeriv_dualHeight {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    dirDeriv (coordinateVector n i) (dualHeight u) x =
      ∑ k, x k * hessian u x i k := by
  have he : dualHeight u = fun y => (∑ k, y k * dirDeriv (coordinateVector n k) u y) + u 0 - u y :=
    funext (dualHeight_expansion u)
  rw [he]
  have hk (k : Fin n) := (contDiffAt_dirDeriv hu (coordinateVector n k)).differentiableAt (by simp)
  have hd := hu.differentiableAt (by simp)
  have hc (k : Fin n) : DifferentiableAt ℝ (fun y : Space n => y k) x := (coordinateProjection n k).differentiableAt
  have hs : DifferentiableAt ℝ (fun y : Space n => ∑ k, y k * dirDeriv (coordinateVector n k) u y) x :=
    DifferentiableAt.fun_sum (u := Finset.univ) fun k _ => (hc k).mul (hk k)
  rw [dirDeriv_sub (hs.add_const _) hd]
  have ha : dirDeriv (coordinateVector n i)
      (fun y : Space n => (∑ k, y k * dirDeriv (coordinateVector n k) u y) + u 0) x =
      dirDeriv (coordinateVector n i) (fun y => ∑ k, y k * dirDeriv (coordinateVector n k) u y) x := by
    unfold dirDeriv
    rw [fderiv_add_const]
  rw [ha,dirDeriv_sum (fun (k : Fin n) (y : Space n) => y k * dirDeriv (coordinateVector n k) u y)
    (fun k => (coordinateProjection n k).differentiableAt.mul (hk k))]
  have hterm (k : Fin n) :
      dirDeriv (coordinateVector n i) (fun y : Space n => y k * dirDeriv (coordinateVector n k) u y) x =
        (if i=k then 1 else 0) * dirDeriv (coordinateVector n k) u x + x k * hessian u x i k := by
    rw [dirDeriv_mul (hc k) (hk k),dirDeriv_coordinate]
    rfl
  simp only [hterm,Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq]

lemma contDiff_positionEnergy {n : ℕ} : ContDiff ℝ ∞ (@positionEnergy n) :=
  contDiff_const.mul (ContDiff.sum fun k _ => (coordinateProjection n k).contDiff.pow 2)

lemma dirDeriv_positionEnergy {n : ℕ} (x : Space n) (i : Fin n) :
    dirDeriv (coordinateVector n i) positionEnergy x = x i := by
  change dirDeriv _ (fun y : Space n => (1/2:ℝ)*∑ k, (y k)^2) x = _
  have hs : ContDiffAt ℝ ∞ (fun y : Space n => ∑ k, (y k)^2) x :=
    ContDiffAt.sum fun k _ => (coordinateProjection n k).contDiff.contDiffAt.pow 2
  rw [dirDeriv_const_mul (hs.differentiableAt (by simp)),
    dirDeriv_sum (fun (k : Fin n) (y : Space n) => (y k)^2)
      (fun k => (coordinateProjection n k).differentiableAt.pow 2)]
  have hc (k : Fin n) : DifferentiableAt ℝ (fun y : Space n => y k) x := (coordinateProjection n k).differentiableAt
  have ht (k : Fin n) : dirDeriv (coordinateVector n i) (fun y : Space n => (y k)^2) x =
      2*x k*(if i=k then 1 else 0) := by
    simp only [pow_two]
    rw [dirDeriv_mul (hc k) (hc k),dirDeriv_coordinate]
    ring
  simp only [ht]
  simp [mul_ite,Finset.sum_ite_eq]

lemma hessian_positionEnergy {n : ℕ} (x : Space n) : hessian positionEnergy x = 1 := by
  ext i j
  change dirDeriv _ (dirDeriv _ positionEnergy) x = _
  rw [show dirDeriv (coordinateVector n j) positionEnergy = (fun y : Space n => y j) from
    funext (fun y => dirDeriv_positionEnergy y j),dirDeriv_coordinate]
  rfl

lemma inverseHessianTrace_positionEnergy {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    inverseHessianTrace u positionEnergy x = (hessian u x)⁻¹.trace := by
  simp [inverseHessianTrace,hessian_positionEnergy,Matrix.one_apply,Matrix.trace,Matrix.diag_apply]

lemma inverseHessianPair_dualHeight {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (f : Space n → ℝ) :
    inverseHessianPair u (dualHeight u) f x =
      ∑ k, x k * dirDeriv (coordinateVector n k) f x := by
  unfold inverseHessianPair
  simp_rw [dirDeriv_dualHeight hu]
  have hs := Matrix.isHermitian_iff_isSymm.mp hp.isHermitian
  have he (i : Fin n) : (∑ k, x k * hessian u x i k) = ∑ k, x k * hessian u x k i := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hs.apply k i]
  simp only [he]
  exact inverse_radial_contraction hp _ _

lemma inverseHessianTrace_dualHeight {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (dualHeight u) x = (n:ℝ) +
      ∑ k, x k * dirDeriv (coordinateVector n k) (logHessianDet u) x := by
  have hk (k : Fin n) := contDiffOn_dirDeriv hΩ hu (coordinateVector n k)
  have hc (k : Fin n) : ContDiffOn ℝ ∞ (fun y : Space n => y k) Ω :=
    (coordinateProjection n k).contDiff.contDiffOn
  have he : dualHeight u = fun y => (∑ k, y k * dirDeriv (coordinateVector n k) u y) + u 0 - u y :=
    funext (dualHeight_expansion u)
  rw [he]
  have hsum : ContDiffOn ℝ ∞ (fun y : Space n => ∑ k, y k * dirDeriv (coordinateVector n k) u y) Ω :=
    ContDiffOn.sum (fun k _ => (hc k).mul (hk k))
  have hm (i j : Fin n) : hessian (fun y => (∑ k, y k * dirDeriv (coordinateVector n k) u y) + u 0 - u y) x i j =
      (∑ k, hessian (fun y => y k * dirDeriv (coordinateVector n k) u y) x i j) - hessian u x i j := by
    rw [hessian_sub_on hΩ (hsum.add contDiffOn_const) hu hx,hessian_add_constant]
    simp only [Matrix.sub_apply,hessian_sum_on hΩ (fun k => (hc k).mul (hk k)) hx]
  change (∑ i, ∑ j, (hessian u x)⁻¹ i j * _) = _
  simp only [hm,mul_sub,Finset.sum_sub_distrib]
  have ht (k : Fin n) : (∑ i, ∑ j, (hessian u x)⁻¹ i j *
      hessian (fun y => y k * dirDeriv (coordinateVector n k) u y) x i j) =
        x k * dirDeriv (coordinateVector n k) (logHessianDet u) x + 2 := by
    rw [hessian_product_trace hΩ (hc k) (hk k) hx (inverseHessian_isSymm hp)]
    change dirDeriv (coordinateVector n k) u x * inverseHessianTrace u (fun y => y k) x +
      x k * inverseHessianTrace u (dirDeriv (coordinateVector n k) u) x +
      2 * inverseHessianPair u (fun y => y k) (dirDeriv (coordinateVector n k) u) x = _
    rw [inverseHessianTrace_dirDeriv hΩ hu hx hp]
    have hz : inverseHessianTrace u (fun y => y k) x = 0 := by
      simp [inverseHessianTrace,hessian_coordinate]
    have hq : inverseHessianPair u (fun y => y k) (dirDeriv (coordinateVector n k) u) x = 1 := by
      unfold inverseHessianPair
      simp only [dirDeriv_coordinate]
      simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      change (∑ j, (hessian u x)⁻¹ k j * hessian u x j k) = 1
      have HH := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k k)
        (Matrix.nonsing_inv_mul (hessian u x) (isUnit_iff_ne_zero.mpr (ne_of_gt hp.det_pos)))
      simpa only [Matrix.mul_apply,Matrix.one_apply_eq] using HH
    rw [hz,hq]
    ring
  have hex : (∑ i, ∑ j, (hessian u x)⁻¹ i j *
      ∑ k, hessian (fun y => y k * dirDeriv (coordinateVector n k) u y) x i j) =
      ∑ k, (x k * dirDeriv (coordinateVector n k) (logHessianDet u) x + 2) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_comm,ht]
  rw [hex]
  change (∑ k, (_+2)) - inverseHessianTrace u u x = _
  rw [inverseHessianTrace_self hp,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end DualHeightCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DualDetBarrier
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

section DualDetBarrier
open Filter
open scoped Topology

lemma dirDeriv_dualCutoff {n : ℕ} (u : Space n → ℝ) (h : ℝ) (x : Space n) (i : Fin n) :
    dirDeriv (coordinateVector n i) (dualCutoff u h) x =
      dirDeriv (coordinateVector n i) (dualHeight u) x := by
  unfold dirDeriv dualCutoff
  rw [fderiv_sub_const]

lemma hessian_dualCutoff {n : ℕ} (u : Space n → ℝ) (h : ℝ) (x : Space n) :
    hessian (dualCutoff u h) x = hessian (dualHeight u) x := by
  have he : dualCutoff u h = fun y => dualHeight u y + (-h) := by funext y; simp [dualCutoff,sub_eq_add_neg]
  rw [he,hessian_add_constant]

lemma contDiffOn_dualCutoff {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (h : ℝ) :
    ContDiffOn ℝ ∞ (dualCutoff u h) Ω := (contDiffOn_dualHeight hΩ hu).sub contDiffOn_const

lemma inverseHessianPair_dualCutoff {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (h : ℝ) (f : Space n → ℝ) :
    inverseHessianPair u (dualCutoff u h) f x =
      ∑ k, x k * dirDeriv (coordinateVector n k) f x := by
  have he : inverseHessianPair u (dualCutoff u h) f x = inverseHessianPair u (dualHeight u) f x := by
    simp only [inverseHessianPair,dirDeriv_dualCutoff]
  rw [he,inverseHessianPair_dualHeight hu hp]

lemma inverseHessianTrace_log_function {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u f : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hneg : ∀ y ∈ Ω, f y < 0)
    {x : Space n} (hx : x ∈ Ω) :
    inverseHessianTrace u (fun y => Real.log (f y)) x =
      inverseHessianTrace u f x / f x - inverseHessianPair u f f x / (f x)^2 := by
  have he (i j : Fin n) : hessian (fun y => Real.log (f y)) x i j =
      hessian f x i j / f x -
        dirDeriv (coordinateVector n i) f x * dirDeriv (coordinateVector n j) f x / (f x)^2 :=
    second_dirDeriv_log_of_neg hΩ hf hneg hx _ _
  simp only [inverseHessianTrace,inverseHessianPair,he,mul_sub,Finset.sum_sub_distrib,
    Finset.sum_div,mul_div_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma contDiffOn_dualDetBarrier {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (h β γ : ℝ)
    (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) : ContDiffOn ℝ ∞ (dualDetBarrier u h β γ) Ω :=
  ((contDiffOn_const.mul (contDiffOn_logHessianDet hΩ hu hp)).add
    (contDiffOn_const.mul ((contDiffOn_dualCutoff hΩ hu h).log (fun x hx => ne_of_lt (hneg x hx))))).add
      (contDiffOn_const.mul contDiff_positionEnergy.contDiffOn)

lemma dualDetBarrier_critical_gradient {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (hp : (hessian u x).PosDef) (h β γ : ℝ) (hn : dualCutoff u h x ≠ 0)
    (hm : IsLocalMax (dualDetBarrier u h β γ) x) (i : Fin n) :
    dirDeriv (coordinateVector n i) (logHessianDet u) x =
      (β/dualCutoff u h x)*dirDeriv (coordinateVector n i) (dualCutoff u h) x +
        γ*dirDeriv (coordinateVector n i) positionEnergy x := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds hx)
  have hφ := (contDiffAt_logHessianDet hu' hp).differentiableAt (by simp)
  have hv := ((contDiffOn_dualCutoff hΩ hu h).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  have hP := contDiff_positionEnergy.differentiable (by simp) x
  have hd := (((hφ.hasFDerivAt.const_mul (-1)).add
    ((hv.log hn).hasFDerivAt.const_mul β)).add (hP.hasFDerivAt.const_mul γ)).fderiv
  have hz : dirDeriv (coordinateVector n i) (dualDetBarrier u h β γ) x = 0 := by
    simp only [dirDeriv,hm.fderiv_eq_zero,zero_apply]
  change (fderiv ℝ (fun y => (-1:ℝ)*logHessianDet u y + β*Real.log (dualCutoff u h y) +
    γ*positionEnergy y) x) (coordinateVector n i) = 0 at hz
  change fderiv ℝ (fun y => (-1:ℝ)*logHessianDet u y + β*Real.log (dualCutoff u h y) +
    γ*positionEnergy y) x = _ at hd
  rw [hd] at hz
  simp only [add_apply,smul_apply,smul_eq_mul] at hz
  change (-1:ℝ)*dirDeriv _ (logHessianDet u) x +
    β*dirDeriv _ (fun y => Real.log (dualCutoff u h y)) x + γ*dirDeriv _ positionEnergy x = 0 at hz
  rw [dirDeriv_real_log hv hn] at hz
  linear_combination (norm := ring_nf) -hz

lemma inverseHessianTrace_dualDetBarrier {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) {x : Space n} (hx : x ∈ Ω) (β γ : ℝ) :
    inverseHessianTrace u (dualDetBarrier u h β γ) x =
      -(((n:ℝ)+1)/((n:ℝ)+2))*inverseHessianPair u (logHessianDet u) (logHessianDet u) x +
      β*(((n:ℝ) + ∑ k, x k * dirDeriv (coordinateVector n k) (logHessianDet u) x)/dualCutoff u h x -
        inverseHessianPair u (dualCutoff u h) (dualCutoff u h) x/(dualCutoff u h x)^2) +
      γ*(hessian u x)⁻¹.trace := by
  have hφ := contDiffOn_logHessianDet hΩ hu hp
  have hl := (contDiffOn_dualCutoff hΩ hu h).log (fun x hx => ne_of_lt (hneg x hx))
  unfold dualDetBarrier
  rw [inverseHessianTrace_add hΩ ((contDiffOn_const.mul hφ).add (contDiffOn_const.mul hl))
      (contDiffOn_const.mul contDiff_positionEnergy.contDiffOn) hx,
    inverseHessianTrace_add hΩ (contDiffOn_const.mul hφ) (contDiffOn_const.mul hl) hx,
    inverseHessianTrace_const_mul hΩ hφ hx,inverseHessianTrace_const_mul hΩ hl hx,
    inverseHessianTrace_const_mul hΩ contDiff_positionEnergy.contDiffOn hx,
    affineMaximal_logHessianDet_equation hΩ hu hp hm hx,
    inverseHessianTrace_log_function hΩ (contDiffOn_dualCutoff hΩ hu h) hneg hx,
    inverseHessianTrace_positionEnergy]
  have he : inverseHessianTrace u (dualCutoff u h) x = inverseHessianTrace u (dualHeight u) x := by
    simp only [inverseHessianTrace,hessian_dualCutoff]
  rw [he,inverseHessianTrace_dualHeight hΩ hu hx (hp x hx)]
  ring

lemma inverseHessianPair_position_le_trace {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) :
    inverseHessianPair u positionEnergy positionEnergy x ≤ (hessian u x)⁻¹.trace * positionSquared x := by
  have he : inverseHessianPair u positionEnergy positionEnergy x =
      (fun i => x i) ⬝ᵥ (hessian u x)⁻¹.mulVec (fun i => x i) := by
    simp only [inverseHessianPair,dirDeriv_positionEnergy,dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  exact posSemidef_quadratic_le_trace_mul_sq hp.posSemidef.inv _

/-- Exact pulled-back dual equation at a critical point. The Q term cancels
for β=n+2, retaining the original (n+1)/(n+2) exponent. -/
lemma dualDetBarrier_peak_identity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) {x : Space n} (hx : x ∈ Ω) (γ : ℝ)
    (hmax : IsLocalMax (dualDetBarrier u h ((n:ℝ)+2) γ) x) :
    inverseHessianTrace u (dualDetBarrier u h ((n:ℝ)+2) γ) x =
      γ*(hessian u x)⁻¹.trace - (((n:ℝ)+1)/((n:ℝ)+2))*γ^2 *
        inverseHessianPair u positionEnergy positionEnergy x +
      ((n:ℝ)*((n:ℝ)+2) - γ*(n:ℝ)*positionSquared x)/dualCutoff u h x := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds hx)
  have hn : dualCutoff u h x ≠ 0 := ne_of_lt (hneg x hx)
  have hcrit := dualDetBarrier_critical_gradient hΩ hu hx (hp x hx) h ((n:ℝ)+2) γ hn hmax
  have hpair := inverseHessianPair_grad_linear (hp x hx) (((n:ℝ)+2)/dualCutoff u h x) γ hcrit
  have hcross : inverseHessianPair u positionEnergy (dualCutoff u h) x = positionSquared x := by
    rw [inverseHessianPair_symm (hp x hx),inverseHessianPair_dualCutoff hu' (hp x hx)]
    simp only [dirDeriv_positionEnergy,positionSquared,pow_two]
  rw [hcross] at hpair
  have hrad : (∑ k, x k * dirDeriv (coordinateVector n k) (logHessianDet u) x) =
      (((n:ℝ)+2)/dualCutoff u h x)*inverseHessianPair u (dualCutoff u h) (dualCutoff u h) x +
        γ*positionSquared x := by
    rw [inverseHessianPair_dualCutoff hu' (hp x hx)]
    simp only [hcrit,Finset.mul_sum,← Finset.sum_add_distrib,positionSquared,dirDeriv_positionEnergy,pow_two]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [inverseHessianTrace_dualDetBarrier hΩ hu hp hm h hneg hx,hpair,hrad]
  have hd : (n:ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

end DualDetBarrier


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DualDetBound
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

section DualDetBound

lemma dualDetBarrier_peak_trace_algebra {N T P R v γ : ℝ}
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hP : 0 ≤ P)
    (hv : v < 0) (hγ : 0 < γ) (hRP : R ≤ T * P) (hγP : γ*P ≤ 1/2)
    (hpeak : γ*T - ((N+1)/(N+2))*γ^2*R + (N*(N+2)-γ*N*P)/v ≤ 0) :
    (-v)*T ≤ 2*N*(N+2)/γ := by
  have hden : 0 < N+2 := by linarith
  have ha : 0 ≤ (N+1)/(N+2) := by positivity
  have ha1 : (N+1)/(N+2) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hc : 0 ≤ ((N+1)/(N+2))*γ^2 := by positivity
  have hsmall : ((N+1)/(N+2))*γ^2*P ≤ γ/2 := by
    calc
      _ = ((N+1)/(N+2))*γ*(γ*P) := by ring
      _ ≤ ((N+1)/(N+2))*γ*(1/2) := mul_le_mul_of_nonneg_left hγP (by positivity)
      _ ≤ γ/2 := by nlinarith [mul_le_mul_of_nonneg_right ha1 hγ.le]
  have hex : ((N+1)/(N+2))*γ^2*R ≤ T*(γ/2) := by
    calc
      _ ≤ ((N+1)/(N+2))*γ^2*(T*P) := mul_le_mul_of_nonneg_left hRP hc
      _ = T*(((N+1)/(N+2))*γ^2*P) := by ring
      _ ≤ T*(γ/2) := mul_le_mul_of_nonneg_left hsmall hT
  have hdrop : γ*N*P/v ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hv.le
  have hm : γ*T/2 + N*(N+2)/v ≤ 0 := by rw [sub_div] at hpeak; linarith
  have hprod := mul_le_mul_of_nonneg_left hm (le_of_lt (neg_pos.mpr hv))
  have hv0 : v ≠ 0 := ne_of_lt hv
  have hsimp : (-v)*(γ*T/2 + N*(N+2)/v) = (-v)*γ*T/2 - N*(N+2) := by field_simp; ring
  rw [hsimp,mul_zero] at hprod
  apply (le_div_iff₀ hγ).mpr
  nlinarith

lemma dualDetBarrier_peak_trace_bound {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) {x : Space n} (hx : x ∈ Ω) {γ : ℝ}
    (hγ : 0 < γ) (hsmall : γ * positionSquared x ≤ 1/2)
    (hmax : IsLocalMax (dualDetBarrier u h ((n:ℝ)+2) γ) x) :
    (-dualCutoff u h x) * (hessian u x)⁻¹.trace ≤ 2*(n:ℝ)*((n:ℝ)+2)/γ := by
  have hb := (contDiffOn_dualDetBarrier hΩ hu hp h ((n:ℝ)+2) γ hneg).contDiffAt
    (hΩ.mem_nhds hx)
  have hnon := inverseHessianTrace_nonpos_of_localMax hb (hp x hx) hmax
  rw [dualDetBarrier_peak_identity hΩ hu hp hm h hneg hx γ hmax] at hnon
  have ht : 0 ≤ (hessian u x)⁻¹.trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun _ _ => (hp x hx).posSemidef.inv.diag_nonneg)
  exact dualDetBarrier_peak_trace_algebra (Nat.cast_nonneg n) ht
    (Finset.sum_nonneg (fun coordinate _ => sq_nonneg (x coordinate)))
    (hneg x hx) hγ (inverseHessianPair_position_le_trace (hp x hx)) hsmall hnon

end DualDetBound


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DualDetPhase
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

section DualDetPhase

lemma dualDetPhase_eq_exp {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) {h : ℝ} (hn : dualCutoff u h x < 0) (γ : ℝ) :
    dualDetPhase u h γ x = Real.exp (dualDetBarrier u h ((n:ℝ)+2) γ x) := by
  unfold dualDetPhase dualDetBarrier logHessianDet
  rw [Real.exp_add,Real.exp_add,neg_one_mul,Real.exp_neg,Real.exp_log hp.det_pos]
  rw [← Real.log_neg_eq_log (dualCutoff u h x)]
  congr 2
  have hh := Real.exp_nat_mul (Real.log (-dualCutoff u h x)) (n+2)
  rw [Real.exp_log (neg_pos.mpr hn)] at hh
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh.symm

lemma dualDetPhase_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) {h : ℝ} (hn : dualCutoff u h x < 0) (γ : ℝ) :
    0 < dualDetPhase u h γ x := by
  rw [dualDetPhase_eq_exp hp hn]
  exact Real.exp_pos _

lemma continuousOn_dualDetPhase {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (h γ : ℝ) :
    ContinuousOn (dualDetPhase u h γ) Ω := by
  have hh : ContinuousOn (fun x => (hessian u x).det) Ω := by
    intro x hx
    exact (contDiffAt_det_hessian (hu.contDiffAt (hΩ.mem_nhds hx))).continuousAt.continuousWithinAt
  exact (((hh.inv₀ (fun x hx => ne_of_gt (hp x hx).det_pos)).mul
    ((contDiffOn_dualCutoff hΩ hu h).continuousOn.neg.pow (n+2))).mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul contDiff_positionEnergy.continuous.continuousOn)))

lemma dualDetPhase_peak_bound {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0) {x : Space n} (hx : x ∈ Ω)
    {γ M D : ℝ} (hγ : 0 < γ) (_ : 0 ≤ M) (_ : 0 ≤ D)
    (hsmall : γ*M ≤ 1/2) (hrad : positionSquared x ≤ M) (hdepth : -dualCutoff u h x ≤ D)
    (hmax : IsLocalMax (dualDetBarrier u h ((n:ℝ)+2) γ) x) :
    dualDetPhase u h γ x ≤ (2*(n:ℝ)*((n:ℝ)+2)/γ)^n * D^2 * Real.exp (γ*M/2) := by
  have hd : 0 < -dualCutoff u h x := neg_pos.mpr (hneg x hx)
  have ht : 0 ≤ (hessian u x)⁻¹.trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun _ _ => (hp x hx).posSemidef.inv.diag_nonneg)
  have hc : 0 ≤ 2*(n:ℝ)*((n:ℝ)+2)/γ := by positivity
  have hsm : γ * positionSquared x ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hrad hγ.le).trans hsmall
  have htrace := dualDetBarrier_peak_trace_bound hΩ hu hp hm h hneg hx hγ hsm hmax
  have hpow := pow_le_pow_left₀ (mul_nonneg hd.le ht) htrace n
  have hdet : ((hessian u x).det)⁻¹ ≤ (hessian u x)⁻¹.trace^n := by
    have H := posSemidef_det_le_trace_pow (hp x hx).posSemidef.inv
    simpa only [Matrix.det_nonsing_inv,Ring.inverse_eq_inv] using H
  have he : γ*positionEnergy x ≤ γ*M/2 := by
    change γ*((1/2)*positionSquared x) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hrad hγ.le]
  unfold dualDetPhase
  calc
    _ ≤ (hessian u x)⁻¹.trace^n * (-dualCutoff u h x)^(n+2) * Real.exp (γ*positionEnergy x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdet (by positivity)) (Real.exp_pos _).le
    _ = ((-dualCutoff u h x)*(hessian u x)⁻¹.trace)^n * (-dualCutoff u h x)^2 * Real.exp (γ*positionEnergy x) := by
      rw [pow_add,mul_pow]
      ring
    _ ≤ (2*(n:ℝ)*((n:ℝ)+2)/γ)^n * D^2 * Real.exp (γ*M/2) := by
      apply mul_le_mul
      · exact mul_le_mul hpow (pow_le_pow_left₀ hd.le hdepth 2) (sq_nonneg _) (pow_nonneg hc n)
      · exact Real.exp_le_exp.mpr he
      · exact (Real.exp_pos _).le
      · positivity

end DualDetPhase


end
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

end TangentShiftCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DualDetCompact
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

section DualDetCompact
open Filter
open scoped Topology

lemma affineMaximal_dual_det_phase_bound {n : ℕ} {V Ω K : Set (Space n)}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hΩK : Ω ⊆ K) (hKV : K ⊆ V) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (hp : ∀ x ∈ V, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (h : ℝ) (hneg : ∀ x ∈ Ω, dualCutoff u h x < 0)
    (hbd : ∀ x ∈ K, x ∉ Ω → dualCutoff u h x = 0)
    {γ M D : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hsmall : γ*M ≤ 1/2) (hrad : ∀ x ∈ Ω, positionSquared x ≤ M)
    (hdepth : ∀ x ∈ Ω, -dualCutoff u h x ≤ D) {x : Space n} (hx : x ∈ Ω) :
    dualDetPhase u h γ x ≤ (2*(n:ℝ)*((n:ℝ)+2)/γ)^n * D^2 * Real.exp (γ*M/2) := by
  obtain ⟨y,hyK,hymax⟩ := hK.exists_isMaxOn ⟨x,hΩK hx⟩
    ((continuousOn_dualDetPhase hV hu hp h γ).mono hKV)
  have hxy : dualDetPhase u h γ x ≤ dualDetPhase u h γ y := hymax (hΩK hx)
  have hyp : 0 < dualDetPhase u h γ y :=
    (dualDetPhase_pos (hp x (hKV (hΩK hx))) (hneg x hx) γ).trans_le hxy
  have hy : y ∈ Ω := by
    by_contra hn
    have hz : dualDetPhase u h γ y = 0 := by simp [dualDetPhase,hbd y hyK hn]
    rw [hz] at hyp
    exact (lt_irrefl 0) hyp
  have hmax : IsLocalMax (dualDetBarrier u h ((n:ℝ)+2) γ) y := by
    filter_upwards [hΩ.mem_nhds hy] with z hz
    apply Real.exp_le_exp.mp
    rw [← dualDetPhase_eq_exp (hp z (hKV (hΩK hz))) (hneg z hz) γ,
      ← dualDetPhase_eq_exp (hp y (hKV hyK)) (hneg y hy) γ]
    exact hymax (hΩK hz)
  exact hxy.trans (dualDetPhase_peak_bound hΩ (hu.mono (hΩK.trans hKV))
    (fun z hz => hp z (hKV (hΩK hz))) hm h hneg hy hγ hM hD hsmall
    (hrad y hy) (hdepth y hy) hmax)

lemma positionSquared_eq_norm_sq {n : ℕ} (x : Space n) : positionSquared x = ‖x‖^2 := by
  simpa only [positionSquared,Real.norm_eq_abs,sq_abs] using (EuclideanSpace.norm_sq_eq x).symm

lemma dualHeight_zero {n : ℕ} (u : Space n → ℝ) : dualHeight u 0 = 0 := by
  simp [dualHeight,tangentHeight]

/-- Determinant lower estimate from the original PDE and the genuinely
geometric, all-base section modulus. The dual section is pulled back to
primal coordinates, avoiding any assumed Legendre-PDE regularity. -/
lemma affineMaximal_det_inverse_upper_of_modulus {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hcv : Convex ℝ O) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (hp : ∀ x ∈ O, (hessian u x).PosDef)
    (hm : AffineMaximalOn O u) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0:Space n) r ⊆ O) (b : ℝ → ℝ)
    (hb : 0 < b r) (hmod : HasLowerSectionModulus O u b) :
    ((hessian u 0).det)⁻¹ ≤
      (2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)))^n * (b r/2)^2 *
        Real.exp (r^2/(4*(r^2+1))) / (b r/2)^(n+2) := by
  let h := b r/2
  let Ω := O ∩ (dualHeight u) ⁻¹' Iio h
  let K := Metric.closedBall (0:Space n) r ∩ (dualHeight u) ⁻¹' Iic h
  have hh : 0 < h := half_pos hb
  have h0 : (0:Space n) ∈ O := hball (Metric.mem_closedBall_self hr.le)
  have hc := (contDiffOn_dualHeight hO hu).continuousOn
  have hΩ : IsOpen Ω := hc.isOpen_inter_preimage hO isOpen_Iio
  have hΩr : Ω ⊆ Metric.ball 0 r := by
    intro x hx
    have hs : (0:Space n) ∈ tangentSection O u x (b r) := by
      refine ⟨h0,?_⟩
      have HH : dualHeight u x < h := hx.2
      change tangentHeight u x 0 < b r
      change dualHeight u x < b r
      exact HH.trans (by dsimp [h]; linarith)
    have H := hmod x hx.1 r hr hs
    simpa only [Metric.mem_ball,dist_comm] using H
  have hΩK : Ω ⊆ K := fun x hx => ⟨Metric.ball_subset_closedBall (hΩr hx),(show dualHeight u x < h from hx.2).le⟩
  have hKO : K ⊆ O := fun _ hx => hball hx.1
  have hK : IsCompact K := (isCompact_closedBall (0:Space n) r).of_isClosed_subset
    ((hc.mono hball).preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic) inter_subset_left
  have hneg : ∀ x ∈ Ω, dualCutoff u h x < 0 := fun _ hx => sub_neg.mpr hx.2
  have hbd : ∀ x ∈ K, x ∉ Ω → dualCutoff u h x = 0 := by
    intro x hx hn
    have hlo : h ≤ dualHeight u x := by
      by_contra nh
      exact hn ⟨hKO hx,lt_of_not_ge nh⟩
    exact sub_eq_zero.mpr (le_antisymm hx.2 hlo)
  have hdepth : ∀ x ∈ Ω, -dualCutoff u h x ≤ h := by
    intro x hx
    have H := tangentHeight_nonneg hO hcv hu hp hx.1 h0
    change 0 ≤ dualHeight u x at H
    dsimp [dualCutoff]
    linarith
  have hrad : ∀ x ∈ Ω, positionSquared x ≤ r^2 := by
    intro x hx
    rw [positionSquared_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (by have H := hΩr hx; rw [Metric.mem_ball,dist_zero_right] at H; exact H.le) 2
  let γ : ℝ := 1/(2*(r^2+1))
  have hden : 0 < 2*(r^2+1) := by positivity
  have hγ : 0 < γ := one_div_pos.mpr hden
  have hsmall : γ*r^2 ≤ 1/2 := by
    dsimp [γ]
    rw [one_div_mul_eq_div,div_le_iff₀ hden]
    linarith [sq_nonneg r]
  have h0Ω : (0:Space n) ∈ Ω := ⟨h0,by simpa only [dualHeight_zero,Set.mem_preimage,Set.mem_Iio] using hh⟩
  have H := affineMaximal_dual_det_phase_bound hO hΩ hK hΩK hKO hu hp
    (fun x hx => hm x hx.1) h hneg hbd hγ (sq_nonneg r) hh.le hsmall hrad hdepth h0Ω
  have he : γ*r^2/2 = r^2/(4*(r^2+1)) := by dsimp [γ]; field_simp; ring
  have hd : 2*(n:ℝ)*((n:ℝ)+2)/γ = 2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)) := by
    simp only [γ,div_eq_mul_inv,one_mul,inv_inv]
  rw [he,hd] at H
  have hz : dualDetPhase u h γ 0 = ((hessian u 0).det)⁻¹ * h^(n+2) := by
    simp [dualDetPhase,dualCutoff,dualHeight_zero,positionEnergy]
  rw [hz] at H
  exact (le_div_iff₀ (pow_pos hh _)).mpr H

end DualDetCompact


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TranslateDet
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

section TranslateDet

lemma hessian_translate {n : ℕ} (f : Space n → ℝ) (a x : Space n) :
    hessian (fun y => f (a+y)) x = hessian f (a+x) := by
  ext i j
  simp only [hessian, fderiv_comp_add_left]
  exact congrArg (fun D : Space n →L[ℝ] ℝ => D (coordinateVector n i))
    (fderiv_comp_add_left (𝕜 := ℝ) (f := fun y => fderiv ℝ f y (coordinateVector n j)) a)

lemma tangentHeight_translate {n : ℕ} (f : Space n → ℝ) (a x y : Space n) :
    tangentHeight (fun z => f (a+z)) x y = tangentHeight f (a+x) (a+y) := by
  simp only [tangentHeight, fderiv_comp_add_left, add_sub_add_left_eq_sub]

lemma affineMaximalOn_translate {n : ℕ} {O : Set (Space n)} {f : Space n → ℝ}
    (hm : AffineMaximalOn O f) (a : Space n) :
    AffineMaximalOn ((fun x => a+x) ⁻¹' O) (fun x => f (a+x)) := by
  have hw : affineWeight (fun x => f (a+x)) = fun x => affineWeight f (a+x) := by
    ext x
    simp only [affineWeight,hessian_translate]
  intro x hx
  simpa only [cofactorHessian,hessian_translate,hw] using hm (a+x) hx

lemma sectionModulus_translate {n : ℕ} {O : Set (Space n)} {f : Space n → ℝ}
    {b : ℝ → ℝ} (hmod : HasLowerSectionModulus O f b) (a : Space n) :
    HasLowerSectionModulus ((fun x => a+x) ⁻¹' O) (fun x => f (a+x)) b := by
  intro x hx r hr y hy
  have hs : a+y ∈ tangentSection O f (a+x) (b r) := by
    refine ⟨hy.1,?_⟩
    have H : tangentHeight (fun z => f (a+z)) x y < b r := hy.2
    exact (tangentHeight_translate f a x y) ▸ H
  have H := hmod (a+x) hx r hr hs
  simpa only [Metric.mem_ball,dist_add_left] using H

lemma affineMaximal_det_inverse_upper_at_of_modulus {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hcv : Convex ℝ O) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) (hp : ∀ x ∈ O, (hessian u x).PosDef)
    (hm : AffineMaximalOn O u) {a : Space n} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ O) (b : ℝ → ℝ)
    (hb : 0 < b r) (hmod : HasLowerSectionModulus O u b) :
    ((hessian u a).det)⁻¹ ≤
      (2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)))^n * (b r/2)^2 *
        Real.exp (r^2/(4*(r^2+1))) / (b r/2)^(n+2) := by
  let V := (fun x : Space n => a+x) ⁻¹' O
  have hV : IsOpen V := hO.preimage (continuous_const.add continuous_id)
  have hVc : Convex ℝ V := by
    intro x hx y hy c d hc hd hcd
    change a+(c • x+d • y) ∈ O
    have H := hcv hx hy hc hd hcd
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    calc
      a+(c • x+d • y) = (c+d) • a+(c • x+d • y) := by rw [hcd,one_smul]
      _ = c • (a+x)+d • (a+y) := by module
  have hv : ContDiffOn ℝ ∞ (fun x => u (a+x)) V :=
    hu.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hx => hx)
  have hpv : ∀ x ∈ V, (hessian (fun y => u (a+y)) x).PosDef := by
    intro x hx
    rw [hessian_translate]
    exact hp _ hx
  have hballs : Metric.closedBall (0:Space n) r ⊆ V := by
    intro x hx
    apply hball
    simpa only [Metric.mem_closedBall,dist_zero_right,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx
  have H := affineMaximal_det_inverse_upper_of_modulus hV hVc hv hpv
    (affineMaximalOn_translate hm a) hr hballs b hb (sectionModulus_translate hmod a)
  simpa only [hessian_translate,add_zero] using H

end TranslateDet


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DetInteriorBall
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

section DetInteriorBall

/-- Uniform two-sided determinant estimates throughout the smaller ball,
with constants independent of both solution and evaluation point. This
supplies the first regularity stage, but still not uniform ellipticity. -/
theorem normalized_det_interior_ball_producer (n : ℕ) (b : ℝ → ℝ)
    (hb : ∀ r : ℝ, 0 < r → 0 < b r) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ f : Space n → ℝ,
      ContDiffOn ℝ ∞ f (Metric.ball 0 (1/4 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), (hessian f x).PosDef) →
      AffineMaximalOn (Metric.ball 0 (1/4 : ℝ)) f →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), -1 ≤ f x ∧ f x ≤ 0) →
      HasLowerSectionModulus (Metric.ball 0 (1/4 : ℝ)) f b →
      ∀ a ∈ Metric.ball (0 : Space n) (1/8 : ℝ),
        c ≤ (hessian f a).det ∧ (hessian f a).det ≤ C := by
  let r : ℝ := 1/32
  let h := b r / 2
  let L : ℝ := (2*(n:ℝ)*((n:ℝ)+2)*(2*(r^2+1)))^n * h^2 *
    Real.exp (r^2/(4*(r^2+1))) / h^(n+2)
  let U : ℝ := (2*(n:ℝ)*(((n:ℝ)+2)*(2*((4*(1:ℝ)/r)^2+1))+ (4*(1:ℝ)/r)^2))^n * h^2 *
    Real.exp ((4*(1:ℝ)/r)^2/(4*((4*(1:ℝ)/r)^2+1))) / h^(n+2)
  have hr : 0 < r := by norm_num [r]
  have hh : 0 < h := half_pos (hb r hr)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  refine ⟨1/(L+1),U+1,by positivity,by positivity,?_⟩
  intro f hf hp hm hfb hmod a ha
  have hball : Metric.closedBall a (2*r) ⊆ Metric.ball (0:Space n) (1/4 : ℝ) := by
    intro z hz
    have H := dist_triangle z a 0
    rw [Metric.mem_ball] at ha ⊢
    rw [Metric.mem_closedBall] at hz
    dsimp [r] at hz
    linarith
  have haa : a ∈ Metric.ball (0:Space n) (1/4 : ℝ) :=
    hball (Metric.mem_closedBall_self (by positivity))
  have Hupper : (hessian f a).det ≤ U := by
    apply affineMaximal_det_upper_of_section_control Metric.isOpen_ball (convex_ball _ _) hf hp hm hr hh (by norm_num) hball
    · intro x hx
      exact abs_le.mpr ⟨(hfb x hx).1,(hfb x hx).2.trans zero_le_one⟩
    · have He : 2*h=b r := by dsimp [h]; ring
      rw [He]
      exact hmod a haa r hr
  have Hlower : ((hessian f a).det)⁻¹ ≤ L :=
    affineMaximal_det_inverse_upper_at_of_modulus Metric.isOpen_ball (convex_ball _ _) hf hp hm hr
      ((Metric.closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hball) b (hb r hr) hmod
  refine ⟨?_,Hupper.trans (le_add_of_nonneg_right zero_le_one)⟩
  have hd : 0 < (hessian f a).det := (hp a haa).det_pos
  have H' := mul_le_mul_of_nonneg_left (Hlower.trans (le_add_of_nonneg_right zero_le_one)) hd.le
  rw [mul_inv_cancel₀ hd.ne'] at H'
  exact (div_le_iff₀ (by positivity : 0 < L+1)).mpr H'

end DetInteriorBall


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

/-- All normalized solutions have the same determinant bounds on the fixed
inner ball. The constants precede the function; no local analytic estimate
is postulated. -/
theorem normalized_balanced_det_bounds_oai {n : ℕ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ v : Space n → ℝ,
      ContDiff ℝ ∞ v → (∀ x, (hessian v x).PosDef) →
      AffineMaximalOn univ v → v 0=0 → fderiv ℝ v 0=0 →
      SectionBalance univ v ρ →
      Metric.ball 0 1 ⊆ tangentSection univ v 0 1 →
      tangentSection univ v 0 1 ⊆ Metric.ball 0 R →
      ∀ x ∈ Metric.ball (0:Space n) (1/8:ℝ),
        c ≤ (hessian v x).det ∧ (hessian v x).det ≤ C := by
  obtain ⟨c,C,hc,hC,H⟩ := normalized_det_interior_ball_producer n (normalizedModulus ρ R)
    (fun _ _ => normalizedModulus_pos hρ)
  refine ⟨c,C,hc,hC,?_⟩
  intro v hv hp hm hv0 hdv0 hbal hin hout
  let f := tangentShift v 0 1
  have hf := contDiffOn_tangentShift hv.contDiffOn 0 1 (Ω := Metric.ball 0 (1/4:ℝ))
  have he (x : Space n) : f x = v x-1 := by simp [f,tangentShift,tangentHeight,hv0,hdv0]
  have hh (x : Space n) : hessian f x = hessian v x :=
    hessian_tangentShift isOpen_univ hv.contDiffOn 0 1 (mem_univ x)
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ convex_univ hv.contDiffOn
    (fun x _ => (hp x).posSemidef)
  have hm' : AffineMaximalOn (Metric.ball 0 (1/4:ℝ)) f :=
    fun x _ => affineMaximalOn_tangentShift isOpen_univ hv.contDiffOn hm 0 1 x (mem_univ x)
  have hfb (x : Space n) (hx : x ∈ Metric.ball 0 (1/4:ℝ)) : -1 ≤ f x ∧ f x ≤ 0 := by
    rw [he]
    have hlo : 0 ≤ v x := by
      have H := tangentHeight_nonneg isOpen_univ convex_univ hv.contDiffOn
        (fun z _ => hp z) (mem_univ 0) (mem_univ x)
      simpa only [tangentHeight,hv0,hdv0,sub_zero,zero_apply] using H
    have hhi := normalized_value_le_quarter hcv hv0 hdv0 hin (mem_ball_zero_iff.mp hx)
    constructor <;> linarith
  have hmod : HasLowerSectionModulus (Metric.ball 0 (1/4:ℝ)) f (normalizedModulus ρ R) := by
    intro x hx r hr y hy
    apply normalized_modulus_of_sectionBalance hv hp (euclideanGraphComplete_entire hv)
      hv0 hdv0 hρ hρ1 hR hbal hin hout hx hr
    refine ⟨mem_univ y,?_⟩
    have HH : tangentHeight f x y < normalizedModulus ρ R r := hy.2
    dsimp only [f] at HH
    rwa [tangentHeight_tangentShift (hv.differentiable (by simp))] at HH
  intro x hx
  simpa only [hh] using H f hf (fun x _ => hh x ▸ hp x) hm' hfb hmod x hx

end NormalizedFamilyDet


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.normalized_balanced_det_bounds_oai := @OAI.AffineBernstein.normalized_balanced_det_bounds_oai
