-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_det_upper_of_section_control
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:59:25.859477+00:00
-- url     : https://prove2.me/submissions/5d0bb09f-f439-4588-9389-eefb2908a977

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

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

lemma inverse_column_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (k : ι) (p : ι → ℝ) :
    (∑ i, ∑ j, H⁻¹ i j * H i k * p j) = p k := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hH.isHermitian
  have hh := inverse_radial_contraction hH (Pi.single k 1) p
  simpa [Pi.single_apply, hs.apply k] using hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixMetric
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

lemma inverseMatrixPair_eq_dot (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A x y = y ⬝ᵥ A⁻¹.mulVec x := by
  simp only [inverseMatrixPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inverseMatrixPair_self_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) (x : ι → ℝ) :
    0 ≤ inverseMatrixPair A x x := by
  rw [inverseMatrixPair_eq_dot]
  simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg x

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
-- module Solutions.OAIQ22_AB.AffineBernstein_EuclideanChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma euclideanGradientSquare_eq_norm {k : ℕ} (φ : Space k → ℝ) (s : Space k) :
    euclideanGradientSquare φ s = ‖fderiv ℝ φ s‖^2 := by
  have hh := (EuclideanSpace.basisFun (Fin k) ℝ).sum_sq_inner_left
    ((InnerProductSpace.toDual ℝ (Space k)).symm (fderiv ℝ φ s))
  simpa only [euclideanGradientSquare,InnerProductSpace.toDual_symm_apply,LinearIsometryEquiv.norm_map] using hh

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

theorem continuousOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) (a : Space n) :
    ContinuousOn (tangentHeight u a) Ω := by
  exact (hu.sub continuousOn_const).sub
    ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const)).continuousOn

/- Tangent-plane sublevels are closed, by closedness of the actual epigraph.
No implicit completeness-invariance under a shear is needed. -/

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
-- module Solutions.OAIQ22_AB.AffineBernstein_LogDetGradientEnergy
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

section LogDetGradientEnergy

lemma contDiffOn_gradientEnergy {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) :
    ContDiffOn ℝ ∞ (gradientEnergy u) Ω := by
  exact contDiffOn_const.mul (ContDiffOn.sum fun k _ => (contDiffOn_dirDeriv hΩ hu _).pow 2)

lemma dirDeriv_gradientEnergy {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    dirDeriv (coordinateVector n i) (gradientEnergy u) x =
      ∑ k, dirDeriv (coordinateVector n k) u x * hessian u x i k := by
  change dirDeriv _ (fun y => (1/2:ℝ) * ∑ k, (dirDeriv (coordinateVector n k) u y)^2) x = _
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ k, (dirDeriv (coordinateVector n k) u y)^2) x :=
    ContDiffAt.sum fun k _ => (contDiffAt_dirDeriv hu _).pow 2
  rw [dirDeriv_const_mul (hs.differentiableAt (by simp)),
    dirDeriv_sum (fun (k : Fin n) (y : Space n) => (dirDeriv (coordinateVector n k) u y)^2)
      (fun k => ((contDiffAt_dirDeriv hu _).differentiableAt (by simp)).pow 2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [pow_two]
  rw [dirDeriv_mul ((contDiffAt_dirDeriv hu _).differentiableAt (by simp))
    ((contDiffAt_dirDeriv hu _).differentiableAt (by simp))]
  change (1/2:ℝ) * (hessian u x i k * dirDeriv (coordinateVector n k) u x +
    dirDeriv (coordinateVector n k) u x * hessian u x i k) = _
  ring

lemma inverseHessian_pair_gradient {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (f : Space n → ℝ) :
    inverseHessianPair u (gradientEnergy u) f x =
      ∑ k, dirDeriv (coordinateVector n k) u x * dirDeriv (coordinateVector n k) f x := by
  unfold inverseHessianPair
  simp_rw [dirDeriv_gradientEnergy hu]
  have hs := Matrix.isHermitian_iff_isSymm.mp hp.isHermitian
  have he (i : Fin n) : (∑ k, dirDeriv (coordinateVector n k) u x * hessian u x i k) =
      ∑ k, dirDeriv (coordinateVector n k) u x * hessian u x k i := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hs.apply k i]
  simp only [he]
  exact inverse_radial_contraction hp _ _

lemma inverseHessianTrace_gradientEnergy {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (gradientEnergy u) x =
      (hessian u x).trace + ∑ k,
        dirDeriv (coordinateVector n k) u x * dirDeriv (coordinateVector n k) (logHessianDet u) x := by
  have hk (k : Fin n) := contDiffOn_dirDeriv hΩ hu (coordinateVector n k)
  have he (i j : Fin n) : hessian (gradientEnergy u) x i j =
      (1/2 : ℝ) * ∑ k, hessian (fun y => dirDeriv (coordinateVector n k) u y *
        dirDeriv (coordinateVector n k) u y) x i j := by
    change dirDeriv _ (dirDeriv _ (fun y => (1/2:ℝ) * ∑ k,
      (dirDeriv (coordinateVector n k) u y)^2)) x = _
    rw [second_dirDeriv_const_mul hΩ (ContDiffOn.sum fun k _ => (hk k).pow 2) hx]
    congr 1
    change hessian (fun y => ∑ k, (dirDeriv (coordinateVector n k) u y)^2) x i j = _
    simp only [pow_two]
    exact hessian_sum_on hΩ (fun k => (hk k).mul (hk k)) hx i j
  have hsum : inverseHessianTrace u (gradientEnergy u) x =
      (1/2:ℝ) * ∑ k, ∑ i, ∑ j, (hessian u x)⁻¹ i j *
        hessian (fun y => dirDeriv (coordinateVector n k) u y *
          dirDeriv (coordinateVector n k) u y) x i j := by
    unfold inverseHessianTrace
    simp only [he, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    try simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  have hterm (k : Fin n) : (∑ i, ∑ j, (hessian u x)⁻¹ i j *
      hessian (fun y => dirDeriv (coordinateVector n k) u y *
        dirDeriv (coordinateVector n k) u y) x i j) =
      2 * dirDeriv (coordinateVector n k) u x *
        dirDeriv (coordinateVector n k) (logHessianDet u) x + 2 * hessian u x k k := by
    rw [hessian_product_trace hΩ (hk k) (hk k) hx (inverseHessian_isSymm hp)]
    change dirDeriv (coordinateVector n k) u x *
        inverseHessianTrace u (dirDeriv (coordinateVector n k) u) x +
      dirDeriv (coordinateVector n k) u x *
        inverseHessianTrace u (dirDeriv (coordinateVector n k) u) x +
      2 * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian u x i k * hessian u x j k) = _
    rw [inverseHessianTrace_dirDeriv hΩ hu hx hp, inverse_column_contraction hp]
    ring
  simp_rw [hterm]
  rw [Finset.mul_sum]
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end LogDetGradientEnergy

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

lemma inverseHessianTrace_log {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hneg : ∀ y ∈ Ω, u y < 0)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (fun y => Real.log (u y)) x =
      (n:ℝ) / u x - inverseHessianPair u u u x / (u x)^2 := by
  have he (i j : Fin n) : hessian (fun y => Real.log (u y)) x i j =
      hessian u x i j / u x -
        dirDeriv (coordinateVector n i) u x * dirDeriv (coordinateVector n j) u x / (u x)^2 :=
    second_dirDeriv_log_of_neg hΩ hu hneg hx _ _
  have hh : inverseHessianTrace u (fun y => Real.log (u y)) x =
      inverseHessianTrace u u x / u x - inverseHessianPair u u u x / (u x)^2 := by
    simp only [inverseHessianTrace,inverseHessianPair,he,mul_sub,Finset.sum_sub_distrib,
      Finset.sum_div,mul_div_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hh,inverseHessianTrace_self hp]

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

lemma inverseHessianPair_self_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (f : Space n → ℝ) : 0 ≤ inverseHessianPair u f f x := by
  have hh := inverseMatrixPair_self_nonneg hp (fun i => dirDeriv (coordinateVector n i) f x)
  unfold inverseHessianPair inverseMatrixPair at *
  rw [Finset.sum_comm] at hh
  simpa only [mul_right_comm] using hh

lemma contDiffOn_affineDetBarrier {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hneg : ∀ x ∈ Ω, u x < 0) (β γ : ℝ) :
    ContDiffOn ℝ ∞ (affineDetBarrier u β γ) Ω :=
  ((contDiffOn_logHessianDet hΩ hu hp).add
    (contDiffOn_const.mul (hu.log (fun x hx => ne_of_lt (hneg x hx))))).add
      (contDiffOn_const.mul (contDiffOn_gradientEnergy hΩ hu))

lemma dirDeriv_affineDetBarrier {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (hn : u x ≠ 0)
    (β γ : ℝ) (i : Fin n) :
    dirDeriv (coordinateVector n i) (affineDetBarrier u β γ) x =
      dirDeriv (coordinateVector n i) (logHessianDet u) x +
        β * dirDeriv (coordinateVector n i) u x / u x +
        γ * dirDeriv (coordinateVector n i) (gradientEnergy u) x := by
  have hd := hu.differentiableAt (by simp)
  have hφ := (contDiffAt_logHessianDet hu hp).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (gradientEnergy u) x :=
    (contDiffAt_const.mul (ContDiffAt.sum fun k _ => (contDiffAt_dirDeriv hu _).pow 2)).differentiableAt (by simp)
  have hh := ((hφ.hasFDerivAt.add ((hd.log hn).hasFDerivAt.const_mul β)).add
    (hG.hasFDerivAt.const_mul γ)).fderiv
  change (fderiv ℝ (fun y => logHessianDet u y + β * Real.log (u y) + γ * gradientEnergy u y) x) _ = _
  change (fderiv ℝ (fun y => logHessianDet u y + β * Real.log (u y) + γ * gradientEnergy u y) x) = _ at hh
  rw [hh]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change dirDeriv _ (logHessianDet u) x + β * dirDeriv _ (fun y => Real.log (u y)) x + _ = _
  rw [dirDeriv_real_log hd hn]
  simp only [dirDeriv]
  ring

lemma inverseHessianTrace_affineDetBarrier {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hneg : ∀ x ∈ Ω, u x < 0) {x : Space n} (hx : x ∈ Ω) (β γ : ℝ) :
    inverseHessianTrace u (affineDetBarrier u β γ) x =
      (((n:ℝ)+1)/((n:ℝ)+2)) * inverseHessianPair u (logHessianDet u) (logHessianDet u) x +
      β * ((n:ℝ)/u x - inverseHessianPair u u u x / (u x)^2) +
      γ * ((hessian u x).trace + ∑ k, dirDeriv (coordinateVector n k) u x *
        dirDeriv (coordinateVector n k) (logHessianDet u) x) := by
  have hφ := contDiffOn_logHessianDet hΩ hu hp
  have hl := hu.log (fun y hy => ne_of_lt (hneg y hy))
  have hG := contDiffOn_gradientEnergy hΩ hu
  unfold affineDetBarrier
  rw [inverseHessianTrace_add hΩ (hφ.add (contDiffOn_const.mul hl)) (contDiffOn_const.mul hG) hx,
    inverseHessianTrace_add hΩ hφ (contDiffOn_const.mul hl) hx,
    inverseHessianTrace_const_mul hΩ hl hx, inverseHessianTrace_const_mul hΩ hG hx,
    affineMaximal_logHessianDet_equation hΩ hu hp hm hx,
    inverseHessianTrace_log hΩ hu hneg hx (hp x hx),
    inverseHessianTrace_gradientEnergy hΩ hu hx (hp x hx)]

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

lemma gradientSquared_nonneg {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    0 ≤ gradientSquared u x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma inverseHessianPair_gradient_self {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) :
    inverseHessianPair u (gradientEnergy u) u x = gradientSquared u x := by
  rw [inverseHessian_pair_gradient hu hp]
  simp only [gradientSquared,pow_two]

lemma gradientHessianSquare_eq_dotProduct {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : gradientHessianSquare u x =
      (fun i => dirDeriv (coordinateVector n i) u x) ⬝ᵥ
        (hessian u x).mulVec (fun i => dirDeriv (coordinateVector n i) u x) := by
  simp only [gradientHessianSquare,dirDeriv_gradientEnergy hu,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma gradientHessianSquare_le_trace {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) :
    gradientHessianSquare u x ≤ (hessian u x).trace * gradientSquared u x := by
  rw [gradientHessianSquare_eq_dotProduct hu]
  exact posSemidef_quadratic_le_trace_mul_sq hp.posSemidef _

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

lemma affineDetBarrier_critical_gradient {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (hn : u x ≠ 0)
    (β γ : ℝ) (hm : IsLocalMax (affineDetBarrier u β γ) x) (i : Fin n) :
    dirDeriv (coordinateVector n i) (logHessianDet u) x =
      (-β / u x) * dirDeriv (coordinateVector n i) u x +
        (-γ) * dirDeriv (coordinateVector n i) (gradientEnergy u) x := by
  have hz : dirDeriv (coordinateVector n i) (affineDetBarrier u β γ) x = 0 := by
    simp only [dirDeriv,hm.fderiv_eq_zero,zero_apply]
  rw [dirDeriv_affineDetBarrier hu hp hn] at hz
  linear_combination (norm := ring_nf) hz

lemma inverseHessianPair_logHessianDet_of_barrier_max {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (hn : u x ≠ 0)
    (β γ : ℝ) (hm : IsLocalMax (affineDetBarrier u β γ) x) :
    inverseHessianPair u (logHessianDet u) (logHessianDet u) x =
      β^2 / (u x)^2 * inverseHessianPair u u u x +
        (2*β*γ/u x) * gradientSquared u x + γ^2 * gradientHessianSquare u x := by
  rw [inverseHessianPair_grad_linear hp (-β/u x) (-γ)
    (affineDetBarrier_critical_gradient hu hp hn β γ hm),
    inverseHessianPair_gradient_self hu hp,inverseHessian_pair_gradient hu hp]
  change (-β/u x)^2 * _ + 2*(-β/u x)*(-γ)*_ + (-γ)^2 * gradientHessianSquare u x = _
  ring

lemma gradient_logHessianDet_of_barrier_max {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (hn : u x ≠ 0)
    (β γ : ℝ) (hm : IsLocalMax (affineDetBarrier u β γ) x) :
    (∑ k, dirDeriv (coordinateVector n k) u x * dirDeriv (coordinateVector n k) (logHessianDet u) x) =
      (-β/u x) * gradientSquared u x - γ * gradientHessianSquare u x := by
  simp only [affineDetBarrier_critical_gradient hu hp hn β γ hm,
    gradientSquared,gradientHessianSquare,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The unabridged differential barrier identity at a local maximum. Its
coefficient is the original affine maximal exponent. -/
lemma affineDetBarrier_peak_identity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hneg : ∀ x ∈ Ω, u x < 0) {x : Space n} (hx : x ∈ Ω) (γ : ℝ)
    (hmax : IsLocalMax (affineDetBarrier u ((n:ℝ)+2) γ) x) :
    inverseHessianTrace u (affineDetBarrier u ((n:ℝ)+2) γ) x =
      ((n:ℝ)*((n:ℝ)+2)/(u x)^2) * inverseHessianPair u u u x +
      γ * (hessian u x).trace - γ^2/((n:ℝ)+2) * gradientHessianSquare u x +
      ((n:ℝ)*((n:ℝ)+2) + γ*(n:ℝ)*gradientSquared u x) / u x := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds hx)
  have hn : u x ≠ 0 := ne_of_lt (hneg x hx)
  have hd : (n:ℝ)+2 ≠ 0 := by positivity
  rw [inverseHessianTrace_affineDetBarrier hΩ hu hp hm hneg hx,
    inverseHessianPair_logHessianDet_of_barrier_max hu' (hp x hx) hn _ γ hmax,
    gradient_logHessianDet_of_barrier_max hu' (hp x hx) hn _ γ hmax]
  field_simp
  ring

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DetBarrierBound
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

section DetBarrierBound

lemma detBarrier_peak_trace_algebra {N T P Q R v γ : ℝ}
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hv : v < 0) (hγ : 0 < γ) (hRP : R ≤ T * P) (hγP : γ*P ≤ 1/2)
    (hpeak : N*(N+2)/v^2*Q + γ*T - γ^2/(N+2)*R +
      (N*(N+2)+γ*N*P)/v ≤ 0) :
    (-v)*T ≤ 2*N*((N+2)/γ+P) := by
  have hden : 0 < N+2 := by linarith
  have hμ : 0 ≤ γ^2/(N+2) := by positivity
  have hfirst : 0 ≤ N*(N+2)/v^2*Q := by positivity
  have hsmall : γ^2/(N+2)*P ≤ γ/2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    have hi : γ*(γ*P) ≤ γ*(1/2) := mul_le_mul_of_nonneg_left hγP hγ.le
    nlinarith [mul_nonneg hN hγ.le]
  have hex : γ^2/(N+2)*R ≤ T*(γ/2) := by
    calc
      _ ≤ γ^2/(N+2)*(T*P) := mul_le_mul_of_nonneg_left hRP hμ
      _ = T*(γ^2/(N+2)*P) := by ring
      _ ≤ T*(γ/2) := mul_le_mul_of_nonneg_left hsmall hT
  have hm : γ*T/2 + (N*(N+2)+γ*N*P)/v ≤ 0 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hm (le_of_lt (neg_pos.mpr hv))
  have hv0 : v ≠ 0 := ne_of_lt hv
  have hsimp : (-v)*(γ*T/2 + (N*(N+2)+γ*N*P)/v) =
      (-v)*γ*T/2 - (N*(N+2)+γ*N*P) := by field_simp [hv0]; ring
  rw [hsimp,mul_zero] at hprod
  apply (mul_le_mul_iff_right₀ hγ).mp
  calc
    γ*((-v)*T) ≤ 2*(N*(N+2)+γ*N*P) := by nlinarith
    _ = γ*(2*N*((N+2)/γ+P)) := by field_simp [ne_of_gt hγ]

lemma affineDetBarrier_peak_trace_bound {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hneg : ∀ x ∈ Ω, u x < 0) {x : Space n} (hx : x ∈ Ω) {γ : ℝ}
    (hγ : 0 < γ) (hsmall : γ * gradientSquared u x ≤ 1/2)
    (hmax : IsLocalMax (affineDetBarrier u ((n:ℝ)+2) γ) x) :
    (-u x) * (hessian u x).trace ≤
      2*(n:ℝ)*(((n:ℝ)+2)/γ+gradientSquared u x) := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds hx)
  have hb := (contDiffOn_affineDetBarrier hΩ hu hp hneg ((n:ℝ)+2) γ).contDiffAt
    (hΩ.mem_nhds hx)
  have hnon := inverseHessianTrace_nonpos_of_localMax hb (hp x hx) hmax
  rw [affineDetBarrier_peak_identity hΩ hu hp hm hneg hx γ hmax] at hnon
  have ht : 0 ≤ (hessian u x).trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun _ _ => (hp x hx).posSemidef.diag_nonneg)
  exact detBarrier_peak_trace_algebra (Nat.cast_nonneg n) ht
    (gradientSquared_nonneg u x) (inverseHessianPair_self_nonneg (hp x hx) u)
    (hneg x hx) hγ (gradientHessianSquare_le_trace hu' (hp x hx)) hsmall hnon

end DetBarrierBound


end
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

lemma affineDetPhase_eq_exp {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (hn : u x < 0) (γ : ℝ) :
    affineDetPhase u γ x = Real.exp (affineDetBarrier u ((n:ℝ)+2) γ x) := by
  unfold affineDetPhase affineDetBarrier logHessianDet
  rw [Real.exp_add,Real.exp_add,Real.exp_log hp.det_pos]
  rw [← Real.log_neg_eq_log (u x)]
  congr 2
  have hh := Real.exp_nat_mul (Real.log (-u x)) (n+2)
  rw [Real.exp_log (neg_pos.mpr hn)] at hh
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh.symm

lemma affineDetPhase_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (hn : u x < 0) (γ : ℝ) :
    0 < affineDetPhase u γ x := by
  rw [affineDetPhase_eq_exp hp hn]
  exact Real.exp_pos _

lemma continuousOn_affineDetPhase {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (γ : ℝ) :
    ContinuousOn (affineDetPhase u γ) Ω := by
  have hh : ContinuousOn (fun x => (hessian u x).det) Ω := by
    intro x hx
    exact (contDiffAt_det_hessian (hu.contDiffAt (hΩ.mem_nhds hx))).continuousAt.continuousWithinAt
  exact ((hh.mul (hu.continuousOn.neg.pow (n+2))).mul
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (contDiffOn_gradientEnergy hΩ hu).continuousOn)))

lemma affineDetPhase_peak_bound {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hneg : ∀ x ∈ Ω, u x < 0) {x : Space n} (hx : x ∈ Ω)
    {γ M D : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hsmall : γ*M ≤ 1/2) (hgrad : gradientSquared u x ≤ M) (hdepth : -u x ≤ D)
    (hmax : IsLocalMax (affineDetBarrier u ((n:ℝ)+2) γ) x) :
    affineDetPhase u γ x ≤ (2*(n:ℝ)*(((n:ℝ)+2)/γ+M))^n * D^2 * Real.exp (γ*M/2) := by
  have hd : 0 < -u x := neg_pos.mpr (hneg x hx)
  have ht : 0 ≤ (hessian u x).trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun i hi => (hp x hx).posSemidef.diag_nonneg)
  have hc : 0 ≤ 2*(n:ℝ)*(((n:ℝ)+2)/γ+M) := by positivity
  have hsm : γ * gradientSquared u x ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hgrad hγ.le).trans hsmall
  have htrace := affineDetBarrier_peak_trace_bound hΩ hu hp hm hneg hx hγ hsm hmax
  have htrace' : (-u x)*(hessian u x).trace ≤ 2*(n:ℝ)*(((n:ℝ)+2)/γ+M) :=
    htrace.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hgrad) (by positivity))
  have hpow : ((-u x)*(hessian u x).trace)^n ≤ (2*(n:ℝ)*(((n:ℝ)+2)/γ+M))^n :=
    pow_le_pow_left₀ (mul_nonneg hd.le ht) htrace' n
  have hdet := posSemidef_det_le_trace_pow (hp x hx).posSemidef
  have he : γ*gradientEnergy u x ≤ γ*M/2 := by
    change γ*((1/2)*gradientSquared u x) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hgrad hγ.le]
  unfold affineDetPhase
  calc
    _ ≤ (hessian u x).trace^n * (-u x)^(n+2) * Real.exp (γ*gradientEnergy u x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdet (by positivity)) (Real.exp_pos _).le
    _ = ((-u x)*(hessian u x).trace)^n * (-u x)^2 * Real.exp (γ*gradientEnergy u x) := by
      rw [pow_add,mul_pow]
      ring
    _ ≤ (2*(n:ℝ)*(((n:ℝ)+2)/γ+M))^n * D^2 * Real.exp (γ*M/2) := by
      apply mul_le_mul
      · exact mul_le_mul hpow ((sq_le_sq₀ hd.le hD).mpr hdepth) (sq_nonneg _) (pow_nonneg hc n)
      · exact Real.exp_le_exp.mpr he
      · exact (Real.exp_pos _).le
      · positivity

end DetBarrierPhase


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DetCompactBound
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

section DetCompactBound
open Filter
open scoped Topology

/-- Maximum-principle determinant upper estimate on a literal compact negative
section. The compact section and gradient/depth bounds are geometric inputs;
no Hessian, determinant, ellipticity or derivative bound is assumed. -/
lemma affineMaximal_det_phase_bound {n : ℕ} {V Ω K : Set (Space n)}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hΩK : Ω ⊆ K) (hKV : K ⊆ V) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (hp : ∀ x ∈ V, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (hneg : ∀ x ∈ Ω, u x < 0)
    (hbd : ∀ x ∈ K, x ∉ Ω → u x = 0)
    {γ M D : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hsmall : γ*M ≤ 1/2) (hgrad : ∀ x ∈ Ω, gradientSquared u x ≤ M)
    (hdepth : ∀ x ∈ Ω, -u x ≤ D) {x : Space n} (hx : x ∈ Ω) :
    affineDetPhase u γ x ≤ (2*(n:ℝ)*(((n:ℝ)+2)/γ+M))^n * D^2 * Real.exp (γ*M/2) := by
  obtain ⟨y,hyK,hymax⟩ := hK.exists_isMaxOn ⟨x,hΩK hx⟩
    ((continuousOn_affineDetPhase hV hu γ).mono hKV)
  have hxy : affineDetPhase u γ x ≤ affineDetPhase u γ y := hymax (hΩK hx)
  have hyp : 0 < affineDetPhase u γ y :=
    (affineDetPhase_pos (hp x (hKV (hΩK hx))) (hneg x hx) γ).trans_le hxy
  have hy : y ∈ Ω := by
    by_contra h
    have hz : affineDetPhase u γ y = 0 := by
      simp [affineDetPhase,hbd y hyK h]
    rw [hz] at hyp
    exact (lt_irrefl 0) hyp
  have hmax : IsLocalMax (affineDetBarrier u ((n:ℝ)+2) γ) y := by
    filter_upwards [hΩ.mem_nhds hy] with z hz
    apply Real.exp_le_exp.mp
    rw [← affineDetPhase_eq_exp (hp z (hKV (hΩK hz))) (hneg z hz) γ,
      ← affineDetPhase_eq_exp (hp y (hKV hyK)) (hneg y hy) γ]
    exact hymax (hΩK hz)
  exact hxy.trans (affineDetPhase_peak_bound hΩ (hu.mono (hΩK.trans hKV))
    (fun z hz => hp z (hKV (hΩK hz))) hm hneg hy hγ hM hD hsmall
    (hgrad y hy) (hdepth y hy) hmax)

lemma affineDetPhase_ge_det_mul_depth {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (hn : u x < 0) {γ δ : ℝ} (hγ : 0 ≤ γ)
    (hδ : 0 < δ) (hdepth : δ ≤ -u x) :
    (hessian u x).det * δ^(n+2) ≤ affineDetPhase u γ x := by
  have hGE : 0 ≤ gradientEnergy u x := by
    unfold gradientEnergy
    positivity
  have hexp : 1 ≤ Real.exp (γ*gradientEnergy u x) := Real.one_le_exp_iff.mpr (mul_nonneg hγ hGE)
  unfold affineDetPhase
  calc
    _ ≤ (hessian u x).det * (-u x)^(n+2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le hdepth _) hp.det_pos.le
    _ = ((hessian u x).det * (-u x)^(n+2))*1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp
      (mul_nonneg hp.det_pos.le (pow_nonneg (neg_nonneg.mpr hn.le) _))

lemma affineMaximal_det_upper_on_compact_section {n : ℕ} {V Ω K : Set (Space n)}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hΩK : Ω ⊆ K) (hKV : K ⊆ V) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u V) (hp : ∀ x ∈ V, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (hneg : ∀ x ∈ Ω, u x < 0)
    (hbd : ∀ x ∈ K, x ∉ Ω → u x = 0)
    {M D δ : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hgrad : ∀ x ∈ Ω, gradientSquared u x ≤ M)
    (hdepth : ∀ x ∈ Ω, -u x ≤ D) {x : Space n} (hx : x ∈ Ω)
    (hxdepth : δ ≤ -u x) :
    (hessian u x).det ≤
      (2*(n:ℝ)*(((n:ℝ)+2)*(2*(M+1))+M))^n * D^2 *
        Real.exp (M/(4*(M+1))) / δ^(n+2) := by
  let γ : ℝ := 1/(2*(M+1))
  have hden : 0 < 2*(M+1) := by linarith
  have hγ : 0 < γ := one_div_pos.mpr hden
  have hsmall : γ*M ≤ 1/2 := by
    dsimp [γ]
    rw [one_div_mul_eq_div,div_le_iff₀ hden]
    linarith
  have hbound := affineMaximal_det_phase_bound hV hΩ hK hΩK hKV hu hp hm hneg hbd
    hγ hM hD hsmall hgrad hdepth hx
  have hlower := affineDetPhase_ge_det_mul_depth (hp x (hKV (hΩK hx))) (hneg x hx)
    hγ.le hδ hxdepth
  have he : γ*M/2 = M/(4*(M+1)) := by
    dsimp [γ]
    field_simp [ne_of_gt (show 0 < M + 1 by linarith)]
    ring
  rw [he] at hbound
  have hd : ((n:ℝ)+2)/γ = ((n:ℝ)+2)*(2*(M+1)) := by
    dsimp [γ]
    simp only [div_eq_mul_inv,one_mul,inv_inv]
  rw [hd] at hbound
  exact (le_div_iff₀ (pow_pos hδ _)).mpr (hlower.trans hbound)

end DetCompactBound


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

lemma gradientSquared_eq_norm_fderiv {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    gradientSquared f x = ‖fderiv ℝ f x‖^2 := by
  simpa only [gradientSquared,dirDeriv,euclideanGradientSquare,EuclideanSpace.basisFun_apply,
    coordinateVector] using euclideanGradientSquare_eq_norm f x

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
-- module Solutions.OAIQ22_AB.AffineBernstein_LocalDet
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

section LocalDetProducer

/-- A quantitative determinant upper producer using only one finite section
modulus and the original PDE. In particular the Hessian determinant is an
output, not an ellipticity hypothesis. -/
lemma affineMaximal_det_upper_of_section_control_oai {n : ℕ} {O : Set (Space n)}
    (hO : IsOpen O) (hcv : Convex ℝ O) {f : Space n → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) (hp : ∀ x ∈ O, (hessian f x).PosDef)
    (hm : AffineMaximalOn O f) {a : Space n} {r h M : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hM : 0 ≤ M)
    (hball : Metric.closedBall a (2*r) ⊆ O)
    (hb : ∀ x ∈ O, |f x| ≤ M)
    (hsection : tangentSection O f a (2*h) ⊆ Metric.ball a r) :
    (hessian f a).det ≤
      (2*(n:ℝ)*(((n:ℝ)+2)*(2*((4*M/r)^2+1))+(4*M/r)^2))^n * h^2 *
        Real.exp ((4*M/r)^2/(4*((4*M/r)^2+1))) / h^(n+2) := by
  let g := tangentShift f a h
  let Ω := tangentSection O f a h
  let K := Metric.closedBall a r ∩ (tangentHeight f a) ⁻¹' Iic h
  have hsmallball : Metric.closedBall a r ⊆ O :=
    (Metric.closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hball
  have ha : a ∈ O := hball (Metric.mem_closedBall_self (by linarith))
  have hc : ConvexOn ℝ O f := convexOn_of_hessian_posSemidef hO hcv hf
    (fun x hx => (hp x hx).posSemidef)
  have hcont := continuousOn_tangentHeight hf.continuousOn a
  have hΩ : IsOpen Ω := hcont.isOpen_inter_preimage hO isOpen_Iio
  have hΩr : Ω ⊆ Metric.ball a r := by
    intro x hx
    exact hsection ⟨hx.1,by dsimp [Ω,tangentSection] at hx; linarith [hx.2]⟩
  have hΩK : Ω ⊆ K := by
    intro x hx
    exact ⟨Metric.ball_subset_closedBall (hΩr hx),hx.2.le⟩
  have hKV : K ⊆ O := fun _ hx => hsmallball hx.1
  have hK : IsCompact K := (isCompact_closedBall a r).of_isClosed_subset
    ((hcont.mono hsmallball).preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic) inter_subset_left
  have hg : ContDiffOn ℝ ∞ g O := contDiffOn_tangentShift hf a h
  have hpg : ∀ x ∈ O, (hessian g x).PosDef := by
    intro x hx
    dsimp [g]
    rw [hessian_tangentShift hO hf a h hx]
    exact hp x hx
  have hmg : AffineMaximalOn Ω g := by
    have hfull := affineMaximalOn_tangentShift hO hf hm a h
    exact fun x hx => hfull x hx.1
  have hneg : ∀ x ∈ Ω, g x < 0 := by
    intro x hx
    dsimp [g,tangentShift]
    exact sub_neg.mpr hx.2
  have hbd : ∀ x ∈ K, x ∉ Ω → g x = 0 := by
    intro x hx hn
    have hlo : h ≤ tangentHeight f a x := by
      by_contra nh
      exact hn ⟨hKV hx,lt_of_not_ge nh⟩
    exact sub_eq_zero.mpr (le_antisymm hx.2 hlo)
  have hgFnorm : ∀ x ∈ Metric.closedBall a r, ‖fderiv ℝ f x‖ ≤ 2*M/r := by
    intro x hx
    apply norm_fderiv_le_of_convex_bounded hc (hsmallball hx)
      ((hf.contDiffAt (hO.mem_nhds (hsmallball hx))).differentiableAt (by simp)) hr hM _ hb
    intro y hy
    apply hball
    rw [Metric.mem_closedBall] at *
    have htri := dist_triangle y x a
    linarith
  have hgrad : ∀ x ∈ Ω, gradientSquared g x ≤ (4*M/r)^2 := by
    intro x hx
    rw [gradientSquared_eq_norm_fderiv]
    have hga := hgFnorm a (Metric.mem_closedBall_self hr.le)
    have hgx := hgFnorm x (Metric.ball_subset_closedBall (hΩr hx))
    have hdiff : ‖fderiv ℝ g x‖ ≤ 4*M/r := by
      dsimp [g]
      rw [fderiv_tangentShift ((hf.contDiffAt (hO.mem_nhds hx.1)).differentiableAt (by simp))]
      exact (norm_sub_le _ _).trans ((add_le_add hgx hga).trans_eq (by ring))
    exact pow_le_pow_left₀ (norm_nonneg _) hdiff 2
  have hdepth : ∀ x ∈ Ω, -g x ≤ h := by
    intro x hx
    have hn := tangentHeight_nonneg hO hcv hf hp ha hx.1
    dsimp [g,tangentShift]
    linarith
  have haΩ : a ∈ Ω := ⟨ha,by simpa using hh⟩
  have habase : h ≤ -g a := by simp [g,tangentShift]
  have hbnd := affineMaximal_det_upper_on_compact_section hO hΩ hK hΩK hKV hg hpg hmg
    hneg hbd (sq_nonneg (4*M/r)) hh.le hh hgrad hdepth haΩ habase
  rwa [hessian_tangentShift hO hf a h ha] at hbnd

end LocalDetProducer


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.affineMaximal_det_upper_of_section_control_oai := @OAI.AffineBernstein.affineMaximal_det_upper_of_section_control_oai
