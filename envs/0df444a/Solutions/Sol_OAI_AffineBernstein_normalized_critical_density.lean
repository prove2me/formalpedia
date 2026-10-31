-- Prove2me | solution 1 for OAI.AffineBernstein.normalized_critical_density
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:18:44.308505+00:00
-- url     : https://prove2.me/submissions/dca74ebf-7cfa-4c69-b5c4-1387010a037d

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_normalized_balanced_det_bounds

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

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

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

section MatrixConcavity
open scoped MatrixOrder

/-- Congruence by the inverse positive square root converts the determinant
ratio and the mixed trace to the same positive semidefinite matrix. -/
theorem exists_normalized_posSemidef {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    ∃ C : Matrix (Fin n) (Fin n) ℝ, C.PosSemidef ∧
      C.det = B.det / A.det ∧ C.trace = (A⁻¹ * B).trace := by
  let S := CFC.sqrt A⁻¹
  have hS : S.conjTranspose = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A⁻¹)).isHermitian.eq
  have hSsq : S * S = A⁻¹ := by
    simpa only [S, pow_two] using CFC.sq_sqrt A⁻¹ hA.inv.posSemidef.nonneg
  let C := S * B * S.conjTranspose
  refine ⟨C, hB.mul_mul_conjTranspose_same S, ?_, ?_⟩
  · calc
      C.det = (S * S).det * B.det := by
        simp only [C, hS, Matrix.det_mul]
        ring
      _ = B.det / A.det := by
        rw [hSsq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
        ring
  · dsimp only [C]
    rw [hS, Matrix.trace_mul_cycle, hSsq]

end MatrixConcavity

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

/-- The true Euclidean gradient has Jacobian determinant equal to the
coordinate Hessian determinant, including dimension zero. -/
lemma det_fderiv_gradient_eq_hessian {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) :
    (fderiv ℝ (gradient u) x).det = (hessian u x).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have he : LinearMap.toMatrix b b (fderiv ℝ (gradient u) x).toLinearMap =
      (hessian u x).transpose := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change (OrthonormalBasis.repr (EuclideanSpace.basisFun (Fin n) ℝ)
      (fderiv ℝ (gradient u) x ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i = _
    rw [OrthonormalBasis.repr_apply_apply,real_inner_comm,
      inner_fderiv_gradient hu,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_apply]
    exact (hessian_eq_second hu j i).symm
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,he,Matrix.det_transpose]

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

lemma hessian_neg {k : ℕ} (f : Space k → ℝ) (x : Space k) :
    hessian (fun y => -f y) x = -hessian f x := by
  ext i j
  simp only [hessian,fderiv_fun_neg,neg_apply,Matrix.neg_apply]

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

end LogBarrierCalculus


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

end DetBarrierPhase


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ABPMatrix
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

section ABPMatrix

lemma det_le_det_mul_mixed_trace_pow {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hB : B.PosSemidef) :
    B.det ≤ A.det * ((A⁻¹ * B).trace)^n := by
  obtain ⟨C,hC,hCd,hCt⟩ := exists_normalized_posSemidef hA hB
  have hh := posSemidef_det_le_trace_pow hC
  rw [hCd,hCt] at hh
  have he := (div_le_iff₀ hA.det_pos).mp hh
  simpa only [mul_comm] using he

lemma hessian_det_le_of_linearized_bound {n : ℕ} {u f : Space n → ℝ}
    {x : Space n} (hu : (hessian u x).PosDef) (hf : (hessian f x).PosSemidef)
    {K : ℝ} (_ : 0 ≤ K) (hL : inverseHessianTrace u f x ≤ K) :
    (hessian f x).det ≤ (hessian u x).det * K^n := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hf.isHermitian
  have ht : ((hessian u x)⁻¹ * hessian f x).trace = inverseHessianTrace u f x := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,inverseHessianTrace]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs.apply i j]
  have hh := det_le_det_mul_mixed_trace_pow hu hf
  rw [ht] at hh
  have hn : 0 ≤ inverseHessianTrace u f x := by
    rw [← ht]
    exact trace_mul_posSemidef_nonneg hu.posSemidef.inv hf
  exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn hL n) hu.det_pos.le)

end ABPMatrix

open Filter
open scoped Topology

lemma hessian_posSemidef_of_localMin {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ ∞ f x) (hm : IsLocalMin f x) : (hessian f x).PosSemidef := by
  have hh := hessian_neg_posSemidef_of_localMax hf.neg hm.neg
  simpa only [hessian_neg,neg_neg] using hh

/-- The elementary supporting-plane step of ABP, without convex-envelope axioms. -/
lemma abp_gradient_coverage {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set (Space n)} (hK : IsCompact K) {a : Space n} (ha : a ∈ K)
    {m R : ℝ} (hm : 0 < m) (hR : 0 < R)
    (hKR : K ⊆ Metric.closedBall a R) (hfa : f a ≤ -m)
    (hb : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x) :
    ∀ p ∈ Metric.ball (0 : Space n) (m/(2*R)),
      ∃ x ∈ interior K, f x < 0 ∧ (hessian f x).PosSemidef ∧ gradient f x = p := by
  intro p hp
  have hpN : ‖p‖ * R < m/2 := by
    rw [Metric.mem_ball,dist_zero_right] at hp
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*R)).mp hp
    nlinarith
  let g := graphAffineFunction f (-innerSL ℝ p) 1 (inner ℝ p a)
  have hg : ContDiff ℝ ∞ g :=
    ((-innerSL ℝ p).contDiff.add (contDiff_const.mul hf)).add contDiff_const
  have hge (x : Space n) : g x = f x - inner ℝ p (x-a) := by
    simp only [g,graphAffineFunction,neg_apply,innerSL_apply_apply,
      one_mul,inner_sub_right]
    ring
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn ⟨a,ha⟩ hg.continuous.continuousOn
  have hxR : ‖x-a‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hKR hx
  have hip : inner ℝ p (x-a) < m/2 :=
    (real_inner_le_norm _ _).trans_lt ((mul_le_mul_of_nonneg_left hxR (norm_nonneg p)).trans_lt hpN)
  have hlow : f x < 0 := by
    have ht : g x ≤ g a := hmin ha
    rw [hge,hge] at ht
    simp only [sub_self,inner_zero_right,sub_zero] at ht
    linarith
  have hxi : x ∈ interior K := by
    by_contra H
    exact (not_lt_of_ge (hb x hx H)) hlow
  have hl : IsLocalMin g x :=
    hmin.isLocalMin (mem_of_superset (isOpen_interior.mem_nhds hxi) interior_subset)
  have hhe : hessian g x = hessian f x := by
    ext i j
    simpa only [g,one_mul] using hessian_graphAffineFunction isOpen_univ hf.contDiffOn
      (mem_univ x) (-innerSL ℝ p) 1 (inner ℝ p a) i j
  refine ⟨x,hxi,hlow,?_,?_⟩
  · rw [← hhe]
    exact hessian_posSemidef_of_localMin hg.contDiffAt hl
  · apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left]
    have hdz : dirDeriv v g x = 0 := by rw [dirDeriv,hl.fderiv_eq_zero]; rfl
    rw [dirDeriv_graphAffineFunction (hf.differentiable (by simp) x)] at hdz
    simp only [neg_apply,innerSL_apply_apply,one_mul] at hdz
    change fderiv ℝ f x v = inner ℝ p v
    change -inner ℝ p v + fderiv ℝ f x v = 0 at hdz
    linarith

lemma isCompact_abpContactSet {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) : IsCompact (abpContactSet K f) := by
  have hf2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    ((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous
  apply hK.of_isClosed_subset _ (fun _ hx => hx.1)
  have hc : IsClosed {x | ∀ v : Space n, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v} := by
    simpa only [ofPred_forall] using
      (isClosed_iInter fun v : Space n => isClosed_le (continuous_const (y := (0:ℝ)))
        ((hf2.clm_apply (continuous_const (y := v))).clm_apply (continuous_const (y := v))))
  exact hK.isClosed.inter ((isClosed_le hf.continuous continuous_const).inter hc)

lemma abpContactSet_hessian {n : ℕ} {K : Set (Space n)} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) {x : Space n} (hx : x ∈ abpContactSet K f) :
    (hessian f x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (hessian_isSymm hf.contDiffAt)
  intro p
  let v : Space n := (WithLp.equiv 2 (Fin n → ℝ)).symm p
  have hh := hx.2.2 v
  rw [second_fderiv_eq_sum hf.contDiffAt] at hh
  simpa [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc,v] using hh

/-- The measure-theoretic ABP estimate uses the genuine gradient Jacobian.
No injectivity of the gradient or convexity of the tested function is assumed. -/
theorem abp_contact_measure {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    {K : Set (Space n)} (hK : IsCompact K) {a : Space n} (ha : a ∈ K)
    {m R D : ℝ} (hm : 0 < m) (hR : 0 < R)
    (hKR : K ⊆ Metric.closedBall a R) (hfa : f a ≤ -m)
    (hb : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    (hdet : ∀ x ∈ abpContactSet K f, (hessian f x).det ≤ D) :
    volume (Metric.ball (0 : Space n) (m/(2*R))) ≤
      ENNReal.ofReal D * volume (abpContactSet K f) := by
  let C := abpContactSet K f
  have hC := isCompact_abpContactSet hK hf
  have hg : Metric.ball (0 : Space n) (m/(2*R)) ⊆ gradient f '' C := by
    intro p hp
    obtain ⟨x,hxi,hfx,hpx,hgx⟩ := abp_gradient_coverage hf hK ha hm hR hKR hfa hb p hp
    refine ⟨x,⟨interior_subset hxi,hfx.le,?_⟩,hgx⟩
    intro v
    exact second_fderiv_nonneg hf.contDiffAt hpx v
  calc
    _ ≤ volume (gradient f '' C) := measure_mono hg
    _ ≤ ∫⁻ x in C, ENNReal.ofReal |(fderiv ℝ (gradient f) x).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume hC.measurableSet
        (fun _ _ => ((contDiffAt_gradient hf.contDiffAt).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    _ ≤ ∫⁻ _x in C, ENNReal.ofReal D := by
      apply setLIntegral_mono' hC.measurableSet
      intro x hx
      rw [det_fderiv_gradient_eq_hessian hf.contDiffAt,
        abs_of_nonneg (abpContactSet_hessian hf hx).det_nonneg]
      exact ENNReal.ofReal_le_ofReal (hdet x hx)
    _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,C]

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

end TangentShiftCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ABPCriticalDensity
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

section ABPCriticalDensity

/-- Critical density for a positive supersolution of the actual linearized
Monge--Ampère operator. The touching paraboloid is replaced by the genuine
convex tangent section, so no ellipticity-ratio bound is presupposed. -/
theorem linearizedMA_critical_density {n : ℕ} {u s : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hs : ContDiff ℝ ∞ s)
    (hp : ∀ x, (hessian u x).PosDef)
    {a : Space n} {h ε R D : ℝ} (hh : 0 < h) (hε : 0 < ε) (hR : 0 < R)
    (hD : 0 ≤ D)
    (hK : IsCompact {x | tangentHeight u a x ≤ h})
    (hKR : {x | tangentHeight u a x ≤ h} ⊆ Metric.closedBall a R)
    (hspos : ∀ x, 0 ≤ s x) (hsa : s a ≤ ε)
    (hLs : ∀ x, inverseHessianTrace u s x ≤ 0)
    (hdet : ∀ x, tangentHeight u a x ≤ h → (hessian u x).det ≤ D) :
    volume (Metric.ball (0 : Space n) (1/(2*R))) ≤
      ENNReal.ofReal (D * (2*(n:ℝ)/h)^n) *
        volume {x | tangentHeight u a x ≤ h ∧ s x ≤ 2*ε} := by
  let K : Set (Space n) := {x | tangentHeight u a x ≤ h}
  let q := tangentShift u a h
  let f : Space n → ℝ := fun x => ε⁻¹ * s x + (2/h)*q x
  have hq : ContDiff ℝ ∞ q :=
    contDiffOn_univ.mp (contDiffOn_tangentShift hu.contDiffOn a h)
  have hf : ContDiff ℝ ∞ f := (contDiff_const.mul hs).add (contDiff_const.mul hq)
  have ha : a ∈ K := by simp only [K,mem_ofPred_eq,tangentHeight,sub_self,map_zero]; linarith
  have hfa : f a ≤ -(1:ℝ) := by
    have he : q a = -h := by simp [q,tangentShift,tangentHeight]
    dsimp only [f]
    rw [he]
    have hdiv := (div_le_one hε).mpr hsa
    rw [div_eq_mul_inv,mul_comm] at hdiv
    have hht : (2/h)*(-h) = -(2:ℝ) := by field_simp [hh.ne']
    rw [hht]
    linarith
  have hboundary (x : Space n) (hx : x ∈ K) (hxi : x ∉ interior K) : q x = 0 := by
    have hle : tangentHeight u a x ≤ h := hx
    have he : tangentHeight u a x = h := by
      by_contra H
      have hlt : tangentHeight u a x < h := lt_of_le_of_ne hle H
      have hcont : Continuous (tangentHeight u a) := by
        exact ((hu.continuous.sub continuous_const).sub
          ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const)))
      have hopen : IsOpen {y | tangentHeight u a y < h} := isOpen_lt hcont continuous_const
      have hi : {y | tangentHeight u a y < h} ⊆ interior K :=
        interior_maximal (fun y hy => (show tangentHeight u a y ≤ h from le_of_lt hy)) hopen
      exact hxi (hi hlt)
    simp only [q,tangentShift,he,sub_self]
  have hb : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x := by
    intro x hx hxi
    simp only [f,hboundary x hx hxi,mul_zero,add_zero]
    exact mul_nonneg (inv_nonneg.mpr hε.le) (hspos x)
  have hL (x : Space n) : inverseHessianTrace u f x ≤ 2*(n:ℝ)/h := by
    rw [show f = (fun y => ε⁻¹*s y+(2/h)*q y) from rfl,
      inverseHessianTrace_add isOpen_univ (contDiffOn_const.mul hs.contDiffOn)
        (contDiffOn_const.mul hq.contDiffOn) (mem_univ x),
      inverseHessianTrace_const_mul isOpen_univ hs.contDiffOn (mem_univ x),
      inverseHessianTrace_const_mul isOpen_univ hq.contDiffOn (mem_univ x)]
    have he : inverseHessianTrace u q x = (n:ℝ) := by
      change (∑ i,∑ j, (hessian u x)⁻¹ i j * hessian q x i j) = _
      rw [show hessian q x = hessian u x from hessian_tangentShift isOpen_univ hu.contDiffOn a h (mem_univ x)]
      exact inverseHessianTrace_self (hp x)
    rw [he]
    have hn := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hε.le) (hLs x)
    have ht : (2/h)*(n:ℝ) = 2*(n:ℝ)/h := by ring
    rw [ht]
    linarith
  have hd (x : Space n) (hx : x ∈ abpContactSet K f) :
      (hessian f x).det ≤ D*(2*(n:ℝ)/h)^n := by
    have ht := hessian_det_le_of_linearized_bound (hp x) (abpContactSet_hessian hf hx)
      (by positivity : 0 ≤ 2*(n:ℝ)/h) (hL x)
    exact ht.trans (mul_le_mul (hdet x hx.1) le_rfl (by positivity) hD)
  have haB := abp_contact_measure hf hK ha zero_lt_one hR hKR hfa hb hd
  have hlow : abpContactSet K f ⊆ {x | tangentHeight u a x ≤ h ∧ s x ≤ 2*ε} := by
    intro x hx
    refine ⟨hx.1,?_⟩
    have hqnonneg := tangentHeight_nonneg isOpen_univ convex_univ hu.contDiffOn
      (fun y hy => hp y) (mem_univ a) (mem_univ x)
    have hxF : ε⁻¹*s x+(2/h)*(tangentHeight u a x-h) ≤ 0 := hx.2.1
    have htwo : (2/h)*h = (2:ℝ) := by field_simp [hh.ne']
    have hn : 0 ≤ (2/h)*tangentHeight u a x := mul_nonneg (by positivity) hqnonneg
    rw [mul_sub,htwo] at hxF
    have hr : s x/ε ≤ 2 := by rw [div_eq_mul_inv,mul_comm]; linarith
    exact (div_le_iff₀ hε).mp hr
  exact haB.trans (mul_le_mul_right (measure_mono (μ := volume) hlow) _)

end ABPCriticalDensity



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
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedCriticalDensity
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

section NormalizedCriticalDensity

/-- Uniform positive low-set measure, with no hidden ellipticity assumption. -/
theorem normalized_critical_density_oai {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ s : Space n → ℝ, ContDiff ℝ ∞ s → (∀ x, 0 ≤ s x) →
      (∀ x, inverseHessianTrace v s x ≤ 0) → ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ),
      ∀ ε : ℝ, 0 < ε → s a ≤ ε →
      δ ≤ (volume {x | x ∈ Metric.closedBall (0:Space n) (1/16:ℝ) ∧ s x ≤ 2*ε}).toReal := by
  obtain ⟨c,C,hc,hC,Hdet⟩ := normalized_balanced_det_bounds hρ hρ1 hR (n := n)
  let h := normalizedModulus ρ R (1/64:ℝ)/2
  have hh : 0 < h := half_pos (normalizedModulus_pos hρ)
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  let D := C*(2*(n:ℝ)/h)^n
  have hD : 0 < D := by dsimp [D]; positivity
  let δ := (volume (Metric.ball (0:Space n) (32:ℝ))).toReal/D
  have hballfin : volume (Metric.ball (0:Space n) (32:ℝ)) ≠ ⊤ := measure_ball_lt_top.ne
  have hballpos : 0 < volume (Metric.ball (0:Space n) (32:ℝ)) :=
    Metric.measure_ball_pos volume _ (by norm_num)
  have hδ : 0 < δ := div_pos (ENNReal.toReal_pos hballpos.ne' hballfin) hD
  refine ⟨δ,hδ,?_⟩
  intro v hv s hs hspos hLs a ha ε hε hsa
  let K := {x | tangentHeight v a x ≤ h}
  let B := Metric.closedBall (0:Space n) (1/16:ℝ)
  have hK : IsCompact K := by
    simpa only [K,mem_univ,true_and] using isCompact_tangent_sublevel isOpen_univ convex_univ hv.smooth.contDiffOn
      (fun x _ => hv.posDef x) (euclideanGraphComplete_entire hv.smooth) (mem_univ a) h
  have han : ‖a‖ < (1/64:ℝ) := by simpa only [Metric.mem_ball,dist_zero_right] using ha
  have ham : a ∈ Metric.ball (0:Space n) (1/4:ℝ) := by
    rw [Metric.mem_ball,dist_zero_right]; linarith
  have hsmall (x : Space n) (hx : x ∈ K) : x ∈ Metric.ball a (1/64:ℝ) := by
    apply normalized_modulus_of_sectionBalance hv.smooth hv.posDef
      (euclideanGraphComplete_entire hv.smooth) hv.zero hv.deriv_zero hρ hρ1 hR
      hv.balance hv.inner hv.outer ham (by norm_num : (0:ℝ)<1/64)
    refine ⟨mem_univ x,?_⟩
    have hx' : tangentHeight v a x ≤ h := hx
    have hh' := normalizedModulus_pos (R := R) (r := (1/64:ℝ)) hρ
    dsimp [h] at hx'
    linarith
  have hKB : K ⊆ B := by
    intro x hx
    have hxn : ‖x-a‖ < (1/64:ℝ) := by
      simpa only [Metric.mem_ball,dist_eq_norm] using hsmall x hx
    have H := norm_add_le (x-a) a
    rw [sub_add_cancel] at H
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith
  have hKC (x : Space n) (hx : tangentHeight v a x ≤ h) : (hessian v x).det ≤ C := by
    have hxB := hKB hx
    have hxn : ‖x‖ ≤ (1/16:ℝ) := by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hxB
    exact (Hdet v hv.smooth hv.posDef hv.maximal hv.zero hv.deriv_zero hv.balance hv.inner hv.outer x
      (by rw [Metric.mem_ball,dist_zero_right]; linarith)).2
  have habp := linearizedMA_critical_density hv.smooth hs hv.posDef hh hε
    (by norm_num : (0:ℝ)<1/64) hC.le hK (fun x hx => Metric.ball_subset_closedBall (hsmall x hx))
    hspos hsa hLs hKC
  norm_num only [show 1/(2*(1/64:ℝ))=(32:ℝ) by norm_num] at habp
  let L := {x | tangentHeight v a x ≤ h ∧ s x ≤ 2*ε}
  let T := {x | x ∈ B ∧ s x ≤ 2*ε}
  have hLT : L ⊆ T := fun _ hx => ⟨hKB hx.1,hx.2⟩
  have hTf : volume T ≠ ⊤ := ne_top_of_le_ne_top
    (isCompact_closedBall (0:Space n) (1/16:ℝ)).measure_lt_top.ne (measure_mono fun _ hx => hx.1)
  have hLf : volume L ≠ ⊤ := ne_top_of_le_ne_top hTf (measure_mono hLT)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLf) habp
  change (volume (Metric.ball (0:Space n) (32:ℝ))).toReal ≤
    (ENNReal.ofReal D * volume L).toReal at hreal
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hD.le] at hreal
  have hmono := ENNReal.toReal_mono hTf (measure_mono hLT)
  change δ ≤ (volume T).toReal
  exact ((div_le_iff₀ hD).mpr (by nlinarith)).trans hmono

end NormalizedCriticalDensity


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.normalized_critical_density_oai := @OAI.AffineBernstein.normalized_critical_density_oai
