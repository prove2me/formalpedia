-- Prove2me | solution 1 for OAI.AffineBernstein.normalized_model_positive_face_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:21:38.130967+00:00
-- url     : https://prove2.me/submissions/136bc4ed-9a06-419b-bffb-c7106ef12970

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_complete_affineMaximal_positive_cap_area

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

end RadialCalculus

/-- Smoothness of the area density on the original domain. -/
theorem contDiffAt_affineAreaDensity {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef) :
    ContDiffAt ℝ ∞ (affineAreaDensity u) x :=
  (contDiffAt_det_hessian hu).rpow_const_of_ne (ne_of_gt hpos.det_pos)

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

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma toEuclideanCLM_equivMatrix {n : ℕ} (B : Space n ≃L[ℝ] Space n) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (equivMatrix B) = B.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_toMatrix _ _ _

lemma equivMatrix_det_ne {n : ℕ} (B : Space n ≃L[ℝ] Space n) :
    (equivMatrix B).det ≠ 0 :=
  isUnit_iff_ne_zero.mp (B.toLinearEquiv.isUnit_det _ _)

lemma equivMatrix_det {n : ℕ} (B : Space n ≃L[ℝ] Space n) :
    (equivMatrix B).det = B.toContinuousLinearMap.det :=
  LinearMap.det_toMatrix _ _

lemma cleGraphPullback_eq {n : ℕ} (u : Space n → ℝ) (B : Space n ≃L[ℝ] Space n)
    (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) :
    cleGraphPullback u B d a c e = affineGraphPullback u (equivMatrix B) d a c e := by
  funext x
  simp only [cleGraphPullback, affineGraphPullback, graphAffineFunction, affineBaseMap,
    toEuclideanCLM_equivMatrix, ContinuousLinearEquiv.coe_coe]

lemma verticalShear_straightens {n : ℕ} (e : Space n × ℝ) (he : e.2 ≠ 0) :
    verticalShear (e.2⁻¹ • e.1) e = ((0 : Space n),e.2) := by
  simp [smul_smul,he]

lemma triangular_snd {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (x : Space n) (t : ℝ) :
    (M (x,t)).2 = (M (x,0)).2+c*t := by
  have he : (x,t) = (x,0)+((0 : Space n),t) := by simp
  rw [he,map_add,vertical_map M hc]
  rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapChangeOfVariables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma determinant_triangular {n : ℕ}
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) :
    M.toContinuousLinearMap.det = (triangularBaseEquiv M hc hcn).toContinuousLinearMap.det*c := by
  change LinearMap.det M.toLinearEquiv.toLinearMap = _
  rw [← LinearMap.det_toMatrix (graphAmbientBasis n)]
  have he : LinearMap.toMatrix (graphAmbientBasis n) (graphAmbientBasis n) M.toLinearEquiv.toLinearMap =
      Matrix.fromBlocks (equivMatrix (triangularBaseEquiv M hc hcn)) 0
        (Matrix.of fun (_ : Unit) j => (M ((EuclideanSpace.basisFun (Fin n) ℝ) j,0)).2)
        (Matrix.of fun (_ _ : Unit) => c) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,equivMatrix,
        Matrix.fromBlocks,triangularBaseEquiv_apply]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks,hc]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks,hc]
  rw [he,Matrix.det_fromBlocks_zero₁₂,equivMatrix_det,Matrix.det_unique]
  rfl

lemma det_verticalShear {n : ℕ} (p : Space n) :
    (verticalShear p).toContinuousLinearMap.det = 1 := by
  change LinearMap.det (verticalShear p).toLinearEquiv.toLinearMap = _
  rw [← LinearMap.det_toMatrix (graphAmbientBasis n)]
  have he : LinearMap.toMatrix (graphAmbientBasis n) (graphAmbientBasis n)
      (verticalShear p).toLinearEquiv.toLinearMap =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ)
        (Matrix.of fun i (_ : Unit) => -p i) 0 (1 : Matrix Unit Unit ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks,Matrix.one_apply]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks]
    · simp [LinearMap.toMatrix_apply,graphAmbientBasis,Matrix.fromBlocks]
  rw [he,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,Matrix.det_one,mul_one]

lemma affineAreaDensity_cleGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (B : Space n ≃L[ℝ] Space n) (d : Space n) (a : Space n →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (e : ℝ) {x : Space n} (hx : B x+d ∈ Ω) :
    affineAreaDensity (cleGraphPullback u B d a c e) x =
      Real.rpow (c^n*(equivMatrix B).det^2) (1/((n:ℝ)+2))*affineAreaDensity u (B x+d) := by
  have he : affineBaseMap (equivMatrix B) d x = B x+d := by
    simp [affineBaseMap,toEuclideanCLM_equivMatrix]
  rw [cleGraphPullback_eq,affineAreaDensity,
    hessian_affineGraphPullback hΩ hu (equivMatrix B) d a c e (he ▸ hx),
    det_affine_congruence,he]
  exact Real.mul_rpow (mul_nonneg (pow_nonneg hc.le _) (sq_nonneg _)) (hp _ hx).det_pos.le

lemma integral_affine_base_preimage {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    (d : Space n) {E : Set (Space n)} (hE : MeasurableSet E) (f : Space n → ℝ) :
    (∫ x in E, f x) = |B.toContinuousLinearMap.det| *
      ∫ y in {y | B y+d ∈ E}, f (B y+d) := by
  have hc : Continuous (fun y => B y+d) := B.continuous.add_const d
  have himg : (fun y => B y+d) '' {y | B y+d ∈ E} = E := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩; exact hy
    · intro hx; exact ⟨B.symm (x-d),by simpa using hx,by simp⟩
  have hi := integral_image_eq_integral_abs_det_fderiv_smul (s := {y | B y+d ∈ E})
    (f := fun y => B y+d) (f' := fun _ => B.toContinuousLinearMap)
    volume (hE.preimage hc.measurable)
    (fun y hy => (B.hasFDerivAt.add_const d).hasFDerivWithinAt)
    (fun y hy z hz he => B.injective (add_right_cancel he)) f
  simpa only [himg,smul_eq_mul,integral_const_mul] using hi

lemma affine_area_pullback_integral {n : ℕ} {Ω E : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hE : MeasurableSet E) (hEΩ : E ⊆ Ω)
    (B : Space n ≃L[ℝ] Space n) (d : Space n) (a : Space n →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (e : ℝ) :
    |(equivMatrix B).det| * (∫ y in {y | B y+d ∈ E},
        affineAreaDensity (cleGraphPullback u B d a c e) y) =
      Real.rpow (c^n*(equivMatrix B).det^2) (1/((n:ℝ)+2)) *
        ∫ x in E, affineAreaDensity u x := by
  have hm : MeasurableSet {y | B y+d ∈ E} :=
    hE.preimage (B.continuous.add_const d).measurable
  have hi : (∫ y in {y | B y+d ∈ E}, affineAreaDensity (cleGraphPullback u B d a c e) y) =
      Real.rpow (c^n*(equivMatrix B).det^2) (1/((n:ℝ)+2)) *
        ∫ y in {y | B y+d ∈ E}, affineAreaDensity u (B y+d) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hm
    intro y hy
    exact affineAreaDensity_cleGraphPullback hΩ hu hp B d a hc e (hEΩ hy)
  rw [hi,integral_affine_base_preimage B d hE,equivMatrix_det]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AmbientStraightening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma ambientSwap_coordinates {n : ℕ} (j : Fin n ⊕ Unit) (z : Space n × ℝ)
    (i : Fin n ⊕ Unit) :
    ambientCoordinates n (ambientSwap j z) i =
      ambientCoordinates n z (Equiv.swap j (Sum.inr ()) i) := by
  simp [ambientSwap,LinearEquiv.funCongrLeft]

lemma ambientSwap_involutive {n : ℕ} (j : Fin n ⊕ Unit) :
    Function.Involutive (ambientSwap j) := by
  intro z
  apply (ambientCoordinates n).injective
  ext i
  simp only [ambientSwap_coordinates,Equiv.swap_apply_self]

lemma abs_det_involutive {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : V ≃L[ℝ] V) (h : Function.Involutive L) :
    |L.toContinuousLinearMap.det| = 1 := by
  have he : L.toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap = LinearMap.id := by
    ext x
    exact h x
  have hd := congrArg LinearMap.det he
  rw [LinearMap.det_comp,LinearMap.det_id] at hd
  change L.toContinuousLinearMap.det*L.toContinuousLinearMap.det = 1 at hd
  have hs := sq_abs L.toContinuousLinearMap.det
  have hn := abs_nonneg L.toContinuousLinearMap.det
  nlinarith

lemma abs_det_trans {n : ℕ} (L M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) :
    |(L.trans M).toContinuousLinearMap.det| =
      |M.toContinuousLinearMap.det| * |L.toContinuousLinearMap.det| := by
  change |LinearMap.det (M.toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap)| = _
  rw [LinearMap.det_comp,abs_mul]
  rfl

/-- A determinant-one-in-absolute-value coordinate change straightens any nonzero
vector upwards, with a uniform factor two bound on coordinate boxes. No Euclidean
structure is falsely assigned to the max-norm product. -/
theorem bounded_ambient_straightening {n : ℕ} {e : Space n × ℝ} (he : e ≠ 0) :
    ∃ (A : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (c : ℝ),
      0 < c ∧ A e = (0,c) ∧ |A.toContinuousLinearMap.det| = 1 ∧
      ∀ {R : ℝ}, 0 ≤ R → ∀ z : Space n × ℝ,
        (∀ i, |z.1 i| ≤ R) → |z.2| ≤ R →
        (∀ i, |(A z).1 i| ≤ 2*R) ∧ |(A z).2| ≤ 2*R := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ
    (fun i => |ambientCoordinates n e i|) Finset.univ_nonempty
  have hjmax (i) : |ambientCoordinates n e i| ≤ |ambientCoordinates n e j| := hj i (Finset.mem_univ _)
  have hjn : ambientCoordinates n e j ≠ 0 := by
    intro h
    apply he
    apply (ambientCoordinates n).injective
    ext i
    have hi := hjmax i
    simp only [h,abs_zero] at hi
    simpa using (abs_nonpos_iff.mp hi)
  let P := ambientSwap j
  have hP2 : (P e).2 = ambientCoordinates n e j := by
    have h := ambientSwap_coordinates j e (Sum.inr ())
    simpa only [ambientCoordinates_inr,Equiv.swap_apply_right] using h
  have hdetP : |P.toContinuousLinearMap.det| = 1 := abs_det_involutive P (ambientSwap_involutive j)
  have hPb {R : ℝ} (z : Space n × ℝ) (hz : ∀ i, |z.1 i| ≤ R) (ht : |z.2| ≤ R) :
      ∀ i, |ambientCoordinates n (P z) i| ≤ R := by
    intro i
    rw [show P = ambientSwap j from rfl,ambientSwap_coordinates]
    cases Equiv.swap j (Sum.inr ()) i with
    | inl l => simpa using hz l
    | inr l => simpa using ht
  let N : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ) :=
    if 0 < ambientCoordinates n e j then ContinuousLinearEquiv.refl ℝ _
    else (LinearEquiv.neg ℝ).toContinuousLinearEquiv
  have hN (z : Space n × ℝ) (i : Fin n ⊕ Unit) :
      |ambientCoordinates n (N z) i| = |ambientCoordinates n z i| := by
    dsimp [N]
    split_ifs <;> simp
  have hdetN : |N.toContinuousLinearMap.det| = 1 := by
    apply abs_det_involutive
    intro z
    dsimp [N]
    split_ifs <;> simp
  let Q := P.trans N
  have hQ2 : (Q e).2 = |ambientCoordinates n e j| := by
    dsimp [Q,N]
    split_ifs with h
    · simpa [abs_of_pos h] using hP2
    · have hn : ambientCoordinates n e j < 0 := lt_of_le_of_ne (le_of_not_gt h) hjn
      simpa [abs_of_neg hn] using congrArg Neg.neg hP2
  have hQmax (i : Fin n) : |(Q e).1 i| ≤ (Q e).2 := by
    rw [hQ2]
    change |ambientCoordinates n (N (P e)) (Sum.inl i)| ≤ _
    rw [hN,show P = ambientSwap j from rfl,ambientSwap_coordinates]
    exact hjmax _
  have hc : 0 < (Q e).2 := hQ2 ▸ (abs_pos.mpr hjn)
  let p := ((Q e).2)⁻¹ • (Q e).1
  have hp (i) : |p i| ≤ 1 := by
    change |((Q e).2)⁻¹*(Q e).1 i| ≤ 1
    rw [abs_mul,abs_inv,abs_of_pos hc]
    simpa only [inv_mul_cancel₀ hc.ne'] using mul_le_mul_of_nonneg_left (hQmax i) (inv_nonneg.mpr hc.le)
  refine ⟨Q.trans (verticalShear p),(Q e).2,hc,?_,?_,?_⟩
  · exact verticalShear_straightens (Q e) hc.ne'
  · simp only [abs_det_trans,det_verticalShear,abs_one,Q,hdetP,hdetN,mul_one]
  · intro R hR z hz ht
    have hQb (i) : |ambientCoordinates n (Q z) i| ≤ R := by
      change |ambientCoordinates n (N (P z)) i| ≤ R
      rw [hN]
      exact hPb z hz ht i
    have hs : |(Q z).2| ≤ R := by simpa using hQb (Sum.inr ())
    constructor
    · intro i
      change |(Q z).1 i-(Q z).2*p i| ≤ 2*R
      calc
        _ ≤ |(Q z).1 i|+|(Q z).2*p i| := abs_sub _ _
        _ = |(Q z).1 i|+|(Q z).2| * |p i| := by rw [abs_mul]
        _ ≤ R+R*1 := add_le_add (by simpa using hQb (Sum.inl i))
          (mul_le_mul hs (hp i) (abs_nonneg _) hR)
        _ = _ := by ring
    · change |(Q z).2| ≤ 2*R
      linarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphAreaCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {n : ℕ}

lemma det_updateCol_identity (i : Fin n) (v : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).updateCol i v).det = v i := by
  have hh := Matrix.det_updateCol_sum (1 : Matrix (Fin n) (Fin n) ℝ) i v
  simpa only [Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,Matrix.det_one] using hh

lemma toMatrix_fderiv_euclidean {F : Space n → Space n} {x : Space n}
    (hd : DifferentiableAt ℝ F x) (i j : Fin n) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fderiv ℝ F x).toLinearMap i j =
      fderiv ℝ (fun y => F y i) x (coordinateVector n j) := by
  have he := ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  rw [LinearMap.toMatrix_apply]
  change ((EuclideanSpace.basisFun (Fin n) ℝ).repr
    (fderiv ℝ F x ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i = _
  rw [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply]
  exact (congrArg (fun T : Space n →L[ℝ] ℝ => T (coordinateVector n j)) he).symm

lemma reciprocalChart_involutive (i : Fin n) {p : Space n} (hp : p i ≠ 0) :
    reciprocalChart i (reciprocalChart i p) = p := by
  ext j
  by_cases hj : j=i
  · subst j
    simp [reciprocalChart]
  · simp [reciprocalChart,hj,hp]

lemma reciprocalChart_injOn (i : Fin n) :
    Set.InjOn (reciprocalChart i) {p : Space n | p i ≠ 0} := by
  intro p hp q hq he
  have hh := congrArg (reciprocalChart i) he
  rwa [reciprocalChart_involutive i hp,reciprocalChart_involutive i hq] at hh

lemma contDiffAt_reciprocalChart (i : Fin n) {p : Space n} (hp : p i ≠ 0) :
    ContDiffAt ℝ ∞ (reciprocalChart i) p := by
  apply (contDiffAt_piLp 2).mpr
  intro j
  by_cases hj : j=i
  · simpa only [reciprocalChart,WithLp.ofLp_toLp,hj,ite_true,Pi.inv_def,EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).contDiff.contDiffAt.inv hp)
  · simpa only [reciprocalChart,WithLp.ofLp_toLp,hj,ite_false,Pi.div_def,EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj j : Space n →L[ℝ] ℝ).contDiff.contDiffAt).div
        ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).contDiff.contDiffAt) hp

lemma det_fderiv_reciprocalChart (i : Fin n) {p : Space n} (hp : p i ≠ 0) :
    (fderiv ℝ (reciprocalChart i) p).det = -((p i)⁻¹)^(n+1) := by
  let v : Fin n → ℝ := fun j => if j=i then -(p i)⁻¹ else -p j / p i
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hm : LinearMap.toMatrix b b (fderiv ℝ (reciprocalChart i) p).toLinearMap =
      (p i)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ).updateCol i v := by
    ext j k
    rw [toMatrix_fderiv_euclidean ((contDiffAt_reciprocalChart i hp).differentiableAt (by simp))]
    have hi : HasFDerivAt (fun z : Space n => (z i)⁻¹)
        (-(p i ^ 2)⁻¹ • (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) p :=
      (hasDerivAt_inv hp).comp_hasFDerivAt p
        (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).hasFDerivAt
    by_cases hj : j=i
    · subst j
      simp only [reciprocalChart,WithLp.ofLp_toLp,ite_true]
      rw [hi.fderiv]
      by_cases hk : k=i
      · subst k
        simp [Matrix.smul_apply,v,coordinateVector,pow_two,mul_inv_rev]
      · simp [Matrix.smul_apply,v,coordinateVector,hk,Ne.symm hk]
    · simp only [reciprocalChart,WithLp.ofLp_toLp,hj,ite_false,div_eq_mul_inv]
      have hmul := ((EuclideanSpace.proj j : Space n →L[ℝ] ℝ).hasFDerivAt.fun_mul hi).fderiv
      simp only [EuclideanSpace.coe_proj] at hmul
      rw [hmul]
      by_cases hk : k=i
      · subst k
        simp [Matrix.smul_apply,v,coordinateVector,hj,pow_two,div_eq_mul_inv]
        ring
      · by_cases hkj : k=j
        · subst k
          simp [Matrix.smul_apply,v,coordinateVector,hj,Ne.symm hj]
        · simp [Matrix.smul_apply,v,coordinateVector,hk,Ne.symm hk,Ne.symm hkj]
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,hm,Matrix.det_smul,
    det_updateCol_identity]
  simp only [Fintype.card_fin,v,ite_true,pow_succ,mul_neg]

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
section GraphProjection
variable {n : ℕ}

lemma norm_le_card_of_coord_bound {p : Space n} {R : ℝ}
    (_hR : 0 ≤ R) (hp : ∀ i, |p i| ≤ R) : ‖p‖ ≤ n*R := by
  rw [← sum_coordinateVector p]
  calc
    _ ≤ ∑ i, ‖p i • coordinateVector n i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, R := by
      apply Finset.sum_le_sum
      intro i _
      simpa [norm_smul,coordinateVector,Real.norm_eq_abs] using hp i
    _ = _ := by simp

lemma contDiffAt_graphProjection {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    ContDiffAt ℝ ∞ (graphProjection u i) x := by
  apply (contDiffAt_piLp 2).mpr
  intro j
  by_cases hj : j=i
  · simpa [graphProjection,hj] using hu
  · simpa [graphProjection,hj] using (EuclideanSpace.proj j : Space n →L[ℝ] ℝ).contDiff.contDiffAt

lemma det_fderiv_graphProjection {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    (fderiv ℝ (graphProjection u i) x).det = gradient u x i := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hm : LinearMap.toMatrix b b (fderiv ℝ (graphProjection u i) x).toLinearMap =
      (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => gradient u x j) := by
    ext j k
    rw [toMatrix_fderiv_euclidean ((contDiffAt_graphProjection hu i).differentiableAt (by simp))]
    by_cases hj : j=i
    · subst j
      simp only [graphProjection,WithLp.ofLp_toLp,Function.update_self,Matrix.updateRow_self]
      change fderiv ℝ u x (coordinateVector n k) = _
      rw [← inner_gradient_left]
      simp only [coordinateVector,EuclideanSpace.inner_single_right,
        RCLike.conj_to_real,one_mul]
    · simp only [graphProjection,WithLp.ofLp_toLp,Function.update_of_ne hj,
        Matrix.updateRow_ne hj]
      change fderiv ℝ (EuclideanSpace.proj j : Space n →L[ℝ] ℝ) x (coordinateVector n k) = _
      rw [ContinuousLinearMap.fderiv]
      simp [coordinateVector,Matrix.one_apply]
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,hm,← Matrix.det_transpose]
  rw [← Matrix.updateCol_transpose,Matrix.transpose_one]
  exact det_updateCol_identity i (fun j => gradient u x j)

lemma graphProjection_difference {u : Space n → ℝ} (i : Fin n) {x y : Space n}
    (he : graphProjection u i x = graphProjection u i y) :
    y-x = (y i-x i) • coordinateVector n i ∧ u x = u y := by
  have hh (j : Fin n) := congrArg (fun z : Space n => z j) he
  have heq : u x=u y := by simpa [graphProjection] using hh i
  refine ⟨?_,heq⟩
  ext j
  by_cases hj : j=i
  · subst j
    simp [coordinateVector]
  · have hxy : x j=y j := by simpa [graphProjection,hj] using hh j
    simp [coordinateVector,hj,hxy]

lemma graphProjection_injOn_signed {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : ConvexOn ℝ Ω u) (hu : ∀ x ∈ Ω, DifferentiableAt ℝ u x)
    (i : Fin n) {K : Set (Space n)} (hKΩ : K ⊆ Ω)
    (hs : (∀ x ∈ K, 0 < gradient u x i) ∨ (∀ x ∈ K, gradient u x i < 0)) :
    Set.InjOn (graphProjection u i) K := by
  intro x hx y hy he
  obtain ⟨hd,heq⟩ := graphProjection_difference i he
  have hd' : x-y = (x i-y i) • coordinateVector n i := by
    rw [← neg_sub y x,hd,← neg_smul,neg_sub]
  have hxy := convex_fderiv_support hc (hKΩ hx) (hKΩ hy) (hu x (hKΩ hx))
  have hyx := convex_fderiv_support hc (hKΩ hy) (hKΩ hx) (hu y (hKΩ hy))
  have hemi (z : Space n) : fderiv ℝ u z (coordinateVector n i) = gradient u z i := by
    rw [← inner_gradient_left]
    simp only [coordinateVector,EuclideanSpace.inner_single_right,
      RCLike.conj_to_real,one_mul]
  rw [hd,map_smul,smul_eq_mul,hemi,heq,sub_self] at hxy
  rw [hd',map_smul,smul_eq_mul,hemi,heq,sub_self] at hyx
  have hcoord : x i=y i := by
    rcases hs with hs|hs
    · have hp := hs x hx
      have hq := hs y hy
      nlinarith
    · have hp := hs x hx
      have hq := hs y hy
      nlinarith
  apply sub_eq_zero.mp
  rw [hd',hcoord,sub_self,zero_smul]

lemma reciprocalChart_coord_le_one (i : Fin n) {p : Space n}
    (hi : 1 ≤ |p i|) (hmax : ∀ j, |p j| ≤ |p i|) (j : Fin n) :
    |reciprocalChart i p j| ≤ 1 := by
  have hp : 0 < |p i| := lt_of_lt_of_le zero_lt_one hi
  by_cases hj : j=i
  · subst j
    simp only [reciprocalChart,WithLp.ofLp_toLp,ite_true,abs_inv]
    exact inv_le_one_of_one_le₀ hi
  · simp only [reciprocalChart,WithLp.ofLp_toLp,hj,ite_false,abs_div]
    exact (div_le_one hp).mpr (hmax j)

end GraphProjection

/-- Holder interpolation, with weights rather than reciprocal exponents.
The endpoint masses may be infinite; no hidden integrability premise is used. -/
lemma lintegral_geometric_mean_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x ^ p * g x ^ (1-p) ∂μ) ≤
      (∫⁻ x, f x ∂μ)^p * (∫⁻ x, g x ∂μ)^(1-p) := by
  have hconj : p⁻¹.HolderConjugate (1-p)⁻¹ := by
    apply Real.holderConjugate_iff.mpr
    exact ⟨(one_lt_inv₀ hp).mpr hp1,by simp⟩
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj (hf.pow_const p) (hg.pow_const (1-p))
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  simpa only [← ENNReal.rpow_mul,mul_inv_cancel₀ hp.ne',mul_inv_cancel₀ hq,
    ENNReal.rpow_one,one_div,inv_inv,Pi.mul_apply] using hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TriangularGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma triangularGraphFunction_eval {n : ℕ} (u : Space n → ℝ)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (v : Space n × ℝ) (y : Space n) :
    triangularGraphFunction u M hc hcn v y =
      triangularLinearHeight M ((triangularBaseEquiv M hc hcn).symm (y-v.1)) +
        c*u ((triangularBaseEquiv M hc hcn).symm (y-v.1))+v.2 := by
  simp only [triangularGraphFunction,cleGraphPullback,sub_eq_add_neg,map_add,map_neg,
    ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  ring

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

section CapCovariance

lemma affine_area_scaling_identity (n : ℕ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Real.rpow (c^n*d^2) (1/((n:ℝ)+2)) =
      d*Real.rpow (c/d) ((n:ℝ)/((n:ℝ)+2)) := by
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  have hfrac : (n:ℝ)*(1/((n:ℝ)+2)) = (n:ℝ)/((n:ℝ)+2) := by ring
  have hsum : (n:ℝ)/((n:ℝ)+2)+2*(1/((n:ℝ)+2)) = 1 := by field_simp
  have hh := Real.rpow_add hd ((n:ℝ)/((n:ℝ)+2)) (2*(1/((n:ℝ)+2)))
  rw [hsum,Real.rpow_one] at hh
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hc.le _) (sq_nonneg _),
    ← Real.rpow_natCast_mul hc.le n, ← Real.rpow_natCast_mul hd.le 2,hfrac,
    Real.div_rpow hc.le hd.le]
  have hdne : Real.rpow d ((n:ℝ)/((n:ℝ)+2)) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  apply (mul_right_cancel₀ hdne)
  field_simp
  norm_num only [Nat.cast_ofNat] at *
  rw [show (2:ℝ)*(1/((n:ℝ)+2)) = 2/((n:ℝ)+2) by ring] at hh
  nlinarith [hh]

lemma triangular_area_scaling {n : ℕ} (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    {c : ℝ} (hc : M (0,1) = (0,c)) (hcp : 0 < c) :
    Real.rpow (c^n*(equivMatrix (triangularBaseEquiv M hc hcp.ne').symm).det^2)
        (1/((n:ℝ)+2)) =
      |(equivMatrix (triangularBaseEquiv M hc hcp.ne').symm).det| *
        Real.rpow |M.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) := by
  let P := triangularBaseEquiv M hc hcp.ne'
  have hid : |P.toContinuousLinearMap.det| * |P.symm.toContinuousLinearMap.det| = 1 := by
    rw [← abs_mul]
    have hi := P.toLinearEquiv.det_mul_det_symm
    change P.toContinuousLinearMap.det*P.symm.toContinuousLinearMap.det = 1 at hi
    rw [hi,abs_one]
  have hpos : 0 < |(equivMatrix P.symm).det| := abs_pos.mpr (equivMatrix_det_ne _)
  have hdiv : c/|(equivMatrix P.symm).det| = |M.toContinuousLinearMap.det| := by
    apply (div_eq_iff hpos.ne').mpr
    rw [equivMatrix_det,determinant_triangular M hc hcp.ne',abs_mul,abs_of_pos hcp]
    change c = (|P.toContinuousLinearMap.det| * c) * |P.symm.toContinuousLinearMap.det|
    calc
      _ = c*1 := (mul_one c).symm
      _ = _ := by rw [← hid]; ring
  change Real.rpow (c^n*(equivMatrix P.symm).det^2) _ = _
  rw [← sq_abs (equivMatrix P.symm).det,affine_area_scaling_identity n hcp hpos,hdiv]

end CapCovariance
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

/-- The actual gradient of a strictly positive-Hessian function is injective;
in particular this applies to every principal-coordinate slice in the source. -/
lemma gradient_injOn_of_hessian_posDef {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) :
    Set.InjOn (gradient u) Ω := by
  apply injOn_of_positive_derivative hcv
  · intro x hx
    exact (contDiffAt_gradient (hu.contDiffAt (hΩ.mem_nhds hx))).differentiableAt (by simp)
  · intro x hx v hv
    rw [inner_fderiv_gradient (hu.contDiffAt (hΩ.mem_nhds hx))]
    exact second_fderiv_pos (hu.contDiffAt (hΩ.mem_nhds hx)) (hp x hx) hv

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

section GraphPatchArea
variable {n : ℕ}

lemma jacobian_geometric_mean_image_bound {K : Set (Space n)} (hK : MeasurableSet K)
    {F G : Space n → Space n}
    {F' G' : Space n → Space n →L[ℝ] Space n}
    (hF : ∀ x ∈ K, HasFDerivWithinAt F (F' x) K x)
    (hG : ∀ x ∈ K, HasFDerivWithinAt G (G' x) K x)
    (hiF : Set.InjOn F K) (hiG : Set.InjOn G K)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {d : Space n → ℝ}
    (hd : ∀ x ∈ K, d x = |(G' x).det|^p * |(F' x).det|^(1-p))
    {BF BG : Set (Space n)} (hbF : F '' K ⊆ BF) (hbG : G '' K ⊆ BG) :
    (∫⁻ x in K, ENNReal.ofReal (d x)) ≤
      (volume BG)^p * (volume BF)^(1-p) := by
  have hmF := aemeasurable_ofReal_abs_det_fderivWithin volume hK hF
  have hmG := aemeasurable_ofReal_abs_det_fderivWithin volume hK hG
  have hh := lintegral_geometric_mean_le (volume.restrict K) hp hp1 hmG hmF
  have he : (∫⁻ x in K, ENNReal.ofReal (d x)) =
      ∫⁻ x in K, (ENNReal.ofReal |(G' x).det|)^p *
        (ENNReal.ofReal |(F' x).det|)^(1-p) := by
    apply setLIntegral_congr_fun hK
    intro x hx
    dsimp only
    rw [hd x hx,ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _),
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (sub_pos.mpr hp1).le]
  rw [he]
  apply hh.trans
  rw [lintegral_abs_det_fderiv_eq_addHaar_image volume hK hG hiG,
    lintegral_abs_det_fderiv_eq_addHaar_image volume hK hF hiF]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (measure_mono hbG) hp.le)
    (ENNReal.rpow_le_rpow (measure_mono hbF) (sub_pos.mpr hp1).le)

lemma det_fderiv_reciprocal_gradient {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) (hi : gradient u x i ≠ 0) :
    (fderiv ℝ (reciprocalChart i ∘ gradient u) x).det =
      -((gradient u x i)⁻¹)^(n+1) * (hessian u x).det := by
  have hr := (contDiffAt_reciprocalChart i hi).differentiableAt (by simp)
  have hg := (contDiffAt_gradient hu).differentiableAt (by simp)
  rw [(hr.hasFDerivAt.comp x hg.hasFDerivAt).fderiv]
  change LinearMap.det ((fderiv ℝ (reciprocalChart i) (gradient u x)).toLinearMap.comp
    (fderiv ℝ (gradient u) x).toLinearMap) = _
  rw [LinearMap.det_comp]
  change (fderiv ℝ (reciprocalChart i) (gradient u x)).det *
    (fderiv ℝ (gradient u) x).det = _
  rw [det_fderiv_reciprocalChart i hi,det_fderiv_gradient_eq_hessian hu]

lemma graph_area_jacobian_factor {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef)
    (i : Fin n) (hi : gradient u x i ≠ 0) :
    (hessian u x).det ^ (1/((n:ℝ)+2)) =
      |(fderiv ℝ (reciprocalChart i ∘ gradient u) x).det|^(1/((n:ℝ)+2)) *
      |(fderiv ℝ (graphProjection u i) x).det|^(1-1/((n:ℝ)+2)) := by
  rw [det_fderiv_reciprocal_gradient hu i hi,det_fderiv_graphProjection hu i,
    abs_mul,abs_neg,abs_pow,abs_inv,abs_of_pos hpos.det_pos]
  have ha : 0 < |gradient u x i| := abs_pos.mpr hi
  have hn : (n:ℝ)+2 ≠ 0 := by positivity
  rw [Real.mul_rpow (by positivity) hpos.det_pos.le]
  rw [← Real.rpow_natCast (|gradient u x i|⁻¹),
    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ |gradient u x i|⁻¹),
    Real.inv_rpow ha.le]
  rw [mul_comm ((|gradient u x i| ^ ((n+1:ℕ) * (1/((n:ℝ)+2))))⁻¹),mul_assoc]
  have hexp : 1-1/((n:ℝ)+2) = (n+1:ℕ) * (1/((n:ℝ)+2)) := by
    push_cast
    field_simp
    ring
  rw [hexp,inv_mul_cancel₀ (Real.rpow_pos_of_pos ha _).ne',mul_one]

lemma graph_area_dominant_patch_bound {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hcu : ConvexOn ℝ Ω u)
    (i : Fin n) (hm : ∀ x ∈ K, 1 ≤ |gradient u x i| ∧ ∀ j, |gradient u x j| ≤ |gradient u x i|)
    (hs : (∀ x ∈ K, 0 < gradient u x i) ∨ (∀ x ∈ K, gradient u x i < 0))
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ K, ∀ j, |x j| ≤ R)
    (huR : ∀ x ∈ K, |u x| ≤ R) :
    (∫⁻ x in K, ENNReal.ofReal ((hessian u x).det^(1/((n:ℝ)+2)))) ≤
      (volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
      (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2)) := by
  have hux (x) (hx : x ∈ Ω) := hu.contDiffAt (hΩ.mem_nhds hx)
  have hi (x) (hx : x ∈ K) : gradient u x i ≠ 0 := by
    have := (hm x hx).1
    intro he
    norm_num [he] at this
  apply jacobian_geometric_mean_image_bound hK
    (fun x hx => ((contDiffAt_graphProjection (hux x (hKΩ hx)) i).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (fun x hx => (((contDiffAt_reciprocalChart i (hi x hx)).comp x
      (contDiffAt_gradient (hux x (hKΩ hx)))).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (graphProjection_injOn_signed hcu (fun x hx => (hux x hx).differentiableAt (by simp)) i hKΩ hs)
    ((reciprocalChart_injOn i).comp
      ((gradient_injOn_of_hessian_posDef hΩ hc hu hp).mono hKΩ) (fun x hx => hi x hx))
    (by positivity) (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; rw [div_lt_one (by positivity)]; linarith)
    (fun x hx => graph_area_jacobian_factor (hux x (hKΩ hx)) (hp x (hKΩ hx)) i (hi x hx))
  · rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    apply norm_le_card_of_coord_bound hR
    intro j
    by_cases hj : j=i
    · simpa [graphProjection,hj] using huR x hx
    · simpa [graphProjection,hj] using hxR x hx j
  · rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    simpa using norm_le_card_of_coord_bound (by norm_num : (0:ℝ)≤1)
      (reciprocalChart_coord_le_one i (hm x hx).1 (hm x hx).2)

end GraphPatchArea

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
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphBallArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section GraphBallArea
variable {n : ℕ}

lemma measurableSet_inter_preimage_continuousOn {E F : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [MeasurableSpace F] [TopologicalSpace F]
    [BorelSpace E] [BorelSpace F] {K : Set E} (hK : MeasurableSet K)
    {f : E → F} (hf : ContinuousOn f K) {B : Set F} (hB : MeasurableSet B) :
    MeasurableSet (K ∩ f ⁻¹' B) := by
  have hh := (MeasurableEmbedding.subtype_coe hK).measurableSet_image.mpr
    (hB.preimage hf.domRestrict.measurable)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  constructor
  · rintro ⟨hx,hf⟩
    exact ⟨⟨x,hx⟩,hf,rfl⟩
  · rintro ⟨⟨y,hy⟩,hz,rfl⟩
    exact ⟨hy,hz⟩

lemma graph_area_vertical_patch_bound {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : ∀ x ∈ K, ∀ j, |gradient u x j| ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ K, ∀ j, |x j| ≤ R) :
    (∫⁻ x in K, ENNReal.ofReal ((hessian u x).det^(1/((n:ℝ)+2)))) ≤
      (volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
      (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2)) := by
  have hux (x) (hx : x ∈ Ω) := hu.contDiffAt (hΩ.mem_nhds hx)
  apply jacobian_geometric_mean_image_bound hK
    (fun x _ => (hasFDerivAt_id (𝕜 := ℝ) x).hasFDerivWithinAt)
    (fun x hx => ((contDiffAt_gradient (hux x (hKΩ hx))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt)
    (Set.injOn_id K)
    ((gradient_injOn_of_hessian_posDef hΩ hc hu hp).mono hKΩ)
    (by positivity) (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; rw [div_lt_one (by positivity)]; linarith)
  · intro x hx
    rw [det_fderiv_gradient_eq_hessian (hux x (hKΩ hx)),abs_of_pos (hp x (hKΩ hx)).det_pos]
    simp [ContinuousLinearMap.det]
  · rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact norm_le_card_of_coord_bound hR (hxR x hx)
  · rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    simpa using norm_le_card_of_coord_bound (by norm_num : (0:ℝ)≤1) (hm x hx)

/-- A dimension/radius-only bound for the literal affine area on any measurable
part of a smooth strictly convex graph with |x_i|,|u| ≤ R. This proves the
area-in-a-ball producer without assuming a surface-area or Gauss-map theorem:
two injective coordinate projections supply its Jacobians directly. -/
theorem graph_affine_area_in_box {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ K, ∀ j, |x j| ≤ R)
    (huR : ∀ x ∈ K, |u x| ≤ R) :
    (∫⁻ x in K, ENNReal.ofReal ((hessian u x).det^(1/((n:ℝ)+2)))) ≤
      (2*n+1 : ℕ) * ((volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
      (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2))) := by
  classical
  let B0 : Set (Space n) := {p | ∀ j, |p j| ≤ 1}
  let Bp (i : Fin n) : Set (Space n) := {p | 1 ≤ p i ∧ ∀ j, |p j| ≤ |p i|}
  let Bm (i : Fin n) : Set (Space n) := {p | p i ≤ -1 ∧ ∀ j, |p j| ≤ |p i|}
  let K0 := K ∩ gradient u ⁻¹' B0
  let Kp (i : Fin n) := K ∩ gradient u ⁻¹' Bp i
  let Km (i : Fin n) := K ∩ gradient u ⁻¹' Bm i
  let C : ℝ≥0∞ := (volume (Metric.closedBall (0 : Space n) n))^(1/((n:ℝ)+2)) *
    (volume (Metric.closedBall (0 : Space n) (n*R)))^(1-1/((n:ℝ)+2))
  let A := fun x => ENNReal.ofReal ((hessian u x).det^(1/((n:ℝ)+2)))
  have hg : ContinuousOn (gradient u) K := fun x hx =>
    (contDiffAt_gradient (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))).continuousAt.continuousWithinAt
  have hmeas0 : MeasurableSet B0 := by
    dsimp [B0]
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) measurable_const
  have hmeasp (i : Fin n) : MeasurableSet (Bp i) := by
    change MeasurableSet ({p : Space n | 1 ≤ p i} ∩ {p | ∀ j, |p j| ≤ |p i|})
    apply MeasurableSet.inter (measurableSet_le measurable_const (by fun_prop))
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  have hmeasm (i : Fin n) : MeasurableSet (Bm i) := by
    change MeasurableSet ({p : Space n | p i ≤ -1} ∩ {p | ∀ j, |p j| ≤ |p i|})
    apply MeasurableSet.inter (measurableSet_le (by fun_prop) measurable_const)
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  have hm0 : MeasurableSet K0 := measurableSet_inter_preimage_continuousOn hK hg hmeas0
  have hmp (i : Fin n) : MeasurableSet (Kp i) := measurableSet_inter_preimage_continuousOn hK hg (hmeasp i)
  have hmm (i : Fin n) : MeasurableSet (Km i) := measurableSet_inter_preimage_continuousOn hK hg (hmeasm i)
  have hc0 : (∫⁻ x in K0, A x) ≤ C :=
    graph_area_vertical_patch_bound hΩ hc hm0 (fun _ hx => hKΩ hx.1) hu hp
      (fun _ hx => hx.2) hR (fun _ hx => hxR _ hx.1)
  have hcu := convexOn_of_hessian_posSemidef hΩ hc hu (fun x hx => (hp x hx).posSemidef)
  have hcp (i : Fin n) : (∫⁻ x in Kp i, A x) ≤ C := by
    apply graph_area_dominant_patch_bound hΩ hc (hmp i) (fun _ hx => hKΩ hx.1) hu hp hcu i
    · intro x hx
      have h1 := hx.2.1
      exact ⟨h1.trans (le_abs_self _),hx.2.2⟩
    · exact Or.inl (fun _ hx => lt_of_lt_of_le zero_lt_one hx.2.1)
    · exact hR
    · exact fun _ hx => hxR _ hx.1
    · exact fun _ hx => huR _ hx.1
  have hcm (i : Fin n) : (∫⁻ x in Km i, A x) ≤ C := by
    apply graph_area_dominant_patch_bound hΩ hc (hmm i) (fun _ hx => hKΩ hx.1) hu hp hcu i
    · intro x hx
      have h1 := hx.2.1
      refine ⟨?_,hx.2.2⟩
      have := neg_le_abs (gradient u x i)
      linarith
    · exact Or.inr (fun _ hx => lt_of_le_of_lt hx.2.1 (by norm_num))
    · exact hR
    · exact fun _ hx => hxR _ hx.1
    · exact fun _ hx => huR _ hx.1
  have hcover : K ⊆ K0 ∪ ⋃ i, (Kp i ∪ Km i) := by
    intro x hx
    by_cases hv : ∀ j, |gradient u x j| ≤ 1
    · exact Or.inl ⟨hx,hv⟩
    · obtain ⟨j,hj⟩ := not_forall.mp hv
      obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin n => |gradient u x i|)
        ⟨j,Finset.mem_univ j⟩
      have him : ∀ j, |gradient u x j| ≤ |gradient u x i| := fun j => hi j (Finset.mem_univ j)
      have hia : 1 < |gradient u x i| := (lt_of_not_ge hj).trans_le (him j)
      refine Or.inr (Set.mem_iUnion.mpr ⟨i,?_⟩)
      rcases le_total 0 (gradient u x i) with hsign|hsign
      · left
        refine ⟨hx,?_,him⟩
        rw [abs_of_nonneg hsign] at hia
        exact hia.le
      · right
        refine ⟨hx,?_,him⟩
        rw [abs_of_nonpos hsign] at hia
        linarith
  calc
    (∫⁻ x in K, A x) ≤ ∫⁻ x in K0 ∪ ⋃ i, (Kp i ∪ Km i), A x := lintegral_mono_set hcover
    _ ≤ (∫⁻ x in K0, A x) + ∫⁻ x in ⋃ i, (Kp i ∪ Km i), A x := lintegral_union_le A _ _
    _ ≤ C + ∑' i, ∫⁻ x in Kp i ∪ Km i, A x := add_le_add hc0 (lintegral_iUnion_le _ A)
    _ ≤ C + ∑' _i : Fin n, (C+C) := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro i
      exact (lintegral_union_le A _ _).trans (add_le_add (hcp i) (hcm i))
    _ = _ := by
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      push_cast
      ring

end GraphBallArea

lemma graphAreaBoxBound_ne_top (n : ℕ) (R : ℝ) : graphAreaBoxBound n R ≠ ⊤ := by
  have hd : 0 ≤ 1/((n:ℝ)+2) := by positivity
  have hd1 : 0 ≤ 1-1/((n:ℝ)+2) := by
    have : 1/((n:ℝ)+2) < 1 := by
      rw [div_lt_one (by positivity)]
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    linarith
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hd measure_closedBall_lt_top.ne)
    (ENNReal.rpow_ne_top_of_nonneg hd1 measure_closedBall_lt_top.ne))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineBoxArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma triangular_graph_patch_area {n : ℕ} {Ω K : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) :
    (∫ y in {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ K},
       affineAreaDensity (triangularGraphFunction u M hc hcp.ne' v) y) =
      Real.rpow |M.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        ∫ x in K, affineAreaDensity u x := by
  let P := triangularBaseEquiv M hc hcp.ne'
  let a := (triangularLinearHeight M).comp P.symm.toContinuousLinearMap
  have hi := affine_area_pullback_integral hΩ hu hp hK hKΩ
    P.symm (-P.symm v.1) a hcp (v.2-a v.1)
  change |(equivMatrix P.symm).det| * (∫ y in {y | P.symm y+(-P.symm v.1) ∈ K},
      affineAreaDensity (triangularGraphFunction u M hc hcp.ne' v) y) = _ at hi
  have he : {y | P.symm y+(-P.symm v.1) ∈ K} = {y | P.symm (y-v.1) ∈ K} := by
    ext y
    simp only [sub_eq_add_neg,mem_ofPred_eq,map_add,map_neg]
  rw [he,triangular_area_scaling M hc hcp] at hi
  apply mul_left_cancel₀ (abs_pos.mpr (equivMatrix_det_ne P.symm)).ne'
  exact hi.trans (by ring)

lemma triangularGraph_smooth_positive {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) :
    let Ω' := {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω}
    let g := triangularGraphFunction u M hc hcp.ne' v
    IsOpen Ω' ∧ ContDiffOn ℝ ∞ g Ω' ∧ (∀ y ∈ Ω', (hessian g y).PosDef) := by
  let B := (triangularBaseEquiv M hc hcp.ne').symm
  let a := (triangularLinearHeight M).comp B.toContinuousLinearMap
  have he : {y | B (y-v.1) ∈ Ω} = affineBaseMap (equivMatrix B) (-B v.1) ⁻¹' Ω := by
    ext y
    simp only [mem_ofPred_eq,mem_preimage,affineBaseMap,toEuclideanCLM_equivMatrix,
      ContinuousLinearEquiv.coe_coe,sub_eq_add_neg,map_add,map_neg]
  change IsOpen {y | B (y-v.1) ∈ Ω} ∧
    ContDiffOn ℝ ∞ (cleGraphPullback u B (-B v.1) a c (v.2-a v.1)) {y | B (y-v.1) ∈ Ω} ∧ _
  rw [cleGraphPullback_eq,he]
  refine ⟨hΩ.preimage (contDiff_affineBaseMap _ _).continuous,
    contDiffOn_affineGraphPullback hu _ _ _ _ _,?_⟩
  intro y hy
  change (hessian (cleGraphPullback u B (-B v.1) a c (v.2-a v.1)) y).PosDef
  rw [cleGraphPullback_eq]
  exact posDef_hessian_affineGraphPullback hΩ hu hp (equivMatrix_det_ne B) (-B v.1) a hcp (v.2-a v.1) hy

lemma integral_affineAreaDensity_le_box_measurable {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ K, ∀ j, |x j| ≤ R)
    (huR : ∀ x ∈ K, |u x| ≤ R) :
    (∫ x in K, affineAreaDensity u x) ≤ (graphAreaBoxBound n R).toReal := by
  have hcont : ContinuousOn (affineAreaDensity u) K := fun x hx =>
    (contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx))).continuousAt.continuousWithinAt
  have hnn : 0 ≤ᵐ[volume.restrict K] affineAreaDensity u := by
    filter_upwards [ae_restrict_mem hK] with x hx
    exact Real.rpow_nonneg (hp x (hKΩ hx)).det_pos.le _
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hcont.aestronglyMeasurable hK)]
  exact ENNReal.toReal_mono (graphAreaBoxBound_ne_top n R)
    (graph_affine_area_in_box hΩ hc hK hKΩ hu hp hR hxR huR)

/-- Genuine affine area of every bounded measurable patch of an arbitrary
invertible affine image of the original convex graph. The constant depends
only on dimension and the physical coordinate radius, not on the affine map. -/
theorem affine_image_graph_area_in_box {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (hxR : ∀ x ∈ K, ∀ i, |(L (x,u x)+v).1 i| ≤ R)
    (htR : ∀ x ∈ K, |(L (x,u x)+v).2| ≤ R) :
    Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      (∫ x in K, affineAreaDensity u x) ≤ (graphAreaBoxBound n (2*R)).toReal := by
  have he : L ((0 : Space n),1) ≠ 0 := by
    intro he
    have : ((0 : Space n),(1 : ℝ)) = 0 := L.injective (show L ((0 : Space n),1) = L 0 by simpa only [map_zero] using he)
    exact one_ne_zero (congrArg Prod.snd this)
  obtain ⟨A,c,hc,hAe,hAd,hAb⟩ := bounded_ambient_straightening he
  let M := L.trans A
  have hMc : M (0,1) = (0,c) := hAe
  let P := triangularBaseEquiv M hMc hc.ne'
  let Ω' : Set (Space n) := {y | P.symm (y-(A v).1) ∈ Ω}
  let K' : Set (Space n) := {y | P.symm (y-(A v).1) ∈ K}
  let g := triangularGraphFunction u M hMc hc.ne' (A v)
  have hreg := triangularGraph_smooth_positive hΩ hu hp M hMc hc (A v)
  have hΩ' : IsOpen Ω' := hreg.1
  have hg : ContDiffOn ℝ ∞ g Ω' := hreg.2.1
  have hgp : ∀ y ∈ Ω', (hessian g y).PosDef := hreg.2.2
  have hK' : MeasurableSet K' := hK.preimage (P.symm.continuous.comp (continuous_id.sub continuous_const)).measurable
  have hKΩ' : K' ⊆ Ω' := fun _ hy => hKΩ hy
  have hcv' : Convex ℝ Ω' := by
    intro x hx y hy a b ha hb hab
    change P.symm (a • x+b • y-(A v).1) ∈ Ω
    have heq : P.symm (a • x+b • y-(A v).1) =
        a • P.symm (x-(A v).1)+b • P.symm (y-(A v).1) := by
      rw [← map_smul,← map_smul,← map_add]
      congr 1
      calc
        _ = a • x+b • y-(a+b) • (A v).1 := by rw [hab,one_smul]
        _ = _ := by module
    rw [heq]
    exact hcv hx hy ha hb hab
  have himage (y : Space n) :
      M (P.symm (y-(A v).1),u (P.symm (y-(A v).1)))+A v = (y,g y) := by
    apply Prod.ext
    · change (M (_,u _)).1+(A v).1 = y
      rw [triangular_fst M hMc]
      change P (P.symm (y-(A v).1))+(A v).1 = y
      simp
    · rw [Prod.snd_add,triangular_snd M hMc]
      exact (triangularGraphFunction_eval u M hMc hc.ne' (A v) y).symm
  have hbox (y : Space n) (hy : y ∈ K') :
      (∀ i, |y i| ≤ 2*R) ∧ |g y| ≤ 2*R := by
    let x := P.symm (y-(A v).1)
    have hb := hAb hR (L (x,u x)+v) (hxR x hy) (htR x hy)
    have heq : A (L (x,u x)+v) = (y,g y) := by
      rw [map_add]
      exact himage y
    rwa [heq] at hb
  have hi := integral_affineAreaDensity_le_box_measurable hΩ' hcv' hK' hKΩ' hg hgp
    (mul_nonneg (by norm_num) hR) (fun y hy => (hbox y hy).1) (fun y hy => (hbox y hy).2)
  have har := triangular_graph_patch_area hΩ hu hp hK hKΩ M hMc hc (A v)
  have hd : |M.toContinuousLinearMap.det| = |L.toContinuousLinearMap.det| := by
    rw [show M = L.trans A from rfl,abs_det_trans,hAd,one_mul]
  rw [hd] at har
  exact har ▸ hi

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexLocalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Topology NNReal

open Filter Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- The local distance-function topology used in geometry.tex:70–101. Sets
are separately required to be nonempty and closed when those properties enter. -/

omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.pointwise {Cj : ℕ → Set E} {C : Set E}
    (h : LocalDistanceConverges Cj C) (x : E) :
    Tendsto (fun j => infDist x (Cj j)) atTop (𝓝 (infDist x C)) := by
  exact ((tendstoLocallyUniformly_iff_forall_isCompact.mp h) {x}
    (isCompact_singleton)).tendsto_at (mem_singleton x)

/- Every point of a local limit has an actual sequence of nearby points
in the approximating closed convex bodies (convexity is not needed here). -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.exists_approximating {Cj : ℕ → Set E} {C : Set E}
    (h : LocalDistanceConverges Cj C) (hcl : ∀ j, IsClosed (Cj j))
    (hne : ∀ j, (Cj j).Nonempty) {x : E} (hx : x ∈ C) :
    ∃ xj : ℕ → E, (∀ j, xj j ∈ Cj j) ∧ Tendsto xj atTop (𝓝 x) := by
  choose xj hmem heq using fun j => (hcl j).exists_infDist_eq_dist (hne j) x
  refine ⟨xj, hmem, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_comm, ← heq, infDist_zero_of_mem hx] using h.pointwise x

/- Local convergence prevents approximants from meeting any fixed compact
set disjoint from the closed limit. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.eventually_disjoint_compact
    {Cj : ℕ → Set E} {C S : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hne : C.Nonempty) (hS : IsCompact S)
    (hdis : Disjoint C S) : ∀ᶠ j in atTop, Disjoint (Cj j) S := by
  rcases S.eq_empty_or_nonempty with rfl | hSn
  · simp
  obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn hSn (continuous_infDist_pt C).continuousOn
  have hxnot : x ∉ C := fun hc => Set.disjoint_left.mp hdis hc hx
  have hδ : 0 < infDist x C := (hcl.notMem_iff_infDist_pos hne).mp hxnot
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp h S hS
  have he := Metric.tendstoUniformlyOn_iff.mp hU (infDist x C) hδ
  filter_upwards [he] with j hj
  rw [Set.disjoint_left]
  intro y hyC hyS
  have hd := hj y hyS
  have hmin' : infDist x C ≤ infDist y C := hmin hyS
  rw [infDist_zero_of_mem hyC, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at hd
  linarith

/- Limits of convergent points of approximants belong to the local limit. -/
theorem LocalDistanceConverges.eventually_bounded_caps
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hclj : ∀ j, IsClosed (Cj j))
    (hcvj : ∀ j, Convex ℝ (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (ell : E →L[ℝ] ℝ) (b : ℝ)
    (hbounded : Bornology.IsBounded (C ∩ {x | ell x ≤ b}))
    {q : E} (hq : q ∈ C) (hqb : ell q < b) :
    ∃ R > 0, ∀ᶠ j in atTop, Cj j ∩ {x | ell x ≤ b} ⊆ Metric.ball 0 R := by
  obtain ⟨R, hR, hcap⟩ := hbounded.subset_ball_lt (0 : ℝ) (0 : E)
  have hqR : ‖q‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hcap ⟨hq, hqb.le⟩
  let S : Set E := Metric.sphere (0 : E) R ∩ {x | ell x ≤ b}
  have hSc : IsCompact S := (isCompact_sphere (0 : E) R).inter_right
    (isClosed_le ell.continuous continuous_const)
  have hSd : Disjoint C S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    have he : ‖x‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hxs.1
    have hl : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hcap ⟨hx, hxs.2⟩
    linarith
  obtain ⟨qj, hqj, hqjt⟩ := h.exists_approximating hclj hnej hq
  have hqjR : ∀ᶠ j in atTop, ‖qj j‖ < R := hqjt.norm.eventually_lt_const hqR
  have hqjb : ∀ᶠ j in atTop, ell (qj j) < b :=
    (ell.continuous.tendsto q |>.comp hqjt).eventually_lt_const hqb
  refine ⟨R, hR, ?_⟩
  filter_upwards [h.eventually_disjoint_compact hcl ⟨q, hq⟩ hSc hSd, hqjR, hqjb]
    with j hj hqRj hqbj
  intro p hp
  by_contra hn
  have hpR : R ≤ ‖p‖ := by simpa [Metric.mem_ball, dist_zero_right, not_lt] using hn
  let f : ℝ → E := fun t => (1 - t) • qj j + t • p
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = qj j := by simp [f]
  have hf1 : f 1 = p := by simp [f]
  have hRim : R ∈ (fun t => ‖f t‖) '' Icc (0 : ℝ) 1 :=
    intermediate_value_Icc (by norm_num) hf.norm.continuousOn (by simp [hf0, hf1, hqRj.le, hpR])
  obtain ⟨t, ht, htR⟩ := hRim
  have hft : f t ∈ Cj j := hcvj j (hqj j) hp.1 (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hfb : ell (f t) ≤ b := by
    dsimp [f]
    simp only [map_add, map_smul, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hqbj.le (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left hp.2 ht.1
    nlinarith
  exact Set.disjoint_left.mp hj hft ⟨by simpa [Metric.mem_sphere, dist_zero_right] using htR, hfb⟩

/- A point on the top of a limit cap is approximated from strictly below
its top by contracting toward a fixed strict point. -/

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

section AffineFamily
open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- For distance functions, pointwise convergence is automatically locally
uniform, by the common unit Lipschitz constant and a finite compact cover. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.of_pointwise {Cj : ℕ → Set E} {C : Set E}
    (hpt : ∀ x, Tendsto (fun j => infDist x (Cj j)) atTop (𝓝 (infDist x C))) :
    LocalDistanceConverges Cj C := by
  classical
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, htK, ht⟩ := hK.elim_nhds_subcover (fun x => ball x (ε / 3))
    (fun x _ => ball_mem_nhds x (by positivity))
  have he : ∀ x ∈ t, ∀ᶠ j in atTop, dist (infDist x C) (infDist x (Cj j)) < ε / 3 := by
    intro x hx
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpt x) (ε / 3) (by positivity)
    filter_upwards [eventually_ge_atTop N] with j hj
    simpa [dist_comm] using hN j hj
  filter_upwards [(t.eventually_all).mpr he] with j hj x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  have hd : dist x y < ε / 3 := hxy
  have h1 : dist (infDist x C) (infDist y C) ≤ dist x y := by
    simpa using (lipschitz_infDist_pt C).dist_le_mul x y
  have h2 : dist (infDist y (Cj j)) (infDist x (Cj j)) ≤ dist x y := by
    simpa [dist_comm] using (lipschitz_infDist_pt (Cj j)).dist_le_mul y x
  calc
    dist (infDist x C) (infDist x (Cj j)) ≤
        dist (infDist x C) (infDist y C) + dist (infDist y C) (infDist y (Cj j)) +
          dist (infDist y (Cj j)) (infDist x (Cj j)) := dist_triangle4 _ _ _ _
    _ < ε := by linarith [hj y hyt]

/- Fixed changes of coordinates preserve local set convergence. A proper
homeomorphism suffices: compact preimages supply the lower distance bound and
actual approximating points supply the upper bound. In particular this applies
to every fixed invertible affine change of coordinates. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.homeomorph
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hne : C.Nonempty)
    (hclj : ∀ j, IsClosed (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (A : E ≃ₜ F) : LocalDistanceConverges (fun j => A '' Cj j) (A '' C) := by
  apply LocalDistanceConverges.of_pointwise
  intro x
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases haneg : a < 0
    · exact Eventually.of_forall fun j => haneg.trans_le infDist_nonneg
    let S : Set E := A.symm '' closedBall x a
    have hSc : IsCompact S := (isCompact_closedBall x a).image A.symm.continuous
    have hdis : Disjoint C S := by
      rw [Set.disjoint_left]
      rintro y hy ⟨z, hz, rfl⟩
      have he : infDist x (A '' C) ≤ dist x z := by
        apply infDist_le_dist_of_mem
        exact ⟨A.symm z, hy, A.apply_symm_apply z⟩
      have hz' : dist x z ≤ a := by simpa [mem_closedBall, dist_comm] using hz
      linarith
    filter_upwards [h.eventually_disjoint_compact hcl hne hSc hdis] with j hj
    obtain ⟨z, hz, hdist⟩ := (A.isClosedMap _ (hclj j)).exists_infDist_eq_dist ((hnej j).image A) x
    rw [hdist]
    by_contra hn
    obtain ⟨y, hy, rfl⟩ := hz
    apply Set.disjoint_left.mp hj hy
    exact ⟨A y, by simpa [mem_closedBall, dist_comm] using not_lt.mp hn, A.symm_apply_apply y⟩
  · intro b hb
    obtain ⟨z, hz, hdist⟩ := (A.isClosedMap _ hcl).exists_infDist_eq_dist (hne.image A) x
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨yj, hyj, hyt⟩ := h.exists_approximating hclj hnej hy
    have ht : Tendsto (fun j => dist x (A (yj j))) atTop (𝓝 (dist x (A y))) :=
      tendsto_const_nhds.dist ((A.continuous.tendsto y).comp hyt)
    have hb' : dist x (A y) < b := by simpa [hdist] using hb
    filter_upwards [ht.eventually_lt_const hb'] with j hj
    exact (infDist_le_dist_of_mem (s := A '' Cj j) ⟨yj j, hyj j, rfl⟩).trans_lt hj

/- A diagonal choice of approximating bodies. The bounds on the growing
closed balls are the literal metric construction behind the affine-family
closure assertion, not an assumed transitivity of sequential limits. -/

end AffineFamily

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/
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

open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineStripArea
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

lemma det_verticalScale {n : ℕ} (c : ℝ) (hc : c ≠ 0) :
    (verticalScale (n := n) c hc).toContinuousLinearMap.det = c := by
  let V := verticalScale (n := n) c hc
  have hV : V (0,1) = (0,c) := by simp [V]
  have hbase : (triangularBaseEquiv V hV hc).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (Space n) := by
    ext x
    rfl
  rw [determinant_triangular V hV hc,hbase]
  change LinearMap.det (LinearMap.id : Space n →ₗ[ℝ] Space n)*c = c
  rw [LinearMap.det_id,one_mul]

/- The exact epsilon power in source (strip-area), for the actual area of
an affine-image boundary patch. Only this patch, not the whole transformed
cap or graph, needs to lie in the coordinate box. -/
theorem affine_image_strip_area {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (j : Fin n ⊕ Unit) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hxR : ∀ x ∈ K, ∀ i, |(L (x,u x)+v).1 i| ≤ R)
    (htR : ∀ x ∈ K, |(L (x,u x)+v).2| ≤ R)
    (hstrip : ∀ x ∈ K, |ambientCoordinates n (L (x,u x)+v) j| ≤ ε) :
    Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      (∫ x in K, affineAreaDensity u x) ≤
      (graphAreaBoxBound n (2*max R 1)).toReal * ε^((n:ℝ)/((n:ℝ)+2)) := by
  let P := ambientSwap j
  let T := verticalScale (n := n) ε⁻¹ (inv_ne_zero hε.ne')
  let M := (L.trans P).trans T
  let w := T (P v)
  have hcoord (x : Space n) : M (x,u x)+w = T (P (L (x,u x)+v)) := by
    simp only [M,w,ContinuousLinearEquiv.trans_apply,map_add]
  have hswap (z : Space n × ℝ) (i : Fin n ⊕ Unit) :
      ambientCoordinates n (P z) i = ambientCoordinates n z (Equiv.swap j (Sum.inr ()) i) :=
    ambientSwap_coordinates j z i
  have hb (x : Space n) (hx : x ∈ K) : ∀ i, |(M (x,u x)+w).1 i| ≤ max R 1 := by
    intro i
    rw [hcoord]
    change |ambientCoordinates n (P (L (x,u x)+v)) (Sum.inl i)| ≤ _
    rw [hswap]
    cases Equiv.swap j (Sum.inr ()) (Sum.inl i) with
    | inl l => exact (hxR x hx l).trans (le_max_left _ _)
    | inr l => simpa only [ambientCoordinates_inr] using (htR x hx).trans (le_max_left R 1)
  have ht (x : Space n) (hx : x ∈ K) : |(M (x,u x)+w).2| ≤ max R 1 := by
    rw [hcoord]
    change |ε⁻¹*(P (L (x,u x)+v)).2| ≤ _
    rw [← ambientCoordinates_inr (P (L (x,u x)+v)) (),hswap,
      Equiv.swap_apply_right,abs_mul,abs_inv,abs_of_pos hε]
    calc
      _ ≤ ε⁻¹*ε := mul_le_mul_of_nonneg_left (hstrip x hx) (inv_nonneg.mpr hε.le)
      _ = 1 := inv_mul_cancel₀ hε.ne'
      _ ≤ _ := le_max_right _ _
  have hi := affine_image_graph_area_in_box hΩ hcv hK hKΩ hu hp M w
    (hR.trans (le_max_left _ _)) hb ht
  have hd : |M.toContinuousLinearMap.det| = ε⁻¹*|L.toContinuousLinearMap.det| := by
    simp only [M,abs_det_trans,T,det_verticalScale,abs_inv,abs_of_pos hε,
      show |P.toContinuousLinearMap.det| = 1 from abs_det_involutive P (ambientSwap_involutive j),one_mul]
  rw [hd] at hi
  simp only [Real.rpow_eq_pow] at hi ⊢
  rw [Real.mul_rpow (inv_nonneg.mpr hε.le) (abs_nonneg _),Real.inv_rpow hε.le] at hi
  have hpow : 0 < ε^((n:ℝ)/((n:ℝ)+2)) := Real.rpow_pos_of_pos hε _
  have hm := mul_le_mul_of_nonneg_left hi hpow.le
  have heval : ε^((n:ℝ)/((n:ℝ)+2))*
      ((ε^((n:ℝ)/((n:ℝ)+2)))⁻¹*|L.toContinuousLinearMap.det|^((n:ℝ)/((n:ℝ)+2))*
        (∫ x in K, affineAreaDensity u x)) =
      |L.toContinuousLinearMap.det|^((n:ℝ)/((n:ℝ)+2))*(∫ x in K, affineAreaDensity u x) := by
    field_simp
  rw [heval] at hm
  simpa only [mul_comm] using hm

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FixedBasisCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section FixedBasisCoordinates
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
lemma targetBasisCoordinates_map {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ G) :
    b.map (targetBasisCoordinates b).toLinearEquiv = graphAmbientBasis n := by
  simp [targetBasisCoordinates,Module.Basis.map_equiv]
lemma targetBasisCoordinates_det {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ G)
    (L : G ≃L[ℝ] (Space n × ℝ)) :
    (L.symm.trans (targetBasisCoordinates b)).toContinuousLinearMap.det =
      b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv) := by
  let T := targetBasisCoordinates b
  have hm := Module.Basis.det_map b T.toLinearEquiv
    (fun i => (L.symm.trans T) (graphAmbientBasis n i))
  rw [targetBasisCoordinates_map] at hm
  have hc : ((L.symm.trans T).toContinuousLinearMap.det) =
      (graphAmbientBasis n).det (fun i => (L.symm.trans T) (graphAmbientBasis n i)) := by
    change LinearMap.det (L.symm.trans T).toLinearEquiv.toLinearMap = _
    simpa only [Module.Basis.det_self,mul_one,Function.comp_def,LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] using
      (Module.Basis.det_comp (graphAmbientBasis n)
        (L.symm.trans T).toLinearEquiv.toLinearMap (graphAmbientBasis n)).symm
  rw [hc,hm]
  congr 1
  funext i
  simp [ContinuousLinearEquiv.trans_apply]

end FixedBasisCoordinates

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
-- module Solutions.OAIQ22_AB.AffineBernstein_CompletePositiveCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise
open Filter
open scoped Topology
open Filter
open scoped Topology

section CompletePositiveCap

lemma sourceEpigraph_convex {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) :
    Convex ℝ (sourceEpigraph Ω u) :=
  (convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)).convex_epigraph

lemma sourceEpigraph_closed {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) : IsClosed (sourceEpigraph Ω u) :=
  isClosed_epigraph_of_complete hΩ hne hu
    (convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)) hc

end CompletePositiveCap

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma affineEpigraphPullback_eq_image {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) :
    affineEpigraphPullback Ω u a L = (fun p => L.symm (p-a)) '' sourceEpigraph Ω u := by
  ext p
  constructor
  · intro hp
    refine ⟨a+L p,hp,?_⟩
    simp
  · rintro ⟨q,hq,rfl⟩
    simpa [affineEpigraphPullback,sourceEpigraph] using hq

lemma affineEpigraphPullback_isClosed {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : IsClosed (sourceEpigraph Ω u)) (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : IsClosed (affineEpigraphPullback Ω u a L) :=
  hc.preimage (continuous_const.add L.continuous)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CompletePositiveCapFurther
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

lemma affineSourceEpigraph_convex {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    Convex ℝ ((fun z => L z+v) '' sourceEpigraph Ω u) := by
  let F : (Space n × ℝ) →ᵃ[ℝ] (Space n × ℝ) :=
    L.toLinearEquiv.toLinearMap.toAffineMap + AffineMap.const ℝ _ v
  exact (sourceEpigraph_convex hΩ hcv hu hp).affine_image F

lemma affineSourceEpigraph_closed {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    IsClosed ((fun z => L z+v) '' sourceEpigraph Ω u) := by
  exact (L.toHomeomorph.trans (Homeomorph.addRight v)).isClosed_image.mpr
    (sourceEpigraph_closed hΩ hne hcv hu hp hc)

/- Source positive-cap-area lemma (bounds.tex:18–126) for the actual affine
images of the original complete graph, with all image hypotheses derived. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FiniteAreaCover
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

section FiniteAreaCover
/- Subadditivity for a finite (not disjoint) measurable cover, including
 the nonintegrable convention for the left-hand Bochner integral. -/
lemma integral_le_sum_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {K : Set X} {S : ι → Set X} {f : X → ℝ}
    (hK : MeasurableSet K) (hS : ∀ i, MeasurableSet (S i))
    (hsub : ∀ i, S i ⊆ K) (hcover : K ⊆ ⋃ i, S i)
    (hn : ∀ x ∈ K, 0 ≤ f x) :
    (∫ x in K, f x ∂μ) ≤ ∑ i, ∫ x in S i, f x ∂μ := by
  classical
  by_cases hi : IntegrableOn f K μ
  · have his (i : ι) : Integrable ((S i).indicator f) μ :=
      (hi.mono_set (hsub i)).integrable_indicator (hS i)
    have hb : ∀ x, K.indicator f x ≤ ∑ i, (S i).indicator f x := by
      intro x
      have hp (i : ι) : 0 ≤ (S i).indicator f x := by
        by_cases hx : x ∈ S i
        · simpa only [Set.indicator_of_mem hx] using hn x (hsub i hx)
        · simp [hx]
      by_cases hx : x ∈ K
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
        rw [Set.indicator_of_mem hx]
        calc
          f x = (S i).indicator f x := (Set.indicator_of_mem hxi f).symm
          _ ≤ ∑ i, (S i).indicator f x := Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ i)
      · simpa only [Set.indicator_of_notMem hx] using Finset.sum_nonneg (fun i _ => hp i)
    have hh := integral_mono (hi.integrable_indicator hK)
      (integrable_finsetSum _ fun i _ => his i) hb
    simpa only [integral_indicator hK,integral_finsetSum _ (fun i _ => his i),
      integral_indicator (hS _)] using hh
  · rw [integral_undef hi]
    exact Finset.sum_nonneg fun i _ => setIntegral_nonneg (hS i) (fun x hx => hn x (hsub i hx))
end FiniteAreaCover
open Filter Metric
open scoped Topology

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_InteriorLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter Metric
open scoped Topology Pointwise

/- The geometric conditions of a k-model, in its distinguished coordinates.
Membership in the affine local-limit family is separate from these conditions. -/
theorem closed_convex_add_of_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hc : IsClosed C) (hv : Convex ℝ C) {x v : E}
    (hx : x ∈ C) (hray : ∀ t : ℝ, 0 ≤ t → t • v ∈ C) : x + v ∈ C := by
  have htend : Tendsto (fun t : ℝ => (1 - t) • x + v) (𝓝[>] 0) (𝓝 (x + v)) := by
    have hc : Continuous (fun t : ℝ => (1 - t) • x + v) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hc.mem_of_tendsto htend
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
  have ht0 : 0 < t := ht
  have h := hv hx (hray t⁻¹ (inv_nonneg.mpr ht0.le))
    (show 0 ≤ 1 - t by linarith) ht0.le (by ring)
  simpa only [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul] using h

namespace IsModelShape

variable {k m : ℕ} {C : Set (Space k × Space m)} (h : IsModelShape C)
include h

theorem zero_mem : (0 : Space k × Space m) ∈ C := by
  exact h.orthant 0 (by simp)

theorem add_nonnegative_base {s v : Space k} {y : Space m}
    (hy : (s, y) ∈ C) (hv : ∀ i, 0 ≤ v i) : (s + v, y) ∈ C := by
  have hh := closed_convex_add_of_ray h.closed h.convex hy (v := (v, 0)) (by
    intro t ht
    simpa only [Prod.smul_mk, smul_zero] using
      h.orthant (t • v) (fun i => mul_nonneg ht (hv i)))
  simpa using hh

theorem fiber_mono {s t : Space k} (hst : ∀ i, s i ≤ t i) :
    modelFiber C s ⊆ modelFiber C t := by
  intro y hy
  have hh := h.add_nonnegative_base hy (v := t - s) (by intro i; exact sub_nonneg.mpr (hst i))
  simpa only [add_sub_cancel, modelFiber, mem_ofPred_eq] using hh

theorem fiber_contract {s : Space k} {a : ℝ} (ha : 1 ≤ a) :
    modelFiber C (a • s) ⊆ a • modelFiber C s := by
  have hp : 0 < a := by linarith
  intro y hy
  have hh := h.convex.smul_mem_of_zero_mem h.zero_mem hy
    (show a⁻¹ ∈ Icc (0 : ℝ) 1 from ⟨inv_nonneg.mpr hp.le, inv_le_one_of_one_le₀ ha⟩)
  have hm : a⁻¹ • y ∈ modelFiber C s := by
    simpa only [modelFiber, mem_ofPred_eq, Prod.smul_mk, smul_smul,
      inv_mul_cancel₀ hp.ne', one_smul] using hh
  exact Set.mem_smul_set.mpr ⟨a⁻¹ • y, hm, by simp [smul_smul, hp.ne']⟩

/- Every strictly positive fiber is full dimensional; this proof also covers
m=0, using the ordinary topology of the zero-dimensional space. -/
theorem fiber_box_bound {R T : ℝ} (hT : 1 ≤ T)
    (hR : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) ⊆ Metric.closedBall 0 R)
    {s : Space k} (hs : ∀ i, s i ≤ T) {y : Space m} (hy : y ∈ modelFiber C s) :
    ‖y‖ ≤ T * R := by
  have hp : 0 < T := by linarith
  have hmono : y ∈ modelFiber C (T • WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) :=
    h.fiber_mono (fun i => by simpa using hs i) hy
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp (h.fiber_contract hT hmono)
  have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hz
  simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hp] using mul_le_mul_of_nonneg_left hzR hp.le

end IsModelShape

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormedCompactInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

/- The lower inclusion in geometry.tex (normalized-fiber-box), with the
source's exact radius a*r. It is a convexity/recession consequence. -/
lemma IsModelShape.fiber_small_ball {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    {s : Space k} (hs : ∀ i, a ≤ s i) :
    closedBall (0 : Space m) (a*r) ⊆ modelFiber C s := by
  intro y hy
  have hny : ‖y‖ ≤ a*r := by simpa only [mem_closedBall,dist_zero_right] using hy
  have hz : a⁻¹ • y ∈ closedBall (0 : Space m) r := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_le_iff₀ ha).mpr hny
  have hc := hC.convex.smul_mem_of_zero_mem hC.zero_mem (hin hz) ⟨ha.le,ha1⟩
  have hc' : y ∈ modelFiber C (a • WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) := by
    simpa only [modelFiber,mem_ofPred_eq,Prod.smul_mk,smul_smul,
      mul_inv_cancel₀ ha.ne',one_smul] using hc
  exact hC.fiber_mono (fun i => by simpa using hs i) hc'

lemma IsModelShape.normalized_fiber_interior {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    {s : Space k} (hs : ∀ i, a ≤ s i) {y : Space m} (hy : ‖y‖ ≤ a*r/2) :
    (s,y) ∈ interior C := by
  let U : Set (Space k × Space m) := {p | (∀ i, 3*a/4 < p.1 i) ∧ ‖p.2‖ < 3*a*r/4}
  have hU : IsOpen U := by
    have hi (i : Fin k) : IsOpen {p : Space k × Space m | 3*a/4 < p.1 i} :=
      isOpen_lt continuous_const
        ((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst)
    have he : U = (⋂ i : Fin k, {p : Space k × Space m | 3*a/4 < p.1 i}) ∩
        {p : Space k × Space m | ‖p.2‖ < 3*a*r/4} := by ext p; simp [U]
    rw [he]
    exact (isOpen_iInter_of_finite hi).inter
      (isOpen_lt (continuous_snd.norm) continuous_const)
  have hz : (s,y) ∈ U := by
    refine ⟨fun i => by dsimp; linarith [hs i],?_⟩
    dsimp
    nlinarith
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hU.mem_nhds hz)
  intro p hp
  exact hC.fiber_small_ball (a := 3*a/4) (by positivity) (by linarith) hin
    (fun i => (hp.1 i).le) (mem_closedBall_zero_iff.mpr (by nlinarith [hp.2]))

/- Centering gives the exact normalization constants before the model and
positive fiber are selected. No compactness modulus or analytic estimate is
assumed. This is the first part of the manuscript's normalized-fibers corollary. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

/- Quantitative cap transfer: a given limit radius costs only one unit.
The constant does not depend on the sequence or its limit set. -/

lemma norm_le_sqrt_card_mul_of_coord_le {k : ℕ} {x : Space k} {T : ℝ}
    (hT : 0 < T) (hx : ∀ i, |x i| ≤ T) : ‖x‖ ≤ Real.sqrt k*T := by
  have hh := norm_le_sqrt_card_of_coordinate_le (T⁻¹ • x) (fun i => by
    change |T⁻¹ * x i| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr hT)]
    exact (inv_mul_le_iff₀ hT).mpr (by simpa using hx i))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hT)] at hh
  exact (inv_mul_le_iff₀ hT).mp hh |>.trans_eq (mul_comm _ _)

lemma IsModelShape.normalized_cap_box {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {R B α : ℝ} {a : Fin k → ℝ}
    (hα : 0 < α) (ha : ∀ i, α ≤ a i)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    C ∩ {p | positiveBaseForm a p ≤ B} ⊆
      {s : Space k | ∀ i, s i ∈ Icc 0 (max 1 (B/α))} ×ˢ
      closedBall (0 : Space m) (max 1 (B/α)*R) := by
  rintro ⟨s,y⟩ ⟨hp,hcap⟩
  have hs := hC.support (s,y) hp
  have hb (i : Fin k) : s i ≤ max 1 (B/α) := by
    have hi : α*s i ≤ B := calc
      _ ≤ a i*s i := mul_le_mul_of_nonneg_right (ha i) (hs i)
      _ ≤ ∑ j, a j*s j := Finset.single_le_sum (fun j _ => mul_nonneg (hα.le.trans (ha j)) (hs j)) (Finset.mem_univ i)
      _ ≤ B := by simpa using hcap
    exact ((le_div_iff₀ hα).mpr (by simpa [mul_comm] using hi)).trans (le_max_right _ _)
  exact ⟨fun i => ⟨hs i,hb i⟩,mem_closedBall_zero_iff.mpr
    (hC.fiber_box_bound (le_max_left _ _) hout hb hp)⟩

lemma IsModelShape.normalized_cap_radius {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {R B α : ℝ} {a : Fin k → ℝ}
    (hα : 0 < α) (ha : ∀ i, α ≤ a i)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    C ∩ {p | positiveBaseForm a p ≤ B} ⊆
      closedBall 0 (max (Real.sqrt k * max 1 (B/α)) (max 1 (B/α)*R)) := by
  intro p hp
  have hh := hC.normalized_cap_box hα ha hout hp
  rw [mem_closedBall_zero_iff,Prod.norm_def]
  apply max_le_max
  · exact norm_le_sqrt_card_mul_of_coord_le (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (fun i => by rw [abs_of_nonneg (hh.1 i).1]; exact (hh.1 i).2)
  · exact mem_closedBall_zero_iff.mp hh.2

/- Uniform interior ball about (1,0), with an explicit positive radius. -/
lemma IsModelShape.normalized_center_ball {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r : ℝ} (hr : 0 < r)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) :
    closedBall ((WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))), (0 : Space m))
      (min (1/4) (r/4)) ⊆ interior C := by
  rintro ⟨s,y⟩ hp
  have hd := mem_closedBall.mp hp
  have hs : ‖s - WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))‖ ≤ min (1/4) (r/4) := by
    rw [← dist_eq_norm]
    exact le_trans (le_max_left _ _) hd
  have hy : ‖y‖ ≤ min (1/4) (r/4) := by
    simpa only [dist_zero_right] using le_trans (le_max_right _ _) hd
  apply hC.normalized_fiber_interior hr (a := 1/2) (by norm_num) (by norm_num) hin
  · intro i
    have hi := (PiLp.norm_apply_le (s - WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) i).trans hs
    change |s i-1| ≤ min (1/4) (r/4) at hi
    linarith [le_abs_self (-(s i-1)),abs_neg (s i-1),min_le_left (1/4:ℝ) (r/4)]
  · linarith [hy.trans (min_le_right (1/4:ℝ) (r/4))]

/- Eventual cap bounds with constants fixed before the approximating sequence. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_OrthantGeometry
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

open Filter Metric
open scoped Topology

lemma continuous_ambientCoordinate {n : ℕ} (i : Fin n ⊕ Unit) :
    Continuous (fun z : Space n × ℝ => ambientCoordinates n z i) := by
  cases i with
  | inl i => simpa only [ambientCoordinates_inl,Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_fst
  | inr i => simpa only [ambientCoordinates_inr] using continuous_snd

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NoOrthant
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

open Filter Metric
open scoped Topology

lemma exists_pos_mul_rpow_lt {p c : ℝ} (hp : 0 < p) (hc : 0 < c) (d : ℝ) :
    ∃ ε > 0, d * ε^p < c := by
  have hf : ContinuousAt (fun t : ℝ => d*t^p) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
  have hh : ∀ᶠ t in 𝓝 (0 : ℝ), d*t^p < c :=
    hf.eventually_lt_const (by simpa only [Real.zero_rpow hp.ne',mul_zero] using hc)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨r/2,half_pos hr,hball ?_⟩
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hr)] using
    (show r/2 < r by linarith)

/- A finite union of actual affine-image thin strips obeys the sum of the
source strip-area bounds, without a disjointness or integrability premise. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveFaceMass
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

open Filter Metric
open scoped Topology

lemma integral_le_good_add_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {K G : Set X} {S : ι → Set X} {f : X → ℝ}
    (hK : MeasurableSet K) (hG : MeasurableSet G) (hS : ∀ i, MeasurableSet (S i))
    (hGK : G ⊆ K) (hsub : ∀ i, S i ⊆ K) (hcover : K ⊆ G ∪ ⋃ i, S i)
    (hn : ∀ x ∈ K, 0 ≤ f x) :
    (∫ x in K, f x ∂μ) ≤ (∫ x in G, f x ∂μ) + ∑ i, ∫ x in S i, f x ∂μ := by
  let T : Option ι → Set X := fun i => Option.casesOn i G S
  have hh : (∫ x in K, f x ∂μ) ≤ ∑ i, ∫ x in T i, f x ∂μ := by
    apply integral_le_sum_cover hK (fun i => by cases i; exact hG; exact hS _)
      (fun i => by cases i; exact hGK; exact hsub _)
    · intro x hx
      rcases hcover hx with h | h
      · exact mem_iUnion.mpr ⟨none,h⟩
      · obtain ⟨i,hi⟩ := mem_iUnion.mp h
        exact mem_iUnion.mpr ⟨some i,hi⟩
    · exact hn
  simpa [T,Fintype.sum_option] using hh

/- Quantitative positive area away from finitely many supporting faces. -/
theorem affine_image_good_area_lower {n k : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (s : Fin k → Fin n ⊕ Unit) {R ε c : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hxR : ∀ x ∈ K, ∀ i, |(L (x,u x)+v).1 i| ≤ R)
    (htR : ∀ x ∈ K, |(L (x,u x)+v).2| ≤ R)
    (hlow : ∀ x ∈ K, ∀ i, -ε ≤ ambientCoordinates n (L (x,u x)+v) (s i))
    (harea : c ≤ Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      (∫ x in K, affineAreaDensity u x))
    (heps : (k:ℝ)*(graphAreaBoxBound n (2*max R 1)).toReal*ε^((n:ℝ)/((n:ℝ)+2)) ≤ c/2) :
    c/2 ≤ Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      ∫ x in K ∩ {x | ∀ i, ε < ambientCoordinates n (L (x,u x)+v) (s i)}, affineAreaDensity u x := by
  classical
  let F := fun x => L (x,u x)+v
  let G := K ∩ {x | ∀ i, ε < ambientCoordinates n (F x) (s i)}
  let S (i : Fin k) := K ∩ {x | ambientCoordinates n (F x) (s i) ≤ ε}
  let a := Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))
  have hF : ContinuousOn F K :=
    ((L.continuous.comp_continuousOn (continuousOn_id.prodMk (hu.continuousOn.mono hKΩ))).add continuousOn_const)
  have hmS (i : Fin k) : MeasurableSet (S i) :=
    measurableSet_inter_preimage_continuousOn hK
      ((continuous_ambientCoordinate (s i)).comp_continuousOn hF) measurableSet_Iic
  have hmG : MeasurableSet G := by
    change MeasurableSet (K ∩ F ⁻¹' {z : Space n × ℝ | ∀ i, ε < ambientCoordinates n z (s i)})
    apply measurableSet_inter_preimage_continuousOn hK hF
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (continuous_ambientCoordinate (s i)).measurable
  have hcov : K ⊆ G ∪ ⋃ i, S i := by
    intro x hx
    by_cases hh : ∀ i, ε < ambientCoordinates n (F x) (s i)
    · exact Or.inl ⟨hx,hh⟩
    · push Not at hh
      obtain ⟨i,hi⟩ := hh
      exact Or.inr (mem_iUnion.mpr ⟨i,hx,hi⟩)
  have hsum := integral_le_good_add_cover (μ := volume) (f := affineAreaDensity u)
    hK hmG hmS inter_subset_left (fun i => inter_subset_left) hcov
    (fun x hx => Real.rpow_nonneg (hp x (hKΩ hx)).det_pos.le _)
  have hbound : a * ∑ i, ∫ x in S i, affineAreaDensity u x ≤ c/2 := by
    calc
      _ = ∑ i, a * ∫ x in S i, affineAreaDensity u x := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : Fin k, (graphAreaBoxBound n (2*max R 1)).toReal * ε^((n:ℝ)/((n:ℝ)+2)) := by
        apply Finset.sum_le_sum
        intro i _
        exact affine_image_strip_area hΩ hcv (hmS i) (fun x hx => hKΩ hx.1) hu hp L v (s i) hR hε
          (fun x hx => hxR x hx.1) (fun x hx => htR x hx.1)
          (fun x hx => abs_le.mpr ⟨hlow x hx.1 i,hx.2⟩)
      _ = (k:ℝ)*(graphAreaBoxBound n (2*max R 1)).toReal*ε^((n:ℝ)/((n:ℝ)+2)) := by simp; ring
      _ ≤ c/2 := heps
  have hh := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (abs_nonneg L.toContinuousLinearMap.det) ((n:ℝ)/((n:ℝ)+2)))
  change a * _ ≤ a * _ at hh
  rw [mul_add] at hh
  change c ≤ a * _ at harea
  change c/2 ≤ a * _
  linarith

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveFaceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

section PositiveFaceDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

section PositiveFaceLimit
open Filter Metric
open scoped Topology

lemma LocalDistanceConverges.eventually_support_coordinate_lower {n k : ℕ}
    {Cj : ℕ → Set (Space n × ℝ)} {C : Set (Space n × ℝ)}
    (h : LocalDistanceConverges Cj C) (hcl : IsClosed C) (hne : C.Nonempty)
    (s : Fin k → Fin n ⊕ Unit)
    (hs : ∀ z ∈ C, ∀ i, 0 ≤ ambientCoordinates n z (s i)) {R ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ z ∈ Cj j, ‖z‖ ≤ R → ∀ i, -ε ≤ ambientCoordinates n z (s i) := by
  have he (i : Fin k) : ∀ᶠ j in atTop,
      Disjoint (Cj j) (Metric.closedBall (0 : Space n × ℝ) R ∩
        {z | ambientCoordinates n z (s i) ≤ -ε}) := by
    apply h.eventually_disjoint_compact hcl hne
      ((isCompact_closedBall _ _).inter_right
        (isClosed_le (continuous_ambientCoordinate (s i)) continuous_const))
    rw [disjoint_left]
    intro z hz hz'
    have hh := hs z hz i
    have hn : ambientCoordinates n z (s i) ≤ -ε := hz'.2
    linarith
  filter_upwards [Filter.eventually_all.mpr he] with j hj
  intro z hz hzR i
  by_contra hh
  have hzB : z ∈ Metric.closedBall (0 : Space n × ℝ) R := by simpa using hzR
  exact Set.disjoint_left.mp (hj i) hz ⟨hzB,(lt_of_not_ge hh).le⟩

/- The exact positive boundary mass left after removing all finitely many
face strips, uniformly along affine local limits. This is before tube charts;
the integral remains the literal original-graph affine area. -/
theorem complete_affineMaximal_positive_face_mass {n k : ℕ} (hn : 0 < n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hell : ell ≠ 0)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | ell z ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : ell o < b)
    (s : Fin k → Fin n ⊕ Unit) (hs : ∀ z ∈ C, ∀ i, 0 ≤ ambientCoordinates n z (s i)) :
    ∃ R > 0, ∃ ε > 0, ∃ a > 0, ∀ᶠ j in atTop,
      (∀ x ∈ Ω, ell (L j (x,u x)+v j) < b → ‖L j (x,u x)+v j‖ ≤ R) ∧
      a ≤ Real.rpow |(L j).toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        ∫ x in {x | x ∈ Ω ∧ ell (L j (x,u x)+v j) < b} ∩
          {x | ∀ i, ε < ambientCoordinates n (L j (x,u x)+v j) (s i)}, affineAreaDensity u x := by
  let Cj := fun j => (fun z => L j z+v j) '' sourceEpigraph Ω u
  have hclj j : IsClosed (Cj j) := affineSourceEpigraph_closed hΩ hne hcv hu hp hc _ _
  have hcvj j : Convex ℝ (Cj j) := affineSourceEpigraph_convex hΩ hcv hu hp _ _
  have hnej j : (Cj j).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨L j (x,u x)+v j,mem_image_of_mem _ ⟨hx,le_rfl⟩⟩
  obtain ⟨c,hcpos,harea⟩ := complete_affineMaximal_positive_cap_area hΩ hne hcv hu hp hm hc L v
    hC hlim ell hell hcapC ho hob
  obtain ⟨R,hR,hcaps⟩ := hlim.eventually_bounded_caps hC hclj hcvj hnej ell b hcapC (interior_subset ho) hob
  have hpwr : 0 < (n:ℝ)/((n:ℝ)+2) := div_pos (Nat.cast_pos.mpr hn) (by positivity)
  obtain ⟨ε,hε,heps⟩ := exists_pos_mul_rpow_lt hpwr (half_pos hcpos)
    ((k:ℝ)*(graphAreaBoxBound n (2*max R 1)).toReal)
  have hlow := hlim.eventually_support_coordinate_lower hC ⟨o,interior_subset ho⟩ s hs (R := R) hε
  refine ⟨R,hR,ε,hε,c/2,half_pos hcpos,?_⟩
  filter_upwards [harea,hcaps,hlow] with j hja hjc hjl
  let K : Set (Space n) := {x | x ∈ Ω ∧ ell (L j (x,u x)+v j) < b}
  have hG : ContinuousOn (fun x => L j (x,u x)+v j) Ω :=
    ((L j).continuous.comp_continuousOn (continuousOn_id.prodMk hu.continuousOn)).add continuousOn_const
  have hKm : MeasurableSet K := measurableSet_inter_preimage_continuousOn hΩ.measurableSet
    (ell.continuous.comp_continuousOn hG) measurableSet_Iio
  have hKr (x : Space n) (hx : x ∈ K) : ‖L j (x,u x)+v j‖ ≤ R := by
    have hh := hjc ⟨mem_image_of_mem _ ⟨hx.1,le_rfl⟩,hx.2.le⟩
    exact (show ‖L j (x,u x)+v j‖ < R by simpa using hh).le
  refine ⟨fun x hx hb => hKr x ⟨hx,hb⟩,?_⟩
  apply affine_image_good_area_lower hΩ hcv hKm (fun x hx => hx.1) hu hp (L j) (v j) s hR.le hε
  · intro x hx i
    exact (show |(L j (x,u x)+v j).1 i| ≤ ‖(L j (x,u x)+v j).1‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (L j (x,u x)+v j).1 i).trans
      ((le_max_left _ _).trans (hKr x hx))
  · intro x hx
    exact (show |(L j (x,u x)+v j).2| ≤ ‖L j (x,u x)+v j‖ by
        simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_right ‖(L j (x,u x)+v j).1‖ ‖(L j (x,u x)+v j).2‖).trans
      (hKr x hx)
  · intro x hx i
    exact hjl _ (mem_image_of_mem _ ⟨hx.1,le_rfl⟩) (hKr x hx) i
  · exact hja
  · exact heps.le
end PositiveFaceLimit

-- END

end PositiveFaceDependencies

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProductAmbientCoordinates
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

section ProductAmbientCoordinates
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
lemma targetBasisCoordinates_coord {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ G)
    (z : G) (i : Fin n ⊕ Unit) :
    ambientCoordinates n (targetBasisCoordinates b z) i = b.equivFun z i := by
  have he : (ambientCoordinates n).toLinearMap.comp (targetBasisCoordinates b).toLinearMap =
      b.equivFun.toLinearMap := by
    apply b.ext
    intro j
    simp [targetBasisCoordinates,ambientCoordinates]
  exact congrFun (LinearMap.congr_fun he z) i
end ProductAmbientCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
lemma productAmbientCoordinates_base {n k : ℕ} (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ Fin k ⊕ κ) (z : Space k × E) (i : Fin k) :
    ambientCoordinates n (targetBasisCoordinates (productAmbientBasis bE e) z)
      (productBaseIndex e i) = z.1 i := by
  rw [targetBasisCoordinates_coord]
  change (productAmbientBasis bE e).repr z (productBaseIndex e i) = z.1 i
  rw [productAmbientBasis,Module.Basis.repr_reindex_apply]
  simp only [productBaseIndex, Equiv.symm_symm, Equiv.apply_symm_apply,
    Module.Basis.prod_repr_inl]
  simp

lemma ambientCoordinate_abs_le_norm {n : ℕ} (z : Space n × ℝ) (i : Fin n ⊕ Unit) :
    |ambientCoordinates n z i| ≤ ‖z‖ := by
  rcases i with i | i
  · rw [ambientCoordinates_inl]
    have hi : |z.1 i| ≤ ‖z.1‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z.1 i
    exact hi.trans (le_max_left _ _)
  · rw [ambientCoordinates_inr]
    exact le_max_right _ _

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelFaceMass
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

section ModelFaceMass
open Filter Metric

theorem normalized_model_positive_face_mass_oai {n k m d : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hm : 1 ≤ m) (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) :
    ∃ R > 0, ∃ ε > 0, ∃ c > 0, ∀ᶠ j in atTop,
      ∃ K : Set (Space n), K ⊆ Ω ∧
        (∀ x ∈ K, ∀ i, ε ≤ ((L j).symm ((x,u x)-a j)).1 i ∧
          ((L j).symm ((x,u x)-a j)).1 i ≤ R) ∧
        c ≤ Real.rpow |(productAmbientBasis ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE) e).det
          ((graphAmbientBasis n).map (L j).symm.toLinearEquiv)| ((n:ℝ)/((n:ℝ)+2)) *
            ∫ x in K, affineAreaDensity u x := by
  let : NeZero m := ⟨by omega⟩
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  let b := productAmbientBasis bE e
  let T := targetBasisCoordinates b
  let A := fun j => (L j).symm.trans T
  let v := fun j => -(A j) (a j)
  let ell := (positiveBaseForm (m := m) (fun _ : Fin k => (1:ℝ))).comp T.symm.toContinuousLinearMap
  let o : Space k × Space m := (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)),0)
  have hellT (p : Space k × Space m) : ell (T p) = ∑ i, p.1 i := by
    simp [ell]
  have hoC : o ∈ interior C := by
    exact hC.normalized_center_ball hr hin (mem_closedBall_self (by positivity : 0 ≤ min (1/4:ℝ) (r/4)))
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hclj j : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) :=
    affineEpigraphPullback_isClosed hclosed _ _
  have hnej j : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  have hjT (j : ℕ) : (fun p => A j p + v j) '' sourceEpigraph Ω u =
      T '' affineEpigraphPullback Ω u (a j) (L j) := by
    rw [affineEpigraphPullback_eq_image,Set.image_image]
    congr 1
    funext p
    simp [A,v,sub_eq_add_neg]
  have hlimT : LocalDistanceConverges
      (fun j => (fun p => A j p+v j) '' sourceEpigraph Ω u) (T '' C) := by
    have hh := hlim.homeomorph hC.closed ⟨0,hC.zero_mem⟩ hclj hnej T.toHomeomorph
    change LocalDistanceConverges (fun j => T '' affineEpigraphPullback Ω u (a j) (L j)) (T '' C) at hh
    simpa only [hjT] using hh
  have hell : ell ≠ 0 := by
    intro hz
    have hh := hellT o
    rw [hz] at hh
    have : (0:ℝ) = k := by simpa [o] using hh
    have : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
    linarith
  have hcap : Bornology.IsBounded ((T '' C) ∩ {z | ell z ≤ (k:ℝ)+1}) := by
    have hb := (isCompact_closedBall (0:Space k × Space m)
      (max (Real.sqrt k * max 1 (((k:ℝ)+1)/1)) (max 1 (((k:ℝ)+1)/1)*R₀))).isBounded.subset
      (hC.normalized_cap_radius (B := (k:ℝ)+1) (by norm_num : (0:ℝ)<1)
        (fun _ => le_rfl) hout)
    apply (hb.image T.toContinuousLinearMap).subset
    rintro z ⟨⟨p,hp,rfl⟩,hz⟩
    refine ⟨p,⟨hp,?_⟩,rfl⟩
    simpa [ell] using hz
  have hoT : T o ∈ interior (T '' C) := by
    change T.toHomeomorph o ∈ interior (T.toHomeomorph '' C)
    rw [← T.toHomeomorph.image_interior]
    exact mem_image_of_mem _ hoC
  have hob : ell (T o) < (k:ℝ)+1 := by simp [hellT,o]
  have hs : ∀ z ∈ T '' C, ∀ i, 0 ≤ ambientCoordinates n z (productBaseIndex e i) := by
    rintro _ ⟨p,hp,rfl⟩ i
    rw [show ambientCoordinates n (T p) (productBaseIndex e i) = p.1 i from
      productAmbientCoordinates_base bE e p i]
    exact hC.support p hp i
  obtain ⟨R,hR,ε,hε,c,hc,hh⟩ := complete_affineMaximal_positive_face_mass
    (by omega : 0 < n) hΩ hne hcv hu hp hmP hcomplete A v
    (T.toHomeomorph.isClosedMap C hC.closed) hlimT ell hell hcap hoT hob (productBaseIndex e) hs
  refine ⟨R,hR,ε,hε,c,hc,?_⟩
  filter_upwards [hh] with j hj
  let K : Set (Space n) := {x | x ∈ Ω ∧ ell (A j (x,u x)+v j) < (k:ℝ)+1} ∩
    {x | ∀ i, ε < ambientCoordinates n (A j (x,u x)+v j) (productBaseIndex e i)}
  have hpull (x : Space n) : A j (x,u x)+v j = T ((L j).symm ((x,u x)-a j)) := by
    simp [A,v,sub_eq_add_neg]
  refine ⟨K,fun x hx => hx.1.1,?_,?_⟩
  · intro x hx i
    have he : ambientCoordinates n (A j (x,u x)+v j) (productBaseIndex e i) =
        ((L j).symm ((x,u x)-a j)).1 i := by rw [hpull]; exact productAmbientCoordinates_base bE e _ i
    refine ⟨by rw [← he]; exact (hx.2 i).le,?_⟩
    rw [← he]
    exact (le_abs_self _).trans ((ambientCoordinate_abs_le_norm _ _).trans
      (hj.1 x hx.1.1 hx.1.2))
  · have hh := hj.2
    change c ≤ Real.rpow |((L j).symm.trans (targetBasisCoordinates b)).toContinuousLinearMap.det|
      ((n:ℝ)/((n:ℝ)+2)) * ∫ x in K, affineAreaDensity u x at hh
    rw [targetBasisCoordinates_det] at hh
    exact hh
end ModelFaceMass


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.normalized_model_positive_face_mass_oai := @OAI.AffineBernstein.normalized_model_positive_face_mass_oai
