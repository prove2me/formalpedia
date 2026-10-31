-- Prove2me | solution 1 for OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:16:55.064278+00:00
-- url     : https://prove2.me/submissions/68216fbd-56c7-4f29-90fa-3e8db3418a90

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

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

end RadialCalculus

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

/-- Hessians depend only on the germ of a function, also with the total derivative
convention at points outside the domain. -/
theorem hessian_eq_of_eventuallyEq {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    (h : f =ᶠ[nhds x] g) : hessian f x = hessian g x := by
  ext i j
  have h' : (fun y => fderiv ℝ f y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ g y (coordinateVector n j)) :=
    (h.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg (fun L => L (coordinateVector n j)) hy
  exact congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinateVector n i)) h'.fderiv_eq

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

lemma parametricSecondForm_affine {n : ℕ} (X : Space n → E)
    (L : E ≃L[ℝ] E) (v : E) (ν : E →L[ℝ] ℝ) (x : Space n) :
    parametricSecondForm (fun y => L (X y) + v) (ν.comp L.symm.toContinuousLinearMap) x =
      parametricSecondForm X ν x := by
  have he : (fun y => (ν.comp L.symm.toContinuousLinearMap) (L (X y) + v)) =
      (fun y => ν (X y) + ν (L.symm v)) := by
    funext y
    simp
  simp only [parametricSecondForm, he, hessian_add_constant]

lemma parametricFrame_affine {n : ℕ} {X : Space n → E} {x : Space n}
    (hX : DifferentiableAt ℝ X x) (L : E ≃L[ℝ] E) (v ξ : E) :
    parametricFrame (fun y => L (X y) + v) (L ξ) x =
      L.toLinearEquiv.toLinearMap ∘ parametricFrame X ξ x := by
  have hd := ((L.hasFDerivAt.comp x hX.hasFDerivAt).add_const v).fderiv
  funext i
  rcases i with i | i
  · change (fderiv ℝ (fun y => L (X y) + v) x) (coordinateVector n i) = _
    convert! congrArg (fun T : Space n →L[ℝ] E => T (coordinateVector n i)) hd using 1
  · rfl

/- Full ambient affine covariance, not restricted to fiber-preserving maps. -/
theorem parametricAreaDensity_affine {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X : Space n → E} {x : Space n} (hX : DifferentiableAt ℝ X x)
    (L : E ≃L[ℝ] E) (v ξ : E) (ν : E →L[ℝ] ℝ) :
    parametricAreaDensity b (fun y => L (X y) + v)
      (ν.comp L.symm.toContinuousLinearMap) (L ξ) x =
      Real.rpow |LinearMap.det L.toLinearEquiv.toLinearMap| ((n : ℝ) / ((n : ℝ) + 2)) *
        parametricAreaDensity b X ν ξ x := by
  rw [parametricAreaDensity, parametricSecondForm_affine,
    parametricFrame_affine hX, b.det_comp, abs_mul]
  have hr := Real.mul_rpow (z := (n : ℝ) / ((n : ℝ) + 2))
    (abs_nonneg (LinearMap.det L.toLinearEquiv.toLinearMap))
    (abs_nonneg (b.det (parametricFrame X ξ x)))
  change Real.rpow _ _ = _ at hr
  rw [hr]
  unfold parametricAreaDensity
  simp only [Real.rpow_eq_pow]
  ring

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

lemma differentiableAt_horizontalVelocity {n : ℕ} {a : Fin n → Space n → ℝ}
    {x : Space n} (ha : ∀ k, DifferentiableAt ℝ (a k) x) :
    DifferentiableAt ℝ (horizontalVelocity a) x :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.differentiableAt.comp x (differentiableAt_pi.mpr ha)

lemma differentiableAt_graphParamVariation {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    (hβ : DifferentiableAt ℝ β x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) (t : ℝ) :
    DifferentiableAt ℝ (graphParamVariation u β a t) x :=
  (differentiableAt_id.add ((differentiableAt_horizontalVelocity ha).const_smul t)).prodMk
    (hu.add (hβ.const_mul t))

lemma graphParamVariation_fderiv {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    (hβ : DifferentiableAt ℝ β x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) (t : ℝ) (j : Fin n) :
    fderiv ℝ (graphParamVariation u β a t) x (coordinateVector n j) =
      (coordinateVector n j + t • (EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun k => dirDeriv (coordinateVector n j) (a k) x),
       dirDeriv (coordinateVector n j) u x + t * dirDeriv (coordinateVector n j) β x) := by
  have hv := (EuclideanSpace.equiv (Fin n) ℝ).symm.hasFDerivAt.comp x
    (hasFDerivAt_pi.mpr (fun k => (ha k).hasFDerivAt))
  have hh := ((hasFDerivAt_id x).add (hv.const_smul t)).prodMk
    (hu.hasFDerivAt.add (hβ.hasFDerivAt.const_mul t))
  convert! congrArg (fun T : Space n →L[ℝ] (Space n × ℝ) => T (coordinateVector n j)) hh.fderiv using 1
  all_goals try with_reducible_and_instances rfl

lemma graphParam_frame_determinant {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    (hβ : DifferentiableAt ℝ β x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) (t : ℝ) :
    (graphAmbientBasis n).det (parametricFrame (graphParamVariation u β a t) ((0 : Space n), 1) x) =
      (1 + t • horizontalJacobian a x).det := by
  rw [Module.Basis.det_apply]
  have he : (graphAmbientBasis n).toMatrix
      (parametricFrame (graphParamVariation u β a t) ((0 : Space n), 1) x) =
      Matrix.fromBlocks (1 + t • horizontalJacobian a x) 0
        (Matrix.of fun (_ : Unit) j => dirDeriv (coordinateVector n j) u x +
          t * dirDeriv (coordinateVector n j) β x) (1 : Matrix Unit Unit ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [Module.Basis.toMatrix_apply, graphAmbientBasis, parametricFrame,
        Sum.elim_inl, Module.Basis.prod_repr_inl]
      rw [graphParamVariation_fderiv hu hβ ha]
      simp [coordinateVector, Matrix.fromBlocks, Matrix.one_apply, horizontalJacobian]
    · simp [Module.Basis.toMatrix_apply, graphAmbientBasis, parametricFrame, Matrix.fromBlocks]
    · simp [Module.Basis.toMatrix_apply, graphAmbientBasis, parametricFrame,
        graphParamVariation_fderiv hu hβ ha, Matrix.fromBlocks]
    · simp [Module.Basis.toMatrix_apply, graphAmbientBasis, parametricFrame, Matrix.fromBlocks]
  rw [he, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

lemma hessian_coordinate {n : ℕ} (k : Fin n) (x : Space n) :
    hessian (fun y : Space n => y k) x = 0 := by
  change hessian (coordinateProjection n k) x = 0
  ext i j
  simp [hessian, (coordinateProjection n k).fderiv]

lemma graphParam_secondForm {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) {x : Space n} (hx : x ∈ Ω) (t : ℝ) :
    parametricSecondForm (graphParamVariation u β a t) (graphParamConormal u β a x t) x =
      variationSecondForm (hessian u x) (hessian β x) (horizontalJacobian a x)
        (fun k => dirDeriv (coordinateVector n k) u x)
        (fun k => dirDeriv (coordinateVector n k) β x)
        (fun k => hessian (a k) x) t := by
  let q := variationConormal (horizontalJacobian a x)
    (fun k => dirDeriv (coordinateVector n k) u x)
    (fun k => dirDeriv (coordinateVector n k) β x) t
  have he : (fun y => graphParamConormal u β a x t (graphParamVariation u β a t y)) =
      fun y => u y + t * β y - ∑ k, q k * (y k + t * a k y) := by
    funext y
    simp [graphParamVariation, horizontalVelocity, q]
  have hcoord (k : Fin n) : ContDiffOn ℝ ∞ (fun y : Space n => y k) Ω :=
    (coordinateProjection n k).contDiff.contDiffOn
  have hc (k : Fin n) : ContDiffOn ℝ ∞ (fun y : Space n => y k + t * a k y) Ω :=
    (hcoord k).add (contDiffOn_const.mul (ha k))
  unfold parametricSecondForm
  rw [he, hessian_sub_on hΩ (hu.add (contDiffOn_const.mul hβ))
    (ContDiffOn.sum (fun k _ => contDiffOn_const.mul (hc k))) hx,
    hessian_add_on hΩ hu (contDiffOn_const.mul hβ) hx, hessian_const_mul hΩ hβ t hx]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    hessian_sum_on hΩ (fun k => contDiffOn_const.mul (hc k)) hx,
    hessian_const_mul hΩ (hc _) _ hx,
    hessian_add_on hΩ (hcoord _) (contDiffOn_const.mul (ha _)) hx,
    hessian_const_mul hΩ (ha _) t hx, hessian_coordinate, zero_add,
    variationSecondForm, Matrix.of_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/- The abstract conormal formula is exactly the literal graph-variation density. -/
theorem parametricAreaDensity_graphVariation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) {x : Space n} (hx : x ∈ Ω) (t : ℝ) :
    parametricAreaDensity (graphAmbientBasis n) (graphParamVariation u β a t)
      (graphParamConormal u β a x t) ((0 : Space n), 1) x = graphVariationArea u β a x t := by
  rw [parametricAreaDensity, graphParam_secondForm hΩ hu hβ ha hx,
    graphParam_frame_determinant (hu.differentiableOn (by simp) x hx |>.differentiableAt (hΩ.mem_nhds hx))
      (hβ.differentiableOn (by simp) x hx |>.differentiableAt (hΩ.mem_nhds hx))
      (fun k => (ha k).differentiableOn (by simp) x hx |>.differentiableAt (hΩ.mem_nhds hx))]
  unfold graphVariationArea variationAreaDensity
  simp [div_eq_mul_inv]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineParametricStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- The literal arbitrary affine image of a parametrized graph variation. -/

lemma affineParametricVariationArea_eq {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {x : Space n} (hx : x ∈ Ω) (t : ℝ) :
    affineParametricVariationArea L v u β a x t =
      Real.rpow |LinearMap.det L.toLinearEquiv.toLinearMap| ((n : ℝ) / ((n : ℝ) + 2)) *
        graphVariationArea u β a x t := by
  unfold affineParametricVariationArea
  rw [parametricAreaDensity_affine _ (differentiableAt_graphParamVariation
    ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    ((hβ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    (fun k => ((ha k).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) t),
    parametricAreaDensity_graphVariation hΩ hu hβ ha hx]

/- Stationarity is genuinely preserved by every ambient affine transformation.
The integrand is the derivative of the actual transformed parametric density.
No equation for the affine image is assumed. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricChangeOfCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ParametricChangeOfCoordinates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/- At a critical point the Hessian chain rule has no second derivative of the
coordinate change. Here it is proved for the actual Fréchet derivatives. -/
lemma second_comp_of_critical {f : F → ℝ} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (hz : fderiv ℝ f (φ x) = 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ φ)) x v w =
      fderiv ℝ (fderiv ℝ f) (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := by
  have hdf := hf.differentiableAt (by simp)
  have hdφ := hφ.differentiableAt (by simp)
  have hff := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hφφ := (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : fderiv ℝ (f ∘ φ) =ᶠ[nhds x]
      fun y => (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y) := by
    have hf1 := (hf.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)
    have hp1 := (hφ.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)
    filter_upwards [hdφ.continuousAt.eventually hf1, hp1] with y hy hpy
    exact fderiv_comp y (hy.differentiableAt (by norm_num)) (hpy.differentiableAt (by norm_num))
  have hh := (hff.hasFDerivAt.comp x hdφ.hasFDerivAt).clm_comp hφφ.hasFDerivAt
  rw [he.fderiv_eq]
  convert! congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) hh.fderiv using 1
  all_goals try with_reducible_and_instances rfl
  simp [hz]

end ParametricChangeOfCoordinates

lemma hessian_comp_of_critical {n : ℕ} {f : Space n → ℝ} {φ : Space n → Space n}
    {x : Space n} (hf : ContDiffAt ℝ ∞ f (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (hz : fderiv ℝ f (φ x) = 0) :
    hessian (f ∘ φ) x = (parametricJacobian φ x).transpose * hessian f (φ x) * parametricJacobian φ x := by
  ext i j
  change dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j) (f ∘ φ)) x = _
  rw [dirDeriv_eq_second (hf.comp x hφ), second_comp_of_critical hf hφ hz,
    ← sum_coordinateVector (fderiv ℝ φ x (coordinateVector n i)),
    ← sum_coordinateVector (fderiv ℝ φ x (coordinateVector n j))]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, parametricJacobian, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hd : fderiv ℝ (fderiv ℝ f) (φ x) (coordinateVector n l) (coordinateVector n k) =
      hessian f (φ x) l k := (dirDeriv_eq_second hf _ _).symm
  rw [hd]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parametricSecondForm_comp {n : ℕ} {X : Space n → E} {φ : Space n → Space n}
    {x : Space n} (hX : ContDiffAt ℝ ∞ X (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (ν : E →L[ℝ] ℝ) (hν : ν.comp (fderiv ℝ X (φ x)) = 0) :
    parametricSecondForm (X ∘ φ) ν x =
      (parametricJacobian φ x).transpose * parametricSecondForm X ν (φ x) * parametricJacobian φ x := by
  apply hessian_comp_of_critical (ν.contDiff.contDiffAt.comp (φ x) hX) hφ
  have hh := ν.hasFDerivAt.comp (φ x) (hX.differentiableAt (by simp)).hasFDerivAt
  convert! hh.fderiv.trans hν using 1
  all_goals try with_reducible_and_instances rfl

lemma parametricFrame_comp_matrix {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X : Space n → E} {φ : Space n → Space n} {x : Space n}
    (hX : DifferentiableAt ℝ X (φ x)) (hφ : DifferentiableAt ℝ φ x) (ξ : E) :
    b.toMatrix (parametricFrame (X ∘ φ) ξ x) =
      b.toMatrix (parametricFrame X ξ (φ x)) *
        Matrix.fromBlocks (parametricJacobian φ x) 0 0 (1 : Matrix Unit Unit ℝ) := by
  ext i j
  rcases j with j | j
  · simp only [Module.Basis.toMatrix_apply, parametricFrame, Sum.elim_inl]
    rw [fderiv_comp x hX hφ]
    change b.repr (fderiv ℝ X (φ x) (fderiv ℝ φ x (coordinateVector n j))) i = _
    rw [← sum_coordinateVector (fderiv ℝ φ x (coordinateVector n j))]
    simp only [map_sum, map_smul]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, parametricJacobian,
      Module.Basis.toMatrix_apply, mul_comm]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Module.Basis.toMatrix_apply, parametricFrame]

lemma parametricFrame_comp_det {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X : Space n → E} {φ : Space n → Space n} {x : Space n}
    (hX : DifferentiableAt ℝ X (φ x)) (hφ : DifferentiableAt ℝ φ x) (ξ : E) :
    b.det (parametricFrame (X ∘ φ) ξ x) =
      b.det (parametricFrame X ξ (φ x)) * (parametricJacobian φ x).det := by
  simp only [Module.Basis.det_apply, parametricFrame_comp_matrix b hX hφ ξ,
    Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricDensityCoordinates
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

/- Exact density change of variables; its Jacobian has exponent one. -/
theorem parametricAreaDensity_comp {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X : Space n → E} {φ : Space n → Space n} {x : Space n}
    (hX : ContDiffAt ℝ ∞ X (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (ν : E →L[ℝ] ℝ) (ξ : E) (hν : ν.comp (fderiv ℝ X (φ x)) = 0)
    (hH : 0 ≤ (parametricSecondForm X ν (φ x)).det)
    (hJ : (parametricJacobian φ x).det ≠ 0) :
    parametricAreaDensity b (X ∘ φ) ν ξ x =
      |(parametricJacobian φ x).det| * parametricAreaDensity b X ν ξ (φ x) := by
  have hd := parametricSecondForm_comp hX hφ ν hν
  have he : (parametricSecondForm (X ∘ φ) ν x).det =
      |(parametricJacobian φ x).det| ^ 2 * (parametricSecondForm X ν (φ x)).det := by
    rw [hd, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, sq_abs]
    ring
  rw [parametricAreaDensity, he, parametricFrame_comp_det b
    (hX.differentiableAt (by simp)) (hφ.differentiableAt (by simp)) ξ, abs_mul]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (sq_nonneg _) hH,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← Real.rpow_natCast_mul (abs_nonneg _) 2]
  have hp : 0 < |(parametricJacobian φ x).det| := abs_pos.mpr hJ
  have hr : (2 : ℝ) * (1 / ((n : ℝ) + 2)) + (n : ℝ) / ((n : ℝ) + 2) = 1 := by
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  have hc := Real.rpow_add hp (2 * (1 / ((n : ℝ) + 2))) ((n : ℝ) / ((n : ℝ) + 2))
  rw [hr, Real.rpow_one] at hc
  unfold parametricAreaDensity
  simp only [Real.rpow_eq_pow]
  calc
    _ = (|(parametricJacobian φ x).det| ^ (2 * (1 / ((n : ℝ) + 2))) *
          |(parametricJacobian φ x).det| ^ ((n : ℝ) / ((n : ℝ) + 2))) *
        ((parametricSecondForm X ν (φ x)).det ^ (1 / ((n : ℝ) + 2)) *
          |b.det (parametricFrame X ξ (φ x))| ^ ((n : ℝ) / ((n : ℝ) + 2))) := by ring_nf
    _ = _ := by rw [← hc]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma variationConormal_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (g d : ι → ℝ) (t : ℝ) (hJ : (1 + t • D).det ≠ 0) (j : ι) :
    (∑ k, variationConormal D g d t k * (1 + t • D) k j) = g j + t * d j := by
  have hh := Matrix.vecMul_vecMul (fun k => g k + t * d k)
    (1 + t • D)⁻¹ (1 + t • D)
  rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hJ), Matrix.vecMul_one] at hh
  exact congrFun hh j

lemma graphParamConormal_null {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u x)
    (hβ : DifferentiableAt ℝ β x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) (t : ℝ)
    (hJ : (1 + t • horizontalJacobian a x).det ≠ 0) :
    (graphParamConormal u β a x t).comp (fderiv ℝ (graphParamVariation u β a t) x) = 0 := by
  have hv (j : Fin n) : graphParamConormal u β a x t
      (fderiv ℝ (graphParamVariation u β a t) x (coordinateVector n j)) = 0 := by
    rw [graphParamVariation_fderiv hu hβ ha, graphParamConormal_apply]
    have he (k : Fin n) :
        (coordinateVector n j + t • (EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun k => dirDeriv (coordinateVector n j) (a k) x)) k =
        (1 + t • horizontalJacobian a x) k j := by
      simp [coordinateVector, horizontalJacobian, Matrix.one_apply, eq_comm]
    simp_rw [he]
    rw [variationConormal_mul _ _ _ _ hJ, sub_self]
  apply ContinuousLinearMap.ext
  intro z
  rw [← sum_coordinateVector z]
  simp only [ContinuousLinearMap.comp_apply, map_sum, map_smul, hv, smul_zero,
    Finset.sum_const_zero, zero_apply]

lemma contDiffAt_graphParamVariation {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n} (hu : ContDiffAt ℝ ∞ u x)
    (hβ : ContDiffAt ℝ ∞ β x) (ha : ∀ k, ContDiffAt ℝ ∞ (a k) x) (t : ℝ) :
    ContDiffAt ℝ ∞ (graphParamVariation u β a t) x := by
  have hh : ContDiffAt ℝ ∞ (horizontalVelocity a) x :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contDiffAt.comp x (contDiffAt_pi.mpr ha)
  exact (contDiffAt_id.add (hh.const_smul t)).prodMk (hu.add (contDiffAt_const.mul hβ))

lemma parametricJacobian_det {n : ℕ} (φ : Space n → Space n) (x : Space n) :
    (parametricJacobian φ x).det = LinearMap.det (fderiv ℝ φ x).toLinearMap := by
  have he : parametricJacobian φ x = LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (fderiv ℝ φ x).toLinearMap := by
    ext i j
    rfl
  rw [he, LinearMap.det_toMatrix]

lemma coordinateAffineVariationArea_eq {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {φ : Space n → Space n} {x : Space n} (hφ : ContDiffAt ℝ ∞ φ x)
    (hx : φ x ∈ Ω) (hφJ : (parametricJacobian φ x).det ≠ 0) (t : ℝ)
    (hJ : (graphVariationJacobian a (t,φ x)).det ≠ 0)
    (hH : 0 ≤ (graphVariationSecond u β a (t,φ x)).det) :
    coordinateAffineVariationArea L v φ u β a x t =
      |LinearMap.det (fderiv ℝ φ x).toLinearMap| * affineParametricVariationArea L v u β a (φ x) t := by
  have huc := hu.contDiffAt (hΩ.mem_nhds hx)
  have hβc := hβ.contDiffAt (hΩ.mem_nhds hx)
  have hac (k : Fin n) := (ha k).contDiffAt (hΩ.mem_nhds hx)
  have hX := contDiffAt_graphParamVariation huc hβc hac t
  have hXL : ContDiffAt ℝ ∞ (fun y => L (graphParamVariation u β a t y) + v) (φ x) :=
    (L.contDiff.contDiffAt.comp (φ x) hX).add contDiffAt_const
  have hν := graphParamConormal_null (huc.differentiableAt (by simp))
    (hβc.differentiableAt (by simp)) (fun k => (hac k).differentiableAt (by simp)) t hJ
  have hn : ((graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap).comp
      (fderiv ℝ (fun y => L (graphParamVariation u β a t y) + v) (φ x)) = 0 := by
    have hd := ((L.hasFDerivAt.comp (φ x) (hX.differentiableAt (by simp)).hasFDerivAt).add_const v).fderiv
    have hd' : fderiv ℝ (fun y => L (graphParamVariation u β a t y) + v) (φ x) =
        L.toContinuousLinearMap.comp (fderiv ℝ (graphParamVariation u β a t) (φ x)) := by
      convert! hd using 1
      all_goals try with_reducible_and_instances rfl
    rw [hd']
    ext z
    have hh := congrArg (fun A : Space n →L[ℝ] ℝ => A z) hν
    simpa using hh
  have hHH : 0 ≤ (parametricSecondForm (fun y => L (graphParamVariation u β a t y) + v)
      ((graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap) (φ x)).det := by
    rw [parametricSecondForm_affine, graphParam_secondForm hΩ hu hβ ha hx]
    exact hH
  unfold coordinateAffineVariationArea
  rw [parametricAreaDensity_comp _ hXL hφ _ _ hn hHH hφJ, parametricJacobian_det]
  rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LocalVelocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma smooth_chart_jacobian_ne {n : ℕ} (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    {x : Space n} (hx : x ∈ φ.source) : (parametricJacobian φ x).det ≠ 0 := by
  have hd := ((hψ.contDiffAt (φ.open_target.mem_nhds (φ.map_source hx))).differentiableAt (by simp)).hasFDerivAt.comp x
    ((hφ.contDiffAt (φ.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have he : (φ.symm ∘ φ) =ᶠ[nhds x] id := by
    filter_upwards [φ.open_source.mem_nhds hx] with y hy
    exact φ.left_inv hy
  have hder : (fderiv ℝ φ.symm (φ x)).comp (fderiv ℝ φ x) = ContinuousLinearMap.id ℝ (Space n) := by
    rw [← hd.fderiv,he.fderiv_eq,fderiv_id]
  rw [parametricJacobian_det]
  have hdets := congrArg (fun A : Space n →L[ℝ] Space n => LinearMap.det A.toLinearMap) hder
  change LinearMap.det ((fderiv ℝ φ.symm (φ x)).toLinearMap.comp (fderiv ℝ φ x).toLinearMap) = _ at hdets
  rw [LinearMap.det_comp] at hdets
  have hone : LinearMap.det (ContinuousLinearMap.id ℝ (Space n)).toLinearMap = 1 := LinearMap.det_id
  rw [hone] at hdets
  exact right_ne_zero_of_mul_eq_one hdets

/- Every compact smooth ambient velocity in a local chart is a genuine
compact smooth graph velocity. This removes the extension requirement from
the coordinate stationarity theorem. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricNormalization
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

lemma parametricFrame_smul_det {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    (X : Space n → E) (ξ : E) (x : Space n) (c : ℝ) :
    b.det (parametricFrame X (c • ξ) x) = c * b.det (parametricFrame X ξ x) := by
  have he (r : ℝ) : parametricFrame X (r • ξ) x =
      Function.update (parametricFrame X ξ x) (Sum.inr ()) (r • ξ) := by
    funext i
    rcases i with i | i
    · simp [parametricFrame]
    · cases i; simp [parametricFrame]
  rw [he, b.det.map_update_smul]
  have hh : Function.update (parametricFrame X ξ x) (Sum.inr ()) ξ =
      parametricFrame X ξ x := by
    apply Function.update_eq_self
  rw [hh, smul_eq_mul]

lemma parametricSecondForm_smul {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {X : Space n → E} (hX : ContDiffOn ℝ ∞ X U) (ν : E →L[ℝ] ℝ)
    (c : ℝ) {x : Space n} (hx : x ∈ U) :
    parametricSecondForm X (c • ν) x = c • parametricSecondForm X ν x := by
  unfold parametricSecondForm
  change hessian (fun y => c * ν (X y)) x = _
  exact hessian_const_mul hU (ν.contDiff.comp_contDiffOn hX) c hx

/- Invariance under positive rescaling of the conormal and reciprocal scaling
of the transverse vector. Both are actual multilinear expressions. -/
theorem parametricAreaDensity_normalize {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) {U : Set (Space n)} (hU : IsOpen U)
    {X : Space n → E} (hX : ContDiffOn ℝ ∞ X U) (ν : E →L[ℝ] ℝ) (ξ : E)
    {c : ℝ} (hc : 0 < c) {x : Space n} (hx : x ∈ U)
    (hH : 0 ≤ (parametricSecondForm X ν x).det) :
    parametricAreaDensity b X (c • ν) (c⁻¹ • ξ) x =
      parametricAreaDensity b X ν ξ x := by
  rw [parametricAreaDensity, parametricSecondForm_smul hU hX ν c hx,
    Matrix.det_smul, Fintype.card_fin, parametricFrame_smul_det, abs_mul,
    abs_of_pos (inv_pos.mpr hc)]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hc.le _) hH,
    Real.mul_rpow (inv_nonneg.mpr hc.le) (abs_nonneg _),
    ← Real.rpow_natCast_mul hc.le n, Real.inv_rpow hc.le]
  have he : (n : ℝ) * (1 / ((n : ℝ) + 2)) = (n : ℝ) / ((n : ℝ) + 2) := by ring
  rw [he]
  have hz : c ^ ((n : ℝ) / ((n : ℝ) + 2)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hc _)
  unfold parametricAreaDensity
  simp only [Real.rpow_eq_pow]
  field_simp

/- A tangent vector can be added to the transverse column without changing
its affine volume. -/
lemma parametricFrame_add_tangent_det {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E)
    (ξ : E) (x v : Space n) :
    b.det (parametricFrame X (ξ + fderiv ℝ X x v) x) =
      b.det (parametricFrame X ξ x) := by
  let A := b.toMatrix (parametricFrame X ξ x)
  let coeff : Fin n ⊕ Unit → ℝ := Sum.elim v (fun _ => 1)
  have he : b.toMatrix (parametricFrame X (ξ + fderiv ℝ X x v) x) =
      A.updateCol (Sum.inr ()) (fun k => ∑ i, coeff i • A k i) := by
    ext i j
    rcases j with j | j
    · simp [A, Matrix.updateCol, Module.Basis.toMatrix_apply, parametricFrame]
    · cases j
      simp only [Module.Basis.toMatrix_apply, parametricFrame, Sum.elim_inr,
        Matrix.updateCol_self]
      rw [← sum_coordinateVector v]
      simp [A, coeff, Fintype.sum_sum_type, map_sum, map_smul, Module.Basis.toMatrix_apply,
        parametricFrame, add_comm]
  rw [Module.Basis.det_apply, he, Matrix.det_updateCol_sum]
  simp [coeff, A, Module.Basis.det_apply]

lemma parametricAreaDensity_add_tangent {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E)
    (ν : E →L[ℝ] ℝ) (ξ : E) (x v : Space n) :
    parametricAreaDensity b X ν (ξ + fderiv ℝ X x v) x =
      parametricAreaDensity b X ν ξ x := by
  simp only [parametricAreaDensity, parametricFrame_add_tangent_det]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricChoices
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

lemma parametricFrame_decomposition {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E) (ξ : E) (x : Space n)
    (hd : b.det (parametricFrame X ξ x) ≠ 0) (z : E) :
    ∃ w : Space n, ∃ c : ℝ, z = fderiv ℝ X x w+c • ξ := by
  obtain ⟨hi,hs⟩ := (b.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hd)
  let B : Module.Basis (Fin n ⊕ Unit) ℝ E := Module.Basis.mk hi hs.ge
  let w : Space n := ∑ i : Fin n, B.repr z (Sum.inl i) • coordinateVector n i
  refine ⟨w,B.repr z (Sum.inr ()),?_⟩
  have hh := B.sum_repr z
  simp only [Fintype.sum_sum_type,Fintype.sum_unique] at hh
  have he (i : Fin n ⊕ Unit) : B i = parametricFrame X ξ x i := Module.Basis.mk_apply _ _ _
  simp only [he,parametricFrame,Sum.elim_inl,Sum.elim_inr] at hh
  exact hh.symm.trans (by simp [w,map_sum,map_smul])

lemma parametric_conormal_unique {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E) (ξ : E) (x : Space n)
    (hd : b.det (parametricFrame X ξ x) ≠ 0) (ν ν' : E →L[ℝ] ℝ)
    (hν : ν.comp (fderiv ℝ X x) = 0) (hν' : ν'.comp (fderiv ℝ X x) = 0)
    (hξ : ν ξ = 1) : ν' = (ν' ξ) • ν := by
  ext z
  obtain ⟨w,c,rfl⟩ := parametricFrame_decomposition b X ξ x hd z
  have h0 : ν (fderiv ℝ X x w) = 0 := congrArg (fun f : Space n →L[ℝ] ℝ => f w) hν
  have h0' : ν' (fderiv ℝ X x w) = 0 := congrArg (fun f : Space n →L[ℝ] ℝ => f w) hν'
  simp [h0,h0',hξ,mul_comm]

lemma parametric_kernel_is_tangent {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E) (ξ : E) (x : Space n)
    (hd : b.det (parametricFrame X ξ x) ≠ 0) (ν : E →L[ℝ] ℝ)
    (hν : ν.comp (fderiv ℝ X x) = 0) (hξ : ν ξ = 1) {z : E} (hz : ν z = 0) :
    ∃ w : Space n, z = fderiv ℝ X x w := by
  obtain ⟨w,c,he⟩ := parametricFrame_decomposition b X ξ x hd z
  have h0 : ν (fderiv ℝ X x w) = 0 := congrArg (fun f : Space n →L[ℝ] ℝ => f w) hν
  rw [he,map_add,map_smul,hξ,h0,smul_eq_mul,mul_one,zero_add] at hz
  exact ⟨w,by simpa [hz] using he⟩

/- The literal affine area is independent of both allowed choices of
conormal and transverse vector. All transversality and orientation properties
are explicit; no intrinsic-area object is postulated. -/
theorem parametricAreaDensity_choices {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) {U : Set (Space n)} (hU : IsOpen U)
    {X : Space n → E} (hX : ContDiffOn ℝ ∞ X U) {x : Space n} (hx : x ∈ U)
    (ν ν' : E →L[ℝ] ℝ) (ξ ξ' : E)
    (hd : b.det (parametricFrame X ξ x) ≠ 0)
    (hν : ν.comp (fderiv ℝ X x) = 0) (hν' : ν'.comp (fderiv ℝ X x) = 0)
    (hξ : ν ξ = 1) (hξ' : ν' ξ' = 1) (hc : 0 < ν' ξ)
    (hH : 0 ≤ (parametricSecondForm X ν x).det) :
    parametricAreaDensity b X ν' ξ' x = parametricAreaDensity b X ν ξ x := by
  have he := parametric_conormal_unique b X ξ x hd ν ν' hν hν' hξ
  have hξν : ν ξ' = (ν' ξ)⁻¹ := by
    have hh := hξ'
    rw [he,smul_apply,smul_eq_mul] at hh
    have hh' : ν ξ' = 1 / (ν' ξ) := (eq_div_iff hc.ne').mpr (by simpa [mul_comm] using hh)
    simpa only [one_div] using hh'
  have hz : ν (ξ'-(ν' ξ)⁻¹ • ξ) = 0 := by simp [hξν,hξ]
  obtain ⟨w,hw⟩ := parametric_kernel_is_tangent b X ξ x hd ν hν hξ hz
  have hξe : ξ' = (ν' ξ)⁻¹ • ξ + fderiv ℝ X x w := by rw [← hw]; abel
  rw [hξe,parametricAreaDensity_add_tangent,he]
  simp only [smul_apply,smul_eq_mul,hξ,mul_one]
  exact parametricAreaDensity_normalize b hU hX ν ξ hc hx hH

lemma parametricAreaDensity_congr {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X Y : Space n → E} {x : Space n} (h : X =ᶠ[nhds x] Y)
    (ν : E →L[ℝ] ℝ) (ξ : E) :
    parametricAreaDensity b X ν ξ x = parametricAreaDensity b Y ν ξ x := by
  have he : (fun y => ν (X y)) =ᶠ[nhds x] (fun y => ν (Y y)) := h.mono (fun _ hy => congrArg ν hy)
  simp only [parametricAreaDensity,parametricSecondForm,parametricFrame,hessian_eq_of_eventuallyEq he,h.fderiv_eq]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricChoiceTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma affineParametric_conormal_null {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hβ : ContDiffAt ℝ ∞ β x)
    (ha : ∀ k, ContDiffAt ℝ ∞ (a k) x) (t : ℝ)
    (hJ : (graphVariationJacobian a (t,x)).det ≠ 0)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    ((graphParamConormal u β a x t).comp L.symm.toContinuousLinearMap).comp
      (fderiv ℝ (fun y => L (graphParamVariation u β a t y)+v) x) = 0 := by
  have hX := contDiffAt_graphParamVariation hu hβ ha t
  have hd := ((L.hasFDerivAt.comp x (hX.differentiableAt (by simp)).hasFDerivAt).add_const v).fderiv
  have hd' : fderiv ℝ (fun y => L (graphParamVariation u β a t y)+v) x =
      L.toContinuousLinearMap.comp (fderiv ℝ (graphParamVariation u β a t) x) := by
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
  rw [hd']
  have hh := graphParamConormal_null (hu.differentiableAt (by simp))
    (hβ.differentiableAt (by simp)) (fun k => (ha k).differentiableAt (by simp)) t hJ
  ext w
  simpa using congrArg (fun f : Space n →L[ℝ] ℝ => f w) hh

/- The ambient conormal/transverse choices in the local chart stationarity
functional may be replaced by any other inward normalized choices. -/
theorem coordinateAffineVariationArea_choices {n : ℕ}
    {Ω U : Set (Space n)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiff ℝ ∞ β)
    (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {φ : Space n → Space n} (hφ : ContDiffOn ℝ ∞ φ U) (hφΩ : φ '' U ⊆ Ω)
    {x : Space n} (hx : x ∈ U) (hφJ : (parametricJacobian φ x).det ≠ 0) (t : ℝ)
    (hJ : (graphVariationJacobian a (t,φ x)).det ≠ 0)
    (hH : 0 ≤ (graphVariationSecond u β a (t,φ x)).det)
    (ν : (Space n × ℝ) →L[ℝ] ℝ) (ξ : Space n × ℝ)
    (hν : ν.comp (fderiv ℝ ((fun y => L (graphParamVariation u β a t y)+v) ∘ φ) x) = 0)
    (hξ : ν ξ = 1) (hc : 0 < ν (L ((0 : Space n),1))) :
    parametricAreaDensity (graphAmbientBasis n)
      ((fun y => L (graphParamVariation u β a t y)+v) ∘ φ) ν ξ x =
      coordinateAffineVariationArea L v φ u β a x t := by
  let X := fun y => L (graphParamVariation u β a t y)+v
  let μ := (graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap
  have hxΩ := hφΩ (mem_image_of_mem φ hx)
  have huc := hu.contDiffAt (hΩ.mem_nhds hxΩ)
  have hφc := hφ.contDiffAt (hU.mem_nhds hx)
  have hW := contDiffAt_graphParamVariation huc hβ.contDiffAt (fun k => (ha k).contDiffAt) t
  have hX : ContDiffAt ℝ ∞ X (φ x) := (L.contDiff.contDiffAt.comp (φ x) hW).add contDiffAt_const
  have hμ : μ.comp (fderiv ℝ X (φ x)) = 0 := affineParametric_conormal_null huc
    hβ.contDiffAt (fun k => (ha k).contDiffAt) t hJ L v
  have hμc : μ.comp (fderiv ℝ (X ∘ φ) x) = 0 := by
    rw [fderiv_comp x (hX.differentiableAt (by simp)) (hφc.differentiableAt (by simp))]
    rw [← ContinuousLinearMap.comp_assoc,hμ,ContinuousLinearMap.zero_comp]
  have hfull : ContDiffOn ℝ ∞ (X ∘ φ) U := by
    intro z hz
    have huz := hu.contDiffAt (hΩ.mem_nhds (hφΩ (mem_image_of_mem φ hz)))
    have hWz := contDiffAt_graphParamVariation huz hβ.contDiffAt (fun k => (ha k).contDiffAt) t
    exact (((L.contDiff.contDiffAt.comp (φ z) hWz).add contDiffAt_const).comp z
      (hφ.contDiffAt (hU.mem_nhds hz))).contDiffWithinAt
  have hdet : (graphAmbientBasis n).det (parametricFrame (X ∘ φ) (L ((0 : Space n),1)) x) ≠ 0 := by
    rw [parametricFrame_comp_det _ (hX.differentiableAt (by simp)) (hφc.differentiableAt (by simp))]
    apply mul_ne_zero _ hφJ
    change (graphAmbientBasis n).det (parametricFrame (fun y => L (graphParamVariation u β a t y)+v)
      (L ((0 : Space n),1)) (φ x)) ≠ 0
    rw [parametricFrame_affine (hW.differentiableAt (by simp)),Module.Basis.det_comp]
    apply mul_ne_zero
    · rw [← LinearMap.det_toMatrix (graphAmbientBasis n)]
      exact (L.toLinearEquiv.isUnit_det _ _).ne_zero
    · rw [graphParam_frame_determinant (huc.differentiableAt (by simp))
        (hβ.contDiffAt.differentiableAt (by simp))
        (fun k => (ha k).contDiffAt.differentiableAt (by simp)) t]
      exact hJ
  have hsecond : 0 ≤ (parametricSecondForm (X ∘ φ) μ x).det := by
    rw [parametricSecondForm_comp hX hφc μ hμ]
    change 0 ≤ ((parametricJacobian φ x).transpose *
      parametricSecondForm (fun y => L (graphParamVariation u β a t y)+v)
        ((graphParamConormal u β a (φ x) t).comp L.symm.toContinuousLinearMap) (φ x) * _).det
    rw [parametricSecondForm_affine,graphParam_secondForm hΩ hu hβ.contDiffOn (fun k => (ha k).contDiffOn) hxΩ,
      Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
    change 0 ≤ (parametricJacobian φ x).det * (graphVariationSecond u β a (t,φ x)).det * (parametricJacobian φ x).det
    nlinarith [sq_nonneg (parametricJacobian φ x).det]
  exact parametricAreaDensity_choices (graphAmbientBasis n) hU hfull hx μ ν
    (L ((0 : Space n),1)) ξ hdet hμc hν (by simp [μ]) hξ hc hsecond

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AmbientImmersion
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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma parametricAreaDensity_volume_pullback {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ F) (L : E ≃L[ℝ] F) (a : F)
    {X : Space n → E} {x : Space n} (hX : DifferentiableAt ℝ X x)
    (ν : E →L[ℝ] ℝ) (ξ : E) :
    parametricAreaDensity b (fun y => a+L (X y)) (ν.comp L.symm.toContinuousLinearMap) (L ξ) x =
      parametricAreaDensity (b.map L.symm.toLinearEquiv) X ν ξ x := by
  have hS : parametricSecondForm (fun y => a+L (X y)) (ν.comp L.symm.toContinuousLinearMap) x =
      parametricSecondForm X ν x := by
    have he : (fun y => (ν.comp L.symm.toContinuousLinearMap) (a+L (X y))) =
        (fun y => ν (X y)+ν (L.symm a)) := by funext y; simp [add_comm]
    simp only [parametricSecondForm,he,hessian_add_constant]
  have hd := ((L.hasFDerivAt.comp x hX.hasFDerivAt).const_add a).fderiv
  change fderiv ℝ (fun y => a+L (X y)) x = _ at hd
  have hFr : parametricFrame (fun y => a+L (X y)) (L ξ) x =
      L ∘ parametricFrame X ξ x := by
    funext i
    rcases i with i | ⟨⟩
    · change fderiv ℝ (fun y => a+L (X y)) x (coordinateVector n i) = _
      rw [hd]
      rfl
    · rfl
  simp only [parametricAreaDensity,hS,hFr,Module.Basis.det_map]
  rfl

/- Literal local affine stationarity in any ambient vector coordinates.
The reference volume basis is transported exactly, not replaced by a
coordinate-free area axiom. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ParametricBasis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parametricAreaDensity_change_basis {n : ℕ}
    (b b' : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E)
    (ν : E →L[ℝ] ℝ) (ξ : E) (x : Space n) :
    parametricAreaDensity b' X ν ξ x =
      Real.rpow |b'.det b| ((n : ℝ)/((n : ℝ)+2)) * parametricAreaDensity b X ν ξ x := by
  have he : b'.det (parametricFrame X ξ x) = b'.det b * b.det (parametricFrame X ξ x) := by
    conv_lhs => rw [b'.det.eq_smul_basis_det b]
    rfl
  simp only [parametricAreaDensity,he,abs_mul]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  ring

end ParametricBasis

open Filter
open scoped Topology

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualChartArea
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

/- The actual graph area in an arbitrary smooth chart, with arbitrary inward
normalized conormal. This is a density identity, not a stationarity premise. -/
lemma graph_chart_parametricAreaDensity {n : ℕ} {Ω U : Set (Space n)}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {φ : Space n → Space n} (hφ : ContDiffOn ℝ ∞ φ U) (hφΩ : φ '' U ⊆ Ω)
    {x : Space n} (hx : x ∈ U) (hJ : (parametricJacobian φ x).det ≠ 0)
    (ν : (Space n × ℝ) →L[ℝ] ℝ) (ξ : Space n × ℝ)
    (hν : ν.comp (fderiv ℝ (fun y => (φ y,u (φ y))) x) = 0)
    (hξ : ν ξ = 1) (hc : 0 < ν ((0 : Space n),1)) :
    parametricAreaDensity (graphAmbientBasis n) (fun y => (φ y,u (φ y))) ν ξ x =
      |LinearMap.det (fderiv ℝ φ x).toLinearMap| * affineAreaDensity u (φ x) := by
  let L := ContinuousLinearEquiv.refl ℝ (Space n × ℝ)
  let β : Space n → ℝ := fun _ => 0
  let a : Fin n → Space n → ℝ := fun _ _ => 0
  have hβ : ContDiff ℝ ∞ β := contDiff_const
  have ha : ∀ k, ContDiff ℝ ∞ (a k) := fun _ => contDiff_const
  have hX : ((fun y => L (graphParamVariation u β a 0 y)+0) ∘ φ) =
      (fun y => (φ y,u (φ y))) := by funext y; simp [L,graphParamVariation]
  have hJ0 : (graphVariationJacobian a (0,φ x)).det ≠ 0 := by simp [graphVariationJacobian]
  have hH0 : 0 ≤ (graphVariationSecond u β a (0,φ x)).det := by
    simpa [graphVariationSecond] using (hp (φ x) (hφΩ (mem_image_of_mem φ hx))).det_pos.le
  have hh := coordinateAffineVariationArea_choices hΩ hU hu hβ ha L 0 hφ hφΩ hx hJ 0
    hJ0 hH0 ν ξ (by simpa only [hX] using hν) hξ (by simpa [L] using hc)
  rw [hX] at hh
  rw [hh,coordinateAffineVariationArea_eq hΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn) L 0 (hφ.contDiffAt (hU.mem_nhds hx))
    (hφΩ (mem_image_of_mem φ hx)) hJ 0 hJ0 hH0,
    affineParametricVariationArea_eq hΩ hu hβ.contDiffOn (fun k => (ha k).contDiffOn)
      L 0 (hφΩ (mem_image_of_mem φ hx)) 0]
  have hdet : LinearMap.det L.toLinearEquiv.toLinearMap = 1 := by
    change LinearMap.det (LinearMap.id : (Space n × ℝ) →ₗ[ℝ] (Space n × ℝ)) = 1
    simp
  simp [hdet,graphVariationArea,variationAreaDensity,affineAreaDensity]

/- Exact local area transport for an arbitrary immersed parametrization of the
actual graph. The inverse chart is constructed, and all measurable subsets of
its source share the same determinant-normalized area identity. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedChartLIntegral
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

/- Weighted local area transport. The weight is any actual function on the
original graph; no integrability or measure transport premise is introduced. -/
theorem graph_chart_weighted_affineArea_lintegral_oai {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → E} {u : Space n → ℝ}
    (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : E ≃L[ℝ] (Space n × ℝ))
    (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hs : φ.source ⊆ U) (ht : φ.target ⊆ Ω)
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    (he : ∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x)))
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKW : K ⊆ φ.source)
    (ν : Space n → E →L[ℝ] ℝ) (ξ : Space n → E)
    (hν : ∀ x ∈ K, (ν x).comp (fderiv ℝ X x) = 0)
    (hξ : ∀ x ∈ K, ν x (ξ x) = 1)
    (hc : ∀ x ∈ K, 0 < ν x (L.symm ((0 : Space n),1))) (w : Space n → ℝ≥0∞) :
    (∫⁻ x in K, ENNReal.ofReal (parametricAreaDensity b X (ν x) (ξ x) x) * w (φ x)) =
      ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
        ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * w y := by
  let Z : Space n → Space n × ℝ := fun y => a+L (X y)
  let b₀ := (graphAmbientBasis n).map L.symm.toLinearEquiv
  let c := Real.rpow |b.det b₀| ((n : ℝ)/((n : ℝ)+2))
  have hpt (x : Space n) (hx : x ∈ K) :
      parametricAreaDensity b X (ν x) (ξ x) x =
        c * (|LinearMap.det (fderiv ℝ φ x).toLinearMap| * affineAreaDensity u (φ x)) := by
    have hxU := hs (hKW hx)
    have hdX := (hX.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have heg : Z =ᶠ[nhds x] (fun y => (φ y,u (φ y))) := by
      filter_upwards [φ.open_source.mem_nhds (hKW hx)] with y hy
      exact he y hy
    have hdZ : fderiv ℝ Z x = L.toContinuousLinearMap.comp (fderiv ℝ X x) :=
      ((L.hasFDerivAt.comp x hdX.hasFDerivAt).const_add a).fderiv
    have hνZ : ((ν x).comp L.symm.toContinuousLinearMap).comp (fderiv ℝ Z x) = 0 := by
      rw [hdZ]
      ext v
      simpa using congrArg (fun T : Space n →L[ℝ] ℝ => T v) (hν x hx)
    rw [parametricAreaDensity_change_basis b₀ b]
    change c * parametricAreaDensity b₀ X (ν x) (ξ x) x = _
    congr 1
    rw [← parametricAreaDensity_volume_pullback (graphAmbientBasis n) L a hdX]
    change parametricAreaDensity (graphAmbientBasis n) Z _ _ x = _
    rw [parametricAreaDensity_congr (graphAmbientBasis n) heg]
    apply graph_chart_parametricAreaDensity hΩ φ.open_source hu hp hφ
      (by rintro _ ⟨y,hy,rfl⟩; exact ht (φ.map_source hy)) (hKW hx)
      (smooth_chart_jacobian_ne φ hφ hψ (hKW hx))
    · rw [← heg.fderiv_eq (𝕜 := ℝ)]
      exact hνZ
    · simpa using hξ x hx
    · exact hc x hx
  have hc : 0 ≤ c := Real.rpow_nonneg (abs_nonneg _) _
  change (∫⁻ x in K, _) = ENNReal.ofReal c * _
  calc
    _ = ∫⁻ x in K, ENNReal.ofReal c * (ENNReal.ofReal |LinearMap.det (fderiv ℝ φ x).toLinearMap| *
        (ENNReal.ofReal (affineAreaDensity u (φ x)) * w (φ x))) := by
      apply setLIntegral_congr_fun hK
      intro x hx
      dsimp only
      rw [hpt x hx,ENNReal.ofReal_mul hc,ENNReal.ofReal_mul (abs_nonneg _)]
      ring
    _ = ENNReal.ofReal c * ∫⁻ x in K, ENNReal.ofReal |LinearMap.det (fderiv ℝ φ x).toLinearMap| *
        (ENNReal.ofReal (affineAreaDensity u (φ x)) * w (φ x)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK
        (fun x hx => ((hφ.contDiffAt (φ.open_source.mem_nhds (hKW hx))).differentiableAt
          (by simp)).hasFDerivAt.hasFDerivWithinAt)
        (φ.injOn.mono hKW) (fun y => ENNReal.ofReal (affineAreaDensity u y) * w y)).symm

end AffineBernstein
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral_oai.{u_1} := @OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral_oai.{u_1}
