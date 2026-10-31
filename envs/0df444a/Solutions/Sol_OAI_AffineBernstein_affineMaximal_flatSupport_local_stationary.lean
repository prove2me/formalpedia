-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:00:57.971447+00:00
-- url     : https://prove2.me/submissions/4bc3fca5-b807-42aa-a2b9-08003c43112e

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_parametrization
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_supportConormal_inward
import Theorems.Thm_OAI_AffineBernstein_affineMaximal_local_chart_stationary

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

lemma contDiffAt_graphVariationJacobian {n : ℕ} {a : Fin n → Space n → ℝ}
    {p : ℝ × Space n} (ha : ∀ k, ContDiffAt ℝ ∞ (a k) p.2) :
    ContDiffAt ℝ ∞ (fun q i j => graphVariationJacobian a q i j) p := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp only [graphVariationJacobian, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    horizontalJacobian]
  exact contDiffAt_const.add (contDiffAt_fst.mul
    ((contDiffAt_dirDeriv (ha i) _).comp p contDiffAt_snd))

lemma contDiffAt_graphVariationSecond {n : ℕ} {u β : Space n → ℝ}
    {a : Fin n → Space n → ℝ} {p : ℝ × Space n}
    (hu : ContDiffAt ℝ ∞ u p.2) (hβ : ContDiffAt ℝ ∞ β p.2)
    (ha : ∀ k, ContDiffAt ℝ ∞ (a k) p.2)
    (hJ : (graphVariationJacobian a p).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q i j => graphVariationSecond u β a q i j) p := by
  have hC (k : Fin n) : ContDiffAt ℝ ∞ (fun q : ℝ × Space n =>
      variationConormal (horizontalJacobian a q.2)
        (fun l => dirDeriv (coordinateVector n l) u q.2)
        (fun l => dirDeriv (coordinateVector n l) β q.2) q.1 k) p := by
    apply ContDiffAt.sum
    intro l _
    apply ContDiffAt.mul
    · exact ((contDiffAt_dirDeriv hu _).comp p contDiffAt_snd).add
        (contDiffAt_fst.mul ((contDiffAt_dirDeriv hβ _).comp p contDiffAt_snd))
    · exact contDiffAt_inverse_matrix_entry_param (contDiffAt_graphVariationJacobian ha) hJ l k
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp only [graphVariationSecond, variationSecondForm, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  apply ContDiffAt.sub
    (((contDiffAt_hessian_entry hu i j).comp p contDiffAt_snd).add
      (contDiffAt_fst.mul ((contDiffAt_hessian_entry hβ i j).comp p contDiffAt_snd)))
  apply ContDiffAt.mul contDiffAt_fst
  apply ContDiffAt.sum
  intro k _
  exact (hC k).mul ((contDiffAt_hessian_entry (ha k) i j).comp p contDiffAt_snd)

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

lemma eventually_uniform_compact_zero {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {P : ℝ × E → Prop}
    (hP : ∀ x ∈ K, {q | P q} ∈ nhds (0,x)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ x ∈ K, P (t,x) := by
  have hs : {0} ×ˢ K ⊆ interior {q | P q} := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    simp only [mem_singleton_iff] at ht
    subst t
    exact mem_interior_iff_mem_nhds.mpr (hP x hx)
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK isOpen_interior hs
  filter_upwards [hV.mem_nhds (h0V (by simp))] with t ht
  intro x hx
  exact interior_subset (hVW ⟨ht,hKW hx⟩)

lemma eventually_graphVariation_positive {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) :
    ∀ᶠ t : ℝ in nhds 0, ∀ x ∈ K,
      (graphVariationJacobian a (t,x)).det ≠ 0 ∧ 0 < (graphVariationSecond u β a (t,x)).det := by
  apply eventually_uniform_compact_zero hK (P := fun q =>
    (graphVariationJacobian a q).det ≠ 0 ∧ 0 < (graphVariationSecond u β a q).det)
  intro x hx
  have huc := hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))
  have hβc := hβ.contDiffAt (hΩ.mem_nhds (hKΩ hx))
  have hac (k : Fin n) := (ha k).contDiffAt (hΩ.mem_nhds (hKΩ hx))
  have hJ0 : (graphVariationJacobian a (0,x)).det ≠ 0 := by simp [graphVariationJacobian]
  have hH0 : 0 < (graphVariationSecond u β a (0,x)).det := by
    simpa [graphVariationSecond] using (hp x (hKΩ hx)).det_pos
  have hJ := ((continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp (0,x)
    (contDiffAt_graphVariationJacobian hac)).continuousAt.eventually_ne hJ0
  have hH := ((continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp (0,x)
    (contDiffAt_graphVariationSecond huc hβc hac hJ0)).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds hH0)
  filter_upwards [hJ,hH] with q hq1 hq2
  exact ⟨hq1,hq2⟩

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
-- module Solutions.OAIQ22_AB.AffineBernstein_LocalAreaStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Literal affine area is stationary for every compact smooth local ambient
variation, with any continuous inward normalized conormal/transverse choices.
The equation on the original graph, not an ambient stationary axiom, is used. -/
theorem affineMaximal_local_parametric_area_stationary {n : ℕ}
    {Ω K : Set (Space n)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    (hKφ : K ⊆ φ.source) (hφΩ : φ.target ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    {V : Space n → Space n × ℝ} (hV : ContDiffOn ℝ ∞ V φ.source)
    (hVK : tsupport V ⊆ K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (ν : ℝ → Space n → (Space n × ℝ) →L[ℝ] ℝ) (ξ : ℝ → Space n → Space n × ℝ)
    (hν : ∀ t x, x ∈ φ.source → (ν t x).comp
      (fderiv ℝ (fun y => L (φ y,u (φ y))+v+t • V y) x) = 0)
    (hξ : ∀ t x, x ∈ φ.source → ν t x (ξ t x) = 1)
    (hc : ∀ x ∈ K, 0 < ν 0 x (L ((0 : Space n),1)))
    (hcont : ∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L ((0 : Space n),1))) (0,x)) :
    HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity (graphAmbientBasis n)
      (fun y => L (φ y,u (φ y))+v+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  obtain ⟨β,a,hβ,ha,hβK,haK,he,hstat⟩ := affineMaximal_local_chart_stationary
    hΩ hK φ hφ hψ hKφ hφΩ hu hp hm hV hVK L v
  have hKi : IsCompact (φ '' K) := hK.image_of_continuousOn (φ.continuousOn.mono hKφ)
  have hiΩ : φ '' K ⊆ Ω := by
    rintro _ ⟨x,hx,rfl⟩
    exact hφΩ (φ.map_source (hKφ hx))
  have hpos : ∀ᶠ t : ℝ in nhds 0, ∀ x ∈ K, 0 < ν t x (L ((0 : Space n),1)) := by
    apply eventually_uniform_compact_zero hK (P := fun q => 0 < ν q.1 q.2 (L ((0 : Space n),1)))
    intro x hx
    exact (hcont x hx).preimage_mem_nhds (Ioi_mem_nhds (hc x hx))
  apply hstat.congr_of_eventuallyEq
  filter_upwards [hpos,eventually_graphVariation_positive hΩ hKi hiΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn) hp] with t ht hreg
  apply setIntegral_congr_fun hK.measurableSet
  intro x hx
  have hg : (fun y => L (φ y,u (φ y))+v+t • V y) =ᶠ[nhds x]
      ((fun y => L (graphParamVariation u β a t y)+v) ∘ φ) := by
    filter_upwards [φ.open_source.mem_nhds (hKφ hx)] with y hy
    exact (he y hy t).symm
  change parametricAreaDensity (graphAmbientBasis n) _ (ν t x) (ξ t x) x = _
  rw [parametricAreaDensity_congr (graphAmbientBasis n) hg]
  exact coordinateAffineVariationArea_choices hΩ φ.open_source hu hβ ha L v hφ
    (by rintro _ ⟨y,hy,rfl⟩; exact hφΩ (φ.map_source hy)) (hKφ hx)
    (smooth_chart_jacobian_ne φ hφ hψ (hKφ hx)) t
    (hreg (φ x) (mem_image_of_mem φ hx)).1 (hreg (φ x) (mem_image_of_mem φ hx)).2.le
    (ν t x) (ξ t x) (by rw [← hg.fderiv_eq]; exact hν t x (hKφ hx))
    (hξ t x (hKφ hx)) (ht x hx)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothGraphChart
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

lemma exists_smooth_local_diffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) {f : E → E}
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) (hfx : f x ∈ V)
    (e : E ≃L[ℝ] E) (he : fderiv ℝ f x = e.toContinuousLinearMap) :
    ∃ φ : OpenPartialHomeomorph E E, x ∈ φ.source ∧ φ.source ⊆ U ∧
      φ.target ⊆ V ∧ (φ : E → E) = f ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target := by
  have hfa := hf.contDiffAt (hU.mem_nhds hx)
  have hd : HasFDerivAt f e.toContinuousLinearMap x := by
    rw [← he]
    exact hfa.differentiableAt (by simp) |>.hasFDerivAt
  let φ₀ := hfa.toOpenPartialHomeomorph f hd (by simp)
  have hx₀ : x ∈ φ₀.source := hfa.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hn : ∀ᶠ y in nhds x, ∃ e' : E ≃L[ℝ] E, e'.toContinuousLinearMap = fderiv ℝ f y := by
    have hc : ContinuousAt (fderiv ℝ f) x := hfa.continuousAt_fderiv (by simp)
    exact hc.preimage_mem_nhds (by rw [he]; exact e.nhds)
  obtain ⟨N,hN,hNo,hxN⟩ := mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hx) (inter_mem (hfa.continuousAt.preimage_mem_nhds (hV.mem_nhds hfx)) hn))
  let φ := φ₀.restrOpen N hNo
  have hφf : (φ : E → E) = f := rfl
  have hs : φ.source ⊆ U := fun y hy => (hN hy.2).1
  refine ⟨φ,⟨hx₀,hxN⟩,hs,?_,hφf,?_,?_⟩
  · intro y hy
    have hys := φ.map_target hy
    have hh := (hN hys.2).2.1
    change f (φ.symm y) ∈ V at hh
    simpa only [← hφf,φ.right_inv hy] using hh
  · simpa only [hφf] using hf.mono hs
  · intro y hy
    have hys := φ.map_target hy
    obtain ⟨e',he'⟩ := (hN hys.2).2.2
    have hg : ContDiffAt ℝ ∞ f (φ.symm y) := hf.contDiffAt (hU.mem_nhds (hs hys))
    apply (φ.contDiffAt_symm hy (f₀' := e') ?_ ?_).contDiffWithinAt
    · rw [hφf,he']
      exact hg.differentiableAt (by simp) |>.hasFDerivAt
    · simpa only [hφf] using hg

/- The graph projection of a smooth immersed parametrization of a graph
has nonsingular derivative. This is the differential input to the local
chart used in the support-coordinate stationarity calculation. -/
lemma graph_projection_derivative_bijective {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → Space n × ℝ}
    {u : Space n → ℝ} (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    {x : Space n} (hx : x ∈ U) (hi : Function.Injective (fderiv ℝ X x)) :
    Function.Bijective (fderiv ℝ (fun y => (X y).1) x) := by
  have hXa := hX.contDiffAt (hU.mem_nhds hx)
  have hd := hXa.differentiableAt (by simp)
  have he : X =ᶠ[nhds x] (fun y => ((X y).1,u (X y).1)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Prod.ext rfl (him y hy).2
  have hu' := (hu.contDiffAt (hΩ.mem_nhds (him x hx).1)).differentiableAt (by simp)
  have heD := he.fderiv_eq (𝕜 := ℝ)
  have hg : fderiv ℝ X x =
      (fderiv ℝ (fun y => (X y).1) x).prod
        ((fderiv ℝ u (X x).1).comp (fderiv ℝ (fun y => (X y).1) x)) := by
    rw [heD]
    exact ((hd.fst.hasFDerivAt).prodMk (hu'.hasFDerivAt.comp x hd.fst.hasFDerivAt)).fderiv
  have hinj : Function.Injective (fderiv ℝ (fun y => (X y).1) x) := by
    intro v w hvw
    apply hi
    rw [hg]
    simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,hvw]
  exact ⟨hinj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩

theorem exists_smooth_graph_chart {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → Space n × ℝ}
    {u : Space n → ℝ} (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    {x : Space n} (hx : x ∈ U) (hi : Function.Injective (fderiv ℝ X x)) :
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n), x ∈ φ.source ∧ φ.source ⊆ U ∧
      φ.target ⊆ Ω ∧ (∀ y ∈ φ.source, X y = (φ y,u (φ y))) ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target := by
  have hb := graph_projection_derivative_bijective hU hΩ hX hu him hx hi
  let e := (LinearEquiv.ofBijective (fderiv ℝ (fun y => (X y).1) x).toLinearMap hb).toContinuousLinearEquiv
  obtain ⟨φ,hxφ,hs,ht,he,hφ,hψ⟩ := exists_smooth_local_diffeomorph hU hΩ hX.fst hx (him x hx).1 e rfl
  refine ⟨φ,hxφ,hs,ht,?_,hφ,hψ⟩
  intro y hy
  rw [he]
  exact Prod.ext rfl (him y (hs hy)).2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ImmersionStationary
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

theorem affineMaximal_immersed_graph_local_stationary {n : ℕ}
    {U Ω : Set (Space n)} (hU : IsOpen U) (hΩ : IsOpen Ω)
    {X : Space n → Space n × ℝ} {u : Space n → ℝ}
    (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    {x₀ : Space n} (hx₀ : x₀ ∈ U) (hi : Function.Injective (fderiv ℝ X x₀))
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (V : Space n → Space n × ℝ), ContDiffOn ℝ ∞ V W → tsupport V ⊆ K →
      ∀ (ν : ℝ → Space n → (Space n × ℝ) →L[ℝ] ℝ) (ξ : ℝ → Space n → Space n × ℝ),
      (∀ t x, x ∈ W → (ν t x).comp (fderiv ℝ (fun y => L (X y)+v+t • V y) x) = 0) →
      (∀ t x, x ∈ W → ν t x (ξ t x) = 1) →
      (∀ x ∈ K, 0 < ν 0 x (L ((0 : Space n),1))) →
      (∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L ((0 : Space n),1))) (0,x)) →
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity (graphAmbientBasis n)
        (fun y => L (X y)+v+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  obtain ⟨φ,hxφ,hs,ht,he,hφ,hψ⟩ := exists_smooth_graph_chart hU hΩ hX hu him hx₀ hi
  refine ⟨φ.source,φ.open_source,hxφ,hs,?_⟩
  intro K hK hKW V hV hVK ν ξ hν hξ hc hcont
  have hg (t : ℝ) (x : Space n) (hx : x ∈ φ.source) :
      (fun y => L (X y)+v+t • V y) =ᶠ[nhds x]
        (fun y => L (φ y,u (φ y))+v+t • V y) := by
    filter_upwards [φ.open_source.mem_nhds hx] with y hy
    rw [he y hy]
  have hh := affineMaximal_local_parametric_area_stationary hΩ hK φ hφ hψ hKW ht hu hp hm
    hV hVK L v ν ξ (fun t x hx => by rw [← (hg t x hx).fderiv_eq (𝕜 := ℝ)]; exact hν t x hx)
    hξ hc hcont
  apply hh.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t => setIntegral_congr_fun hK.measurableSet
    (fun x hx => parametricAreaDensity_congr (graphAmbientBasis n) (hg t x (hKW hx)) _ _)

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
theorem affineMaximal_ambient_immersed_local_stationary {n : ℕ}
    {U Ω : Set (Space n)} (hU : IsOpen U) (hΩ : IsOpen Ω)
    {X : Space n → E} {u : Space n → ℝ}
    (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : E ≃L[ℝ] (Space n × ℝ))
    (him : ∀ y ∈ U, (a+L (X y)).1 ∈ Ω ∧ (a+L (X y)).2 = u (a+L (X y)).1)
    {x₀ : Space n} (hx₀ : x₀ ∈ U) (hi : Function.Injective (fderiv ℝ X x₀)) :
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (V : Space n → E), ContDiffOn ℝ ∞ V W → tsupport V ⊆ K →
      ∀ (ν : ℝ → Space n → E →L[ℝ] ℝ) (ξ : ℝ → Space n → E),
      (∀ t x, x ∈ W → (ν t x).comp (fderiv ℝ (fun y => X y+t • V y) x) = 0) →
      (∀ t x, x ∈ W → ν t x (ξ t x) = 1) →
      (∀ x ∈ K, 0 < ν 0 x (L.symm ((0 : Space n),1))) →
      (∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L.symm ((0 : Space n),1))) (0,x)) →
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity
        ((graphAmbientBasis n).map L.symm.toLinearEquiv)
        (fun y => X y+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  let Z : Space n → Space n × ℝ := fun y => a+L (X y)
  have hZ : ContDiffOn ℝ ∞ Z U := contDiffOn_const.add (L.contDiff.comp_contDiffOn hX)
  have hiZ : Function.Injective (fderiv ℝ Z x₀) := by
    have hd := ((L.hasFDerivAt.comp x₀
      ((hX.contDiffAt (hU.mem_nhds hx₀)).differentiableAt (by simp)).hasFDerivAt).const_add a).fderiv
    change fderiv ℝ Z x₀ = _ at hd
    rw [hd]
    exact L.injective.comp hi
  obtain ⟨W,hW,hxW,hWU,hstat⟩ := affineMaximal_immersed_graph_local_stationary hU hΩ hZ hu hp hm
    him hx₀ hiZ (ContinuousLinearEquiv.refl ℝ (Space n × ℝ)) 0
  refine ⟨W,hW,hxW,hWU,?_⟩
  intro K hK hKW V hV hVK ν ξ hν hξ hc hcont
  have hLV : tsupport (fun y => L (V y)) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    apply hVK (subset_closure ?_)
    intro hz
    exact hy (by simp [hz])
  have hXW : ContDiffOn ℝ ∞ X W := hX.mono hWU
  have hdt (t : ℝ) (x : Space n) (hx : x ∈ W) :
      DifferentiableAt ℝ (fun y => X y+t • V y) x :=
    ((hXW.add (hV.const_smul t)).contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have he (t : ℝ) :
      (fun y => (ContinuousLinearEquiv.refl ℝ (Space n × ℝ)) (Z y)+0+t • L (V y)) =
        (fun y => a+L (X y+t • V y)) := by funext y; simp [Z,map_add,map_smul,add_assoc]
  have hh := hstat K hK hKW (fun y => L (V y)) (L.contDiff.comp_contDiffOn hV) hLV
    (fun t x => (ν t x).comp L.symm.toContinuousLinearMap) (fun t x => L (ξ t x))
    (by
      intro t x hx
      rw [he]
      have hd := ((L.hasFDerivAt.comp x (hdt t x hx).hasFDerivAt).const_add a).fderiv
      change fderiv ℝ (fun y => a+L (X y+t • V y)) x = _ at hd
      rw [hd]
      ext w
      have h0 := congrArg (fun T : Space n →L[ℝ] ℝ => T w) (hν t x hx)
      simpa using h0)
    (by intro t x hx; simpa using hξ t x hx)
    (by intro x hx; simpa using hc x hx)
    (by intro x hx; simpa using hcont x hx)
  apply hh.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro t
  apply setIntegral_congr_fun hK.measurableSet
  intro x hx
  rw [he]
  exact (parametricAreaDensity_volume_pullback (graphAmbientBasis n) L a
    (hdt t x (hKW hx)) (ν t x) (ξ t x)).symm

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
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/- The literal PDE supplies stationarity on every actual flat-normal support
chart. The chart inverse and conormal orientation are derived, not assumed. -/
theorem affineMaximal_flatSupport_local_stationary_oai {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0)
    (b : Module.Basis (Fin n ⊕ Unit) ℝ (S × E))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let X := fun x : Space n => supportParam Y (q₀+J x)
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (V : Space n → S × E), ContDiffOn ℝ ∞ V W → tsupport V ⊆ K →
      ∀ (ν : ℝ → Space n → (S × E) →L[ℝ] ℝ) (ξ : ℝ → Space n → S × E),
      (∀ t x, x ∈ W → (ν t x).comp (fderiv ℝ (fun y => X y+t • V y) x) = 0) →
      (∀ t x, x ∈ W → ν t x (ξ t x) = 1) →
      (∀ x ∈ K, ν 0 x = supportConormal H (q₀+J x)) →
      (∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L.symm ((0 : Space n),1))) (0,x)) →
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity b
        (fun y => X y+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let X := fun x : Space n => supportParam Y (q₀+J x)
  let U := {x : Space n | (q₀+J x).1 ∈ B}
  obtain ⟨hU,hLX,him,hiLX⟩ := affineEpigraph_flat_parametrization hΩ hcv hu hp a L hB hK hzero q₀ d hd J hi hJ
  have he : (fun x => L.symm ((a+L (X x))-a)) = X := by funext x; simp
  have hX : ContDiffOn ℝ ∞ X U := by
    rw [← he]
    exact L.symm.contDiff.comp_contDiffOn (hLX.sub contDiffOn_const)
  have hiX : Function.Injective (fderiv ℝ X x₀) := by
    have hdX : fderiv ℝ (fun x => a+L (X x)) x₀ = L.toContinuousLinearMap.comp (fderiv ℝ X x₀) :=
      ((L.hasFDerivAt.comp x₀ ((hX.contDiffAt (hU.mem_nhds hx₀)).differentiableAt (by simp)).hasFDerivAt).const_add a).fderiv
    have hh := hiLX x₀ hx₀
    change Function.Injective (fderiv ℝ (fun x => a+L (X x)) x₀) at hh
    rw [hdX] at hh
    exact Function.Injective.of_comp hh
  obtain ⟨W,hW,hxW,hWU,hstat⟩ := affineMaximal_ambient_immersed_local_stationary hU hΩ hX hu hp hm a L him hx₀ hiX
  change ∃ W, _
  refine ⟨W,hW,hxW,hWU,?_⟩
  intro K hKc hKW V hV hVK ν ξ hν hξ heν hcν
  have hpos (x : Space n) (hx : x ∈ K) : 0 < ν 0 x (L.symm ((0 : Space n),1)) := by
    rw [heν x hx]
    apply affineEpigraph_supportConormal_inward hΩ hcv hu hp a L hB hK hzero (hWU (hKW hx))
    intro hz
    have hh : inner ℝ (q₀+J x).2 d = 1 := by simp [inner_add_left,hd,hJ]
    simp [hz] at hh
  have hh := hstat K hKc hKW V hV hVK ν ξ hν hξ hpos hcν
  let b₀ := (graphAmbientBasis n).map L.symm.toLinearEquiv
  let c := Real.rpow |b.det b₀| ((n : ℝ)/((n : ℝ)+2))
  have heq : (fun t : ℝ => ∫ x in K, parametricAreaDensity b (fun y => X y+t • V y) (ν t x) (ξ t x) x) =
      (fun t => c * ∫ x in K, parametricAreaDensity b₀ (fun y => X y+t • V y) (ν t x) (ξ t x) x) := by
    funext t
    simp only [parametricAreaDensity_change_basis b₀ b,← integral_const_mul]
    rfl
  rw [heq]
  convert! hh.const_mul c using 1
  all_goals try with_reducible_and_instances rfl
  simp [mul_zero]

end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary_oai.{u_1, u_2} := @OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary_oai.{u_1, u_2}
