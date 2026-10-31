-- Prove2me | solution 1 for OAI.AffineBernstein.normalized_log_variance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:19:50.471025+00:00
-- url     : https://prove2.me/submissions/cb4aa528-ee28-4cf8-b523-e0834597fc5b

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_normalized_balanced_det_bounds

section
-- module Solutions.OAIQ22_AB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

/-- Exchanging two independently replaced rows reverses the determinant. -/
theorem det_updateRow_pair_swap (A : Matrix ι ι ℝ) {i l : ι} (hil : i ≠ l)
    (v w : ι → ℝ) :
    ((A.updateRow i v).updateRow l w).det =
      -((A.updateRow i w).updateRow l v).det := by
  have hm : ((A.updateRow i w).updateRow l v) ∘ Equiv.swap i l =
      (A.updateRow i v).updateRow l w := by
    funext k j
    change ((A.updateRow i w).updateRow l v) (Equiv.swap i l k) j = _
    by_cases hki : k = i
    · subst k
      simp [hil]
    by_cases hkl : k = l
    · subst k
      simp [hil]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkl, hki, hkl]
  have hs := (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).map_swap
    (fun k => ((A.updateRow i w).updateRow l v) k) hil
  rw [show (fun k => ((A.updateRow i w).updateRow l v) k) ∘ Equiv.swap i l =
      (fun k => ((A.updateRow i v).updateRow l w) k) from hm] at hs
  exact hs

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

/-- Symmetric coefficients contract to zero with an alternating pair of rows. -/
theorem sum_two_rows_eq_zero (A : Matrix ι ι ℝ) {i l : ι} (hil : i ≠ l)
    (T : ι → ι → ℝ) (hT : ∀ j m, T j m = T m j) :
    (∑ j, ∑ m, T j m *
      ((A.updateRow i (Pi.single j 1)).updateRow l (Pi.single m 1)).det) = 0 := by
  let S := ∑ j, ∑ m, T j m *
      ((A.updateRow i (Pi.single j 1)).updateRow l (Pi.single m 1)).det
  have hs : S = -S := by
    dsimp [S]
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro m hm
    rw [hT m j]
    exact (congrArg (fun r : ℝ => T j m * r)
      (det_updateRow_pair_swap A hil (Pi.single m 1) (Pi.single j 1))).trans
      (mul_neg _ _)
  change S = 0
  linarith

/-- The algebraic cancellation underlying the Piola identity. -/
theorem piola_cancel (A : Matrix ι ι ℝ) (i : ι) (T : ι → ι → ι → ℝ)
    (hT : ∀ l j m, T l j m = T l m j) :
    (∑ j, ∑ l, ((A.updateRow i (Pi.single j 1)).updateRow l
      (if l = i then 0 else T l j)).det) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hli : l = i
  · subst l
    apply Finset.sum_eq_zero
    intro j hj
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro m
    simp
  · simp only [ite_eq_right hli]
    calc
      _ = ∑ j, ∑ m, T l j m *
          ((A.updateRow i (Pi.single j 1)).updateRow l (Pi.single m 1)).det :=
        Finset.sum_congr rfl fun j _ => det_updateRow_sum _ l _
      _ = 0 := sum_two_rows_eq_zero A (Ne.symm hli) (T l) (hT l)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PiolaDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiate a cofactor by differentiating each of its unfrozen rows. -/
theorem fderiv_adjugate_jacobianRows (F : ι → E → ℝ) (e : ι → E) (x : E)
    (hF : ∀ l, ContDiffAt ℝ 2 (F l) x) (i j : ι) (v : E) :
    fderiv ℝ (fun y => (jacobianRows F e y).adjugate j i) x v =
      ∑ l, (((jacobianRows F e x).updateRow i (Pi.single j 1)).updateRow l
        (if l = i then 0 else fun m => fderiv ℝ (fderiv ℝ (F l)) x v (e m))).det := by
  let M : E → (ι → ι → ℝ) := fun y =>
    Function.update (fun l m => fderiv ℝ (F l) y (e m)) i (Pi.single j 1)
  let D : E →L[ℝ] (ι → ι → ℝ) := ContinuousLinearMap.pi fun l =>
    if l = i then 0 else ContinuousLinearMap.pi fun m =>
      (fderiv ℝ (fderiv ℝ (F l)) x).flip (e m)
  have hD : HasFDerivAt M D x := by
    dsimp [M, D]
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases hli : l = i
    · subst l
      simp only [Function.update_self, ite_true]
      exact hasFDerivAt_const (Pi.single j 1) x
    · simp only [Function.update_of_ne hli, ite_eq_right hli]
      apply hasFDerivAt_pi.mpr
      intro m
      have hf := ((hF l).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
      simpa using hf.hasFDerivAt.clm_apply (hasFDerivAt_const (e m) x)
  have hAdj : (fun y => (jacobianRows F e y).adjugate j i) =
      continuousDetRows ∘ M := by
    funext y
    rw [Matrix.adjugate_apply]
    rfl
  have hc := (continuousDetRows.hasFDerivAt (M x)).comp x hD
  rw [hAdj, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hli : l = i
  · subst l
    simp only [D, ContinuousLinearMap.pi_apply, ite_true, zero_apply]
    rfl
  · simp only [D, ContinuousLinearMap.pi_apply, ite_eq_right hli]
    rfl

/-- Piola's identity in fixed directions; it uses only equality of mixed partials. -/
theorem piola_identity (F : ι → E → ℝ) (e : ι → E) (x : E)
    (hF : ∀ l, ContDiffAt ℝ 2 (F l) x) (i : ι) :
    (∑ j, fderiv ℝ (fun y => (jacobianRows F e y).adjugate j i) x (e j)) = 0 := by
  simp_rw [fderiv_adjugate_jacobianRows F e x hF]
  apply piola_cancel
  intro l j m
  exact (hF l).isSymmSndFDerivAt (by norm_num) (e j) (e m)

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

/-- Smoothness through order three suffices for the cofactor cancellation. -/
theorem adjugate_hessian_divergence {n : ℕ} (u : Space n → ℝ) (x : Space n)
    (hu : ContDiffAt ℝ 3 u x) (i : Fin n) :
    (∑ j, fderiv ℝ (fun y => (hessian u y).adjugate i j) x
      (coordinateVector n j)) = 0 := by
  let F : Fin n → Space n → ℝ := fun l y => fderiv ℝ u y (coordinateVector n l)
  have hF (l : Fin n) : ContDiffAt ℝ 2 (F l) x :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hJ (y : Space n) : jacobianRows F (coordinateVector n) y =
      (hessian u y).transpose := rfl
  simpa only [hJ, ← Matrix.adjugate_transpose, Matrix.transpose_apply] using
    piola_identity F (coordinateVector n) x hF i

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

/-- Both divergences of the actual coefficient matrix vanish on the original domain. -/
theorem cofactorHessian_divergence {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    (u : Space n → ℝ) (hu : ContDiffOn ℝ 3 u Ω)
    (hpos : ∀ x ∈ Ω, (hessian u x).PosDef) (x : Space n) (hx : x ∈ Ω) (i : Fin n) :
    (∑ j, fderiv ℝ (fun y => cofactorHessian u y i j) x (coordinateVector n j)) = 0 ∧
    (∑ j, fderiv ℝ (fun y => cofactorHessian u y j i) x (coordinateVector n j)) = 0 := by
  have hrow : (∑ j, fderiv ℝ (fun y => cofactorHessian u y i j) x
      (coordinateVector n j)) = 0 := by
    have he (j : Fin n) : (fun y => cofactorHessian u y i j) =ᶠ[nhds x]
        (fun y => (hessian u y).adjugate i j) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      rw [cofactorHessian_eq_adjugate u y (ne_of_gt (hpos y hy).det_pos)]
    simp_rw [(he _).fderiv_eq]
    exact adjugate_hessian_divergence u x (hu.contDiffAt (hΩ.mem_nhds hx)) i
  refine ⟨hrow, ?_⟩
  have he (j : Fin n) : (fun y => cofactorHessian u y j i) =ᶠ[nhds x]
      (fun y => cofactorHessian u y i j) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (cofactorHessian_isSymm u y (hpos y hy)).apply i j
  simpa only [(he _).fderiv_eq] using hrow

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

/-- Polynomial cofactor entries are smooth even before invertibility is used. -/
theorem contDiffAt_adjugate_hessian_entry {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => (hessian u y).adjugate i j) x := by
  have hM : ContDiffAt ℝ ∞
      (fun (y : Space n) (l m : Fin n) => if l = j then (Pi.single i (1 : ℝ) : Fin n → ℝ) m else hessian u y l m) x := by
    apply contDiffAt_pi.mpr
    intro l
    apply contDiffAt_pi.mpr
    intro m
    by_cases hlj : l = j
    · simp only [ite_eq_left hlj]
      exact contDiffAt_const
    · simp only [ite_eq_right hlj]
      exact contDiffAt_hessian_entry hu l m
  have hc := continuousDetRows.contDiff.contDiffAt.comp x hM
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  rw [Matrix.adjugate_apply]
  change ((hessian u y).updateRow j (Pi.single i 1)).det =
    (Matrix.of fun l m => if l = j then Pi.single i 1 m else hessian u y l m).det
  congr 1
  ext l m
  exact Matrix.updateRow_apply

/-- Smoothness of U on its actual open domain, with no extension hypothesis. -/
theorem contDiffAt_cofactorHessian_entry {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) {x : Space n} (hx : x ∈ Ω) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun y => cofactorHessian u y i j) x := by
  apply (contDiffAt_adjugate_hessian_entry (hu.contDiffAt (hΩ.mem_nhds hx)) i j).congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hx] with y hy
  rw [cofactorHessian_eq_adjugate u y (ne_of_gt (hpos y hy).det_pos)]

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

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Integrability uses continuity only on a compact set containing the support. -/
theorem integrable_of_support_subset_compact {f : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hs : Function.support f ⊆ K) (hf : ContinuousOn f K) :
    Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset hs).mp
    (ContinuousOn.integrableOn_compact hK hf)

/-- Compact support of the test function removes any global regularity requirement
on the coefficient. This is the integration-by-parts form used on the original Ω. -/
theorem integral_mul_fderiv_compact (f g : E → ℝ) (v : E)
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ 1 f x)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ x, f x * fderiv ℝ g x v ∂μ) =
      -(∫ x, fderiv ℝ f x v * g x ∂μ) := by
  have hf0 : ContinuousOn f (tsupport g) := fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt
  have hf1 : ContinuousOn (fun x => fderiv ℝ f x v) (tsupport g) := fun x hx =>
    (((hf x hx).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      continuousAt_const).continuousWithinAt
  have hg1 : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_of_support_subset_compact hgc.isCompact
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport g))
      (hf1.mul hg.continuous.continuousOn)
  · exact integrable_of_support_subset_compact hgc.isCompact
      ((Function.support_mul_subset_right _ _).trans
        ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v)))
      (hf0.mul hg1.continuousOn)
  · exact integrable_of_support_subset_compact hgc.isCompact
      ((Function.support_mul_subset_right _ _).trans (subset_tsupport g))
      (hf0.mul hg.continuous.continuousOn)
  · intro x hx
    exact (hf x hx).differentiableAt (by norm_num)
  · intro x hx
    exact hg.differentiable (by norm_num) x

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
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixShiftBound
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma adjugate_eq_det_smul_transpose' {Q : Matrix ι ι ℝ} (hQ : Q * Qᵀ = 1) :
    Q.adjugate = Q.det • Qᵀ := by
  calc
    Q.adjugate = Q.adjugate * (Q * Qᵀ) := by rw [hQ, Matrix.mul_one]
    _ = (Q.adjugate * Q) * Qᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = Q.det • Qᵀ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

private lemma adjugate_conjugate_orthogonal' {Q : Matrix ι ι ℝ}
    (hQ : Q * Qᵀ = 1) (hQt : Qᵀ * Q = 1) (A : Matrix ι ι ℝ) :
    (Qᵀ * A * Q).adjugate = Qᵀ * A.adjugate * Q := by
  have hd : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using hh
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    adjugate_eq_det_smul_transpose' hQ,
    adjugate_eq_det_smul_transpose' (Q := Qᵀ) (by simpa using hQt),
    Matrix.transpose_transpose, Matrix.det_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, one_smul, Matrix.mul_assoc]

/- A coarse uniform bound for the sum of all principal cofactors by the
Jacobian of the identity-shifted positive semidefinite map. -/
lemma trace_adjugate_le_card_mul_det_add_one {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) :
    A.adjugate.trace ≤ (Fintype.card ι : ℝ) * (A + 1).det := by
  let Q : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  let d : ι → ℝ := hA.1.eigenvalues
  have hQ : Q * Qᵀ = 1 := by
    simpa only [Q, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (Unitary.coe_mul_star_self hA.1.eigenvectorUnitary)
  have hQt : Qᵀ * Q = 1 := by
    simpa only [Q, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (Unitary.coe_star_mul_self hA.1.eigenvectorUnitary)
  have hspec : A = Q * Matrix.diagonal d * Qᵀ := by
    simpa [Q,d,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.1.spectral_theorem
  have hdetQ : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using hh
  have htrace : A.adjugate.trace = ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
    rw [hspec]
    have had := adjugate_conjugate_orthogonal' (Q := Qᵀ) (by simpa using hQt) (by simpa using hQ) (Matrix.diagonal d)
    simp only [Matrix.transpose_transpose] at had
    rw [had]
    rw [Matrix.trace_mul_cycle,hQt,Matrix.one_mul,Matrix.adjugate_diagonal,Matrix.trace_diagonal]
  have hdet : (A + 1).det = ∏ i, (d i + 1) := by
    have hsum : A + 1 = Q * Matrix.diagonal (fun i => d i + 1) * Qᵀ := by
      have hdadd : Matrix.diagonal (fun i => d i + 1) = Matrix.diagonal d + 1 := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.diagonal,hij]
      rw [hdadd,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,← hspec,hQ]
    rw [hsum,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal]
    calc
      Q.det * (∏ i, (d i + 1)) * Q.det = (Q.det * Q.det) * ∏ i, (d i + 1) := by ring
      _ = _ := by rw [hdetQ,one_mul]
  rw [htrace,hdet]
  calc
    (∑ i, ∏ j ∈ Finset.univ.erase i, d j) ≤ ∑ _i : ι, ∏ j, (d j + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (∏ j ∈ Finset.univ.erase i, d j) ≤ ∏ j ∈ Finset.univ.erase i, (d j + 1) := by
          exact Finset.prod_le_prod (fun index _ => hA.eigenvalues_nonneg index)
            (fun _ _ => by linarith)
        _ ≤ (d i + 1) * ∏ j ∈ Finset.univ.erase i, (d j + 1) := by
          have hp := Finset.prod_nonneg (s := Finset.univ.erase i)
            (fun j _ => add_nonneg (hA.eigenvalues_nonneg j) zero_le_one)
          nlinarith [hA.eigenvalues_nonneg i]
        _ = ∏ j, (d j + 1) := Finset.mul_prod_erase Finset.univ (fun j => d j + 1) (Finset.mem_univ i)
    _ = _ := by simp

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixShiftDet
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma det_le_det_add_one {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : A.det ≤ (A+1).det := by
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
  rw [hsum,hspec,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,
    Matrix.det_transpose,Matrix.det_diagonal,Matrix.det_diagonal]
  have he (a : ℝ) : Q.det * a * Q.det = a := by
    calc
      _ = (Q.det*Q.det)*a := by ring
      _ = a := by rw [hdetQ,one_mul]
  rw [he,he]
  exact Finset.prod_le_prod (fun index _ => hA.eigenvalues_nonneg index)
    (fun _ _ => by linarith)

lemma det_mul_one_add_trace_inv_le {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A.det * (1 + A⁻¹.trace) ≤ ((Fintype.card ι:ℝ)+1)*(A+1).det := by
  have hne := hA.det_pos.ne'
  have he : A.det * A⁻¹.trace = A.adjugate.trace := by
    rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.trace_smul,
      smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hne,one_mul]
  rw [mul_add,mul_one,he]
  have h1 := det_le_det_add_one hA.posSemidef
  have h2 := trace_adjugate_le_card_mul_det_add_one hA.posSemidef
  linarith

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
theorem lintegral_hessian_minors_le_ball {Ω : Set (Space n)}
    (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ∀ x ∈ Ω, ContDiffAt ℝ ∞ u x)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {D : Set (Space n)} (hD : MeasurableSet D) (hDO : D ⊆ Ω)
    {G R : ℝ} (hG : ∀ x ∈ D, ‖gradient u x‖ ≤ G)
    (hR : ∀ x ∈ D, ‖x‖ ≤ R) :
    (∫⁻ x in D, ENNReal.ofReal ((hessian u x).det * (1 + (hessian u x)⁻¹.trace))) ≤
      ((n:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space n) (G+R)) := by
  let F := fun x => gradient u x + x
  have hd (x : Space n) (hx : x ∈ D) : DifferentiableAt ℝ F x :=
    ((contDiffAt_gradient (hu x (hDO hx))).differentiableAt (by simp)).add differentiableAt_id
  have hi : Set.InjOn F D :=
    (shiftedGradient_injOn_of_hessian_posSemidef hcv hu (fun x hx => (hp x hx).posSemidef)).mono hDO
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD
    (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) hi (fun _ : Space n => (1:ℝ≥0∞))
  simp only [lintegral_const,Measure.restrict_apply_univ,mul_one,one_mul] at hj
  have himage : F '' D ⊆ Metric.closedBall 0 (G+R) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add (hG x hx) (hR x hx))
  calc
    _ ≤ ∫⁻ x in D, ((n:ℝ≥0∞)+1)*ENNReal.ofReal |(fderiv ℝ F x).det| := by
      apply setLIntegral_mono' hD
      intro x hx
      have hp' := hp x (hDO hx)
      have hdpos := (hp'.posSemidef.add Matrix.PosSemidef.one).det_nonneg
      rw [show F = (fun x => gradient u x+x) from rfl,
        det_fderiv_shiftedGradient (hu x (hDO hx)),abs_of_nonneg hdpos]
      have hc : ((n:ℝ≥0∞)+1) = ENNReal.ofReal ((n:ℝ)+1) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp
      rw [hc,← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Fintype.card_fin] using det_mul_one_add_trace_inv_le hp'
    _ = ((n:ℝ≥0∞)+1) * ∫⁻ x in D, ENNReal.ofReal |(fderiv ℝ F x).det| := by
      rw [lintegral_const_mul']
      simp
    _ ≤ _ := by
      rw [← hj]
      exact mul_le_mul_right (measure_mono (μ := volume) himage) _

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

lemma inverseMatrixPair_symm {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x y : ι → ℝ) :
    inverseMatrixPair A x y = inverseMatrixPair A y x := by
  have hi : A⁻¹.IsSymm := by rw [Matrix.IsSymm,Matrix.transpose_nonsing_inv,hA.eq]
  unfold inverseMatrixPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.transpose_apply A⁻¹ i j,hi.eq]
  ring

lemma inverseMatrixPair_add_left (A : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    inverseMatrixPair A (fun i => x i+y i) z = inverseMatrixPair A x z+inverseMatrixPair A y z := by
  simp only [inverseMatrixPair,mul_add,add_mul,Finset.sum_add_distrib]

lemma inverseMatrixPair_add_right (A : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    inverseMatrixPair A x (fun i => y i+z i) = inverseMatrixPair A x y+inverseMatrixPair A x z := by
  simp only [inverseMatrixPair,mul_add,Finset.sum_add_distrib]

lemma inverseMatrixPair_smul_left (A : Matrix ι ι ℝ) (t : ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A (fun i => t*x i) y = t*inverseMatrixPair A x y := by
  simp only [inverseMatrixPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma inverseMatrixPair_smul_right (A : Matrix ι ι ℝ) (t : ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A x (fun i => t*y i) = t*inverseMatrixPair A x y := by
  simp only [inverseMatrixPair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/- Cauchy--Schwarz for a positive definite inverse matrix, including zero vectors. -/
lemma inverseMatrixPair_cauchy {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) :
    inverseMatrixPair A x y^2 ≤ inverseMatrixPair A x x*inverseMatrixPair A y y := by
  have hs : A.IsSymm := by simpa only [Matrix.isHermitian_iff_isSymm] using hA.isHermitian
  have hq (t : ℝ) : 0 ≤ inverseMatrixPair A y y*(t*t)+
      (2*inverseMatrixPair A x y)*t+inverseMatrixPair A x x := by
    have hh := inverseMatrixPair_self_nonneg hA (fun i => x i+t*y i)
    rw [inverseMatrixPair_add_left,inverseMatrixPair_add_right,inverseMatrixPair_add_right,
      inverseMatrixPair_smul_right,inverseMatrixPair_smul_left,inverseMatrixPair_smul_left,
      inverseMatrixPair_smul_right,inverseMatrixPair_symm hs y x] at hh
    nlinarith [hh]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

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
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualGlobalCoercive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

theorem paired_cauchy_coercive {P D I a b c : ℝ}
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hI : I ^ 2 ≤ P * D)
    (ha : 0 ≤ a) (hb : 0 < b) (hdet : c ^ 2 ≤ 4 * a * b) :
    0 ≤ a * P + c * I + b * D := by
  by_cases hP0 : P = 0
  · have hI0 : I = 0 := by nlinarith [sq_nonneg I]
    simp only [hI0, mul_zero, add_zero]
    exact add_nonneg (mul_nonneg ha hP) (mul_nonneg hb.le hD)
  have hPp : 0 < P := lt_of_le_of_ne hP (Ne.symm hP0)
  have h1 := mul_nonneg (show 0 ≤ 4 * a * b - c ^ 2 by linarith) (sq_nonneg P)
  have h2 := mul_nonneg (show 0 ≤ P * D - I ^ 2 by linarith) (show 0 ≤ 4 * b ^ 2 by positivity)
  have h3 := sq_nonneg (c * P + 2 * b * I)
  have htot : 0 ≤ 4 * b * P * (a * P + c * I + b * D) := by nlinarith
  exact nonneg_of_mul_nonneg_right htot (by positivity)

/- A fixed explicit lower coercivity constant for the exact source range.
In particular it is independent of the number of directions k >= 2. -/
theorem cauchy_young {P Q J a ε : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hJ : J ^ 2 ≤ P * Q) (hε : 0 < ε) :
    a * J ≤ ε * P + (a ^ 2 / (4 * ε)) * Q := by
  have hdet : (-a) ^ 2 ≤ 4 * (a ^ 2 / (4 * ε)) * ε := by
    field_simp
    nlinarith
  have h := paired_cauchy_coercive hQ hP (by nlinarith [hJ])
    (show 0 ≤ a ^ 2 / (4 * ε) by positivity) hε hdet
  nlinarith

/- The exact coefficients on the right of the source coercive identity. -/

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

lemma inverseHessianPair_self_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (f : Space n → ℝ) : 0 ≤ inverseHessianPair u f f x := by
  have hh := inverseMatrixPair_self_nonneg hp (fun i => dirDeriv (coordinateVector n i) f x)
  unfold inverseHessianPair inverseMatrixPair at *
  rw [Finset.sum_comm] at hh
  simpa only [mul_right_comm] using hh

end LogBarrierCalculus


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogCaccioppoli
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

section LogCaccioppoli

lemma contDiff_cofactorHessian_entry_global {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) (i j : Fin n) :
    ContDiff ℝ ∞ (fun x => cofactorHessian u x i j) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_cofactorHessian_entry isOpen_univ hu.contDiffOn
    (fun y _ => hp y) (mem_univ x) i j

lemma integral_flux_compact {n : ℕ} (F : Fin n → Space n → ℝ)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) {g : Space n → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ x, ∑ j, F j x * dirDeriv (coordinateVector n j) g x) =
      -(∫ x, (∑ j, dirDeriv (coordinateVector n j) (F j) x) * g x) := by
  have hi (j : Fin n) : Integrable (fun x => F j x * dirDeriv (coordinateVector n j) g x) :=
    ((hF j).continuous.mul (contDiff_dirDeriv hg _).continuous).integrable_of_hasCompactSupport
      ((hgc.fderiv_apply ℝ _).mul_left)
  have hj (j : Fin n) : Integrable (fun x => dirDeriv (coordinateVector n j) (F j) x * g x) :=
    ((contDiff_dirDeriv (hF j) _).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left)
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => hj j), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_mul_fderiv_compact _ g _ (fun _ _ => (hF j).contDiffAt.of_le (by norm_num))
    (hg.of_le (by norm_num)) hgc

lemma inverseHessian_ibp {n : ℕ} {u f g : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ x, (hessian u x).det * inverseHessianPair u f g x) =
      -(∫ x, (hessian u x).det * inverseHessianTrace u f x * g x) := by
  let F : Fin n → Space n → ℝ := fun j x => ∑ i,
    cofactorHessian u x i j * dirDeriv (coordinateVector n i) f x
  have hF : ∀ j, ContDiff ℝ ∞ (F j) := fun j => ContDiff.sum fun i _ =>
    (contDiff_cofactorHessian_entry_global hu hp i j).mul (contDiff_dirDeriv hf _)
  have hleft (x : Space n) : (∑ j, F j x * dirDeriv (coordinateVector n j) g x) =
      (hessian u x).det * inverseHessianPair u f g x := by
    simp only [F,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [inverseHessianPair,cofactorHessian,Matrix.smul_apply,smul_eq_mul,
      Finset.mul_sum,mul_assoc]
  have hright (x : Space n) : (∑ j, dirDeriv (coordinateVector n j) (F j) x) =
      (hessian u x).det * inverseHessianTrace u f x := by
    have hd (i j : Fin n) :
        dirDeriv (coordinateVector n j) (fun y => cofactorHessian u y i j *
          dirDeriv (coordinateVector n i) f y) x =
        dirDeriv (coordinateVector n j) (fun y => cofactorHessian u y i j) x *
          dirDeriv (coordinateVector n i) f x +
        cofactorHessian u x i j * hessian f x j i := by
      exact dirDeriv_mul ((contDiff_cofactorHessian_entry_global hu hp i j).differentiable (by simp) x)
        ((contDiff_dirDeriv hf _).differentiable (by simp) x) (coordinateVector n j)
    simp only [F,dirDeriv_sum (fun i y => cofactorHessian u y i _ *
      dirDeriv (coordinateVector n i) f y) (fun i =>
        ((contDiff_cofactorHessian_entry_global hu hp i _).mul (contDiff_dirDeriv hf _)).differentiable (by simp) x),
      hd, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun j i => dirDeriv (coordinateVector n j)
      (fun y => cofactorHessian u y i j) x * dirDeriv (coordinateVector n i) f x)]
    have hzero : (∑ i, ∑ j, dirDeriv (coordinateVector n j)
        (fun y => cofactorHessian u y i j) x * dirDeriv (coordinateVector n i) f x) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [← Finset.sum_mul]
      have hh := (cofactorHessian_divergence isOpen_univ u (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffOn
        (fun y _ => hp y) x (mem_univ x) i).1
      change (∑ j, dirDeriv (coordinateVector n j) (fun y => cofactorHessian u y i j) x) = 0 at hh
      rw [hh,zero_mul]
    rw [hzero,zero_add,Finset.sum_comm]
    have hs : (hessian f x).IsSymm := hessian_isSymm hf.contDiffAt
    simp only [hs.apply,cofactorHessian,Matrix.smul_apply,smul_eq_mul,inverseHessianTrace,
      Finset.mul_sum,mul_assoc]
  simpa only [hleft,hright] using integral_flux_compact F hF hg hgc

lemma contDiff_inverseHessianTrace_global {n : ℕ} {u f : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (inverseHessianTrace u f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (contDiffAt_inverse_matrix_entry_param
      (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu.contDiffAt i j)
      (ne_of_gt (hp x).det_pos) i j).mul
    (contDiffAt_hessian_entry hf.contDiffAt i j)

lemma contDiff_inverseHessianPair_global {n : ℕ} {u f g : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (inverseHessianPair u f g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((contDiffAt_inverse_matrix_entry_param
      (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu.contDiffAt i j)
      (ne_of_gt (hp x).det_pos) i j).mul
    (contDiffAt_dirDeriv hf.contDiffAt _)).mul (contDiffAt_dirDeriv hg.contDiffAt _)

lemma inverseHessianPair_cauchy {n : ℕ} {u f g : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) :
    inverseHessianPair u f g x ^ 2 ≤ inverseHessianPair u f f x * inverseHessianPair u g g x := by
  have he (v w : Space n → ℝ) : inverseHessianPair u v w x =
      inverseMatrixPair (hessian u x) (fun i => dirDeriv (coordinateVector n i) w x)
        (fun i => dirDeriv (coordinateVector n i) v x) := by
    unfold inverseHessianPair inverseMatrixPair
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [he]
  simpa only [mul_comm] using inverseMatrixPair_cauchy hp
    (fun i => dirDeriv (coordinateVector n i) g x) (fun i => dirDeriv (coordinateVector n i) f x)


lemma inverseHessianTrace_log_supersolution {n : ℕ} {u s : Space n → ℝ}
    (hs : ContDiff ℝ ∞ s) (hpos : ∀ x, 0 < s x)
    (hL : ∀ x, inverseHessianTrace u s x ≤ 0) (x : Space n) :
    inverseHessianTrace u (fun y => Real.log (s y)) x +
      inverseHessianPair u (fun y => Real.log (s y)) (fun y => Real.log (s y)) x ≤ 0 := by
  have he : inverseHessianTrace u s x = s x *
      (inverseHessianTrace u (fun y => Real.log (s y)) x +
        inverseHessianPair u (fun y => Real.log (s y)) (fun y => Real.log (s y)) x) := by
    simp only [inverseHessianTrace,inverseHessianPair,mul_add,Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hh := log_second_identity isOpen_univ hs.contDiffOn (fun y _ => hpos y)
      (mem_univ x) (coordinateVector n i) (coordinateVector n j)
    change hessian s x i j = s x * (hessian (fun y => Real.log (s y)) x i j + _) at hh
    rw [hh]
    ring
  have ht := hL x
  rw [he] at ht
  exact nonpos_of_mul_nonpos_right ht (hpos x)

/-- Caccioppoli for the logarithm of a strictly positive supersolution of the
actual cofactor-divergence operator. The coefficients are not assumed uniformly
elliptic, and no Harnack estimate enters this proof. -/
theorem linearizedMA_log_caccioppoli {n : ℕ} {u s η : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hs : ContDiff ℝ ∞ s) (hpos : ∀ x, 0 < s x)
    (hL : ∀ x, inverseHessianTrace u s x ≤ 0)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    (∫ x, (hessian u x).det * (η x)^2 *
      inverseHessianPair u (fun y => Real.log (s y)) (fun y => Real.log (s y)) x) ≤
      4 * ∫ x, (hessian u x).det * inverseHessianPair u η η x := by
  let g := fun y => Real.log (s y)
  have hg : ContDiff ℝ ∞ g := hs.log (fun x => ne_of_gt (hpos x))
  have hdt : Continuous (fun x => (hessian u x).det) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (contDiffAt_det_hessian hu.contDiffAt).continuousAt
  have hQ (f k : Space n → ℝ) (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) :
      Continuous (inverseHessianPair u f k) := (contDiff_inverseHessianPair_global hu hp hf hk).continuous
  have hη2c : HasCompactSupport (fun x => (η x)^2) := by
    apply HasCompactSupport.of_support_subset_isCompact hηc.isCompact
    intro x hx
    exact subset_tsupport η (fun h => hx (by simp only [h,zero_pow (by norm_num : 2 ≠ 0)]))
  have hE : Integrable (fun x => (hessian u x).det * (η x)^2 * inverseHessianPair u g g x) :=
    ((hdt.mul (hη.continuous.pow 2)).mul (hQ g g hg hg)).integrable_of_hasCompactSupport
      (hη2c.mul_left.mul_right)
  have hcut : HasCompactSupport (inverseHessianPair u η η) := by
    apply HasCompactSupport.of_support_subset_isCompact hηc.isCompact
    intro x hx
    by_contra hxi
    apply hx
    have hd : ∀ i, dirDeriv (coordinateVector n i) η x = 0 := fun i => by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hh => hxi (tsupport_fderiv_apply_subset ℝ (coordinateVector n i) hh)
    simp [inverseHessianPair,hd]
  have hC : Integrable (fun x => (hessian u x).det * inverseHessianPair u η η x) :=
    (hdt.mul (hQ η η hη hη)).integrable_of_hasCompactSupport hcut.mul_left
  have hT : Integrable (fun x => (hessian u x).det * inverseHessianTrace u g x * (η x)^2) :=
    ((hdt.mul (contDiff_inverseHessianTrace_global hu hp hg).continuous).mul
      (hη.continuous.pow 2)).integrable_of_hasCompactSupport (hη2c.mul_left)
  have hX : Integrable (fun x => 2*(hessian u x).det*η x*inverseHessianPair u g η x) :=
    (((continuous_const.mul hdt).mul hη.continuous).mul (hQ g η hg hη)).integrable_of_hasCompactSupport
      (hηc.mul_left.mul_right)
  have hpair (x : Space n) : inverseHessianPair u g (fun y => (η y)^2) x =
      2*η x*inverseHessianPair u g η x := by
    have hd (j : Fin n) : dirDeriv (coordinateVector n j) (fun y => (η y)^2) x =
        2*η x*dirDeriv (coordinateVector n j) η x := by
      unfold dirDeriv
      rw [((hη.differentiable (by simp) x).hasFDerivAt.pow 2).fderiv]
      norm_num [smul_apply,smul_eq_mul]
    simp only [inverseHessianPair,hd,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hIBP := inverseHessian_ibp hu hp hg (hη.pow 2) hη2c
  simp only [hpair] at hIBP
  have hIBP' : (∫ x, 2*(hessian u x).det*η x*inverseHessianPair u g η x) =
      -(∫ x, (hessian u x).det* inverseHessianTrace u g x * (η x)^2) := by
    convert hIBP using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    ring
  have hbound := integral_mono hE hT.neg (fun x => by
    have hlog := inverseHessianTrace_log_supersolution hs hpos hL x
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hp x).det_pos.le (sq_nonneg (η x))) hlog
    change (hessian u x).det*(η x)^2*inverseHessianPair u g g x ≤
      -((hessian u x).det*inverseHessianTrace u g x*(η x)^2)
    change inverseHessianTrace u g x + inverseHessianPair u g g x ≤ 0 at hlog
    nlinarith)
  simp only [Pi.neg_apply] at hbound
  rw [integral_neg, ← hIBP'] at hbound
  have hyoung (x : Space n) : 2*(hessian u x).det*η x*inverseHessianPair u g η x ≤
      (1/2:ℝ)*((hessian u x).det*(η x)^2*inverseHessianPair u g g x) +
        2*((hessian u x).det*inverseHessianPair u η η x) := by
    have hh := cauchy_young (inverseHessianPair_self_nonneg (hp x) η)
      (inverseHessianPair_self_nonneg (hp x) g)
      (show inverseHessianPair u g η x ^ 2 ≤
        inverseHessianPair u η η x * inverseHessianPair u g g x by
        simpa only [mul_comm] using inverseHessianPair_cauchy (f := g) (g := η) (hp x))
      (a := 2*η x) (show (0:ℝ)<2 by norm_num)
    have hh' := mul_le_mul_of_nonneg_left hh (hp x).det_pos.le
    nlinarith
  have hy := integral_mono hX ((hE.const_mul (1/2)).add (hC.const_mul 2)) hyoung
  simp only [Pi.add_apply] at hy
  rw [integral_add (hE.const_mul _) (hC.const_mul _),integral_const_mul,integral_const_mul] at hy
  nlinarith

end LogCaccioppoli



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

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogVariance
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

section LogVariance

lemma inverseHessianPair_le_trace_gradientSquared {n : ℕ} {u f : Space n → ℝ}
    {x : Space n} (hp : (hessian u x).PosDef) :
    inverseHessianPair u f f x ≤ (hessian u x)⁻¹.trace * gradientSquared f x := by
  have hh := posSemidef_quadratic_le_trace_mul_sq hp.inv.posSemidef
    (fun i => dirDeriv (coordinateVector n i) f x)
  change _ ≤ _ * gradientSquared f x at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold inverseHessianPair Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inverseHessianPair_eq_zero_outside_tsupport {n : ℕ} (u f g : Space n → ℝ)
    {x : Space n} (hx : x ∉ tsupport g) : inverseHessianPair u f g x = 0 := by
  have hd (i : Fin n) : dirDeriv (coordinateVector n i) g x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (tsupport_fderiv_apply_subset ℝ _ hh))
  simp [inverseHessianPair,hd]

lemma continuous_cofactor_trace {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) :
    Continuous (fun x => (hessian u x).det * (hessian u x)⁻¹.trace) := by
  have he : (fun x => (hessian u x).det * (hessian u x)⁻¹.trace) =
      (fun x => ∑ i, cofactorHessian u x i i) := by
    funext x
    simp [Matrix.trace,cofactorHessian,Finset.mul_sum]
  rw [he]
  exact continuous_finsetSum _ (fun i _ => (contDiff_cofactorHessian_entry_global hu hp i i).continuous)

lemma integral_cofactor_trace_le_ball {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    {D : Set (Space n)} (hD : IsCompact D) {G R : ℝ}
    (hG : ∀ x ∈ D, ‖gradient u x‖ ≤ G) (hR : ∀ x ∈ D, ‖x‖ ≤ R) :
    (∫ x in D, (hessian u x).det * (hessian u x)⁻¹.trace) ≤
      ((n:ℝ)+1)*(volume (Metric.closedBall (0:Space n) (G+R))).toReal := by
  have hi : IntegrableOn (fun x => (hessian u x).det*(hessian u x)⁻¹.trace) D volume :=
    ContinuousOn.integrableOn_compact hD (continuous_cofactor_trace hu hp).continuousOn
  have hnon (x : Space n) : 0 ≤ (hessian u x).det*(hessian u x)⁻¹.trace :=
    mul_nonneg (hp x).det_pos.le (hp x).inv.posSemidef.trace_nonneg
  have hlin := lintegral_hessian_minors_le_ball convex_univ (fun _ _ => hu.contDiffAt)
    (fun x _ => hp x) hD.measurableSet (fun x _ => mem_univ x) hG hR
  have hh : (∫⁻ x in D, ENNReal.ofReal ((hessian u x).det*(hessian u x)⁻¹.trace)) ≤
      ((n:ℝ≥0∞)+1)*volume (Metric.closedBall (0:Space n) (G+R)) := by
    apply le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) hlin
    have hd := (hp x).det_pos
    nlinarith
  have hfin : ((n:ℝ≥0∞)+1)*volume (Metric.closedBall (0:Space n) (G+R)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (isCompact_closedBall (0:Space n) (G+R)).measure_lt_top.ne
  have HH := ENNReal.toReal_mono hfin hh
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnon),
    ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg hnon), ENNReal.toReal_mul] at HH
  simpa [ENNReal.toReal_add (a := (n:ℝ≥0∞)) (b := 1) (by simp) (by simp)] using HH

lemma log_energy_le_cutoff {n : ℕ} {u s η : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hs : ContDiff ℝ ∞ s) (hpos : ∀ x, 0 < s x)
    (hL : ∀ x, inverseHessianTrace u s x ≤ 0)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    {K B : Set (Space n)} (hK : IsCompact K) (hB : IsCompact B)
    (hηB : tsupport η ⊆ B) (hηK : ∀ x ∈ K, η x = 1)
    {c M J : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hdet : ∀ x ∈ K, c ≤ (hessian u x).det)
    (hgrad : ∀ x ∈ B, gradientSquared η x ≤ M)
    (hcof : (∫ x in B, (hessian u x).det*(hessian u x)⁻¹.trace) ≤ J) :
    (∫ x in K, inverseHessianPair u (fun y => Real.log (s y)) (fun y => Real.log (s y)) x) ≤ 4*M*J/c := by
  let f := fun y => Real.log (s y)
  have hf : ContDiff ℝ ∞ f := hs.log (fun x => (hpos x).ne')
  have hQ : Continuous (inverseHessianPair u f f) := (contDiff_inverseHessianPair_global hu hp hf hf).continuous
  have hdt : Continuous (fun x => (hessian u x).det) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (contDiffAt_det_hessian hu.contDiffAt).continuousAt
  have hEn : ∀ x, 0 ≤ (hessian u x).det*(η x)^2*inverseHessianPair u f f x :=
    fun x => mul_nonneg (mul_nonneg (hp x).det_pos.le (sq_nonneg _)) (inverseHessianPair_self_nonneg (hp x) f)
  have hEc : HasCompactSupport (fun x => (hessian u x).det*(η x)^2*inverseHessianPair u f f x) := by
    apply HasCompactSupport.of_support_subset_isCompact hηc.isCompact
    intro x hx
    by_contra hxn
    have hz := image_eq_zero_of_notMem_tsupport hxn
    apply hx
    simp [hz]
  have hEi : Integrable (fun x => (hessian u x).det*(η x)^2*inverseHessianPair u f f x) :=
    ((hdt.mul (hη.continuous.pow 2)).mul hQ).integrable_of_hasCompactSupport hEc
  have hlow : c*(∫ x in K, inverseHessianPair u f f x) ≤
      ∫ x, (hessian u x).det*(η x)^2*inverseHessianPair u f f x := by
    rw [← integral_const_mul]
    apply le_trans (setIntegral_mono_on
      ((ContinuousOn.integrableOn_compact hK hQ.continuousOn).const_mul c)
      hEi.integrableOn hK.measurableSet ?_) (setIntegral_le_integral hEi (Filter.Eventually.of_forall hEn))
    intro x hx
    rw [hηK x hx,one_pow,mul_one]
    exact mul_le_mul_of_nonneg_right (hdet x hx) (inverseHessianPair_self_nonneg (hp x) f)
  have hcut : (∫ x, (hessian u x).det*inverseHessianPair u η η x) ≤ M*J := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) (fun x hx => by
      rw [inverseHessianPair_eq_zero_outside_tsupport u η η (fun hh => hx (hηB hh)),mul_zero])]
    have hi : (∫ x in B, (hessian u x).det*inverseHessianPair u η η x) ≤
        ∫ x in B, M*((hessian u x).det*(hessian u x)⁻¹.trace) := by
      apply setIntegral_mono_on
        (ContinuousOn.integrableOn_compact hB (hdt.mul (contDiff_inverseHessianPair_global hu hp hη hη).continuous).continuousOn)
        ((ContinuousOn.integrableOn_compact hB (continuous_cofactor_trace hu hp).continuousOn).const_mul M)
        hB.measurableSet
      intro x hx
      have hh := (inverseHessianPair_le_trace_gradientSquared (u := u) (f := η) (hp x)).trans
        (mul_le_mul_of_nonneg_left (hgrad x hx) (hp x).inv.posSemidef.trace_nonneg)
      calc
        (hessian u x).det * inverseHessianPair u η η x ≤
            (hessian u x).det * ((hessian u x)⁻¹.trace * M) :=
          mul_le_mul_of_nonneg_left hh (hp x).det_pos.le
        _ = M * ((hessian u x).det * (hessian u x)⁻¹.trace) := by ring
    rw [integral_const_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hcof hM)
  have hC := linearizedMA_log_caccioppoli hu hp hs hpos hL hη hηc
  change _ ≤ 4*(∫ x, (hessian u x).det*inverseHessianPair u η η x) at hC
  apply (le_div_iff₀ hc).mpr
  nlinarith

end LogVariance


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
-- module Solutions.OAIQ22_AB.AffineBernstein_SegmentEnergy
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

section SegmentEnergy

lemma matrix_dual_cauchy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (v p : ι → ℝ) :
    (v ⬝ᵥ p)^2 ≤ (v ⬝ᵥ A.mulVec v) * inverseMatrixPair A p p := by
  have he : A⁻¹.mulVec (A.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
      Matrix.one_mulVec]
  have hc := inverseMatrixPair_cauchy hA (A.mulVec v) p
  rw [inverseMatrixPair_eq_dot, inverseMatrixPair_eq_dot,he] at hc
  simpa only [dotProduct_comm] using hc

lemma directional_derivative_sq_le {n : ℕ} {u f : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (v : Space n) :
    (dirDeriv v f x)^2 ≤ fderiv ℝ (fderiv ℝ u) x v v * inverseHessianPair u f f x := by
  have heQ : inverseHessianPair u f f x = inverseMatrixPair (hessian u x)
      (fun i => dirDeriv (coordinateVector n i) f x) (fun i => dirDeriv (coordinateVector n i) f x) := by
    unfold inverseHessianPair inverseMatrixPair
    rw [Finset.sum_comm]
    simp only [mul_right_comm]
  rw [dirDeriv_coordinate_sum,second_fderiv_eq_sum hu,heQ]
  convert matrix_dual_cauchy hp (fun i => v i) (fun i => dirDeriv (coordinateVector n i) f x) using 1 <;>
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

/-- Integral Cauchy--Schwarz with a pointwise dual pairing. No square roots or
strict positivity assumptions on the two nonnegative factors are required. -/
lemma integral_pair_cauchy {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {H E d : X → ℝ} (hH : Integrable H μ) (hE : Integrable E μ) (hd : Integrable d μ)
    (hHpos : ∀ x, 0 ≤ H x) (hEpos : ∀ x, 0 ≤ E x)
    (hpair : ∀ x, (d x)^2 ≤ H x * E x) :
    (∫ x, d x ∂μ)^2 ≤ (∫ x, H x ∂μ)*(∫ x, E x ∂μ) := by
  have hquad (a : ℝ) : 0 ≤ (∫ x, H x ∂μ)*(a*a) +
      (2*∫ x, d x ∂μ)*a + ∫ x, E x ∂μ := by
    have hp (x : X) : 0 ≤ a^2*H x+(2*a)*d x+E x := by
      have hh := paired_cauchy_coercive (hHpos x) (hEpos x) (hpair x)
        (sq_nonneg a) zero_lt_one (show (2*a)^2 ≤ 4*a^2*1 by nlinarith)
      simpa only [one_mul] using hh
    have hi := MeasureTheory.integral_nonneg (μ := μ) (show 0 ≤ (fun x => a^2*H x+(2*a)*d x+E x) from hp)
    rw [integral_add (f := fun x => a^2*H x+(2*a)*d x) (g := E)
      ((hH.const_mul (a^2)).add (hd.const_mul (2*a))) hE,
      integral_add (f := fun x => a^2*H x) (g := fun x => (2*a)*d x)
      (hH.const_mul (a^2)) (hd.const_mul (2*a)),integral_const_mul,integral_const_mul] at hi
    nlinarith
  have hh := discrim_le_zero hquad
  unfold discrim at hh
  nlinarith

lemma segment_energy_bound {n : ℕ} {u f : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ x, (hessian u x).PosDef) (x y : Space n) :
    (f y-f x)^2 ≤ ((fderiv ℝ u y-fderiv ℝ u x) (y-x)) *
      ∫ t in (0:ℝ)..1, inverseHessianPair u f f (x+t • (y-x)) := by
  let v := y-x
  let α : ℝ → Space n := fun t => x+t • v
  have hα : ContDiff ℝ ∞ α := contDiff_const.add (contDiff_id.smul contDiff_const)
  let H : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (α t) v v
  let E : ℝ → ℝ := fun t => inverseHessianPair u f f (α t)
  let d : ℝ → ℝ := fun t => dirDeriv v f (α t)
  have hHc : Continuous H :=
    (((hu.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous.comp
      hα.continuous).clm_apply continuous_const |>.clm_apply continuous_const
  have hEc : Continuous E := (contDiff_inverseHessianPair_global hu hp hf hf).continuous.comp hα.continuous
  have hdc : Continuous d := (contDiff_dirDeriv hf v).continuous.comp hα.continuous
  have hh := integral_pair_cauchy (μ := volume.restrict (Icc (0:ℝ) 1)) (hHc.integrableOn_Icc) (hEc.integrableOn_Icc) (hdc.integrableOn_Icc)
    (fun t => second_fderiv_nonneg hu.contDiffAt (hp (α t)).posSemidef v)
    (fun t => inverseHessianPair_self_nonneg (hp (α t)) f)
    (fun t => directional_derivative_sq_le hu.contDiffAt (hp (α t)) v)
  have hdi : (∫ t in (0:ℝ)..1, d t) = f y-f x := by
    have hd' (t : ℝ) : HasDerivAt (fun t => f (α t)) (d t) t := by
      apply HasDerivAt.congr_deriv ((hf.differentiable (by simp) (α t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)))
      simp only [zero_add,one_smul]
      rfl
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun parameter _ => hd' parameter) (hdc.intervalIntegrable 0 1)
    simpa only [α,v,zero_smul,add_zero,one_smul,add_sub_cancel] using hi
  have hHi : (∫ t in (0:ℝ)..1, H t) = (fderiv ℝ u y-fderiv ℝ u x) v := by
    let q := fun z => fderiv ℝ u z v
    have hq : ContDiff ℝ ∞ q := (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdq (z : Space n) : dirDeriv v q z = fderiv ℝ (fderiv ℝ u) z v v := by
      unfold dirDeriv q
      rw [((((hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z).hasFDerivAt).clm_apply
        (hasFDerivAt_const v z)).fderiv]
      simp
    have hd' (t : ℝ) : HasDerivAt (fun t => q (α t)) (H t) t := by
      have hdt := ((hq.differentiable (by simp) (α t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)))
      apply hdt.congr_deriv
      simp only [one_smul,zero_add]
      exact hdq (α t)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun parameter _ => hd' parameter) (hHc.intervalIntegrable 0 1)
    simpa only [α,q,v,zero_smul,add_zero,one_smul,add_sub_cancel,sub_apply] using hi
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume))] at hdi hHi ⊢
  rw [← hdi,← hHi]
  exact hh

end SegmentEnergy




end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedPoincare
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

section WeightedPoincare

lemma compact_integrable_pair {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [IsFiniteMeasureOnCompacts (μ.prod ν)]
    {K : Set X} {S : Set Y} (hK : IsCompact K) (hS : IsCompact S)
    {F : X × Y → ℝ} (hF : Continuous F) :
    Integrable F ((μ.restrict K).prod (ν.restrict S)) := by
  rw [Measure.prod_restrict K S]
  exact ContinuousOn.integrableOn_compact (hK.prod hS) hF.continuousOn

lemma integral_affine_convex_le {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) {E : Space n → ℝ}
    (hE : Continuous E) (hEp : ∀ x, 0 ≤ E x) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {a : Space n} (ha : a ∈ K) :
    (∫ x in K, E ((1-t) • a + t • x)) ≤
      (t^n)⁻¹ * ∫ x in K, E x := by
  let F := K.indicator E
  have hFi : Integrable F := (ContinuousOn.integrableOn_compact hK hE.continuousOn).integrable_indicator hK.measurableSet
  have hFa : Integrable (fun x => F ((1-t) • a+x)) :=
    (measurePreserving_add_left volume ((1-t) • a)).integrable_comp_of_integrable hFi
  have hFat : Integrable (fun x => F ((1-t) • a+t • x)) := hFa.comp_smul ht.ne'
  have hFp (x : Space n) : 0 ≤ F x := Set.indicator_nonneg (fun point _ => hEp point) x
  have he : (∫ x in K, E ((1-t) • a+t • x)) = ∫ x in K, F ((1-t) • a+t • x) := by
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    exact (Set.indicator_of_mem (hc ha hx (sub_nonneg.mpr ht1) ht.le (by ring)) E).symm
  rw [he]
  calc
    _ ≤ ∫ x, F ((1-t) • a+t • x) := setIntegral_le_integral hFat (Filter.Eventually.of_forall fun x => hFp _)
    _ = (t^n)⁻¹ * ∫ x in K, E x := by
      rw [Measure.integral_comp_smul_of_nonneg volume (fun x => F ((1-t) • a+x)) t (hR := ht.le),
        integral_add_left_eq_self F ((1-t) • a)]
      simp only [Space,finrank_euclideanSpace, Fintype.card_fin,smul_eq_mul]
      rw [integral_indicator hK.measurableSet]

lemma double_integral_segment_le {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) {E : Space n → ℝ}
    (hE : Continuous E) (hEp : ∀ x, 0 ≤ E x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (∫ x in K, ∫ y in K, E ((1-t) • x+t • y)) ≤
      (volume K).toReal * (2:ℝ)^n * ∫ x in K, E x := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hEc (r : ℝ) : Continuous (fun p : Space n × Space n => E ((1-r) • p.1+r • p.2)) :=
    by fun_prop
  have hEi (r : ℝ) := compact_integrable_pair (μ := volume) (ν := volume) hK hK (hEc r)
  have hIn : 0 ≤ ∫ x in K, E x := MeasureTheory.integral_nonneg hEp
  have hlarge (r : ℝ) (hr : (1/2:ℝ) ≤ r) (hr1 : r ≤ 1) :
      (∫ x in K, ∫ y in K, E ((1-r) • x+r • y)) ≤
        (volume K).toReal * (2:ℝ)^n * ∫ x in K, E x := by
    have hrp : 0 < r := by linarith
    have hinv : (r^n)⁻¹ ≤ (2:ℝ)^n := by
      rw [← inv_pow]
      apply pow_le_pow_left₀ (inv_nonneg.mpr hrp.le)
      exact (inv_le_iff_one_le_mul₀ hrp).mpr (by linarith)
    have hi := setIntegral_mono_on (hEi r).integral_prod_left
      (integrable_const ((2:ℝ)^n * ∫ x in K, E x)) hK.measurableSet (fun x hx =>
        (integral_affine_convex_le hK hc hE hEp hrp hr1 hx).trans
          (mul_le_mul_of_nonneg_right hinv hIn))
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_assoc] using hi
  by_cases hth : (1/2:ℝ) ≤ t
  · exact hlarge t hth ht.2
  · rw [integral_integral_swap (hEi t)]
    have he : (fun y => ∫ x in K, E ((1-t) • x+t • y)) =
        (fun y => ∫ x in K, E ((1-(1-t)) • y+(1-t) • x)) := by
      funext y
      apply setIntegral_congr_fun hK.measurableSet
      intro point _
      simp only [sub_sub_cancel,add_comm]
    rw [he]
    exact hlarge (1-t) (by linarith) (by linarith [ht.1])

lemma average_segment_energy_le {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) {E : Space n → ℝ}
    (hE : Continuous E) (hEp : ∀ x, 0 ≤ E x) :
    (∫ x in K, ∫ y in K, ∫ t in Icc (0:ℝ) 1, E ((1-t) • x+t • y)) ≤
      (volume K).toReal * (2:ℝ)^n * ∫ x in K, E x := by
  have hG : Continuous (fun p : Space n × ℝ => ∫ y in K, E ((1-p.2) • p.1+p.2 • y)) :=
    continuous_parametric_integral_of_continuous (by fun_prop) hK
  have hswap1 (x : Space n) :
      (∫ y in K, ∫ t in Icc (0:ℝ) 1, E ((1-t) • x+t • y)) =
        ∫ t in Icc (0:ℝ) 1, ∫ y in K, E ((1-t) • x+t • y) := by
    apply integral_integral_swap
    exact compact_integrable_pair (μ := volume) (ν := volume) hK isCompact_Icc (by fun_prop)
  simp_rw [hswap1]
  rw [integral_integral_swap (compact_integrable_pair (μ := volume) (ν := volume) hK isCompact_Icc hG)]
  have hi := setIntegral_mono_on
    (compact_integrable_pair (μ := volume) (ν := volume) hK isCompact_Icc hG).integral_prod_right
    (integrable_const ((volume K).toReal * (2:ℝ)^n * ∫ x in K, E x)) measurableSet_Icc
    (fun t ht => double_integral_segment_le hK hc hE hEp ht)
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul] using hi

/-- Weighted Poincare in a compact convex set. The constant uses only chordal
oscillation of the convex gradient, not pointwise ellipticity. -/
theorem weighted_poincare {n : ℕ} {u f : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (hp : ∀ x, (hessian u x).PosDef)
    {K : Set (Space n)} (hK : IsCompact K) (hc : Convex ℝ K) {A : ℝ} (hA : 0 ≤ A)
    (hchord : ∀ x ∈ K, ∀ y ∈ K, (fderiv ℝ u y-fderiv ℝ u x) (y-x) ≤ A) :
    (∫ x in K, ∫ y in K, (f y-f x)^2) ≤
      A*((volume K).toReal * (2:ℝ)^n * ∫ x in K, inverseHessianPair u f f x) := by
  let E := inverseHessianPair u f f
  have hE : Continuous E := (contDiff_inverseHessianPair_global hu hp hf hf).continuous
  have hEp (x : Space n) : 0 ≤ E x := inverseHessianPair_self_nonneg (hp x) f
  let F := fun p : Space n × Space n => ∫ t in Icc (0:ℝ) 1, E ((1-t) • p.1+t • p.2)
  have hF : Continuous F := continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  have hFi := compact_integrable_pair (μ := volume) (ν := volume) hK hK hF
  have hdiff : Continuous (fun p : Space n × Space n => (f p.2-f p.1)^2) := by fun_prop
  have hdiffi := compact_integrable_pair (μ := volume) (ν := volume) hK hK hdiff
  have hpoint (x : Space n) (hx : x ∈ K) (y : Space n) (hy : y ∈ K) :
      (f y-f x)^2 ≤ A*F (x,y) := by
    have hh := segment_energy_bound hu hf hp x y
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      setIntegral_congr_set (Ioc_ae_eq_Icc (μ := volume))] at hh
    have he : (fun t : ℝ => E (x+t • (y-x))) = (fun t => E ((1-t) • x+t • y)) := by
      funext t
      congr 1
      module
    change (f y-f x)^2 ≤ _*(∫ t in Icc (0:ℝ) 1, E (x+t • (y-x))) at hh
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hchord x hx y hy)
      (MeasureTheory.integral_nonneg fun t => hEp _))
  have hi := setIntegral_mono_on hdiffi.integral_prod_left
    ((hFi.const_mul A).integral_prod_left) hK.measurableSet (fun x hx => by
      apply setIntegral_mono_on
        (ContinuousOn.integrableOn_compact hK (hdiff.comp (continuous_const.prodMk continuous_id)).continuousOn)
        (ContinuousOn.integrableOn_compact hK ((hF.comp (continuous_const.prodMk continuous_id)).const_mul A).continuousOn)
        hK.measurableSet
      exact hpoint x hx)
  simp_rw [integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (average_segment_energy_le hK hc hE hEp) hA)

end WeightedPoincare



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

lemma normalized_gradient_chord_bound {n : ℕ} {ρ R : ℝ} {v : Space n → ℝ}
    (hv : BalancedNormalized ρ R v) {x y : Space n}
    (hx : x ∈ Metric.closedBall (0:Space n) (1/16:ℝ))
    (hy : y ∈ Metric.closedBall (0:Space n) (1/16:ℝ)) :
    (fderiv ℝ v y-fderiv ℝ v x) (y-x) ≤ 1 := by
  have hxq := (Metric.closedBall_subset_closedBall (by norm_num : (1/16:ℝ)≤1/4)) hx
  have hyq := (Metric.closedBall_subset_closedBall (by norm_num : (1/16:ℝ)≤1/4)) hy
  have hd : ‖fderiv ℝ v y-fderiv ℝ v x‖ ≤ 8 :=
    (norm_sub_le _ _).trans (by linarith [normalized_gradient_bound hv hxq,normalized_gradient_bound hv hyq])
  have hs : ‖y-x‖ ≤ (1/8:ℝ) := by
    have hxn : ‖x‖ ≤ (1/16:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hyn : ‖y‖ ≤ (1/16:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ ‖(fderiv ℝ v y-fderiv ℝ v x) (y-x)‖ := le_abs_self _
    _ ≤ ‖fderiv ℝ v y-fderiv ℝ v x‖*‖y-x‖ := (fderiv ℝ v y-fderiv ℝ v x).le_opNorm _
    _ ≤ 8*(1/8:ℝ) := mul_le_mul hd hs (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- Uniform logarithmic variance for the *actual* inverse-Hessian operator.
The determinant bounds and all geometric constant dependencies are outputs. -/
theorem normalized_log_variance_oai {n : ℕ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ s : Space n → ℝ, ContDiff ℝ ∞ s → (∀ x, 0 < s x) →
      (∀ x, inverseHessianTrace v s x ≤ 0) →
      (∫ x in Metric.closedBall (0:Space n) (1/16:ℝ),
        ∫ y in Metric.closedBall (0:Space n) (1/16:ℝ),
          (Real.log (s y)-Real.log (s x))^2) ≤ V := by
  obtain ⟨c,C,hc,hC,Hdet⟩ := normalized_balanced_det_bounds hρ hρ1 hR (n := n)
  let η : ContDiffBump (0:Space n) := ⟨1/16,1/4,by norm_num,by norm_num⟩
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  let B := Metric.closedBall (0:Space n) (1/4:ℝ)
  have hη : ContDiff ℝ ∞ (η : Space n → ℝ) := η.contDiff
  have hg : Continuous (gradientSquared (η : Space n → ℝ)) := by
    unfold gradientSquared
    exact continuous_finsetSum _ (fun _ _ => ((contDiff_dirDeriv hη _).continuous.pow 2))
  obtain ⟨M,hMb⟩ := (isCompact_closedBall (0:Space n) (1/4:ℝ)).bddAbove_image hg.continuousOn
  have hM (x : Space n) (hx : x ∈ B) : gradientSquared (η : Space n → ℝ) x ≤ M := hMb ⟨x,hx,rfl⟩
  have hMn : 0 ≤ M := (gradientSquared_nonneg (η : Space n → ℝ) 0).trans
    (hM 0 (by simp [B]))
  let J := ((n:ℝ)+1)*(volume (Metric.closedBall (0:Space n) (4+(1/4:ℝ)))).toReal
  let V := (volume K).toReal*(2:ℝ)^n*(4*M*J/c)
  have hJn : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨V,by dsimp [V]; positivity,?_⟩
  intro v hv s hs hspos hLs
  have hcK : ∀ x ∈ K, c ≤ (hessian v x).det := by
    intro x hx
    have hxn : ‖x‖ ≤ (1/16:ℝ) := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hx
    exact (Hdet v hv.smooth hv.posDef hv.maximal hv.zero hv.deriv_zero hv.balance hv.inner hv.outer x
      (by rw [Metric.mem_ball,dist_zero_right]; linarith)).1
  have hcof : (∫ x in B, (hessian v x).det*(hessian v x)⁻¹.trace) ≤ J := by
    apply integral_cofactor_trace_le_ball hv.smooth hv.posDef (isCompact_closedBall _ _)
    · intro x hx
      simpa only [gradient,LinearIsometryEquiv.norm_map] using normalized_gradient_bound hv hx
    · intro x hx
      simpa only [B,Metric.mem_closedBall,dist_zero_right] using hx
  have he := log_energy_le_cutoff hv.smooth hv.posDef hs hspos hLs hη η.hasCompactSupport
    (isCompact_closedBall (0:Space n) (1/16:ℝ)) (isCompact_closedBall (0:Space n) (1/4:ℝ))
    (by rw [η.tsupport_eq]) (fun x hx => η.one_of_mem_closedBall hx)
    hc hMn hcK hM hcof
  have hw := weighted_poincare hv.smooth (hs.log (fun x => (hspos x).ne')) hv.posDef
    (isCompact_closedBall (0:Space n) (1/16:ℝ)) (convex_closedBall _ _) (by norm_num : (0:ℝ)≤1)
    (fun x hx y hy => normalized_gradient_chord_bound hv hx hy)
  simp only [one_mul] at hw
  exact hw.trans (mul_le_mul_of_nonneg_left he (by positivity))

end NormalizedLogVariance


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.normalized_log_variance_oai := @OAI.AffineBernstein.normalized_log_variance_oai
