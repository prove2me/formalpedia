-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_tube_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:07:36.466385+00:00
-- url     : https://prove2.me/submissions/9ad3c48e-36cb-49f5-b094-34c03bf8b7ff

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_f_smooth
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_tube_angular_pair_nonneg
import Theorems.Thm_OAI_AffineBernstein_affineMaximal_global_d_identity

section
-- module Solutions.OAIQ22_AB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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

end RadialCalculus

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

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
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

section CompleteSphericalDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SupportGeometry
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The literal support value, not a freely chosen support coordinate. -/
theorem convex_first_order {W : Set E} {F : E → ℝ} (hF : ConvexOn ℝ W F)
    {x y : E} (hx : x ∈ W) (hy : y ∈ W) (hd : DifferentiableAt ℝ F x) :
    fderiv ℝ F x (y - x) ≤ F y - F x := by
  let γ : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t => x + t • (y - x)
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (y - x)
      map_vadd' := by intro t s; simp [add_smul]; abel }
  have hc := hF.comp_affineMap γ
  have hdγ : HasDerivAt γ (y - x) 0 := by
    change HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hdx : HasFDerivAt F (fderiv ℝ F x) (γ 0) := by
    simpa [γ] using hd.hasFDerivAt
  have hs := hc.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simpa [γ] using hx) (by simpa [γ] using hy) (by norm_num)
    (by simpa [γ] using hdx.comp_hasDerivAt 0 hdγ)
  simpa [slope_def_field, γ] using hs

/- A nonzero linear functional cannot attain its sublevel maximum below the level. -/
theorem sublevel_max_on_level {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {z : E} (hz : z ∈ W)
    (hzF : F z ≤ 0) (hc : ContinuousAt F z)
    (hmax : IsMaxOn ℓ {y | y ∈ W ∧ F y ≤ 0} z) : F z = 0 := by
  by_contra hn
  have ht : F z < 0 := lt_of_le_of_ne hzF hn
  have hm : IsLocalMax ℓ z := by
    filter_upwards [hW.mem_nhds hz, hc.eventually (eventually_lt_nhds ht)] with y hy hyF
    exact hmax ⟨hy, hyF.le⟩
  exact hℓ (by simpa using hm.fderiv_eq_zero)

/- The support maximum of a compact smooth convex sublevel has a positive
Lagrange multiplier. This includes dimension one without a sphere convention. -/
theorem exists_support_multiplier [CompleteSpace E] {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) (hF : ContDiffOn ℝ ∞ F W)
    {x₀ : E} (hx₀ : x₀ ∈ W) (hneg : F x₀ < 0)
    (hK : IsCompact {y | y ∈ W ∧ F y ≤ 0})
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ∃ z ∈ W, F z = 0 ∧ ∃ lam : ℝ, 0 < lam ∧
      fderiv ℝ F z = lam • ℓ ∧
      (∀ y ∈ W, F y ≤ 0 → ℓ y ≤ ℓ z) ∧
      supportValue {y | y ∈ W ∧ F y ≤ 0} ℓ = ℓ z := by
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀, hneg.le⟩ ℓ.continuous.continuousOn
  have hd := hF.contDiffAt (hW.mem_nhds hz.1)
  have hzF := sublevel_max_on_level hW hℓ hz.1 hz.2 hd.continuousAt hmax
  have he : IsLocalExtrOn ℓ {y | F y = F z} z := by
    apply Or.inr
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hz.1)]
      with y hy hyW
    exact hmax ⟨hyW, by simp [hy, hzF]⟩
  obtain ⟨a, b, hab, heq⟩ := he.exists_multipliers_of_hasStrictFDerivAt_1d
    (hd.hasStrictFDerivAt (by simp)) ℓ.hasStrictFDerivAt
  have ha : a ≠ 0 := by
    intro ha
    have hb : b ≠ 0 := by simpa [ha] using hab
    simp only [ha, zero_smul, zero_add] at heq
    exact hℓ ((smul_eq_zero.mp heq).resolve_left hb)
  let lam := -b / a
  have hder : fderiv ℝ F z = lam • ℓ := by
    ext v
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) heq
    simp only [add_apply, smul_apply, zero_apply, smul_eq_mul] at hh ⊢
    dsimp [lam]
    field_simp
    nlinarith
  have hi := convex_first_order hcv hz.1 hx₀ (hd.differentiableAt (by simp))
  rw [hder, smul_apply, smul_eq_mul, hzF, sub_zero] at hi
  have hlin : ℓ (x₀ - z) ≤ 0 := by
    rw [map_sub, sub_nonpos]
    exact hmax ⟨hx₀, hneg.le⟩
  have hlam : 0 < lam := by
    by_contra ht
    have hh := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ht) hlin
    linarith
  refine ⟨z, hz.1, hzF, lam, hlam, hder, ?_, ?_⟩
  · intro y hy hyF
    exact hmax ⟨hy, hyF⟩
  · unfold supportValue
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (s := ℓ '' {y | y ∈ W ∧ F y ≤ 0}) ?_ ?_ ?_
    · exact ⟨ℓ z, z, hz, rfl⟩
    · rintro v ⟨y, hy, rfl⟩; exact hmax hy
    · intro b hb
      exact ⟨ℓ z, ⟨z, hz, rfl⟩, hb⟩

/- Linearization of the actual support equations `F(y)=0`, `DF(y)=lam*ell`. -/
theorem supportJacobian_injective {d : E →L[ℝ] ℝ}
    {H : E →L[ℝ] (E →L[ℝ] ℝ)} {ℓ : E →L[ℝ] ℝ} {lam : ℝ}
    (hℓ : ℓ ≠ 0) (hlam : lam ≠ 0) (hd : d = lam • ℓ)
    (hH : ∀ v : E, v ≠ 0 → 0 < H v v) :
    Function.Injective (supportJacobian d H ℓ) := by
  apply (injective_iff_map_eq_zero (supportJacobian d H ℓ)).mpr
  rintro ⟨v, a⟩ hv
  change (d v, H v - a • ℓ) = (0, 0) at hv
  have hv1 : d v = 0 := congrArg Prod.fst hv
  have hv2 : H v = a • ℓ := sub_eq_zero.mp (congrArg Prod.snd hv)
  have hlv : ℓ v = 0 := by
    simpa [hd, hlam] using hv1
  have hv0 : v = 0 := by
    by_contra hn
    have hh := hH v hn
    rw [hv2] at hh
    simp [hlv] at hh
  have ha0 : a = 0 := by
    rw [hv0, map_zero] at hv2
    exact (smul_eq_zero.mp hv2.symm).resolve_right hℓ
  simp [hv0, ha0]

theorem supportJacobian_isInvertible [FiniteDimensional ℝ E]
    {d : E →L[ℝ] ℝ} {H : E →L[ℝ] (E →L[ℝ] ℝ)}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hℓ : ℓ ≠ 0) (hlam : lam ≠ 0)
    (hd : d = lam • ℓ) (hH : ∀ v : E, v ≠ 0 → 0 < H v v) :
    (supportJacobian d H ℓ).IsInvertible := by
  have hi := supportJacobian_injective hℓ hlam hd hH
  have hf : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ (ℝ × (E →L[ℝ] ℝ)) := by
    rw [Module.finrank_prod, Module.finrank_prod,
      ← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq,
      Subspace.dual_finrank_eq]
    omega
  let e := (supportJacobian d H ℓ).toLinearMap.linearEquivOfInjective hi hf
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- Fiber derivatives of the actual defining function. -/

theorem contDiffAt_fiberGradient {F : S × E → ℝ} {p : S × E}
    (hF : ContDiffAt ℝ ∞ F p) : ContDiffAt ℝ ∞ (fiberGradient F) p := by
  apply ContDiffAt.fderiv (n := ∞) (g := Prod.snd) _ contDiffAt_snd (by simp)
  exact hF.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)

theorem contDiffAt_supportEquations {F : S × E → ℝ} {s : S} {y : E}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hF : ContDiffAt ℝ ∞ F (s, y)) :
    ContDiffAt ℝ ∞ (supportEquations F) ((s, ℓ), (y, lam)) := by
  have he : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd.fst
  have hc1 : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      F (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) := hF.comp ((s, ℓ), (y, lam)) he
  have hc2 : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      fiberGradient F (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) := by
    have hh := (contDiffAt_fiberGradient (F := F) (p := (s, y)) hF).comp ((s, ℓ), (y, lam)) he
    exact hh
  exact hc1.prodMk (hc2.sub (contDiffAt_snd.snd.smul contDiffAt_fst.snd))

theorem supportEquations_partial {F : S × E → ℝ} {s : S} {y : E}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hF : ContDiffAt ℝ ∞ F (s, y)) :
    fderiv ℝ (supportEquations F) ((s, ℓ), (y, lam)) ∘L
      ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ) =
    supportJacobian (fderiv ℝ (fun z => F (s, z)) y)
      (fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y) ℓ := by
  have hfu : ContDiffAt ℝ ∞ (fun z => F (s, z)) y :=
    hF.comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hdu := hfu.differentiableAt (by simp)
  have h2u := (hfu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hp : HasFDerivAt (fun q : E × ℝ => supportEquations F ((s, ℓ), q))
      (supportJacobian (fderiv ℝ (fun z => F (s, z)) y)
        (fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y) ℓ) (y, lam) := by
    exact (hdu.hasFDerivAt.comp (y, lam) (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).prodMk
      ((h2u.hasFDerivAt.comp (y, lam) (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).sub
        ((ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.smul_const ℓ))
  have hi : HasFDerivAt (fun q : E × ℝ => ((s, ℓ), q))
      (ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ)) (y, lam) := by
    convert (hasFDerivAt_const (s, ℓ) (y, lam)).prodMk (hasFDerivAt_id (y, lam)) using 1 <;>
      ext <;> simp
  exact (((contDiffAt_supportEquations (ℓ := ℓ) (lam := lam) hF).differentiableAt
    (by simp)).hasFDerivAt.comp (y, lam) hi).unique hp

/- A solution of the support equations with positive multiplier is a global,
not merely local, support point. -/
theorem supportValue_of_equations {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {z : E} (hz : z ∈ W) (hzF : F z = 0)
    (hd : DifferentiableAt ℝ F z) {ℓ : E →L[ℝ] ℝ} {lam : ℝ}
    (hlam : 0 < lam) (he : fderiv ℝ F z = lam • ℓ) :
    supportValue {y | y ∈ W ∧ F y ≤ 0} ℓ = ℓ z := by
  unfold supportValue
  have hmax (y : E) (hy : y ∈ W ∧ F y ≤ 0) : ℓ y ≤ ℓ z := by
    have hh := convex_first_order hcv hz hy.1 hd
    simp only [he, smul_apply, smul_eq_mul, map_sub, hzF, sub_zero] at hh
    have hh' : lam * (ℓ y - ℓ z) ≤ 0 := by simpa [mul_sub] using hh.trans hy.2
    nlinarith
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (s := ℓ '' {y | y ∈ W ∧ F y ≤ 0}) ?_ ?_ ?_
  · exact ⟨ℓ z, z, ⟨hz, hzF.le⟩, rfl⟩
  · rintro v ⟨y, hy, rfl⟩; exact hmax y hy
  · intro a ha; exact ⟨ℓ z, ⟨z, ⟨hz, hzF.le⟩, rfl⟩, ha⟩

/- Smooth dependence of the literal support value on base and conormal.
The IFT is applied to the actual defining function and its actual Hessian. -/
theorem contDiffAt_supportValue_fibers [FiniteDimensional ℝ E] [CompleteSpace S]
    {B : Set S} (hB : IsOpen B) {W : Set (S × E)} (hW : IsOpen W)
    {F : S × E → ℝ} (hF : ContDiffOn ℝ ∞ F W)
    (hcv : ∀ s ∈ B, ConvexOn ℝ {y | (s, y) ∈ W} (fun y => F (s, y)))
    {s : S} (hs : s ∈ B) {x₀ : E} (hx₀ : (s, x₀) ∈ W) (hneg : F (s, x₀) < 0)
    (hK : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0})
    (hH : ∀ y, (s, y) ∈ W → F (s, y) = 0 → ∀ v : E, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y v v)
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ W ∧ F (q.1, y) ≤ 0} q.2) (s, ℓ) := by
  have hWs : IsOpen {y | (s, y) ∈ W} := hW.preimage (by fun_prop)
  have hFs : ContDiffOn ℝ ∞ (fun y => F (s, y)) {y | (s, y) ∈ W} :=
    hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  obtain ⟨z, hz, hzF, lam, hlam, hder, -, hsup⟩ :=
    exists_support_multiplier hWs (hcv s hs) hFs hx₀ hneg hK hℓ
  have hcF := hF.contDiffAt (hW.mem_nhds hz)
  have hg := contDiffAt_supportEquations (ℓ := ℓ) (lam := lam) hcF
  have hinv : (fderiv ℝ (supportEquations F) ((s, ℓ), (z, lam)) ∘L
      ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ)).IsInvertible := by
    rw [supportEquations_partial hcF]
    exact supportJacobian_isInvertible hℓ hlam.ne' hder (hH z hz hzF)
  let ψ := hg.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ∞ ψ (s, ℓ) := hg.contDiffAt_implicitFunction (by simp) hinv
  have hψ₀ : ψ (s, ℓ) = (z, lam) := hg.implicitFunction_apply_self (by simp) hinv
  have hge : ∀ᶠ q in 𝓝 (s, ℓ), supportEquations F (q, ψ q) = 0 := by
    have hh := hg.eventually_apply_implicitFunction (by simp) hinv
    have hg0 : supportEquations F ((s, ℓ), (z, lam)) = 0 := by
      simp [supportEquations, fiberGradient, hzF, hder]
    simpa only [hg0, ψ] using hh
  have hnearW : ∀ᶠ q in 𝓝 (s, ℓ), (q.1, (ψ q).1) ∈ W := by
    apply (continuousAt_fst.prodMk hψ.continuousAt.fst).eventually
      (hW.mem_nhds (show ((s, ℓ).1, (ψ (s, ℓ)).1) ∈ W by simpa [hψ₀] using hz))
  have hnearL : ∀ᶠ q in 𝓝 (s, ℓ), 0 < (ψ q).2 := by
    exact hψ.continuousAt.snd.eventually (eventually_gt_nhds (by simpa [hψ₀] using hlam))
  have hnearB : ∀ᶠ q in 𝓝 (s, ℓ), q.1 ∈ B :=
    continuousAt_fst.eventually (hB.mem_nhds hs)
  have heq : (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ W ∧ F (q.1, y) ≤ 0} q.2) =ᶠ[𝓝 (s, ℓ)]
      (fun q => q.2 ((ψ q).1)) := by
    filter_upwards [hge, hnearW, hnearL, hnearB] with q hq hqW hqL hqB
    have hzero : F (q.1, (ψ q).1) = 0 := congrArg Prod.fst hq
    have hgrad : fiberGradient F (q.1, (ψ q).1) = (ψ q).2 • q.2 :=
      sub_eq_zero.mp (congrArg Prod.snd hq)
    apply supportValue_of_equations (hcv q.1 hqB) hqW hzero _ hqL hgrad
    exact ((hF.contDiffAt (hW.mem_nhds hqW)).comp _
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  exact (contDiffAt_snd.clm_apply hψ.fst).congr_of_eventuallyEq heq

/- Finiteness of the literal support value on a compact fiber. -/
theorem le_supportValue {K : Set E} (hK : IsCompact K) {z : E} (hz : z ∈ K)
    (ℓ : E →L[ℝ] ℝ) : ℓ z ≤ supportValue K ℓ := by
  exact le_csSup (hK.image ℓ.continuous).bddAbove ⟨z, hz, rfl⟩

/- The envelope identity recovers the Gauss parametrization from the literal
support function; no choice of a surrogate support coordinate is involved. -/

theorem supportValue_pos [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K)
    (hzero : (0 : E) ∈ interior K) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    0 < supportValue K ℓ := by
  have hex : ∃ v : E, ℓ v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hℓ
    ext v
    exact hn v
  obtain ⟨v, hv⟩ := hex
  let w := (ℓ v) • v
  have hw : 0 < ℓ w := by simp only [w, map_smul, smul_eq_mul]; exact mul_self_pos.mpr hv
  have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  let t := r / (2 * ‖w‖)
  have ht : 0 < t := div_pos hr (by positivity)
  have htw : t • w ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    have hh : r / (2 * ‖w‖) * ‖w‖ = r / 2 := by field_simp
    rw [hh]
    linarith
  have hp : 0 < ℓ (t • w) := by simpa using mul_pos ht hw
  exact hp.trans_le (le_supportValue hK htw ℓ)

end SupportGeometry

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/

end CompleteSphericalDependencies

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A genuine affine slice of the original epigraph, in arbitrary transverse
coordinates. -/
theorem affineEpigraphFiber_no_vertical {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {x : Space n} {z : ℝ} {A : E →L[ℝ] Space n}
    {b : E →L[ℝ] ℝ} (hK : IsCompact (affineEpigraphFiber Ω u x z A b))
    (hne : (affineEpigraphFiber Ω u x z A b).Nonempty)
    {v : E} (hv : A v = 0) : b v = 0 := by
  by_contra hb
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨M, hM⟩ := (hK.image b.continuous).bddAbove
  let r := max M (u (x + A y₀) - z) + 1
  let t := (r - b y₀) / b v
  have hbase : x + A (y₀ + t • v) = x + A y₀ := by simp [hv]
  have hheight : b (y₀ + t • v) = r := by
    simp only [map_add, map_smul, smul_eq_mul, t]
    field_simp
    ring
  have hy : y₀ + t • v ∈ affineEpigraphFiber Ω u x z A b := by
    refine ⟨by rw [hbase]; exact hy₀.1, ?_⟩
    rw [hbase, hheight]
    have hh := le_max_right M (u (x + A y₀) - z)
    dsimp [r]
    linarith
  have hh := hM (show b (y₀ + t • v) ∈ b '' affineEpigraphFiber Ω u x z A b from
    ⟨_, hy, rfl⟩)
  rw [hheight] at hh
  have hh' := le_max_left M (u (x + A y₀) - z)
  dsimp [r] at hh
  linarith

/- For an affine coordinate isomorphism compact fibers force injectivity of
its horizontal linear part. -/
theorem affineEpigraphFiber_injective {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {x : Space n} {z : ℝ} {A : E →L[ℝ] Space n}
    {b : E →L[ℝ] ℝ} (hK : IsCompact (affineEpigraphFiber Ω u x z A b))
    (hne : (affineEpigraphFiber Ω u x z A b).Nonempty)
    (hi : Function.Injective (fun y => (A y, b y))) : Function.Injective A := by
  intro v w hvw
  have hav : A (v - w) = 0 := by simpa [map_sub] using sub_eq_zero.mpr hvw
  have hb := affineEpigraphFiber_no_vertical hK hne hav
  have hbw : b v = b w := sub_eq_zero.mp (by simpa [map_sub] using hb)
  exact hi (Prod.ext hvw hbw)

/- Chain rule for the actual second differential of an affine epigraph slice. -/
theorem affineSlice_second {n : ℕ} {u : Space n → ℝ} {x : Space n} {z : ℝ}
    {A : E →L[ℝ] Space n} {b : E →L[ℝ] ℝ} {y : E}
    (hu : ContDiffAt ℝ ∞ u (x + A y)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => u (x + A q) - (z + b q))) y v w =
      fderiv ℝ (fderiv ℝ u) (x + A y) (A v) (A w) := by
  have he : fderiv ℝ (fun q => u (x + A q) - (z + b q)) =ᶠ[𝓝 y]
      (fun q => (fderiv ℝ u (x + A q)).comp A - b) := by
    have hne : ∀ᶠ q in 𝓝 y, DifferentiableAt ℝ u (x + A q) := by
      apply (continuous_const.add A.continuous).continuousAt.eventually
      have hh : ∀ᶠ p in 𝓝 (x + A y), ContDiffAt ℝ 1 u p :=
        (hu.of_le (by simp)).eventually (by simp)
      exact hh.mono (fun p hp => hp.differentiableAt (by simp))
    filter_upwards [hne] with q hq
    exact ((hq.hasFDerivAt.comp q (A.hasFDerivAt.const_add x)).sub
      (b.hasFDerivAt.const_add z)).fderiv
  rw [he.fderiv_eq]
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hc := (hd.comp y (A.hasFDerivAt.const_add x)).clm_comp (hasFDerivAt_const A y)
  have heq := (hc.sub_const b).fderiv
  simp only [Function.comp_def] at heq
  rw [heq]
  simp

/- An interior point of a convex sublevel is a strict sublevel point whenever
its actual Hessian is positive definite. -/
theorem sublevel_interior_strict [Nontrivial E] {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {z : E}
    (hz : z ∈ interior {y | y ∈ W ∧ F y ≤ 0})
    (hd : DifferentiableAt ℝ F z)
    (hH : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ F) z v v) : F z < 0 := by
  have hzK := interior_subset hz
  by_contra hn
  have hz0 : F z = 0 := le_antisymm hzK.2 (le_of_not_gt hn)
  have hnK : {y | y ∈ W ∧ F y ≤ 0} ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  have hm : IsLocalMax F z := by
    filter_upwards [hnK] with y hy
    simpa [hz0] using hy.2
  have hdz := hm.fderiv_eq_zero
  have he : F =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnK] with y hy
    have hh := convex_first_order hcv hzK.1 hy.1 hd
    simp only [hdz, zero_apply, hz0, sub_zero] at hh
    exact le_antisymm hy.2 hh
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hh := hH v hv
  rw [he.fderiv.fderiv_eq] at hh
  simp at hh

/- Convexity survives the actual affine slice and subtraction of its height. -/
theorem convexOn_affineSlice {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hcv : ConvexOn ℝ Ω u) (x : Space n) (z : ℝ)
    (A : E →L[ℝ] Space n) (b : E →L[ℝ] ℝ) :
    ConvexOn ℝ {y | x + A y ∈ Ω} (fun y => u (x + A y) - (z + b y)) := by
  let g : E →ᵃ[ℝ] Space n :=
    { toFun := fun y => x + A y
      linear := A.toLinearMap
      map_vadd' := by
        intro v p
        change x + A (p + v) = A p + (x + A v)
        rw [map_add]
        abel }
  have hc := hcv.comp_affineMap g
  have hb := (b.toLinearMap.concaveOn hc.1).add_const z
  have hh := hc.sub hb
  change ConvexOn ℝ {y | x + A y ∈ Ω} (fun y => u (x + A y) - (b y + z)) at hh
  simpa only [add_comm (b _) z] using hh

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- The literal inverse image of the original epigraph under affine coordinates. -/

theorem affine_coordinates_split {n : ℕ} (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (s : S) (y : E) :
    a + L (s, y) = ((a + L (s, 0)).1 + affineFiberHorizontal L y,
      (a + L (s, 0)).2 + affineFiberHeight L y) := by
  have hh : L (s, y) = L (s, 0) + L (0, y) := by rw [← map_add]; simp
  rw [hh]
  ext <;> simp [affineFiberHorizontal, affineFiberHeight, add_assoc]

theorem affineEpigraphPullback_fiber {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (s : S) :
    {y | (s, y) ∈ affineEpigraphPullback Ω u a L} =
      affineEpigraphFiber Ω u (a + L (s, 0)).1 (a + L (s, 0)).2
        (affineFiberHorizontal L) (affineFiberHeight L) := by
  ext y
  change ((a + L (s, y)).1 ∈ Ω ∧ u (a + L (s, y)).1 ≤ (a + L (s, y)).2) ↔ _
  rw [affine_coordinates_split a L s y]
  rfl

theorem affineFiberHorizontal_injective {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {a : Space n × ℝ} {L : (S × E) ≃L[ℝ] (Space n × ℝ)} {s : S}
    (hK : IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hne : {y | (s, y) ∈ affineEpigraphPullback Ω u a L}.Nonempty) :
    Function.Injective (affineFiberHorizontal L) := by
  rw [affineEpigraphPullback_fiber] at hK hne
  apply affineEpigraphFiber_injective hK hne
  intro v w hvw
  have hh : L (0, v) = L (0, w) := hvw
  exact congrArg Prod.snd (L.injective hh)

variable [CompleteSpace S]

/- The principal support-coordinate regularity assertion in tubes.tex:39–60,
for actual affine images of the standing epigraph, not abstract smooth bodies.
The transverse dimension is nonzero, as in the manuscript (m=n+1-k≥1). -/
theorem affineEpigraph_support_smooth [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ affineEpigraphPullback Ω u a L} q.2) (s, ℓ) ∧
    0 < supportValue {y | (s, y) ∈ affineEpigraphPullback Ω u a L} ℓ := by
  let W : Set (S × E) := {p | (a + L p).1 ∈ Ω}
  let F : S × E → ℝ := fun p => u (a + L p).1 - (a + L p).2
  have hbase : ContDiff ℝ ∞ (fun p : S × E => (a + L p).1) :=
    (contDiff_const.add L.contDiff).fst
  have hheight : ContDiff ℝ ∞ (fun p : S × E => (a + L p).2) :=
    (contDiff_const.add L.contDiff).snd
  have hW : IsOpen W := hΩ.preimage hbase.continuous
  have hF : ContDiffOn ℝ ∞ F W :=
    (hu.comp hbase.contDiffOn (fun _ h => h)).sub hheight.contDiffOn
  have hFu : ConvexOn ℝ Ω u :=
    convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hFeq (r : S) : (fun q => F (r, q)) = (fun q =>
      u ((a + L (r, 0)).1 + affineFiberHorizontal L q) -
        ((a + L (r, 0)).2 + affineFiberHeight L q)) := by
    funext q
    change u (a + L (r, q)).1 - (a + L (r, q)).2 = _
    rw [affine_coordinates_split a L r q]
  have hWeq (r : S) : {y | (r, y) ∈ W} =
      {y | (a + L (r, 0)).1 + affineFiberHorizontal L y ∈ Ω} := by
    ext y
    change (a + L (r, y)).1 ∈ Ω ↔ _
    rw [affine_coordinates_split a L r y]
    rfl
  have hcvF (r : S) : ConvexOn ℝ {y | (r, y) ∈ W} (fun y => F (r, y)) := by
    rw [hFeq, hWeq]
    exact convexOn_affineSlice hFu (a + L (r, 0)).1 (a + L (r, 0)).2
      (affineFiberHorizontal L) (affineFiberHeight L)
  have hKeq (r : S) : {y | (r, y) ∈ W ∧ F (r, y) ≤ 0} =
      {y | (r, y) ∈ affineEpigraphPullback Ω u a L} := by
    ext y
    simp only [W, F, affineEpigraphPullback, mem_ofPred_eq, sub_nonpos]
  have hK' : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by rw [hKeq]; exact hK s hs
  have hzero' : (0 : E) ∈ interior {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by
    rw [hKeq]; exact hzero s hs
  have hA : Function.Injective (affineFiberHorizontal L) :=
    affineFiberHorizontal_injective (hK s hs) ⟨0, interior_subset (hzero s hs)⟩
  have hH (y : E) (hy : (s, y) ∈ W) (v : E) (hv : v ≠ 0) :
      0 < fderiv ℝ (fderiv ℝ (fun q => F (s, q))) y v v := by
    have huc := hu.contDiffAt (hΩ.mem_nhds hy)
    have hx : (a + L (s, y)).1 = (a + L (s, 0)).1 + affineFiberHorizontal L y :=
      congrArg Prod.fst (affine_coordinates_split a L s y)
    rw [hFeq, affineSlice_second (by rw [← hx]; exact huc)]
    exact second_fderiv_pos (by rw [← hx]; exact huc)
      (by rw [← hx]; exact hp _ hy)
      (fun hh => hv (hA (by simpa using hh)))
  have hzW : (s, (0 : E)) ∈ W := (interior_subset hzero').1
  have hzF : F (s, 0) < 0 := sublevel_interior_strict (hcvF s) hzero'
    (((hF.contDiffAt (hW.mem_nhds hzW)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) (hH 0 hzW)
  have hh := contDiffAt_supportValue_fibers hB hW hF (fun r _ => hcvF r)
    hs hzW hzF hK' (fun y hy _ => hH y hy) hℓ
  refine ⟨?_, supportValue_pos (hK s hs) (hzero s hs) hℓ⟩
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  rw [hKeq]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GaussCoordinates
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/- The one-homogeneous extension of the literal spherical support function. -/

theorem homogeneousSupport_le {K : Set E} (hK : IsCompact K)
    {z : E} (hz : z ∈ K) (e : E) : inner ℝ e z ≤ homogeneousSupport K e :=
  le_supportValue hK hz (InnerProductSpace.toDual ℝ E e)

theorem homogeneousSupport_eq_of_max {K : Set E} {e z : E}
    (hz : z ∈ K) (hm : IsMaxOn (fun y => inner ℝ e y) K z) :
    homogeneousSupport K e = inner ℝ e z := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨inner ℝ e z, z, hz, rfl⟩
  · rintro r ⟨y, hy, rfl⟩; exact hm hy
  · intro r hr; exact ⟨inner ℝ e z, ⟨z, hz, rfl⟩, hr⟩

theorem gaussPoint_eq_of_max {K : Set E} (hK : IsCompact K)
    {e z : E} (hz : z ∈ K) (hm : homogeneousSupport K e = inner ℝ e z)
    (hd : DifferentiableAt ℝ (homogeneousSupport K) e) : gaussPoint K e = z := by
  have hl : IsLocalMin (fun q => homogeneousSupport K q - inner ℝ z q) e := by
    apply Eventually.of_forall
    intro q
    have hh := homogeneousSupport_le hK hz q
    simpa [real_inner_comm z, hm] using sub_nonneg.mpr hh
  have hder := hd.hasFDerivAt.sub (InnerProductSpace.toDual ℝ E z).hasFDerivAt
  have hh : fderiv ℝ (homogeneousSupport K) e - InnerProductSpace.toDual ℝ E z = 0 := by
    rw [← hder.fderiv]
    exact hl.fderiv_eq_zero
  unfold gaussPoint gradient
  rw [sub_eq_zero.mp hh]
  simp

theorem gaussPoint_mem_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {e : E} (hd : DifferentiableAt ℝ (homogeneousSupport K) e) :
    gaussPoint K e ∈ K ∧
      homogeneousSupport K e = inner ℝ e (gaussPoint K e) := by
  obtain ⟨z, hz, hm⟩ := hK.exists_isMaxOn hne (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  have he := homogeneousSupport_eq_of_max hz hm
  rw [gaussPoint_eq_of_max hK hz he hd]
  exact ⟨hz, he⟩

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

omit [CompleteSpace S] in
theorem contDiffAt_gaussPoint_fibers {K : S → Set E} {s : S} {e : E}
    (hh : ContDiffAt ℝ ∞ (fun p : S × E => homogeneousSupport (K p.1) p.2) (s,e)) :
    ContDiffAt ℝ ∞ (fun p : S × E => gaussPoint (K p.1) p.2) (s,e) := by
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt).comp
    (s,e) (contDiffAt_fiberGradient hh)

omit [CompleteSpace S] in
theorem contDiffAt_homogeneousSupport_fibers {K : S → Set E} {s : S} {e : E}
    (hh : ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) => supportValue (K q.1) q.2)
      (s, InnerProductSpace.toDual ℝ E e)) :
    ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) := by
  have hc : ContDiffAt ℝ ∞ (fun q : S × E =>
      (q.1, InnerProductSpace.toDual ℝ E q.2)) (s,e) :=
    contDiffAt_fst.prodMk
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.contDiff.contDiffAt.comp
        (s,e) contDiffAt_snd)
  have ht := hh.comp (s,e) hc
  exact ht

/- Actual smooth Gauss coordinates of each affine epigraph tube. -/

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
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeSecond
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
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma homogeneousSupport_fibers_angular {K : S → Set E} {x : S × E}
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x)
    (w : E) :
    fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x (0,w) =
      inner ℝ (gaussPoint (K x.1) x.2) w := by
  have hd := hH.hasFDerivAt.comp (f := fun y : E => (x.1,y)) x.2
    ((hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2))
  have he : fderiv ℝ (homogeneousSupport (K x.1)) x.2 w =
      fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x (0,w) := by
    change fderiv ℝ ((fun q : S × E => homogeneousSupport (K q.1) q.2) ∘
      (fun y : E => (x.1,y))) x.2 w = _
    rw [hd.fderiv]
    rfl
  rw [← he]
  simp [gaussPoint]

lemma homogeneousSupport_fibers_euler {K : S → Set E} {x : S × E}
    (hK : IsCompact (K x.1)) (hne : (K x.1).Nonempty)
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x) :
    homogeneousSupport (K x.1) x.2 = inner ℝ x.2 (gaussPoint (K x.1) x.2) := by
  exact (gaussPoint_mem_support hK hne
    (hH.comp (f := fun y : E => (x.1,y)) x.2 (differentiableAt_const x.1 |>.prodMk differentiableAt_id))).2

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

lemma second_fderiv_prod_left {H : S × E → ℝ} {s : S} {e : E}
    (hH : ContDiffAt ℝ ∞ H (s,e)) (v w : S) :
    fderiv ℝ (fderiv ℝ (fun y => H (y,e))) s v w =
      fderiv ℝ (fderiv ℝ H) (s,e) (v,0) (w,0) := by
  simpa using second_fderiv_affine_comp (ContinuousLinearMap.inl ℝ S E) (0,e) (by simpa using hH) v w

lemma second_fderiv_prod_right {H : S × E → ℝ} {s : S} {e : E}
    (hH : ContDiffAt ℝ ∞ H (s,e)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v w =
      fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,w) := by
  simpa using second_fderiv_affine_comp (ContinuousLinearMap.inr ℝ S E) (s,0) (by simpa using hH) v w

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeArea
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
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineEpigraph_support_jets {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ContDiffAt ℝ ∞ H (s,e) ∧ ContDiffAt ℝ ∞ Y (s,e) ∧
      H =ᶠ[𝓝 (s,e)] (fun q => inner ℝ q.2 (Y q)) ∧
      ∀ᶠ q in 𝓝 (s,e), ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w := by
  let K : S → Set E := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L}
  let H : S × E → ℝ := fun q => homogeneousSupport (K q.1) q.2
  let Y : S × E → E := fun q => gaussPoint (K q.1) q.2
  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz; apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  have hH : ContDiffAt ℝ ∞ H (s,e) := contDiffAt_homogeneousSupport_fibers
    (K := K) (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hs hℓ).1
  refine ⟨hH, contDiffAt_gaussPoint_fibers (K := K) hH, ?_, ?_⟩
  · filter_upwards [(continuous_fst.continuousAt.preimage_mem_nhds (hB.mem_nhds hs)),
      (hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqs hq
    exact homogeneousSupport_fibers_euler (hK q.1 hqs) ⟨0, interior_subset (hzero q.1 hqs)⟩
      (hq.differentiableAt (by norm_num))
  · filter_upwards [(hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact homogeneousSupport_fibers_angular (hq.differentiableAt (by norm_num))

/- Both matrices in the actual tube area formula are positive definite,
including an empty angular matrix. This is derived from the original graph,
not imposed as an additional curvature assumption. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatBlockCalculus
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

omit [DecidableEq ι] in
lemma contDiffAt_flatBlockHessian {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (v : ι → E) : ContDiffAt ℝ ∞ (fun y i j => flatBlockHessian f v y i j) x := by
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    contDiffAt_dirDeriv (contDiffAt_dirDeriv hf (v j)) (v i)))

lemma contDiffAt_adjugate_entries {A : E → Matrix ι ι ℝ} {x : E}
    (hA : ContDiffAt ℝ ∞ (fun y i j => A y i j) x) (i j : ι) :
    ContDiffAt ℝ ∞ (fun y => (A y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  change ContDiffAt ℝ ∞ (fun y => continuousDetRows (fun l m => (A y).updateRow j (Pi.single i 1) l m)) x
  apply (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x
  apply contDiffAt_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simpa only [Matrix.updateRow_self] using (contDiffAt_const (c := (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simp only [Matrix.updateRow_ne hl]
    exact (contDiffAt_pi.mp hA) l

lemma flatBlockHessian_adjugate_row_divergence {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (v : ι → E) (i : ι) :
    (∑ j, dirDeriv (v j) (fun y => (flatBlockHessian f v y).adjugate i j) x) = 0 := by
  let F : ι → E → ℝ := fun i => dirDeriv (v i) f
  have hF (l : ι) : ContDiffAt ℝ 2 (F l) x :=
    (contDiffAt_dirDeriv hf (v l)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he (y : E) : jacobianRows F v y = (flatBlockHessian f v y).transpose := rfl
  simpa only [he,← Matrix.adjugate_transpose,Matrix.transpose_apply,dirDeriv] using
    piola_identity F v x hF i

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeInvariantSmooth
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
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeFullRadiusMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y i j => tubeFullRadiusMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    (hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const))

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeBaseMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : Module.Basis ι ℝ S) :
    ContDiffAt ℝ ∞ (fun y i j => tubeBaseMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    ((hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const).neg))

omit [CompleteSpace E] in
lemma contDiffAt_tubeAngularDensity {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y => tubeAngularDensity H y b) q := by
  change ContDiffAt ℝ ∞ (fun y => ∑ i, (tubeFullRadiusMatrix H y b).adjugate i i) q
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_adjugate_entries (contDiffAt_tubeFullRadiusMatrix hH b) i i

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeChartConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma tube_dimension_equiv {n : ℕ}
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : Nonempty (Fin n ≃ ι ⊕ κ) := by
  let : FiniteDimensional ℝ S := Module.Finite.of_basis bS
  let : FiniteDimensional ℝ E := Module.Finite.of_basis bE.toBasis
  have hdim := L.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod,Module.finrank_prod,Module.finrank_eq_card_basis bS,
    Module.finrank_eq_card_basis bE.toBasis] at hdim
  simp only [Fintype.card_sum,Fintype.card_unit,Module.finrank_self,
    finrank_euclideanSpace,Fintype.card_fin] at hdim
  apply Fintype.card_eq.mp
  simp only [Fintype.card_fin,Fintype.card_sum]
  omega

/- An actual flat-normal coordinate injection with a continuous linear left
inverse. These chart data are produced from the frames, not postulated. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeWeightAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Literal invariant tube measure coefficient with respect to `ds dω`. -/

lemma tubeMeasureCoefficient_pos {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    0 < tubeMeasureCoefficient n h B Q :=
  mul_pos (Real.rpow_pos_of_pos hh _) (Real.sqrt_pos.2 (mul_pos hB hQ))

lemma tubeMeasureCoefficient_base {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    tubeMeasureCoefficient n h B Q*h/B =
      Real.exp (-(n : ℝ)*Real.log h - (((n : ℝ)+2)/2)*
        ((Real.log B-Real.log Q)/((n : ℝ)+2)-Real.log h)) := by
  have hN : (n : ℝ)+2 ≠ 0 := by positivity
  have hl : 0 < tubeMeasureCoefficient n h B Q*h/B :=
    div_pos (mul_pos (tubeMeasureCoefficient_pos hh hB hQ) hh) hB
  rw [← Real.exp_log hl]
  congr 1
  rw [Real.log_div (mul_ne_zero (tubeMeasureCoefficient_pos hh hB hQ).ne' hh.ne') hB.ne',
    Real.log_mul (tubeMeasureCoefficient_pos hh hB hQ).ne' hh.ne']
  unfold tubeMeasureCoefficient
  rw [Real.log_mul (Real.rpow_pos_of_pos hh _).ne' (Real.sqrt_pos.2 (mul_pos hB hQ)).ne',
    Real.log_rpow hh,Real.log_sqrt (mul_pos hB hQ).le,Real.log_mul hB.ne' hQ.ne']
  field_simp
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The manuscript's invariant density `μ₀` on base times unit normals. -/

omit [DecidableEq ι] [DecidableEq κ] in
lemma tube_dimension_eq {n : ℕ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : n = Fintype.card ι+Fintype.card κ := by
  obtain ⟨j⟩ := tube_dimension_equiv bS bE L
  simpa only [Fintype.card_fin,Fintype.card_sum] using Fintype.card_congr j

lemma invariantTubeF_unit {n : ℕ} (H : S × E → ℝ) (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hn : n = Fintype.card ι+Fintype.card κ) {q : S × E} (he : ‖q.2‖ = 1) :
    invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) q =
      (Real.log (tubeBaseMatrix H q bS).det-Real.log (tubeAngularDensity H q bE))/((n : ℝ)+2)-
        Real.log (H q) := by
  simp only [invariantTubeF,real_inner_self_eq_norm_sq,he,one_pow,Real.log_one,add_zero,hn,Nat.cast_add]
  ring

lemma tubeMeasureDensity_base {n : ℕ} {H : S × E → ℝ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hn : n = Fintype.card ι+Fintype.card κ) {q : S × E} (he : ‖q.2‖ = 1)
    (hh : 0 < H q) (hB : 0 < (tubeBaseMatrix H q bS).det) (hQ : 0 < tubeAngularDensity H q bE) :
    tubeMeasureDensity n H bS bE q*H q/(tubeBaseMatrix H q bS).det =
      Real.exp (-(n : ℝ)*Real.log (H q)-(((n : ℝ)+2)/2)*
        invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) q) := by
  rw [invariantTubeF_unit H bS bE hn he]
  exact tubeMeasureCoefficient_base hh hB hQ

omit [Fintype ι] [DecidableEq ι] in
lemma tubeBaseMatrix_eq_slice [CompleteSpace E] {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S) :
    tubeBaseMatrix H q bS = -flatBlockHessian (fun s => H (s,q.2)) bS q.1 := by
  ext i j
  change -fderiv ℝ (fderiv ℝ H) q (bS i,0) (bS j,0) =
    -dirDeriv (bS i) (dirDeriv (bS j) (fun s => H (s,q.2))) q.1
  have hs : ContDiffAt ℝ ∞ (fun s => H (s,q.2)) q.1 := hH.comp q.1 (contDiffAt_id.prodMk contDiffAt_const)
  rw [dirDeriv_eq_second hs]
  exact congrArg Neg.neg (second_fderiv_prod_left (s := q.1) (e := q.2) hH (bS i) (bS j)).symm

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
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatTubeEuler
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
  {ι κ : Type*}

lemma flatBlockHessian_neg (φ : E → ℝ) (v : ι → E) (x : E) :
    flatBlockHessian (fun y => -φ y) v x = -flatBlockHessian φ v x := by
  ext i j
  have he : dirDeriv (v j) (fun y => -φ y) = fun y => -dirDeriv (v j) φ y := by
    funext y
    simp [dirDeriv]
  change fderiv ℝ (dirDeriv (v j) (fun y => -φ y)) x (v i) =
    -fderiv ℝ (dirDeriv (v j) φ) x (v i)
  rw [he,fderiv_fun_neg]
  rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatLogEuler
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
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma matrix_adjugate_entry {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) (i j : ι) :
    A.adjugate i j = A.det * A⁻¹ i j := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ hA,one_mul]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_InverseTracePullback
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dirDeriv_affine_pullback {f : F → ℝ} (q₀ : F) (J : E →L[ℝ] F) {x : E}
    (hf : DifferentiableAt ℝ f (q₀+J x)) (v : E) :
    dirDeriv v (fun y => f (q₀+J y)) x = dirDeriv (J v) f (q₀+J x) := by
  change fderiv ℝ (fun y => f (q₀+J y)) x v = fderiv ℝ f (q₀+J x) (J v)
  exact congrArg (fun l : E →L[ℝ] ℝ => l v)
    ((hf.hasFDerivAt).comp x (J.hasFDerivAt.const_add q₀)).fderiv

lemma flatInversePair_affine_pullback {f g : F → ℝ} (q₀ : F) (J : E →L[ℝ] F) {x : E}
    (hf : DifferentiableAt ℝ f (q₀+J x)) (hg : DifferentiableAt ℝ g (q₀+J x))
    (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInversePair A v (fun y => f (q₀+J y)) (fun y => g (q₀+J y)) x =
      flatInversePair A (fun i => J (v i)) f g (q₀+J x) := by
  simp only [flatInversePair,dirDeriv_affine_pullback q₀ J hf,dirDeriv_affine_pullback q₀ J hg]

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
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonTensor
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

/- The penultimate Newton tensor, defined polynomially, not using an inverse. -/

theorem contDiff_newtonTensor_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => newtonTensor (Matrix.of A) i j) := by
  exact ((contDiff_adjugate_entry i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JointAngularCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Partial fiber gradient, represented through the derivative of the joint scalar. -/

lemma jointAngularGradient_eq_slice {g : S × E → ℝ} {q : S × E}
    (hg : DifferentiableAt ℝ g q) :
    jointAngularGradient g q = gradient (fun y => g (q.1,y)) q.2 := by
  have hc : HasFDerivAt (fun y : E => (q.1,y)) (ContinuousLinearMap.inr ℝ S E) q.2 := by
    convert (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2) using 1 <;> ext y <;> rfl
  have hd : HasFDerivAt (fun y => g (q.1,y))
      ((fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ S E)) q.2 := hg.hasFDerivAt.comp q.2 hc
  change (InnerProductSpace.toDual ℝ E).symm _ = (InnerProductSpace.toDual ℝ E).symm _
  rw [hd.fderiv]

lemma contDiffAt_jointAngularGradient {g : S × E → ℝ} {q : S × E}
    (hg : ContDiffAt ℝ ∞ g q) : ContDiffAt ℝ ∞ (jointAngularGradient g) q := by
  apply (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp q
  exact (hg.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const

/- Partial angular derivative of the gradient, represented without slice-dependent differentiation. -/

lemma jointNewtonTensor_eq_slice {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    jointNewtonTensor H b q = supportNewtonTensor b (fun y => H (q.1,y)) q.2 := by
  unfold jointNewtonTensor supportNewtonTensor
  congr 2
  ext i j
  exact (second_fderiv_prod_right (s := q.1) (e := q.2) hH (b i) (b j)).symm

lemma contDiffAt_jointNewtonTensor {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (jointNewtonTensor H b) q := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _
  unfold jointNewtonTensor bilinearOfMatrix
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((contDiff_newtonTensor_entry i j).contDiffAt.comp q (contDiffAt_tubeFullRadiusMatrix hH b)).smul contDiffAt_const

lemma continuousOn_sliceAngularGradient {U : Set (S × E)} {g : S × E → ℝ}
    (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) :
    ContinuousOn (fun q : S × E => gradient (fun y => g (q.1,y)) q.2) U := by
  have hc : ContinuousOn (jointAngularGradient g) U :=
    fun q hq => (contDiffAt_jointAngularGradient (hg q hq)).continuousAt.continuousWithinAt
  apply hc.congr
  intro q hq
  exact (jointAngularGradient_eq_slice ((hg q hq).differentiableAt (by simp))).symm

lemma continuousOn_sliceNewtonTensor {U : Set (S × E)} {H : S × E → ℝ}
    (hH : ∀ q ∈ U, ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContinuousOn (fun q : S × E => supportNewtonTensor b (fun y => H (q.1,y)) q.2) U := by
  have hc : ContinuousOn (jointNewtonTensor H b) U :=
    fun q hq => (contDiffAt_jointNewtonTensor (hH q hq) b).continuousAt.continuousWithinAt
  apply hc.congr
  intro q hq
  exact (jointNewtonTensor_eq_slice (hH q hq) b).symm

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
-- module Solutions.OAIQ22_AB.AffineBernstein_JointTubeMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section JointTubeMetrics
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] in
lemma flatInversePair_prod_left {f g : S × E → ℝ} {s : S} {e : E}
    (hf : DifferentiableAt ℝ f (s,e)) (hg : DifferentiableAt ℝ g (s,e))
    (A : Matrix ι ι ℝ) (v : ι → S) :
    flatInversePair A v (fun y => f (y,e)) (fun y => g (y,e)) s =
      flatInversePair A (fun i => (v i,(0:E))) f g (s,e) := by
  simpa using flatInversePair_affine_pullback (0,e) (ContinuousLinearMap.inl ℝ S E)
    (by simpa using hf) (by simpa using hg) A v

omit [CompleteSpace E] in
lemma contDiffAt_tubeBasePair {H f g : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hf : ContDiffAt ℝ ∞ f q) (hg : ContDiffAt ℝ ∞ g q)
    (b : Module.Basis ι ℝ S) (hd : (tubeBaseMatrix H q b).det ≠ 0) :
    ContDiffAt ℝ ∞ (tubeBasePair H b f g) q := by
  apply hH.mul
  unfold flatInversePair
  exact ContDiffAt.sum fun j _ => ContDiffAt.sum fun i _ =>
    ((contDiffAt_inverse_matrix_entry_param (contDiffAt_tubeBaseMatrix hH b) hd i j).mul
      (contDiffAt_dirDeriv hf _)).mul (contDiffAt_dirDeriv hg _)

omit [CompleteSpace E] in
lemma continuousAt_tubeMeasureDensity {n : ℕ} {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hh : 0 < H q) : ContinuousAt (tubeMeasureDensity n H bS bE) q := by
  unfold tubeMeasureDensity tubeMeasureCoefficient
  apply (hH.continuousAt.rpow_const (Or.inl hh.ne')).mul
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp q
    (contDiffAt_tubeBaseMatrix hH bS)).continuousAt.mul
      (contDiffAt_tubeAngularDensity hH bE).continuousAt).sqrt

lemma continuousOn_tubeAngularPair {U : Set (S × E)} {H f g : S × E → ℝ}
    (hH : ∀ q ∈ U, ContDiffAt ℝ ∞ H q) (hf : ∀ q ∈ U, ContDiffAt ℝ ∞ f q)
    (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hQ : ∀ q ∈ U, tubeAngularDensity H q b ≠ 0) :
    ContinuousOn (tubeAngularPair H b f g) U := by
  have ht (g : S × E → ℝ) (hg : ∀ q ∈ U, ContDiffAt ℝ ∞ g q) :
      ContinuousOn (fun q : S × E => tangentProjection q.2 (gradient (fun y => g (q.1,y)) q.2)) U := by
    have hd := continuousOn_sliceAngularGradient hg
    exact hd.sub ((((continuous_snd.continuousOn).inner hd)).smul continuous_snd.continuousOn)
  have hcH : ContinuousOn H U := fun q hq => (hH q hq).continuousAt.continuousWithinAt
  have hcQ : ContinuousOn (fun q => tubeAngularDensity H q b) U :=
    fun q hq => (contDiffAt_tubeAngularDensity (hH q hq) b).continuousAt.continuousWithinAt
  exact (hcH.div hcQ hQ).mul
    (((continuousOn_sliceNewtonTensor hH b).clm_apply (ht f hf)).clm_apply (ht g hg))

end JointTubeMetrics

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
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeCompactIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section
variable {S T : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [TopologicalSpace T] [T2Space T] [CompactSpace T] [SecondCountableTopology T]
  [MeasurableSpace T] [BorelSpace T]
  {μ : Measure S} {ν : Measure T} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasure ν]
lemma integrable_joint_compact_mul {f : S × T → ℝ} {σ : S → ℝ}
    (hσ : Continuous σ) (hc : HasCompactSupport σ)
    (hf : ContinuousOn f (tsupport σ ×ˢ (Set.univ : Set T))) :
    Integrable (fun q : S × T => f q*σ q.1) (μ.prod ν) := by
  have hs : Function.support (fun q : S × T => f q*σ q.1) ⊆ tsupport σ ×ˢ (Set.univ : Set T) := by
    intro q hq
    refine ⟨?_,Set.mem_univ _⟩
    by_contra hn
    simp [image_eq_zero_of_notMem_tsupport hn] at hq
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact ContinuousOn.integrableOn_compact (hc.isCompact.prod isCompact_univ)
    (hf.mul (hσ.comp continuous_fst).continuousOn)
end
open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

omit [MeasurableSpace S] [BorelSpace S]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma continuous_tubeLift : Continuous (tubeLift (S := S) (E := E)) :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

omit [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tubeLift_mem {D : Set S} (q : S × sphere (0:E) 1) (h : q.1 ∈ D) :
    tubeLift q ∈ tubeOpenSet D := by
  refine ⟨h,?_⟩
  have hh : ‖(q.2:E)‖ = 1 := mem_sphere_zero_iff_norm.1 q.2.property
  intro hz
  change (q.2:E) = 0 at hz
  simp [hz] at hh

lemma integrable_tube_compact_mul {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*g (tubeLift q)*σ q.1)
      (μ.prod (volume.toSphere : Measure (sphere (0:E) 1))) := by
  apply integrable_joint_compact_mul hσ hc
  exact (hM.mul hg).comp continuous_tubeLift.continuousOn
    (fun q hq => tubeLift_mem q (hσD hq.1))

lemma integrable_tube_compact_sq {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1^2*g (tubeLift q))
      (μ.prod (volume.toSphere : Measure (sphere (0:E) 1))) := by
  have hh := integrable_tube_compact_mul (μ := μ) hσ hc hσD hM
    (hg.mul (hσ.comp continuous_fst).continuousOn)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  simp only [tubeLift,Pi.mul_apply,Function.comp_apply]
  ring

/- The unrestricted product integral of a cutoff times a tube coefficient. -/

lemma tubeIntegral_add {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hf : ContinuousOn f (tubeOpenSet D))
    (hg : ContinuousOn g (tubeOpenSet D)) :
    tubeIntegral μ M σ (fun q => f q+g q) = tubeIntegral μ M σ f+tubeIntegral μ M σ g := by
  have hi (f) (hf : ContinuousOn f (tubeOpenSet D)) :
      Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*f (tubeLift q)) (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hσD hM hf using 1
    all_goals try with_reducible_and_instances rfl
    ext q; ring
  simp only [tubeIntegral,mul_add]
  exact integral_add (hi f hf) (hi g hg)

omit [NormedAddCommGroup S] [BorelSpace S] [μ.IsAddHaarMeasure] in
lemma tubeIntegral_smul (M f : S × E → ℝ) (σ : S → ℝ) (c : ℝ) :
    tubeIntegral μ M σ (fun q => c*f q) = c*tubeIntegral μ M σ f := by
  simp only [tubeIntegral]
  simp_rw [show ∀ q : S × sphere (0:E) 1,
    M (tubeLift q)*σ q.1*(c*f (tubeLift q)) = c*(M (tubeLift q)*σ q.1*f (tubeLift q)) by intro q; ring]
  exact integral_const_mul _ _

section
variable [NormedSpace ℝ S] [FiniteDimensional ℝ S]

lemma tubeIntegral_base {M g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hg : ContinuousOn g (tubeOpenSet D)) :
    tubeIntegral μ M σ g =
      ∫ e : sphere (0:E) 1, (∫ s, M (s,e)*σ s*g (s,e) ∂μ) ∂volume.toSphere := by
  have hi : Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*g (tubeLift q)) (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hσD hM hg using 1
    all_goals try with_reducible_and_instances rfl
    ext q; ring
  exact (integral_prod _ hi).trans (integral_integral_swap hi)

end

omit [MeasurableSpace S] [BorelSpace S] in
lemma tsupport_sq_subset {σ : S → ℝ} : tsupport (fun s => σ s^2) ⊆ tsupport σ := by
  simpa only [pow_two] using (tsupport_mul_subset_left (f := σ) (g := σ))

omit [MeasurableSpace S] [BorelSpace S] in
lemma compactSupport_sq {σ : S → ℝ} (hc : HasCompactSupport σ) :
    HasCompactSupport (fun s => σ s^2) :=
  hc.isCompact.of_isClosed_subset isClosed_closure tsupport_sq_subset

lemma integrable_tube_supported {f : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hf : ContinuousOn f (tubeOpenSet D))
    (hz : ∀ s ∉ tsupport σ, ∀ e : E, f (s,e) = 0) :
    Integrable (fun q : S × sphere (0:E) 1 => f (tubeLift q)) (μ.prod volume.toSphere) := by
  have hs : Function.support (fun q : S × sphere (0:E) 1 => f (tubeLift q)) ⊆
      tsupport σ ×ˢ (Set.univ : Set (sphere (0:E) 1)) := by
    intro q hq
    refine ⟨?_,Set.mem_univ _⟩
    by_contra hn
    exact hq (hz q.1 hn q.2)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  exact ContinuousOn.integrableOn_compact (hc.isCompact.prod isCompact_univ)
    (hf.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q (hσD hq.1)))

lemma tubeIntegral_linearCombination {M f g : S × E → ℝ} {σ : S → ℝ} {D : Set S}
    (hσ : Continuous σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (hM : ContinuousOn M (tubeOpenSet D)) (hf : ContinuousOn f (tubeOpenSet D))
    (hg : ContinuousOn g (tubeOpenSet D)) (a b : ℝ) :
    tubeIntegral μ M σ (fun q => a*f q+b*g q) = a*tubeIntegral μ M σ f+b*tubeIntegral μ M σ g := by
  calc
    _ = tubeIntegral μ M σ (fun q => a*f q)+tubeIntegral μ M σ (fun q => b*g q) := by
      exact tubeIntegral_add hσ hc hσD hM (continuousOn_const.mul hf) (continuousOn_const.mul hg)
    _ = _ := by rw [tubeIntegral_smul,tubeIntegral_smul]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BaseWeightedIBP
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiffAt_flatCofactorFlux {f β g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hβ : ContDiffAt ℝ ∞ β x)
    (hg : ContDiffAt ℝ ∞ g x) (v : ι → E) (j : ι) :
    ContDiffAt ℝ ∞ (flatCofactorFlux f v β g j) x := by
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_adjugate_entries (contDiffAt_flatBlockHessian hf v) i j).mul hβ).mul
    (contDiffAt_dirDeriv hg (v i))

lemma flatCofactorFlux_divergence {f β g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hβ : ContDiffAt ℝ ∞ β x)
    (hg : ContDiffAt ℝ ∞ g x) (v : ι → E) :
    (∑ j, dirDeriv (v j) (flatCofactorFlux f v β g j) x) =
      β x * flatCofactorTrace f v g x + flatCofactorPair f v β g x := by
  let C := fun i j y => (flatBlockHessian f v y).adjugate i j
  have hC (i j : ι) : ContDiffAt ℝ ∞ (C i j) x :=
    contDiffAt_adjugate_entries (contDiffAt_flatBlockHessian hf v) i j
  have hd (j : ι) : dirDeriv (v j) (flatCofactorFlux f v β g j) x =
      ∑ i, (dirDeriv (v j) (C i j) x * (β x*dirDeriv (v i) g x) +
        C i j x * dirDeriv (v j) β x * dirDeriv (v i) g x +
        β x * (C i j x * dirDeriv (v j) (dirDeriv (v i) g) x)) := by
    change dirDeriv (v j) (fun y => ∑ i, C i j y*β y*dirDeriv (v i) g y) x = _
    rw [dirDeriv_sum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [dirDeriv_mul (((hC i j).mul hβ).differentiableAt (by simp))
        ((contDiffAt_dirDeriv hg (v i)).differentiableAt (by simp)),
        dirDeriv_mul ((hC i j).differentiableAt (by simp)) (hβ.differentiableAt (by simp))]
      change (dirDeriv (v j) (C i j) x*β x+C i j x*dirDeriv (v j) β x)*dirDeriv (v i) g x +
        (C i j x*β x)*dirDeriv (v j) (dirDeriv (v i) g) x = _
      ring
    · intro i
      exact (((hC i j).mul hβ).mul (contDiffAt_dirDeriv hg (v i))).differentiableAt (by simp)
  have hz : (∑ j, ∑ i, dirDeriv (v j) (C i j) x * (β x*dirDeriv (v i) g x)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have hrow (i : ι) : (∑ j, dirDeriv (v j) (C i j) x) = 0 :=
      flatBlockHessian_adjugate_row_divergence hf v i
    simp only [hrow,zero_mul,Finset.sum_const_zero]
  simp only [hd,Finset.sum_add_distrib,hz,zero_add,flatCofactorTrace,flatCofactorPair,
    ← Finset.mul_sum]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BaseWeightedIntegral
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
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrable_local_mul_test {f σ : E → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x) :
    Integrable (fun x => f x*σ x) μ := by
  apply integrable_of_support_subset_compact hc.isCompact
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport σ))
  have hfc : ContinuousOn f (tsupport σ) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  exact hfc.mul hσ.continuous.continuousOn

lemma integrable_local_mul_dirDeriv_test {f σ : E → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x) (v : E) :
    Integrable (fun x => f x*dirDeriv v σ x) μ := by
  have hs : tsupport (dirDeriv v σ) ⊆ tsupport σ := tsupport_fderiv_apply_subset ℝ v
  exact integrable_local_mul_test (contDiff_dirDeriv hσ v)
    (hc.of_isClosed_subset (isClosed_tsupport _) hs) (fun x hx => hf x (hs hx))

variable [FiniteDimensional ℝ E]

/- Base cofactor integration by parts. Only smoothness near the compact test
support is needed; no boundary regularity or global coefficient extension is assumed. -/
theorem integral_flatCofactor_trace {f β g σ : E → ℝ} (v : ι → E)
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x)
    (hβ : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ β x)
    (hg : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ g x) :
    (∫ x, (β x*flatCofactorTrace f v g x+flatCofactorPair f v β g x)*σ x ∂μ) =
      -(∫ x, β x*flatCofactorPair f v σ g x ∂μ) := by
  let J := flatCofactorFlux f v β g
  have hJ (j : ι) (x : E) (hx : x ∈ tsupport σ) : ContDiffAt ℝ ∞ (J j) x :=
    contDiffAt_flatCofactorFlux (hf x hx) (hβ x hx) (hg x hx) v j
  have hi (j : ι) : Integrable (fun x => dirDeriv (v j) (J j) x*σ x) μ :=
    integrable_local_mul_test hσ hc (fun x hx => contDiffAt_dirDeriv (hJ j x hx) (v j))
  have hi' (j : ι) : Integrable (fun x => J j x*dirDeriv (v j) σ x) μ :=
    integrable_local_mul_dirDeriv_test hσ hc (hJ j) (v j)
  have hibp (j : ι) : (∫ x, dirDeriv (v j) (J j) x*σ x ∂μ) =
      -(∫ x, J j x*dirDeriv (v j) σ x ∂μ) := by
    have hh := integral_mul_fderiv_compact (μ := μ) (J j) σ (v j)
      (fun x hx => (hJ j x hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
      (hσ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hc
    change (∫ x, J j x*dirDeriv (v j) σ x ∂μ) = -(∫ x, dirDeriv (v j) (J j) x*σ x ∂μ) at hh
    linarith
  calc
    _ = ∫ x, ∑ j, dirDeriv (v j) (J j) x*σ x ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [← Finset.sum_mul]
      by_cases hx : x ∈ tsupport σ
      · rw [flatCofactorFlux_divergence (hf x hx) (hβ x hx) (hg x hx)]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    _ = ∑ j, ∫ x, dirDeriv (v j) (J j) x*σ x ∂μ := integral_finsetSum _ (fun j _ => hi j)
    _ = -(∑ j, ∫ x, J j x*dirDeriv (v j) σ x ∂μ) := by simp only [hibp,Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ j, J j x*dirDeriv (v j) σ x ∂μ) := by rw [integral_finsetSum _ (fun j _ => hi' j)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [J,flatCofactorFlux,flatCofactorPair,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BaseExponentialIBP
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
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dirDeriv_exp_linear_combination {P F : E → ℝ} {x : E}
    (hP : DifferentiableAt ℝ P x) (hF : DifferentiableAt ℝ F x) (a b : ℝ) (v : E) :
    dirDeriv v (fun y => Real.exp (a*P y+b*F y)) x =
      Real.exp (a*P x+b*F x)*(a*dirDeriv v P x+b*dirDeriv v F x) := by
  have hh : HasFDerivAt (fun y => Real.exp (a*P y+b*F y))
      (Real.exp (a*P x+b*F x) • (a • fderiv ℝ P x+b • fderiv ℝ F x)) x :=
    ((hP.hasFDerivAt.const_mul a).add (hF.hasFDerivAt.const_mul b)).exp
  change fderiv ℝ _ x v = _
  rw [hh.fderiv]
  rfl

lemma flatCofactorPair_exp {P F : E → ℝ} {x : E}
    (hP : DifferentiableAt ℝ P x) (hF : DifferentiableAt ℝ F x)
    (f g : E → ℝ) (v : ι → E) (a b : ℝ) :
    flatCofactorPair f v (fun y => Real.exp (a*P y+b*F y)) g x =
      Real.exp (a*P x+b*F x)*(a*flatCofactorPair f v P g x+b*flatCofactorPair f v F g x) := by
  simp only [flatCofactorPair,dirDeriv_exp_linear_combination hP hF]
  simp only [mul_add,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma flatCofactorPair_test_square {σ : E → ℝ} {x : E}
    (hσ : DifferentiableAt ℝ σ x) (f g : E → ℝ) (v : ι → E) :
    flatCofactorPair f v (fun y => σ y*σ y) g x = 2*σ x*flatCofactorPair f v σ g x := by
  simp only [flatCofactorPair,dirDeriv_mul hσ hσ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/- Base identity for the exact exponential weight and a squared compact test.
It is valid without global smooth extensions of the support function. -/
theorem integral_flatCofactor_exp_square {f P F g σ : E → ℝ} (v : ι → E)
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x)
    (hP : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ P x)
    (hF : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ F x)
    (hg : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ g x) (a b : ℝ) :
    (∫ x, Real.exp (a*P x+b*F x)*σ x^2 *
      (flatCofactorTrace f v g x+a*flatCofactorPair f v P g x+b*flatCofactorPair f v F g x) ∂μ) =
      -2*(∫ x, Real.exp (a*P x+b*F x)*σ x*flatCofactorPair f v σ g x ∂μ) := by
  have hs : tsupport (fun x => σ x*σ x) ⊆ tsupport σ := tsupport_mul_subset_left
  have hh := integral_flatCofactor_trace (μ := μ) v (hσ.mul hσ) (hc.mul_left)
    (fun x hx => hf x (hs hx))
    (fun x hx => (((contDiffAt_const.mul (hP x (hs hx))).add
      (contDiffAt_const.mul (hF x (hs hx)))).exp))
    (fun x hx => hg x (hs hx)) (β := fun x => Real.exp (a*P x+b*F x))
  have hleft : (∫ x, (Real.exp (a*P x+b*F x)*flatCofactorTrace f v g x+
      flatCofactorPair f v (fun y => Real.exp (a*P y+b*F y)) g x)*(σ x*σ x) ∂μ) =
      (∫ x, Real.exp (a*P x+b*F x)*σ x^2 *
        (flatCofactorTrace f v g x+a*flatCofactorPair f v P g x+b*flatCofactorPair f v F g x) ∂μ) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : x ∈ tsupport σ
    · rw [flatCofactorPair_exp ((hP x hx).differentiableAt (by simp))
        ((hF x hx).differentiableAt (by simp))]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [hleft] at hh
  rw [hh]
  rw [← integral_const_mul]
  rw [← integral_neg]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [flatCofactorPair_test_square (hσ.differentiable (by simp) x)]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualWeightedBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineEpigraph_tube_base_smooth {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE δ
    ContDiffOn ℝ ∞ (fun s => H (s,e)) D ∧
    ContDiffOn ℝ ∞ (fun s => P (s,e)) D ∧
    ContDiffOn ℝ ∞ (fun s => F (s,e)) D := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hH (s : S) (hs : s ∈ D) : ContDiffAt ℝ ∞ H (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  refine ⟨?_,?_,?_⟩
  · intro s hs
    exact ((hH s hs).comp s (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · intro s hs
    have hp' := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he bS bE
    exact (((hH s hs).log hp'.2.2.ne').comp s (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · intro s hs
    exact ((affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hs he bS bE δ).comp s
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt

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

lemma flatInversePair_symm (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (v : ι → E) (f g : E → ℝ) (x : E) :
    flatInversePair A v f g x = flatInversePair A v g f x := by
  have hi : A⁻¹.IsSymm := by rw [Matrix.IsSymm,Matrix.transpose_nonsing_inv,hA.eq]
  unfold flatInversePair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hi.apply i j]
  ring

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

lemma flat_log_hessian_trace {W : Set E} (hW : IsOpen W) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ W) (hpos : ∀ y ∈ W, 0 < φ y)
    {x : E} (hx : x ∈ W) (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInverseTrace A v φ x = φ x *
      (flatInverseTrace A v (fun y => Real.log (φ y)) x +
        flatInversePair A v (fun y => Real.log (φ y)) (fun y => Real.log (φ y)) x) := by
  unfold flatInverseTrace flatInversePair
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [log_second_identity hW hφ hpos hx]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatFEquation
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
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma flatInverseTrace_neg_hessian (φ : E → ℝ) (v : ι → E) (x : E)
    (hd : (-flatBlockHessian φ v x).det ≠ 0) :
    flatInverseTrace (-flatBlockHessian φ v x) v φ x = -(Fintype.card ι : ℝ) := by
  have hh := matrix_inverse_contraction_self hd
  simp only [Matrix.neg_apply,mul_neg,Finset.sum_neg_distrib] at hh
  change -flatInverseTrace (-flatBlockHessian φ v x) v φ x = _ at hh
  linarith

/- The exact local flat-chart f equation. At the center of the flat normal
chart its angular terms equal the spherical covariant terms; no derivative
of a determinant or scalar density has been omitted. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BaseLogIdentity
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

lemma flatCofactorTrace_eq_det_mul {f : E → ℝ} (v : ι → E) (g : E → ℝ) (x : E)
    (hd : (flatBlockHessian f v x).det ≠ 0) :
    flatCofactorTrace f v g x = (flatBlockHessian f v x).det *
      flatInverseTrace (flatBlockHessian f v x) v g x := by
  simp only [flatCofactorTrace,flatInverseTrace,matrix_adjugate_entry hd,Finset.mul_sum,mul_assoc]

lemma flatCofactorPair_eq_det_mul {f : E → ℝ} (v : ι → E) (g h : E → ℝ) (x : E)
    (hd : (flatBlockHessian f v x).det ≠ 0) :
    flatCofactorPair f v g h x = (flatBlockHessian f v x).det *
      flatInversePair (flatBlockHessian f v x) v g h x := by
  simp only [flatCofactorPair,flatInversePair,matrix_adjugate_entry hd,Finset.mul_sum,mul_assoc]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma flatCofactorTrace_log {D : Set E} (hD : IsOpen D) {H : E → ℝ}
    (hH : ContDiffOn ℝ ∞ H D) (hpos : ∀ x ∈ D, 0 < H x)
    {x : E} (hx : x ∈ D) (v : ι → E) (hd : (-flatBlockHessian H v x).det ≠ 0) :
    flatCofactorTrace (fun y => -H y) v (fun y => Real.log (H y)) x =
      -((-flatBlockHessian H v x).det/H x*(Fintype.card ι : ℝ)) -
      flatCofactorPair (fun y => -H y) v (fun y => Real.log (H y)) (fun y => Real.log (H y)) x := by
  have hd' : (flatBlockHessian (fun y => -H y) v x).det ≠ 0 := by rwa [flatBlockHessian_neg]
  rw [flatCofactorTrace_eq_det_mul v _ _ hd',flatCofactorPair_eq_det_mul v _ _ _ hd',flatBlockHessian_neg]
  have hh := flat_log_hessian_trace hD hH hpos hx (-flatBlockHessian H v x) v
  rw [flatInverseTrace_neg_hessian _ _ _ hd] at hh
  have hHx := (hpos x hx).ne'
  apply (mul_left_cancel₀ hHx)
  have hm := congrArg (fun t : ℝ => (-flatBlockHessian H v x).det*t) hh
  field_simp
  nlinarith [hm]

variable {μ : Measure E} [μ.IsAddHaarMeasure]

/- Pointwise logarithmic Hessian identity plus genuine base integration by
parts gives the source p-identity. Its density is exactly `W detB/H`. -/
theorem integral_base_log_identity {D : Set E} (hD : IsOpen D) {H F σ : E → ℝ}
    (hH : ContDiffOn ℝ ∞ H D) (hF : ContDiffOn ℝ ∞ F D)
    (hpos : ∀ x ∈ D, 0 < H x) (v : ι → E)
    (hd : ∀ x ∈ D, (-flatBlockHessian H v x).det ≠ 0)
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (n c : ℝ) :
    let K := fun x => -H x
    let P := fun x => Real.log (H x)
    let W := fun x => Real.exp (-n*P x-c*F x)
    (∫ x, W x*σ x^2 *
      (((-flatBlockHessian H v x).det/H x)*(Fintype.card ι : ℝ)+
        (n+1)*flatCofactorPair K v P P x+c*flatCofactorPair K v F P x) ∂μ) =
      2*(∫ x, W x*σ x*flatCofactorPair K v σ P x ∂μ) := by
  dsimp only
  let P := fun x => Real.log (H x)
  have hP : ContDiffOn ℝ ∞ P D := hH.log (fun x hx => (hpos x hx).ne')
  have hh := integral_flatCofactor_exp_square (μ := μ) v hσ hc
    (fun x hx => (hH.contDiffAt (hD.mem_nhds (hσD hx))).neg)
    (fun x hx => hP.contDiffAt (hD.mem_nhds (hσD hx)))
    (fun x hx => hF.contDiffAt (hD.mem_nhds (hσD hx)))
    (fun x hx => hP.contDiffAt (hD.mem_nhds (hσD hx))) (-n) (-c)
  simp only [neg_mul,← sub_eq_add_neg] at hh
  have heq : (∫ x, Real.exp (-n*P x-c*F x)*σ x^2 *
      (((-flatBlockHessian H v x).det/H x)*(Fintype.card ι : ℝ)+
        (n+1)*flatCofactorPair (fun y => -H y) v P P x+
        c*flatCofactorPair (fun y => -H y) v F P x) ∂μ) =
    -(∫ x, Real.exp (-n*P x-c*F x)*σ x^2 *
      (flatCofactorTrace (fun y => -H y) v P x-n*flatCofactorPair (fun y => -H y) v P P x-
        c*flatCofactorPair (fun y => -H y) v F P x) ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : x ∈ tsupport σ
    · rw [flatCofactorTrace_log hD hH hpos (hσD hx) v (hd x (hσD hx))]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hx,zero_pow two_ne_zero,mul_zero,zero_mul,neg_zero]
  rw [heq]
  simp only [neg_mul]
  rw [hh]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeMetricPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tubeBasePair_nonneg {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hh : 0 ≤ H q) (hB : (tubeBaseMatrix H q b).PosDef) (f : S × E → ℝ) :
    0 ≤ tubeBasePair H b f f q := mul_nonneg hh (inverseMatrixPair_self_nonneg hB _)

lemma tubeBasePair_cauchy {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hB : (tubeBaseMatrix H q b).PosDef) (f g : S × E → ℝ) :
    tubeBasePair H b f g q^2 ≤ tubeBasePair H b f f q*tubeBasePair H b g g q := by
  have hc := mul_le_mul_of_nonneg_left (inverseMatrixPair_cauchy hB
    (fun i => dirDeriv (b i,(0:E)) f q) (fun i => dirDeriv (b i,(0:E)) g q)) (sq_nonneg (H q))
  change H q^2 * (flatInversePair _ _ f g q)^2 ≤ H q^2 *
    (flatInversePair _ _ f f q * flatInversePair _ _ g g q) at hc
  unfold tubeBasePair
  nlinarith [hc]

lemma tubeBasePair_symm {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hB : (tubeBaseMatrix H q b).PosDef) (f g : S × E → ℝ) :
    tubeBasePair H b f g q = tubeBasePair H b g f q := by
  unfold tubeBasePair
  rw [flatInversePair_symm _ (by simpa only [Matrix.isHermitian_iff_isSymm] using hB.isHermitian)]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualWeightedLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The actual logarithmic base identity with the manuscript's literal μ₀.
All contractions use the actual positive base Hessian of support. -/
theorem affineEpigraph_base_p_identity {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : ‖e‖ = 1)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun s => Real.log (H (s,e))
    let F := fun s => invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,e)
    let B := fun s => tubeBaseMatrix H (s,e) bS
    let M := fun s => tubeMeasureDensity n H bS bE (s,e)
    (∫ s, M s*σ s^2*((Fintype.card ι : ℝ)+((n : ℝ)+1)*H (s,e)*flatInversePair (B s) bS P P s+
        (((n : ℝ)+2)/2)*H (s,e)*flatInversePair (B s) bS F P s) ∂μ) =
      2*(∫ s, M s*σ s*H (s,e)*flatInversePair (B s) bS σ P s ∂μ) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun s => Real.log (H (s,e))
  let F := fun s => invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,e)
  let B := fun s => tubeBaseMatrix H (s,e) bS
  let M := fun s => tubeMeasureDensity n H bS bE (s,e)
  have hen : e ≠ 0 := by intro hz; simp [hz] at he
  have hsmooth := affineEpigraph_tube_base_smooth hΩ hcv hu hp a L hD hK hzero hen bS bE
    (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  have hH (s : S) (hs : s ∈ D) : ContDiffAt ℝ ∞ H (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs hen).1
  have hpos (s : S) (hs : s ∈ D) := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs hen bS bE
  have hmat (s : S) (hs : s ∈ D) : flatBlockHessian (fun s => -H (s,e)) bS s = B s := by
    rw [flatBlockHessian_neg]
    exact (tubeBaseMatrix_eq_slice (hH s hs) bS).symm
  have hdet (s : S) (hs : s ∈ D) : (-flatBlockHessian (fun s => H (s,e)) bS s).det ≠ 0 := by
    rw [← tubeBaseMatrix_eq_slice (hH s hs) bS]
    exact (hpos s hs).1.det_pos.ne'
  have hweight (s : S) (hs : s ∈ D) : Real.exp (-(n : ℝ)*P s-(((n : ℝ)+2)/2)*F s) = M s*H (s,e)/(B s).det := by
    exact (tubeMeasureDensity_base bS bE (tube_dimension_eq bS bE L) he
      (hpos s hs).2.2 (hpos s hs).1.det_pos (hpos s hs).2.1).symm
  have hh := integral_base_log_identity (μ := μ) hD hsmooth.1 hsmooth.2.2
    (fun s hs => (hpos s hs).2.2) bS hdet hσ hc hσD (n : ℝ) (((n : ℝ)+2)/2)
  dsimp only at hh
  change (∫ s, M s*σ s^2*((Fintype.card ι : ℝ)+((n : ℝ)+1)*H (s,e)*flatInversePair (B s) bS P P s+
        (((n : ℝ)+2)/2)*H (s,e)*flatInversePair (B s) bS F P s) ∂μ) =
      2*(∫ s, M s*σ s*H (s,e)*flatInversePair (B s) bS σ P s ∂μ)
  convert hh using 1
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    by_cases hs : s ∈ tsupport σ
    · change M s*σ s^2*(_+_+_) = Real.exp (-(n : ℝ)*P s-(((n : ℝ)+2)/2)*F s)*σ s^2*_
      have hsd := hσD hs
      rw [flatCofactorPair_eq_det_mul bS _ _ _ (by rw [hmat s hsd]; exact (hpos s hsd).1.det_pos.ne'),
        flatCofactorPair_eq_det_mul bS _ _ _ (by rw [hmat s hsd]; exact (hpos s hsd).1.det_pos.ne'),
        hmat s hsd,← tubeBaseMatrix_eq_slice (hH s hsd) bS,hweight s hsd]
      change M s*σ s^2*((Fintype.card ι : ℝ)+((n : ℝ)+1)*H (s,e)*flatInversePair (B s) bS P P s+
        (((n : ℝ)+2)/2)*H (s,e)*flatInversePair (B s) bS F P s) =
        M s*H (s,e)/(B s).det*σ s^2*((B s).det/H (s,e)*(Fintype.card ι : ℝ)+
          ((n : ℝ)+1)*((B s).det*flatInversePair (B s) bS P P s)+
          (((n : ℝ)+2)/2)*((B s).det*flatInversePair (B s) bS F P s))
      have hb : (B s).det ≠ 0 := (hpos s hsd).1.det_pos.ne'
      have hh : H (s,e) ≠ 0 := (hpos s hsd).2.2.ne'
      field_simp [hb,hh]
    · simp [image_eq_zero_of_notMem_tsupport hs]
  · congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    by_cases hs : s ∈ tsupport σ
    · have hsd := hσD hs
      change M s*σ s*H (s,e)*flatInversePair (B s) bS σ P s =
        Real.exp (-(n : ℝ)*P s-(((n : ℝ)+2)/2)*F s)*σ s*flatCofactorPair (fun s => -H (s,e)) bS σ P s
      rw [flatCofactorPair_eq_det_mul bS _ _ _ (by rw [hmat s hsd]; exact (hpos s hsd).1.det_pos.ne'),hmat s hsd,hweight s hsd]
      have hb : (B s).det ≠ 0 := (hpos s hsd).1.det_pos.ne'
      field_simp [hb]
    · simp [image_eq_zero_of_notMem_tsupport hs]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualGlobalP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The actual p-identity, with all compact product integrations justified. -/
theorem affineEpigraph_global_p_identity {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2) (fun q => (Fintype.card ι : ℝ)+
      ((n : ℝ)+1)*tubeBasePair H bS P P q+(((n : ℝ)+2)/2)*tubeBasePair H bS P F q) =
      2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) P) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let J := fun q => (Fintype.card ι : ℝ)+((n : ℝ)+1)*tubeBasePair H bS P P q+
      (((n : ℝ)+2)/2)*tubeBasePair H bS P F q
  let R := tubeBasePair H bS (fun q => σ q.1) P
  have hH (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : S × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE
  have hF (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ F q :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE _
  have hP (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ P q :=
    (hH q hq).log (hpos q hq).2.2.ne'
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) bS bE (hpos q hq).2.2).continuousWithinAt
  have hJ : ContinuousOn J (tubeOpenSet D) := fun q hq =>
    ((contDiffAt_const.add
      (contDiffAt_const.mul (contDiffAt_tubeBasePair (hH q hq) (hP q hq) (hP q hq) bS (hpos q hq).1.det_pos.ne'))).add
      (contDiffAt_const.mul (contDiffAt_tubeBasePair (hH q hq) (hP q hq) (hF q hq) bS (hpos q hq).1.det_pos.ne'))).continuousAt.continuousWithinAt
  have hR : ContinuousOn R (tubeOpenSet D) := fun q hq =>
    (contDiffAt_tubeBasePair (hH q hq) (hσ.contDiffAt.comp q contDiffAt_fst) (hP q hq) bS
      (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  change tubeIntegral μ M (fun s => σ s^2) J = 2*tubeIntegral μ M σ R
  rw [tubeIntegral_base (σ := fun s => σ s^2) (by fun_prop) (compactSupport_sq hc) (tsupport_sq_subset.trans hσD) hM hJ,
    tubeIntegral_base hσ.continuous hc hσD hM hR,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  dsimp only
  have he : ‖(e:E)‖ = 1 := mem_sphere_zero_iff_norm.1 e.property
  have hen : (e:E) ≠ 0 := by intro hz; simp [hz] at he
  have hh := affineEpigraph_base_p_identity (μ := μ) hΩ hcv hu hp a L hD hK hzero he bS bE hσ hc hσD
  dsimp only at hh
  convert hh using 1
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    by_cases hs : s ∈ tsupport σ
    · have hq : (s,(e:E)) ∈ tubeOpenSet D := ⟨hσD hs,hen⟩
      unfold J
      rw [tubeBasePair_symm bS (hpos (s,e) hq).1 P F]
      unfold tubeBasePair
      rw [← flatInversePair_prod_left ((hP (s,e) hq).differentiableAt (by simp)) ((hP (s,e) hq).differentiableAt (by simp)),
        ← flatInversePair_prod_left ((hF (s,e) hq).differentiableAt (by simp)) ((hP (s,e) hq).differentiableAt (by simp))]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hs]
  · congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s
    dsimp only
    by_cases hs : s ∈ tsupport σ
    · have hq : (s,(e:E)) ∈ tubeOpenSet D := ⟨hσD hs,hen⟩
      unfold R tubeBasePair
      rw [← flatInversePair_prod_left (f := fun q : S × E => σ q.1) ((hσ.contDiffAt.comp (s,(e:E)) contDiffAt_fst).differentiableAt (by simp))
        ((hP (s,e) hq).differentiableAt (by simp))]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hs]

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

section ActualGlobalCoercive
open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineMaximal_global_coercive_identity {n : ℕ} (hn : n ≠ 0) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2) (fun q => (Fintype.card ι : ℝ)-15/8+
      ((n : ℝ)-7/8)*tubeBasePair H bS P P q+(((n : ℝ)+2)/2)*tubeBasePair H bS P F q+
      (15/16)*(tubeBasePair H bS F F q+tubeAngularPair H bE F F q)) =
      tubeIntegral μ M σ (fun q => (2-15/(2*(n : ℝ)))*tubeBasePair H bS (fun q => σ q.1) P q-
        (15/(4*(n : ℝ)))*tubeBasePair H bS (fun q => σ q.1) F q) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let PP := tubeBasePair H bS P P
  let DD := tubeBasePair H bS F F
  let PD := tubeBasePair H bS P F
  let EE := tubeAngularPair H bE F F
  let Rp := tubeBasePair H bS (fun q => σ q.1) P
  let Rd := tubeBasePair H bS (fun q => σ q.1) F
  let Jp := fun q => (Fintype.card ι : ℝ)+((n : ℝ)+1)*PP q+(((n : ℝ)+2)/2)*PD q
  let Jd := fun q => ((n : ℝ)/2)*(DD q+EE q)+((n : ℝ)+2)*(PP q+PD q)-((n : ℝ)-2*Fintype.card ι)
  have hH (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : S × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE
  have hF (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ F q :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE _
  have hP (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ P q :=
    (hH q hq).log (hpos q hq).2.2.ne'
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) bS bE (hpos q hq).2.2).continuousWithinAt
  have hpair (f g : S × E → ℝ) (hf : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ f q)
      (hg : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ g q) : ContinuousOn (tubeBasePair H bS f g) (tubeOpenSet D) :=
    fun q hq => (contDiffAt_tubeBasePair (hH q hq) (hf q hq) (hg q hq) bS
       (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  have hPP := hpair P P hP hP
  have hDD := hpair F F hF hF
  have hPD := hpair P F hP hF
  have hEE : ContinuousOn EE (tubeOpenSet D) := continuousOn_tubeAngularPair hH hF hF bE (fun q hq => (hpos q hq).2.1.ne')
  have hsp (q : S × E) (_ : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (fun q : S × E => σ q.1) q :=
    hσ.contDiffAt.comp q contDiffAt_fst
  have hRp := hpair _ P hsp hP
  have hRd := hpair _ F hsp hF
  have hJp : ContinuousOn Jp (tubeOpenSet D) := (continuousOn_const.add (continuousOn_const.mul hPP)).add
    (continuousOn_const.mul hPD)
  have hJd : ContinuousOn Jd (tubeOpenSet D) := ((continuousOn_const.mul (hDD.add hEE)).add
    (continuousOn_const.mul (hPP.add hPD))).sub continuousOn_const
  have hpI := affineEpigraph_global_p_identity (μ := μ) hΩ hcv hu hp a L hD hK hzero bS bE hσ hc hσD
  have hdI := affineMaximal_global_d_identity (μ := μ) hΩ hcv hu hp hm a L hD hK hzero bS bE hσ hc hσD
  change tubeIntegral μ M (fun s => σ s^2) Jp = 2*tubeIntegral μ M σ Rp at hpI
  change tubeIntegral μ M (fun s => σ s^2) Jd = -2*tubeIntegral μ M σ Rd at hdI
  change tubeIntegral μ M (fun s => σ s^2) (fun q => (Fintype.card ι : ℝ)-15/8+
      ((n : ℝ)-7/8)*PP q+(((n : ℝ)+2)/2)*PD q+(15/16)*(DD q+EE q)) =
      tubeIntegral μ M σ (fun q => (2-15/(2*(n : ℝ)))*Rp q-(15/(4*(n : ℝ)))*Rd q)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfunc : (fun q => (Fintype.card ι : ℝ)-15/8+((n : ℝ)-7/8)*PP q+
      (((n : ℝ)+2)/2)*PD q+(15/16)*(DD q+EE q)) =
      fun q => (1-15/(4*(n : ℝ)))*Jp q+(15/(8*(n : ℝ)))*Jd q := by
    funext q
    dsimp [Jp,Jd]
    field_simp [hn0]
    ring
  rw [hfunc,tubeIntegral_linearCombination (σ := fun s => σ s^2) (by fun_prop)
    (compactSupport_sq hc) (tsupport_sq_subset.trans hσD) hM hJp hJd,hpI,hdI]
  rw [show (fun q => (2-15/(2*(n : ℝ)))*Rp q-(15/(4*(n : ℝ)))*Rd q) =
    (fun q => (2-15/(2*(n : ℝ)))*Rp q+(-15/(4*(n : ℝ)))*Rd q) by funext q; ring,
    tubeIntegral_linearCombination hσ.continuous hc hσD hM hRp hRd]
  field_simp [hn0]
  ring

end ActualGlobalCoercive

theorem tube_paired_determinant {n : ℝ} (hn : 3 ≤ n) (hn9 : n ≤ 9) :
    7 / 128 ≤ (15 / 16) * (n - 7 / 8) - (n + 2) ^ 2 / 16 := by
  nlinarith [mul_nonneg (show 0 ≤ n - 2 by linarith) (show 0 ≤ 9 - n by linarith)]

/- A two-dimensional positive-semidefinite quadratic form, stated in
terms of the actual squared lengths and cross inner product. -/
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
theorem tube_pointwise_coercivity {n k P D I E : ℝ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k)
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hE : 0 ≤ E) (hI : I ^ 2 ≤ P * D) :
    (1 / 512) * (1 + P + D + E) ≤
      k - 15 / 8 + (n - 7 / 8) * P + ((n + 2) / 2) * I + (15 / 16) * (D + E) := by
  have hdet := tube_paired_determinant hn hn9
  have hc : ((n + 2) / 2) ^ 2 ≤
      4 * (n - 7 / 8 - 1 / 512) * (15 / 16 - 1 / 512) := by nlinarith
  have hq := paired_cauchy_coercive hP hD hI
    (show 0 ≤ n - 7 / 8 - 1 / 512 by linarith)
    (show (0 : ℝ) < 15 / 16 - 1 / 512 by norm_num) hc
  nlinarith

/- Cauchy--Schwarz followed by Young, with no choice of orthonormal frame. -/
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
theorem tube_cutoff_coefficients {n : ℝ} (hn : 3 ≤ n) :
    (2 - 15 / (2 * n)) ^ 2 + (-15 / (4 * n)) ^ 2 ≤ 8 := by
  have hn0 : 0 < n := by linarith
  have ha0 : 0 ≤ 15 / (2 * n) := by positivity
  have ha : 15 / (2 * n) ≤ 5 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hb0 : 0 ≤ 15 / (4 * n) := by positivity
  have hb : 15 / (4 * n) ≤ 5 / 4 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  simp only [neg_div]
  nlinarith [mul_nonneg (show 0 ≤ 2 - (2 - 15 / (2 * n)) by linarith)
    (show 0 ≤ 2 + (2 - 15 / (2 * n)) by linarith),
    mul_nonneg (show 0 ≤ 5 / 4 - 15 / (4 * n) by linarith)
      (show 0 ≤ 5 / 4 + 15 / (4 * n) by linarith)]

/- Quantitative absorption in the exact coercive identity, with constants
uniform for every n in [3,9] and every tube direction count. -/
theorem tube_cutoff_absorption {n v P D E Q Jp Jd : ℝ}
    (hn : 3 ≤ n) (hP : 0 ≤ P) (hD : 0 ≤ D) (hE : 0 ≤ E) (hQ : 0 ≤ Q)
    (hJp : Jp ^ 2 ≤ P * Q) (hJd : Jd ^ 2 ≤ D * Q) :
    v * ((2 - 15 / (2 * n)) * Jp - (15 / (4 * n)) * Jd) ≤
      (1 / 1024) * v ^ 2 * (1 + P + D + E) + 4096 * Q := by
  have hCp := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hJp)
  have hCd := mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hJd)
  have hp := cauchy_young (show 0 ≤ v ^ 2 * P by positivity) hQ
    (show (v * Jp) ^ 2 ≤ v ^ 2 * P * Q by nlinarith [hCp])
    (a := 2 - 15 / (2 * n)) (by norm_num : (0 : ℝ) < 1 / 2048)
  have hd := cauchy_young (show 0 ≤ v ^ 2 * D by positivity) hQ
    (show (v * Jd) ^ 2 ≤ v ^ 2 * D * Q by nlinarith [hCd])
    (a := -15 / (4 * n)) (by norm_num : (0 : ℝ) < 1 / 2048)
  simp only [neg_div] at hd ⊢
  norm_num at hp hd
  have hc := mul_nonneg (sub_nonneg.mpr (tube_cutoff_coefficients hn)) hQ
  simp only [neg_div] at hc
  have hrem : 0 ≤ v ^ 2 * (1 + P + D + 2 * E) := by positivity
  nlinarith

/- Exact cancellation of the two stationarity identities in tubes.tex.
The symbols are their actual integrals; this is just their linear combination. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedTubeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

/- Absorption with the literal compact-product density, requiring positivity only
on the actual unit-normal tube. The identity is an input here and will be supplied
by the actual affine-maximal equation. -/
omit [NormedSpace ℝ S] [FiniteDimensional ℝ S] [Nontrivial E] in
theorem tube_compact_energy_of_identity {n k : ℝ} (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k)
    {D : Set S} {σ : S → ℝ} (hσ : Continuous σ) (hc : HasCompactSupport σ) (hsD : tsupport σ ⊆ D)
    {M PP DD EE PD Q Rp Rd : S × E → ℝ}
    (hM : ContinuousOn M (tubeOpenSet D)) (hPP : ContinuousOn PP (tubeOpenSet D))
    (hDD : ContinuousOn DD (tubeOpenSet D)) (hEE : ContinuousOn EE (tubeOpenSet D))
    (hPD : ContinuousOn PD (tubeOpenSet D)) (hQ : ContinuousOn Q (tubeOpenSet D))
    (hRp : ContinuousOn Rp (tubeOpenSet D)) (hRd : ContinuousOn Rd (tubeOpenSet D))
    (hQzero : ∀ s ∉ tsupport σ, ∀ e : E, Q (s,e) = 0)
    (hpos : ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ PP (s,e) ∧ 0 ≤ DD (s,e) ∧
      0 ≤ EE (s,e) ∧ 0 ≤ Q (s,e) ∧ PD (s,e)^2 ≤ PP (s,e)*DD (s,e) ∧
      Rp (s,e)^2 ≤ PP (s,e)*Q (s,e) ∧ Rd (s,e)^2 ≤ DD (s,e)*Q (s,e))
    (hid : tubeIntegral μ M (fun s => σ s^2) (fun q => k-15/8+(n-7/8)*PP q+
        ((n+2)/2)*PD q+(15/16)*(DD q+EE q)) =
      tubeIntegral μ M σ (fun q => (2-15/(2*n))*Rp q-(15/(4*n))*Rd q)) :
    tubeIntegral μ M (fun s => σ s^2) (fun q => 1+PP q+DD q+EE q) ≤
      4194304*tubeIntegral μ M (fun _ => 1) Q := by
  let en := fun q => 1+PP q+DD q+EE q
  let fl := fun q => k-15/8+(n-7/8)*PP q+((n+2)/2)*PD q+(15/16)*(DD q+EE q)
  let rr := fun q => (2-15/(2*n))*Rp q-(15/(4*n))*Rd q
  have hen : ContinuousOn en (tubeOpenSet D) := ((continuousOn_const.add hPP).add hDD).add hEE
  have hfl : ContinuousOn fl (tubeOpenSet D) := ((continuousOn_const.add
    (continuousOn_const.mul hPP)).add (continuousOn_const.mul hPD)).add
      (continuousOn_const.mul (hDD.add hEE))
  have hrr : ContinuousOn rr (tubeOpenSet D) := (continuousOn_const.mul hRp).sub (continuousOn_const.mul hRd)
  have hien := integrable_tube_compact_sq (μ := μ) hσ hc hsD hM hen
  have hifl := integrable_tube_compact_sq (μ := μ) hσ hc hsD hM hfl
  have hirr : Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*σ q.1*rr (tubeLift q))
      (μ.prod volume.toSphere) := by
    convert integrable_tube_compact_mul (μ := μ) hσ hc hsD hM hrr using 1
    all_goals try with_reducible_and_instances rfl
    ext q; ring
  have hiQ : Integrable (fun q : S × sphere (0:E) 1 => M (tubeLift q)*Q (tubeLift q))
      (μ.prod volume.toSphere) := by
    exact integrable_tube_supported hc hsD (hM.mul hQ) (fun s hs e => by simp [hQzero s hs e])
  have hlo := integral_mono_ae (hien.const_mul (1/512)) hifl (Filter.Eventually.of_forall fun q => by
    dsimp only
    by_cases hs : q.1 ∈ tsupport σ
    · have hh := hpos q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)
      have hh' := tube_pointwise_coercivity hn hn9 hk hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.2.1
      have hh'' := mul_le_mul_of_nonneg_left hh' (mul_nonneg hh.1 (sq_nonneg (σ q.1)))
      simpa only [en,fl,tubeLift] using (show (1/512)*(M (q.1,q.2)*σ q.1^2*(1+PP (q.1,q.2)+DD (q.1,q.2)+EE (q.1,q.2))) ≤
        M (q.1,q.2)*σ q.1^2*(k-15/8+(n-7/8)*PP (q.1,q.2)+((n+2)/2)*PD (q.1,q.2)+
        (15/16)*(DD (q.1,q.2)+EE (q.1,q.2))) by nlinarith [hh''])
    · simp [image_eq_zero_of_notMem_tsupport hs])
  have hup := integral_mono_ae hirr ((hien.const_mul (1/1024)).add (hiQ.const_mul 4096))
    (Filter.Eventually.of_forall fun q => by
      dsimp only [Pi.add_apply]
      by_cases hs : q.1 ∈ tsupport σ
      · have hh := hpos q.1 (hsD hs) q.2 (mem_sphere_zero_iff_norm.1 q.2.property)
        have hh' := tube_cutoff_absorption hn hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
          hh.2.2.2.2.2.2.1 hh.2.2.2.2.2.2.2 (v := σ q.1)
        have hh'' := mul_le_mul_of_nonneg_left hh' hh.1
        dsimp only [rr,en,tubeLift]
        nlinarith [hh'']
      · simp [image_eq_zero_of_notMem_tsupport hs,tubeLift,hQzero q.1 hs q.2])
  rw [integral_const_mul] at hlo
  change (1/512)*tubeIntegral μ M (fun s => σ s^2) en ≤ tubeIntegral μ M (fun s => σ s^2) fl at hlo
  change tubeIntegral μ M (fun s => σ s^2) fl = tubeIntegral μ M σ rr at hid
  rw [hid] at hlo
  simp only [Pi.add_apply] at hup
  rw [integral_add (hien.const_mul (1/1024)) (hiQ.const_mul 4096),integral_const_mul,integral_const_mul] at hup
  change tubeIntegral μ M σ rr ≤ (1/1024)*tubeIntegral μ M (fun s => σ s^2) en+
    4096*(∫ q : S × sphere (0:E) 1, M (tubeLift q)*Q (tubeLift q) ∂μ.prod volume.toSphere) at hup
  have hqI : (∫ q : S × sphere (0:E) 1, M (tubeLift q)*Q (tubeLift q) ∂μ.prod volume.toSphere) =
      tubeIntegral μ M (fun _ => 1) Q := by simp [tubeIntegral]
  rw [hqI] at hup
  change tubeIntegral μ M (fun s => σ s^2) en ≤ _
  linarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineMaximal_tube_energy_oai {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hk : 2 ≤ Fintype.card ι)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2) (fun q => 1+tubeBasePair H bS P P q+
      tubeBasePair H bS F F q+tubeAngularPair H bE F F q) ≤
      4194304*tubeIntegral μ M (fun _ => 1) (tubeBasePair H bS (fun q => σ q.1) (fun q => σ q.1)) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let P := fun q => Real.log (H q)
  let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  let M := tubeMeasureDensity n H bS bE
  let V := fun q : S × E => σ q.1
  have hH (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : S × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE
  have hF (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ F q :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 bS bE _
  have hP (q : S × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ P q :=
    (hH q hq).log (hpos q hq).2.2.ne'
  have hV (q : S × E) (_ : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ V q :=
    hσ.contDiffAt.comp q contDiffAt_fst
  have hM : ContinuousOn M (tubeOpenSet D) := fun q hq =>
    (continuousAt_tubeMeasureDensity (hH q hq) bS bE (hpos q hq).2.2).continuousWithinAt
  have hpair (f g : S × E → ℝ) (hf : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ f q)
      (hg : ∀ q ∈ tubeOpenSet D, ContDiffAt ℝ ∞ g q) : ContinuousOn (tubeBasePair H bS f g) (tubeOpenSet D) :=
    fun q hq => (contDiffAt_tubeBasePair (hH q hq) (hf q hq) (hg q hq) bS
       (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  have hEE : ContinuousOn (tubeAngularPair H bE F F) (tubeOpenSet D) :=
    continuousOn_tubeAngularPair hH hF hF bE (fun q hq => (hpos q hq).2.1.ne')
  have hQzero (s : S) (hs : s ∉ tsupport σ) (e : E) : tubeBasePair H bS V V (s,e) = 0 := by
    have hd : fderiv ℝ V (s,e) = 0 := by
      dsimp only [V]
      rw [show (fun q : S × E => σ q.1) = σ ∘ Prod.fst by rfl,
        fderiv_comp (s,e) (hσ.differentiable (by simp) s) differentiableAt_fst,
        fderiv_of_notMem_tsupport ℝ hs]
      simp
    simp [tubeBasePair,flatInversePair,dirDeriv,hd]
  have hid := affineMaximal_global_coercive_identity (μ := μ) (by omega : n ≠ 0)
    hΩ hcv hu hp hm a L hD hK hzero bS bE hσ hc hσD
  apply tube_compact_energy_of_identity (n := (n : ℝ)) (k := (Fintype.card ι : ℝ))
    (by exact_mod_cast hn) (by exact_mod_cast hn9) (by exact_mod_cast hk)
    hσ.continuous hc hσD hM (hpair P P hP hP) (hpair F F hF hF) hEE (hpair P F hP hF)
    (hpair V V hV hV) (hpair V P hV hP) (hpair V F hV hF) hQzero _ hid
  intro s hs e he
  have hen : e ≠ 0 := by intro hz; simp [hz] at he
  have hq : (s,e) ∈ tubeOpenSet D := ⟨hs,hen⟩
  have hz := hpos (s,e) hq
  refine ⟨(tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le,
    tubeBasePair_nonneg bS hz.2.2.le hz.1 P,
    tubeBasePair_nonneg bS hz.2.2.le hz.1 F,
    affineEpigraph_tube_angular_pair_nonneg hΩ hcv hu hp a L hD hK hzero hs he bS bE
      ((hF (s,e) hq).differentiableAt (by simp)),
    tubeBasePair_nonneg bS hz.2.2.le hz.1 V,
    tubeBasePair_cauchy bS hz.1 P F, ?_, ?_⟩
  · simpa only [mul_comm] using tubeBasePair_cauchy bS hz.1 V P
  · simpa only [mul_comm] using tubeBasePair_cauchy bS hz.1 V F

end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.AffineBernstein.affineMaximal_tube_energy_oai.{u_1, u_2, u_3, u_4} := @OAI.AffineBernstein.affineMaximal_tube_energy_oai.{u_1, u_2, u_3, u_4}
