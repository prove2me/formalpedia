-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:02:56.024792+00:00
-- url     : https://prove2.me/submissions/e05afbf2-e752-4a86-9c71-b81b17b7849d

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_f_smooth
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineMaximal_flat_tube_weak_euler

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

/-- The differential part of the double integration by parts. Both zero
cofactor divergences are used; they will be supplied by the proved Piola identity. -/
theorem double_divergence_weighted {Ω : Set E} (hΩ : IsOpen Ω)
    (U : E → ι → ι → ℝ) (w : E → ℝ) (e : ι → E)
    (hU : ∀ x ∈ Ω, ∀ i j, ContDiffAt ℝ ∞ (fun y => U y i j) x)
    (hw : ∀ x ∈ Ω, ContDiffAt ℝ ∞ w x)
    (hrow : ∀ x ∈ Ω, ∀ i, (∑ j, dirDeriv (e j) (fun y => U y i j) x) = 0)
    (hcol : ∀ x ∈ Ω, ∀ j, (∑ i, dirDeriv (e i) (fun y => U y i j) x) = 0)
    {x : E} (hx : x ∈ Ω) :
    (∑ j, ∑ i, dirDeriv (e j) (dirDeriv (e i) (fun y => w y * U y i j)) x) =
      ∑ j, ∑ i, U x i j * dirDeriv (e j) (dirDeriv (e i) w) x := by
  have hfirst (y : E) (hy : y ∈ Ω) (j : ι) :
      (∑ i, dirDeriv (e i) (fun z => w z * U z i j) y) =
        ∑ i, dirDeriv (e i) w y * U y i j := by
    calc
      _ = ∑ i, (dirDeriv (e i) w y * U y i j +
          w y * dirDeriv (e i) (fun z => U z i j) y) :=
        Finset.sum_congr rfl fun i _ => dirDeriv_mul
          ((hw y hy).differentiableAt (by simp)) ((hU y hy i j).differentiableAt (by simp)) _
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcol y hy j, mul_zero, add_zero]
  have he (j : ι) : (fun y => ∑ i, dirDeriv (e i) (fun z => w z * U z i j) y) =ᶠ[nhds x]
      (fun y => ∑ i, dirDeriv (e i) w y * U y i j) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hfirst y hy j
  have hsecond (j : ι) :
      (∑ i, dirDeriv (e j) (dirDeriv (e i) (fun y => w y * U y i j)) x) =
        ∑ i, (dirDeriv (e j) (dirDeriv (e i) w) x * U x i j +
          dirDeriv (e i) w x * dirDeriv (e j) (fun y => U y i j) x) := by
    calc
      _ = dirDeriv (e j) (fun y => ∑ i, dirDeriv (e i) (fun z => w z * U z i j) y) x := by
        symm
        apply dirDeriv_sum
        intro i
        exact (contDiffAt_dirDeriv ((hw x hx).mul (hU x hx i j)) _).differentiableAt (by simp)
      _ = dirDeriv (e j) (fun y => ∑ i, dirDeriv (e i) w y * U y i j) x :=
        congrArg (fun L : E →L[ℝ] ℝ => L (e j)) (he j).fderiv_eq
      _ = ∑ i, dirDeriv (e j) (fun y => dirDeriv (e i) w y * U y i j) x := by
        apply dirDeriv_sum
        intro i
        exact ((contDiffAt_dirDeriv (hw x hx) _).mul (hU x hx i j)).differentiableAt (by simp)
      _ = _ := Finset.sum_congr rfl fun i _ =>
        dirDeriv_mul ((contDiffAt_dirDeriv (hw x hx) _).differentiableAt (by simp))
          ((hU x hx i j).differentiableAt (by simp)) _
  have hzero : (∑ j, ∑ i, dirDeriv (e i) w x *
      dirDeriv (e j) (fun y => U y i j) x) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.mul_sum, hrow x hx i, mul_zero]
  calc
    _ = ∑ j, ∑ i, (dirDeriv (e j) (dirDeriv (e i) w) x * U x i j +
          dirDeriv (e i) w x * dirDeriv (e j) (fun y => U y i j) x) :=
      Finset.sum_congr rfl fun j _ => hsecond j
    _ = ∑ j, ∑ i, dirDeriv (e j) (dirDeriv (e i) w) x * U x i j := by
      simp only [Finset.sum_add_distrib]
      rw [hzero, add_zero]
    _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

end WeightedDivergence

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

/-- Two integrations by parts, without an artificial globally smooth coefficient. -/
theorem integral_mul_second_fderiv_compact (a η : E → ℝ) (v z : E)
    (ha : ∀ x ∈ tsupport η, ContDiffAt ℝ 2 a x)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    (∫ x, a x * fderiv ℝ (fun y => fderiv ℝ η y v) x z ∂μ) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ a y z) x v * η x ∂μ := by
  have hdη : ContDiff ℝ 1 (fun y => fderiv ℝ η y v) :=
    (hη.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hda : ∀ x ∈ tsupport η, ContDiffAt ℝ 1 (fun y => fderiv ℝ a y z) x :=
    fun x hx => ((ha x hx).fderiv_right (by norm_num)).clm_apply contDiffAt_const
  rw [integral_mul_fderiv_compact a (fun y => fderiv ℝ η y v) z
    (fun x hx => (ha x (tsupport_fderiv_apply_subset ℝ v hx)).of_le (by norm_num))
    hdη (hηc.fderiv_apply ℝ v)]
  rw [integral_mul_fderiv_compact _ η v hda (hη.of_le (by norm_num)) hηc, neg_neg]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Global smoothness of a fixed-direction derivative. -/
theorem contDiff_dirDeriv {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (dirDeriv v f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The weak double-divergence formula with precisely a compactly supported test. -/
theorem integral_double_contraction_compact {ι : Type*} [Fintype ι]
    (a : ι → ι → E → ℝ) (e : ι → E) (η : E → ℝ)
    (ha : ∀ i j x, x ∈ tsupport η → ContDiffAt ℝ ∞ (a i j) x)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    (∫ x, ∑ i, ∑ j, a i j x * dirDeriv (e i) (dirDeriv (e j) η) x ∂μ) =
      ∫ x, (∑ j, ∑ i, dirDeriv (e j) (dirDeriv (e i) (a i j)) x) * η x ∂μ := by
  have hleft (i j : ι) : Integrable
      (fun x => a i j x * dirDeriv (e i) (dirDeriv (e j) η) x) μ := by
    apply integrable_of_support_subset_compact hηc.isCompact
    · exact (Function.support_mul_subset_right _ _).trans
        ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (e i)).trans
          (tsupport_fderiv_apply_subset ℝ (e j))))
    · exact (show ContinuousOn (a i j) (tsupport η) from
        fun x hx => (ha i j x hx).continuousAt.continuousWithinAt).mul
        ((contDiff_dirDeriv (contDiff_dirDeriv hη (e j)) (e i)).continuous.continuousOn)
  have hright (i j : ι) : Integrable
      (fun x => dirDeriv (e j) (dirDeriv (e i) (a i j)) x * η x) μ := by
    apply integrable_of_support_subset_compact hηc.isCompact
    · exact (Function.support_mul_subset_right _ _).trans (subset_tsupport η)
    · exact (show ContinuousOn (dirDeriv (e j) (dirDeriv (e i) (a i j))) (tsupport η) from
        fun x hx => (contDiffAt_dirDeriv (contDiffAt_dirDeriv (ha i j x hx) (e i)) (e j)).continuousAt.continuousWithinAt).mul
        hη.continuous.continuousOn
  calc
    _ = ∑ i, ∑ j, ∫ x, a i j x * dirDeriv (e i) (dirDeriv (e j) η) x ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hleft i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum _ (fun j _ => hleft i j)
    _ = ∑ i, ∑ j, ∫ x, dirDeriv (e j) (dirDeriv (e i) (a i j)) x * η x ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_mul_second_fderiv_compact (a i j) η (e j) (e i)
        (fun x hx => (ha i j x hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
        (hη.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hηc
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hright i j))]
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_finsetSum _ (fun i _ => hright i j)).symm

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

omit [Fintype ι] [DecidableEq ι] in
lemma flatBlockHessian_isSymm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (v : ι → E) : (flatBlockHessian f v x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact dirDeriv_comm hf (v j) (v i)

lemma flatBlockHessian_adjugate_row_divergence {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (v : ι → E) (i : ι) :
    (∑ j, dirDeriv (v j) (fun y => (flatBlockHessian f v y).adjugate i j) x) = 0 := by
  let F : ι → E → ℝ := fun i => dirDeriv (v i) f
  have hF (l : ι) : ContDiffAt ℝ 2 (F l) x :=
    (contDiffAt_dirDeriv hf (v l)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he (y : E) : jacobianRows F v y = (flatBlockHessian f v y).transpose := rfl
  simpa only [he,← Matrix.adjugate_transpose,Matrix.transpose_apply,dirDeriv] using
    piola_identity F v x hF i

lemma flatBlockHessian_adjugate_divergence {W : Set E} (hW : IsOpen W)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f W) (v : ι → E) {x : E} (hx : x ∈ W) (i : ι) :
    (∑ j, dirDeriv (v j) (fun y => (flatBlockHessian f v y).adjugate i j) x) = 0 ∧
    (∑ j, dirDeriv (v j) (fun y => (flatBlockHessian f v y).adjugate j i) x) = 0 := by
  have hr := flatBlockHessian_adjugate_row_divergence (hf.contDiffAt (hW.mem_nhds hx)) v i
  refine ⟨hr,?_⟩
  have he (j : ι) : (fun y => (flatBlockHessian f v y).adjugate j i) =ᶠ[𝓝 x]
      (fun y => (flatBlockHessian f v y).adjugate i j) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact ((flatBlockHessian_isSymm (hf.contDiffAt (hW.mem_nhds hy)) v).adjugate.apply i j)
  change (∑ j, fderiv ℝ (fun y => (flatBlockHessian f v y).adjugate j i) x (v j)) = 0
  simp_rw [(he _).fderiv_eq]
  exact hr

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatEulerCore
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
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma integrable_flatTestContraction (A : ι → ι → E → ℝ) (e : ι → E)
    {η : E → ℝ} (ha : ∀ i j x, x ∈ tsupport η → ContDiffAt ℝ ∞ (A i j) x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    Integrable (flatTestContraction A e η) μ := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_of_support_subset_compact hc.isCompact
  · exact (Function.support_mul_subset_right _ _).trans
      ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (e i)).trans
        (tsupport_fderiv_apply_subset ℝ (e j))))
  · exact (show ContinuousOn (A i j) (tsupport η) from
      fun x hx => (ha i j x hx).continuousAt.continuousWithinAt).mul
      ((contDiff_dirDeriv (contDiff_dirDeriv hη (e j)) (e i)).continuous.continuousOn)

omit [MeasurableSpace E] [BorelSpace E] in
lemma contDiffAt_flatDoubleDivergence {A : ι → ι → E → ℝ} (e : ι → E) {x : E}
    (ha : ∀ i j, ContDiffAt ℝ ∞ (A i j) x) :
    ContDiffAt ℝ ∞ (flatDoubleDivergence A e) x := by
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_dirDeriv (contDiffAt_dirDeriv (ha i j) (e i)) (e j)

lemma integrable_flatDoubleDivergence_mul (A : ι → ι → E → ℝ) (e : ι → E)
    {η : E → ℝ} (ha : ∀ i j x, x ∈ tsupport η → ContDiffAt ℝ ∞ (A i j) x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    Integrable (fun x => flatDoubleDivergence A e x * η x) μ := by
  apply integrable_of_support_subset_compact hc.isCompact
  · exact (Function.support_mul_subset_right _ _).trans (subset_tsupport η)
  · exact (show ContinuousOn (flatDoubleDivergence A e) (tsupport η) from
      fun x hx => (contDiffAt_flatDoubleDivergence e (fun i j => ha i j x hx)).continuousAt.continuousWithinAt).mul
      hη.continuous.continuousOn

omit [MeasurableSpace E] [BorelSpace E] in
lemma flatTestContraction_eq_zero_of_notMem_tsupport (A : ι → ι → E → ℝ)
    (e : ι → E) {η : E → ℝ} {x : E} (hx : x ∉ tsupport η) :
    flatTestContraction A e η x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hz : dirDeriv (e i) (dirDeriv (e j) η) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hh => hx ((tsupport_fderiv_apply_subset ℝ (e j))
      ((tsupport_fderiv_apply_subset ℝ (e i)) hh))
  rw [hz,mul_zero]

variable [FiniteDimensional ℝ E]

/- The fundamental variational lemma applied to two independent flat Hessian
blocks. No pointwise PDE is an assumption. -/
theorem flatDoubleDivergence_eq_zero_of_stationary {W : Set E} (hW : IsOpen W)
    (A : ι → ι → E → ℝ) (B : κ → κ → E → ℝ) (e : ι → E) (f : κ → E)
    (ha : ∀ i j x, x ∈ W → ContDiffAt ℝ ∞ (A i j) x)
    (hb : ∀ i j x, x ∈ W → ContDiffAt ℝ ∞ (B i j) x)
    (hstat : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ W →
      (∫ x, flatTestContraction A e η x + flatTestContraction B f η x ∂μ) = 0)
    {x : E} (hx : x ∈ W) :
    flatDoubleDivergence A e x + flatDoubleDivergence B f x = 0 := by
  let F := fun x => flatDoubleDivergence A e x + flatDoubleDivergence B f x
  have hF : ContinuousOn F W := fun y hy =>
    ((contDiffAt_flatDoubleDivergence e (fun i j => ha i j y hy)).add
      (contDiffAt_flatDoubleDivergence f (fun i j => hb i j y hy))).continuousAt.continuousWithinAt
  have he : ∀ᵐ y ∂μ, y ∈ W → F y = 0 := by
    apply hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hF.locallyIntegrableOn hW.measurableSet)
    intro η hη hc hs
    have hA := fun i j y (hy : y ∈ tsupport η) => ha i j y (hs hy)
    have hB := fun i j y (hy : y ∈ tsupport η) => hb i j y (hs hy)
    have heq := hstat η hη hc hs
    rw [integral_add (integrable_flatTestContraction A e hA hη hc)
      (integrable_flatTestContraction B f hB hη hc)] at heq
    change (∫ y, ∑ i, ∑ j, A i j y * dirDeriv (e i) (dirDeriv (e j) η) y ∂μ) +
      (∫ y, ∑ i, ∑ j, B i j y * dirDeriv (f i) (dirDeriv (f j) η) y ∂μ) = 0 at heq
    rw [integral_double_contraction_compact A e η hA hη hc,
      integral_double_contraction_compact B f η hB hη hc] at heq
    have heFun : (fun y => η y • F y) =
        (fun y => flatDoubleDivergence A e y * η y + flatDoubleDivergence B f y * η y) := by
      funext y
      dsimp [F]
      ring
    rw [heFun,integral_add (integrable_flatDoubleDivergence_mul A e hA hη hc)
      (integrable_flatDoubleDivergence_mul B f hB hη hc)]
    exact heq
  have he' : F =ᵐ[μ.restrict W] (fun _ => 0) :=
    (ae_restrict_iff' hW.measurableSet).mpr he
  exact (MeasureTheory.Measure.eqOn_open_of_ae_eq he' hW hF continuousOn_const) hx

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatWeightedEuler
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
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem flatWeightedBlockEuler {W : Set E} (hW : IsOpen W)
    (f g a b : E → ℝ) (v : ι → E) (w : κ → E)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    (ha : ContDiffOn ℝ ∞ a W) (hb : ContDiffOn ℝ ∞ b W)
    (hstat : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ W →
      (∫ x, flatTestContraction (fun i j y => a y * (flatBlockHessian f v y).adjugate i j) v η x +
        flatTestContraction (fun i j y => b y * (flatBlockHessian g w y).adjugate i j) w η x ∂μ) = 0)
    {x : E} (hx : x ∈ W) :
    (∑ j, ∑ i, (flatBlockHessian f v x).adjugate i j * dirDeriv (v j) (dirDeriv (v i) a) x) +
      (∑ j, ∑ i, (flatBlockHessian g w x).adjugate i j * dirDeriv (w j) (dirDeriv (w i) b) x) = 0 := by
  have hF (y : E) (hy : y ∈ W) (i j : ι) :
      ContDiffAt ℝ ∞ (fun y => (flatBlockHessian f v y).adjugate i j) y :=
    contDiffAt_adjugate_entries (contDiffAt_flatBlockHessian (hf.contDiffAt (hW.mem_nhds hy)) v) i j
  have hG (y : E) (hy : y ∈ W) (i j : κ) :
      ContDiffAt ℝ ∞ (fun y => (flatBlockHessian g w y).adjugate i j) y :=
    contDiffAt_adjugate_entries (contDiffAt_flatBlockHessian (hg.contDiffAt (hW.mem_nhds hy)) w) i j
  have hp := flatDoubleDivergence_eq_zero_of_stationary hW _ _ v w
    (fun i j y hy => (ha.contDiffAt (hW.mem_nhds hy)).mul (hF y hy i j))
    (fun i j y hy => (hb.contDiffAt (hW.mem_nhds hy)).mul (hG y hy i j)) hstat hx
  change (∑ j, ∑ i, dirDeriv (v j) (dirDeriv (v i)
      (fun y => a y * (flatBlockHessian f v y).adjugate i j)) x) +
    (∑ j, ∑ i, dirDeriv (w j) (dirDeriv (w i)
      (fun y => b y * (flatBlockHessian g w y).adjugate i j)) x) = 0 at hp
  rw [double_divergence_weighted hW (fun y => (flatBlockHessian f v y).adjugate) a v hF
    (fun y hy => ha.contDiffAt (hW.mem_nhds hy))
    (fun y hy i => (flatBlockHessian_adjugate_divergence hW hf v hy i).1)
    (fun y hy i => (flatBlockHessian_adjugate_divergence hW hf v hy i).2) hx,
    double_divergence_weighted hW (fun y => (flatBlockHessian g w y).adjugate) b w hG
    (fun y hy => hb.contDiffAt (hW.mem_nhds hy))
    (fun y hy i => (flatBlockHessian_adjugate_divergence hW hg w hy i).1)
    (fun y hy i => (flatBlockHessian_adjugate_divergence hW hg w hy i).2) hx] at hp
  exact hp

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

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma contDiffAt_flatEulerWeights {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ}
    {x : E} (hB : ContDiffAt ℝ ∞ (fun y i j => B y i j) x)
    (hR : ContDiffAt ℝ ∞ (fun y i j => R y i j) x)
    (hBd : (B x).det ≠ 0) (hRd : (R x).det ≠ 0) (δ : ℝ) :
    ContDiffAt ℝ ∞ (flatBaseEulerWeight B R δ) x ∧
      ContDiffAt ℝ ∞ (flatAngularEulerWeight B R δ) x := by
  have hb : ContDiffAt ℝ ∞ (fun y => (B y).det) x :=
    (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x hB
  have hr : ContDiffAt ℝ ∞ (fun y => (R y).det) x :=
    (continuousDetRows (ι := κ)).contDiff.contDiffAt.comp x hR
  exact ⟨(contDiffAt_const.mul (hb.rpow_const_of_ne hBd)).mul (hr.rpow_const_of_ne hRd),
    (contDiffAt_const.mul (hb.rpow_const_of_ne hBd)).mul (hr.rpow_const_of_ne hRd)⟩

lemma tubeAreaFirstVariation_eq_flatContraction (φ : E → ℝ) (v : ι → E) (w : κ → E)
    (η : E → ℝ) (x : E) (δ : ℝ)
    (hB : (flatBlockHessian (fun y => -φ y) v x).IsSymm)
    (hR : (flatBlockHessian φ w x).IsSymm) :
    let B := fun y => flatBlockHessian (fun z => -φ z) v y
    let R := fun y => flatBlockHessian φ w y
    tubeAreaFirstVariation (B x) (-flatBlockHessian η v x) (R x) (flatBlockHessian η w x) δ =
      flatTestContraction (fun i j y => flatBaseEulerWeight B R δ y * (B y).adjugate i j) v η x +
      flatTestContraction (fun i j y => flatAngularEulerWeight B R δ y * (R y).adjugate i j) w η x := by
  dsimp only
  unfold tubeAreaFirstVariation flatTestContraction flatBaseEulerWeight flatAngularEulerWeight
  simp only [Matrix.neg_apply,flatBlockHessian,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hB.adjugate.apply i j]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hR.adjugate.apply i j]
    ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/- Two true integrations by parts and Piola cancellation convert flat tube
stationarity to the pointwise Euler equation. -/
theorem flatTubeEuler_of_stationary {W : Set E} (hW : IsOpen W)
    (φ : E → ℝ) (v : ι → E) (w : κ → E) (δ : ℝ)
    (hφ : ContDiffOn ℝ ∞ φ W)
    (hB : ∀ x ∈ W, (flatBlockHessian (fun y => -φ y) v x).PosDef)
    (hR : ∀ x ∈ W, (flatBlockHessian φ w x).PosDef)
    (hstat : ∀ η : E → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ W →
      (∫ x, tubeAreaFirstVariation (flatBlockHessian (fun y => -φ y) v x)
        (-flatBlockHessian η v x) (flatBlockHessian φ w x) (flatBlockHessian η w x) δ ∂μ) = 0)
    {x : E} (hx : x ∈ W) :
    let B := fun y => flatBlockHessian (fun z => -φ z) v y
    let R := fun y => flatBlockHessian φ w y
    (∑ j, ∑ i, (B x).adjugate i j * dirDeriv (v j) (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x) +
      (∑ j, ∑ i, (R x).adjugate i j * dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x) = 0 := by
  let B := fun y => flatBlockHessian (fun z => -φ z) v y
  let R := fun y => flatBlockHessian φ w y
  have hh (y : E) (hy : y ∈ W) := contDiffAt_flatEulerWeights
    (contDiffAt_flatBlockHessian (hφ.contDiffAt (hW.mem_nhds hy)).neg v)
    (contDiffAt_flatBlockHessian (hφ.contDiffAt (hW.mem_nhds hy)) w)
    (ne_of_gt (hB y hy).det_pos) (ne_of_gt (hR y hy).det_pos) δ
  apply flatWeightedBlockEuler (μ := μ) hW (fun y => -φ y) φ
    (flatBaseEulerWeight B R δ) (flatAngularEulerWeight B R δ) v w hφ.neg hφ
    (fun y hy => (hh y hy).1.contDiffWithinAt) (fun y hy => (hh y hy).2.contDiffWithinAt) ?_ hx
  intro η hη hc hs
  rw [← hstat η hη hc hs]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ tsupport η
  · exact (tubeAreaFirstVariation_eq_flatContraction φ v w η y δ
      (Matrix.isHermitian_iff_isSymm.mp (hB y (hs hy)).isHermitian)
      (Matrix.isHermitian_iff_isSymm.mp (hR y (hs hy)).isHermitian)).symm
  · have hv := flatTestContraction_eq_zero_of_notMem_tsupport
      (fun i j z => flatBaseEulerWeight B R δ z * (B z).adjugate i j) v hy
    have hw := flatTestContraction_eq_zero_of_notMem_tsupport
      (fun i j z => flatAngularEulerWeight B R δ z * (R z).adjugate i j) w hy
    rw [hv,hw,zero_add]
    have hz (l m : E) : dirDeriv l (dirDeriv m η) y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht => hy ((tsupport_fderiv_apply_subset ℝ m) ((tsupport_fderiv_apply_subset ℝ l) ht))
    simp [tubeAreaFirstVariation,flatBlockHessian,hz]

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

lemma contDiffAt_flatLogAreaRatio {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ} {x : E}
    (hB : ContDiffAt ℝ ∞ (fun y i j => B y i j) x)
    (hR : ContDiffAt ℝ ∞ (fun y i j => R y i j) x)
    (hBd : (B x).det ≠ 0) (hRd : (R x).det ≠ 0) (δ : ℝ) :
    ContDiffAt ℝ ∞ (flatLogAreaRatio B R δ) x := by
  have hb := (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x hB
  have hr := (continuousDetRows (ι := κ)).contDiff.contDiffAt.comp x hR
  exact contDiffAt_const.mul ((hb.log hBd).sub (hr.log hRd))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma flatEulerWeights_exp {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ} {x : E}
    (hB : 0 < (B x).det) (hR : 0 < (R x).det) {δ c : ℝ} (hc : δ*c = 1-δ) :
    flatBaseEulerWeight B R δ x = -δ * Real.exp (-c * flatLogAreaRatio B R δ x) ∧
      flatAngularEulerWeight B R δ x = (1-δ) * Real.exp (flatLogAreaRatio B R δ x) := by
  unfold flatBaseEulerWeight flatAngularEulerWeight flatLogAreaRatio
  have heB (p : ℝ) : Real.rpow (B x).det p = Real.exp (Real.log (B x).det * p) :=
    Real.rpow_def_of_pos hB p
  have heR (p : ℝ) : Real.rpow (R x).det p = Real.exp (Real.log (R x).det * p) :=
    Real.rpow_def_of_pos hR p
  rw [heB,heR,heB,heR]
  constructor
  · rw [mul_assoc,← Real.exp_add]
    congr 2
    nlinarith [congrArg (fun t : ℝ => Real.log (B x).det * t) hc,
      congrArg (fun t : ℝ => Real.log (R x).det * t) hc]
  · rw [mul_assoc,← Real.exp_add]
    congr 2
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma flatLogAreaRatio_balance {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ} {x : E}
    (hB : 0 < (B x).det) (hR : 0 < (R x).det) {δ c : ℝ} (hc : δ*c = 1-δ) :
    (B x).det * Real.exp (-c * flatLogAreaRatio B R δ x) =
      (R x).det * Real.exp (flatLogAreaRatio B R δ x) := by
  conv_lhs => rw [← Real.exp_log hB]
  conv_rhs => rw [← Real.exp_log hR]
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  unfold flatLogAreaRatio
  nlinarith [congrArg (fun t : ℝ => Real.log (B x).det * t) hc,
    congrArg (fun t : ℝ => Real.log (R x).det * t) hc]

lemma matrix_adjugate_entry {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) (i j : ι) :
    A.adjugate i j = A.det * A⁻¹ i j := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ hA,one_mul]

theorem flat_log_euler_of_weighted {W : Set E} (hW : IsOpen W)
    {B : E → Matrix ι ι ℝ} {R : E → Matrix κ κ ℝ}
    (hB : ∀ x ∈ W, ContDiffAt ℝ ∞ (fun y i j => B y i j) x)
    (hR : ∀ x ∈ W, ContDiffAt ℝ ∞ (fun y i j => R y i j) x)
    (hBd : ∀ x ∈ W, 0 < (B x).det) (hRd : ∀ x ∈ W, 0 < (R x).det)
    (v : ι → E) (w : κ → E) {δ c : ℝ} (hc : δ*c = 1-δ)
    (hnz : δ*c ≠ 0) {x : E} (hx : x ∈ W)
    (heuler :
      (∑ j, ∑ i, (B x).adjugate i j * dirDeriv (v j) (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x) +
      (∑ j, ∑ i, (R x).adjugate i j * dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x) = 0) :
    let t := flatLogAreaRatio B R δ
    flatInverseTrace (B x) v t x - c * flatInversePair (B x) v t t x +
      flatInverseTrace (R x) w t x + flatInversePair (R x) w t t x = 0 := by
  let t := flatLogAreaRatio B R δ
  have ht : ContDiffOn ℝ ∞ t W := fun y hy =>
    (contDiffAt_flatLogAreaRatio (hB y hy) (hR y hy) (ne_of_gt (hBd y hy))
      (ne_of_gt (hRd y hy)) δ).contDiffWithinAt
  have heB : flatBaseEulerWeight B R δ =ᶠ[𝓝 x] (fun y => -δ * Real.exp (-c*t y)) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact (flatEulerWeights_exp (hBd y hy) (hRd y hy) hc).1
  have heR : flatAngularEulerWeight B R δ =ᶠ[𝓝 x] (fun y => (1-δ) * Real.exp (t y)) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact (flatEulerWeights_exp (hBd y hy) (hRd y hy) hc).2
  have hdB (i j : ι) : dirDeriv (v j) (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x =
      δ*c*Real.exp (-c*t x) * (dirDeriv (v j) (dirDeriv (v i) t) x -
        c*dirDeriv (v j) t x*dirDeriv (v i) t x) := by
    rw [second_dirDeriv_congr heB,
      second_dirDeriv_const_mul hW ((contDiffOn_const.mul ht).exp) hx,
      second_dirDeriv_expMul hW ht hx]
    ring
  have hdR (i j : κ) : dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x =
      δ*c*Real.exp (t x) * (dirDeriv (w j) (dirDeriv (w i) t) x +
        dirDeriv (w j) t x*dirDeriv (w i) t x) := by
    rw [second_dirDeriv_congr heR,second_dirDeriv_const_mul hW ht.exp hx]
    have hh := second_dirDeriv_expMul hW ht hx 1 (w j) (w i)
    simp only [one_mul,one_pow] at hh
    rw [hh,← hc]
    ring
  have hbal := flatLogAreaRatio_balance (hBd x hx) (hRd x hx) hc
  change (B x).det * Real.exp (-c*t x) = (R x).det * Real.exp (t x) at hbal
  have hbcon : (∑ j, ∑ i, (B x).adjugate i j * dirDeriv (v j)
      (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x) =
      (δ*c*(R x).det*Real.exp (t x)) *
        (flatInverseTrace (B x) v t x - c*flatInversePair (B x) v t t x) := by
    unfold flatInverseTrace flatInversePair
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hdB,matrix_adjugate_entry (ne_of_gt (hBd x hx))]
    calc
      _ = δ*c*((B x).det*Real.exp (-c*t x)) *
        ((B x)⁻¹ i j * dirDeriv (v j) (dirDeriv (v i) t) x -
          c*((B x)⁻¹ i j*dirDeriv (v j) t x*dirDeriv (v i) t x)) := by ring
      _ = _ := by rw [hbal]; ring
  have hrcon : (∑ j, ∑ i, (R x).adjugate i j * dirDeriv (w j)
      (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x) =
      (δ*c*(R x).det*Real.exp (t x)) *
        (flatInverseTrace (R x) w t x + flatInversePair (R x) w t t x) := by
    unfold flatInverseTrace flatInversePair
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hdR,matrix_adjugate_entry (ne_of_gt (hRd x hx))]
    ring
  rw [hbcon,hrcon,← mul_add] at heuler
  have hz := (mul_eq_zero.mp heuler).resolve_left
    (mul_ne_zero (mul_ne_zero hnz (ne_of_gt (hRd x hx))) (Real.exp_ne_zero _))
  dsimp only
  dsimp only [t] at hz
  linarith

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

lemma second_dirDeriv_sub {W : Set E} (hW : IsOpen W) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    {x : E} (hx : x ∈ W) (v w : E) :
    dirDeriv v (dirDeriv w (fun y => f y-g y)) x =
      dirDeriv v (dirDeriv w f) x-dirDeriv v (dirDeriv w g) x := by
  have he : dirDeriv w (fun y => f y-g y) =ᶠ[𝓝 x]
      (fun y => dirDeriv w f y-dirDeriv w g y) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact dirDeriv_sub ((hf.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) w
  change fderiv ℝ (dirDeriv w (fun y => f y-g y)) x v = _
  rw [he.fderiv_eq]
  exact dirDeriv_sub ((contDiffAt_dirDeriv (hf.contDiffAt (hW.mem_nhds hx)) w).differentiableAt (by simp))
    ((contDiffAt_dirDeriv (hg.contDiffAt (hW.mem_nhds hx)) w).differentiableAt (by simp)) v

lemma flatInverseTrace_sub {W : Set E} (hW : IsOpen W) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    {x : E} (hx : x ∈ W) (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInverseTrace A v (fun y => f y-g y) x =
      flatInverseTrace A v f x-flatInverseTrace A v g x := by
  unfold flatInverseTrace
  simp_rw [second_dirDeriv_sub hW hf hg hx,mul_sub]
  simp only [Finset.sum_sub_distrib]

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

lemma flatInversePair_sub_self {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (v : ι → E) :
    flatInversePair A v (fun y => f y-g y) (fun y => f y-g y) x =
      flatInversePair A v f f x - 2*flatInversePair A v g f x + flatInversePair A v g g x := by
  have he : flatInversePair A v (fun y => f y-g y) (fun y => f y-g y) x =
      flatInversePair A v f f x-flatInversePair A v f g x-
        flatInversePair A v g f x+flatInversePair A v g g x := by
    unfold flatInversePair
    simp_rw [dirDeriv_sub hf hg]
    simp only [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,flatInversePair_symm A hA v f g]
  ring

lemma flatInversePair_sub_right {f g h : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInversePair A v f (fun y => g y-h y) x =
      flatInversePair A v f g x-flatInversePair A v f h x := by
  unfold flatInversePair
  simp_rw [dirDeriv_sub hg hh,mul_sub]
  simp only [Finset.sum_sub_distrib]

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

lemma flatInverseTrace_hessian (φ : E → ℝ) (v : ι → E) (x : E)
    (hd : (flatBlockHessian φ v x).det ≠ 0) :
    flatInverseTrace (flatBlockHessian φ v x) v φ x = Fintype.card ι := by
  exact matrix_inverse_contraction_self hd

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
theorem flat_f_equation_of_log_euler {W : Set E} (hW : IsOpen W)
    {φ t : E → ℝ} (hφ : ContDiffOn ℝ ∞ φ W) (ht : ContDiffOn ℝ ∞ t W)
    (hpos : ∀ y ∈ W, 0 < φ y) (v : ι → E) (w : κ → E)
    {x : E} (hx : x ∈ W) {c : ℝ}
    (hBd : (-flatBlockHessian φ v x).det ≠ 0)
    (hRd : (flatBlockHessian φ w x).det ≠ 0)
    (he : flatInverseTrace (-flatBlockHessian φ v x) v t x -
      c*flatInversePair (-flatBlockHessian φ v x) v t t x +
      flatInverseTrace (flatBlockHessian φ w x) w t x +
      flatInversePair (flatBlockHessian φ w x) w t t x = 0) :
    let B := -flatBlockHessian φ v x
    let R := flatBlockHessian φ w x
    let p := fun y => Real.log (φ y)
    let f := fun y => t y-p y
    (Fintype.card κ : ℝ) - Fintype.card ι + φ x * flatInverseTrace B v f x -
      φ x * flatInversePair B v p p x - c*φ x*flatInversePair B v t t x +
      φ x * flatInverseTrace R w f x + 2*φ x*flatInversePair R w p f x +
      φ x * flatInversePair R w f f x = 0 := by
  let B := -flatBlockHessian φ v x
  let R := flatBlockHessian φ w x
  let p := fun y => Real.log (φ y)
  let f := fun y => t y-p y
  have hp : ContDiffOn ℝ ∞ p W := hφ.log (fun y hy => ne_of_gt (hpos y hy))
  have hpt := (hp.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have htt := (ht.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have hB := flat_log_hessian_trace hW hφ hpos hx B v
  have hR := flat_log_hessian_trace hW hφ hpos hx R w
  rw [flatInverseTrace_neg_hessian φ v x hBd] at hB
  rw [flatInverseTrace_hessian φ w x hRd] at hR
  have hfB := flatInverseTrace_sub hW ht hp hx B v
  have hfR := flatInverseTrace_sub hW ht hp hx R w
  have hpp := flatInversePair_sub_self htt hpt R
    (flatBlockHessian_isSymm (hφ.contDiffAt (hW.mem_nhds hx)) w) w
  have hpf := flatInversePair_sub_right (f := p) htt hpt R w
  change flatInverseTrace B v t x - c*flatInversePair B v t t x +
    flatInverseTrace R w t x + flatInversePair R w t t x = 0 at he
  change flatInverseTrace B v f x = flatInverseTrace B v t x-flatInverseTrace B v p x at hfB
  change flatInverseTrace R w f x = flatInverseTrace R w t x-flatInverseTrace R w p x at hfR
  change flatInversePair R w f f x = flatInversePair R w t t x -
    2*flatInversePair R w p t x+flatInversePair R w p p x at hpp
  change flatInversePair R w p f x = flatInversePair R w p t x-flatInversePair R w p p x at hpf
  change -(Fintype.card ι : ℝ) = φ x *(flatInverseTrace B v p x+flatInversePair B v p p x) at hB
  change (Fintype.card κ : ℝ) = φ x *(flatInverseTrace R w p x+flatInversePair R w p p x) at hR
  change (Fintype.card κ : ℝ) - Fintype.card ι + φ x * flatInverseTrace B v f x -
      φ x * flatInversePair B v p p x - c*φ x*flatInversePair B v t t x +
      φ x * flatInverseTrace R w f x + 2*φ x*flatInversePair R w p f x +
      φ x * flatInversePair R w f f x = 0
  rw [hfB,hfR,hpp,hpf]
  nlinarith [congrArg (fun z : ℝ => φ x*z) he]

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

theorem homogeneousSupport_euler {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {e : E} (hd : DifferentiableAt ℝ (homogeneousSupport K) e) :
    fderiv ℝ (homogeneousSupport K) e e = homogeneousSupport K e := by
  have hh := (gaussPoint_mem_support hK hne hd).2
  rw [real_inner_comm] at hh
  simpa [gaussPoint, gradient] using hh.symm

/- Euler's identity differentiates to the radial null direction of the support
Hessian. This is the ambient version of the spherical radius matrix. -/
theorem homogeneousSupport_hessian_radial {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {e : E} (hh : ContDiffAt ℝ ∞ (homogeneousSupport K) e)
    (v : E) : fderiv ℝ (fderiv ℝ (homogeneousSupport K)) e v e = 0 := by
  have hd := hh.differentiableAt (by simp)
  have hdd := (hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : (fun q => fderiv ℝ (homogeneousSupport K) q q) =ᶠ[𝓝 e]
      homogeneousSupport K := by
    filter_upwards [(hh.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact homogeneousSupport_euler hK hne (hq.differentiableAt (by norm_num))
  have hr := hdd.hasFDerivAt.clm_apply (hasFDerivAt_id e)
  have heq := (hr.congr_of_eventuallyEq he.symm).unique hd.hasFDerivAt
  have hev := congrArg (fun f : E →L[ℝ] ℝ => f v) heq
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, id_eq] at hev
  linarith

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
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportVariation
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
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Homogeneous extension of an actual test function off the affine normal chart. -/

omit [CompleteSpace E] in
lemma contDiffAt_flatNormalProjection (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {q : S × E} (hne : ℓ q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (flatNormalProjection ℓ q₀ C) q := by
  apply C.contDiff.contDiffAt.comp q
  exact (contDiffAt_fst.prodMk
    (((ℓ.contDiff.contDiffAt.comp q contDiffAt_snd).inv hne).smul contDiffAt_snd)).sub contDiffAt_const

omit [CompleteSpace E] in
lemma contDiffAt_flatSupportVariation (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    {q : S × E} (hne : ℓ q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (flatSupportVariation ℓ q₀ C η) q := by
  exact (ℓ.contDiff.contDiffAt.comp q contDiffAt_snd).mul
    (hη.contDiffAt.comp q (contDiffAt_flatNormalProjection ℓ q₀ C hne))

omit [CompleteSpace E] in
lemma flatNormalProjection_on_chart (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (x : F) :
    flatNormalProjection ℓ q₀ C (q₀+J x) = x := by
  have hh : ℓ (q₀+J x).2 = 1 := by simp [hℓ,hJ]
  unfold flatNormalProjection
  rw [hh,inv_one,one_smul]
  change C ((q₀+J x)-q₀) = x
  simpa using hC x

omit [CompleteSpace E] in
lemma flatSupportVariation_on_chart (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (η : F → ℝ) (x : F) :
    flatSupportVariation ℓ q₀ C η (q₀+J x) = η x := by
  simp [flatSupportVariation,flatNormalProjection_on_chart ℓ q₀ C J hℓ hJ hC,hℓ,hJ]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatTestHessian
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
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma flat_hessian_eq_second {n : ℕ} {η : Space n → ℝ} {x : Space n}
    (hη : ContDiffAt ℝ ∞ η x) (i j : Fin n) :
    hessian η x i j = fderiv ℝ (fderiv ℝ η) x (coordinateVector n i) (coordinateVector n j) := by
  have hd := ((hη.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (coordinateVector n j) x)
  change fderiv ℝ (fun y => fderiv ℝ η y (coordinateVector n j)) x (coordinateVector n i) = _
  rw [he.fderiv]
  simp

omit [CompleteSpace S] [CompleteSpace E]

lemma flatSupportVariation_second_on_chart (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    (x v w : F) :
    fderiv ℝ (fderiv ℝ (flatSupportVariation ℓ q₀ C η)) (q₀+J x) (J v) (J w) =
      fderiv ℝ (fderiv ℝ η) x v w := by
  have hG := contDiffAt_flatSupportVariation ℓ q₀ C hη
    (q := q₀+J x) (by simp [hℓ,hJ])
  rw [← second_fderiv_affine_comp J q₀ hG]
  have he : (fun x => flatSupportVariation ℓ q₀ C η (q₀+J x)) = η :=
    funext (flatSupportVariation_on_chart ℓ q₀ C J hℓ hJ hC η)
  rw [he]

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ]

lemma flatSupportVariation_baseMatrix {n : ℕ} (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] Space n) (J : Space n →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) {η : Space n → ℝ} (hη : ContDiff ℝ ∞ η)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    (x : Space n) (i j : ι) :
    tubeBaseMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bS i j =
      -hessian η x (e.symm (Sum.inl i)) (e.symm (Sum.inl j)) := by
  have ht (i : ι) : J (coordinateVector n (e.symm (Sum.inl i))) = (bS i,0) := by
    simp [hJb,tubeTangent]
  have hh := flatSupportVariation_second_on_chart ℓ q₀ C J hℓ hJ hC hη x
    (coordinateVector n (e.symm (Sum.inl i))) (coordinateVector n (e.symm (Sum.inl j)))
  rw [ht,ht] at hh
  change -_ = -_
  congr 1
  rw [hh]
  exact (flat_hessian_eq_second hη.contDiffAt _ _).symm

lemma flatSupportVariation_radiusMatrix {n : ℕ} (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] Space n) (J : Space n →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) {η : Space n → ℝ} (hη : ContDiff ℝ ∞ η)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    (x : Space n) (i j : κ) :
    tubeRadiusMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bE i j =
      hessian η x (e.symm (Sum.inr i)) (e.symm (Sum.inr j)) := by
  have ht (i : κ) : J (coordinateVector n (e.symm (Sum.inr i))) = (0,bE (Sum.inl i)) := by
    simp [hJb,tubeTangent]
  have hh := flatSupportVariation_second_on_chart ℓ q₀ C J hℓ hJ hC hη x
    (coordinateVector n (e.symm (Sum.inr i))) (coordinateVector n (e.symm (Sum.inr j)))
  rw [ht,ht] at hh
  change _ = _
  rw [show tubeRadiusMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bE i j = _ from hh]
  exact (flat_hessian_eq_second hη.contDiffAt _ _).symm

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatTubeChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section FlatTubeChart
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype κ]

lemma tubeBaseMatrix_eq_flatBlockHessian {n : ℕ} {H : S × E → ℝ}
    (q₀ : S × E) (J : Space n →L[ℝ] S × E) {x : Space n}
    (hH : ContDiffAt ℝ ∞ H (q₀+J x))
    (bS : Module.Basis ι ℝ S) (v : ι → Space n) (hv : ∀ i, J (v i) = (bS i,0)) :
    tubeBaseMatrix H (q₀+J x) bS =
      flatBlockHessian (fun y => -H (q₀+J y)) v x := by
  rw [flatBlockHessian_neg]
  ext i j
  change -fderiv ℝ (fderiv ℝ H) (q₀+J x) (bS i,0) (bS j,0) =
    -dirDeriv (v i) (dirDeriv (v j) (fun y => H (q₀+J y))) x
  rw [dirDeriv_eq_second (f := fun y => H (q₀+J y))
    (hH.comp x (contDiffAt_const.add J.contDiff.contDiffAt)),
    second_fderiv_affine_comp J q₀ hH,hv,hv]

lemma tubeRadiusMatrix_eq_flatBlockHessian {n : ℕ} {H : S × E → ℝ}
    (q₀ : S × E) (J : Space n →L[ℝ] S × E) {x : Space n}
    (hH : ContDiffAt ℝ ∞ H (q₀+J x))
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (w : κ → Space n)
    (hw : ∀ i, J (w i) = (0,bE (Sum.inl i))) :
    tubeRadiusMatrix H (q₀+J x) bE =
      flatBlockHessian (fun y => H (q₀+J y)) w x := by
  ext i j
  change fderiv ℝ (fderiv ℝ H) (q₀+J x) (0,bE (Sum.inl i)) (0,bE (Sum.inl j)) =
    dirDeriv (w i) (dirDeriv (w j) (fun y => H (q₀+J y))) x
  rw [dirDeriv_eq_second (f := fun y => H (q₀+J y))
    (hH.comp x (contDiffAt_const.add J.contDiff.contDiffAt)),
    second_fderiv_affine_comp J q₀ hH,hw,hw]

end FlatTubeChart

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The pointwise flat-normal tube Euler equation, derived from the original
PDE by actual support variations and two compact integrations by parts. -/
theorem affineMaximal_flat_tube_euler {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (q₀ : S × E) (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let φ := fun x => H (q₀+J x)
    let v := fun i : ι => coordinateVector n (e.symm (Sum.inl i))
    let w := fun i : κ => coordinateVector n (e.symm (Sum.inr i))
    let B := fun y => flatBlockHessian (fun z => -φ z) v y
    let R := fun y => flatBlockHessian φ w y
    let δ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    (∑ j, ∑ i, (B x₀).adjugate i j * dirDeriv (v j) (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x₀) +
      (∑ j, ∑ i, (R x₀).adjugate i j * dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x₀) = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let φ := fun x => H (q₀+J x)
  let v := fun i : ι => coordinateVector n (e.symm (Sum.inl i))
  let w := fun i : κ => coordinateVector n (e.symm (Sum.inr i))
  let B := fun y => flatBlockHessian (fun z => -φ z) v y
  let R := fun y => flatBlockHessian φ w y
  let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
  let ℓ := InnerProductSpace.toDual ℝ E (bE (Sum.inr ()))
  have hℓ : ℓ q₀.2 = 1 := by simpa [ℓ,real_inner_comm] using hd
  have hℓJ (x : Space n) : ℓ (J x).2 = 0 := by simpa [ℓ,real_inner_comm] using hJ x
  have hv (i : ι) : J (v i) = (bS i,0) := by simp [v,hJb,tubeTangent]
  have hw (i : κ) : J (w i) = (0,bE (Sum.inl i)) := by simp [w,hJb,tubeTangent]
  obtain ⟨W,hW,hxW,hWD,hstat⟩ := affineMaximal_flat_tube_weak_euler hΩ hcv hu hp hm
    a L hD hK hzero bS bE q₀ hd J hi hJ C hC e hJb hx₀
  have hq (x : Space n) : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by
    simp [inner_add_left,hd,hJ]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    simpa [hz] using hq x
  have hH (x : Space n) (hx : x ∈ W) : ContDiffAt ℝ ∞ H (q₀+J x) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero (hWD hx) (hne x)).1
  have hφ : ContDiffOn ℝ ∞ φ W := fun x hx =>
    ((hH x hx).comp x (contDiffAt_const.add J.contDiff.contDiffAt)).contDiffWithinAt
  have hBe (x : Space n) (hx : x ∈ W) : tubeBaseMatrix H (q₀+J x) bS = B x :=
    tubeBaseMatrix_eq_flatBlockHessian q₀ J (hH x hx) bS v hv
  have hRe (x : Space n) (hx : x ∈ W) : tubeRadiusMatrix H (q₀+J x) bE = R x :=
    tubeRadiusMatrix_eq_flatBlockHessian q₀ J (hH x hx) bE w hw
  have hpos (x : Space n) (hx : x ∈ W) : (B x).PosDef ∧ (R x).PosDef := by
    have hh := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero (hWD hx)
      (e := (q₀+J x).2) bS bE (by rw [hq x]; norm_num)
    change (tubeBaseMatrix H (q₀+J x) bS).PosDef ∧
      (tubeRadiusMatrix H (q₀+J x) bE).PosDef at hh
    rwa [hBe x hx,hRe x hx] at hh
  apply flatTubeEuler_of_stationary (μ := volume) hW φ v w δ hφ
    (fun x hx => (hpos x hx).1) (fun x hx => (hpos x hx).2) ?_ hxW
  intro η hη hc hs
  have hweak := hstat (tsupport η) hc.isCompact hs η hη Subset.rfl
  have hGBe (x : Space n) : tubeBaseMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bS =
      -flatBlockHessian η v x := by
    ext i j
    rw [flatSupportVariation_baseMatrix ℓ q₀ C J hℓ hℓJ hC hη bS bE e hJb]
    rfl
  have hGRe (x : Space n) : tubeRadiusMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bE =
      flatBlockHessian η w x := by
    ext i j
    rw [flatSupportVariation_radiusMatrix ℓ q₀ C J hℓ hℓJ hC hη bS bE e hJb]
    rfl
  have heq := setIntegral_congr_fun (μ := volume) hc.isCompact.measurableSet
    (fun x (hx : x ∈ tsupport η) =>
      congrArg₂ (fun l r => tubeAreaFirstVariation l (-flatBlockHessian η v x) r
        (flatBlockHessian η w x) δ) (hBe x (hs hx)) (hRe x (hs hx)))
  change (∫ x in tsupport η, tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
    (tubeBaseMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bS)
    (tubeRadiusMatrix H (q₀+J x) bE)
    (tubeRadiusMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bE) δ) = 0 at hweak
  simp_rw [hGBe,hGRe] at hweak
  rw [heq] at hweak
  rw [← hweak]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz (l m : Space n) : dirDeriv l (dirDeriv m η) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun ht => hx ((tsupport_fderiv_apply_subset ℝ m) ((tsupport_fderiv_apply_subset ℝ l) ht))
  simp [tubeAreaFirstVariation,flatBlockHessian,hz]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualFlatFEquation
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

/- Actual original PDE implies the support tube f equation in every flat normal chart. -/
theorem affineMaximal_flat_tube_f_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (q₀ : S × E) (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let φ := fun x => H (q₀+J x)
    let v := fun i : ι => coordinateVector n (e.symm (Sum.inl i))
    let w := fun i : κ => coordinateVector n (e.symm (Sum.inr i))
    let B := fun y => flatBlockHessian (fun z => -φ z) v y
    let R := fun y => flatBlockHessian φ w y
    let δ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let t := flatLogAreaRatio B R δ
    let p := fun y => Real.log (φ y)
    let f := fun y => t y-p y
    (n : ℝ) - 2*Fintype.card ι + φ x₀*flatInverseTrace (B x₀) v f x₀ -
      φ x₀*flatInversePair (B x₀) v p p x₀ -
      ((n : ℝ)+1)*φ x₀*flatInversePair (B x₀) v t t x₀ +
      φ x₀*flatInverseTrace (R x₀) w f x₀ +
      2*φ x₀*flatInversePair (R x₀) w p f x₀ +
      φ x₀*flatInversePair (R x₀) w f f x₀ = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let φ := fun x => H (q₀+J x)
  let v := fun i : ι => coordinateVector n (e.symm (Sum.inl i))
  let w := fun i : κ => coordinateVector n (e.symm (Sum.inr i))
  let B := fun y => flatBlockHessian (fun z => -φ z) v y
  let R := fun y => flatBlockHessian φ w y
  let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
  let t := flatLogAreaRatio B R δ
  let p := fun y => Real.log (φ y)
  let f := fun y => t y-p y
  let W : Set (Space n) := {x | (q₀+J x).1 ∈ D}
  have hW : IsOpen W := hD.preimage (continuous_const.add J.continuous).fst
  have hxW : x₀ ∈ W := hx₀
  have hv (i : ι) : J (v i) = (bS i,0) := by simp [v,hJb,tubeTangent]
  have hw (i : κ) : J (w i) = (0,bE (Sum.inl i)) := by simp [w,hJb,tubeTangent]
  have hq (x : Space n) : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by
    simp [inner_add_left,hd,hJ]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    have hinner := hq x
    simp [hz] at hinner
  have hH (x : Space n) (hx : x ∈ W) : ContDiffAt ℝ ∞ H (q₀+J x) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hx (hne x)).1
  have hφ : ContDiffOn ℝ ∞ φ W := fun x hx =>
    ((hH x hx).comp x (contDiffAt_const.add J.contDiff.contDiffAt)).contDiffWithinAt
  have hBe (x : Space n) (hx : x ∈ W) : tubeBaseMatrix H (q₀+J x) bS = B x :=
    tubeBaseMatrix_eq_flatBlockHessian q₀ J (hH x hx) bS v hv
  have hRe (x : Space n) (hx : x ∈ W) : tubeRadiusMatrix H (q₀+J x) bE = R x :=
    tubeRadiusMatrix_eq_flatBlockHessian q₀ J (hH x hx) bE w hw
  have hpos (x : Space n) (hx : x ∈ W) : (B x).PosDef ∧ (R x).PosDef := by
    have hh := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero hx
      (e := (q₀+J x).2) bS bE (by rw [hq x]; norm_num)
    change (tubeBaseMatrix H (q₀+J x) bS).PosDef ∧
      (tubeRadiusMatrix H (q₀+J x) bE).PosDef at hh
    rwa [hBe x hx,hRe x hx] at hh
  have hφpos (x : Space n) (hx : x ∈ W) : 0 < φ x := by
    apply supportValue_pos (hK _ hx) (hzero _ hx)
    intro hz
    exact hne x ((InnerProductSpace.toDual ℝ E).injective (by simpa using hz))
  have hB (x : Space n) (hx : x ∈ W) : ContDiffAt ℝ ∞ (fun y i j => B y i j) x :=
    contDiffAt_flatBlockHessian (hφ.contDiffAt (hW.mem_nhds hx)).neg v
  have hR (x : Space n) (hx : x ∈ W) : ContDiffAt ℝ ∞ (fun y i j => R y i j) x :=
    contDiffAt_flatBlockHessian (hφ.contDiffAt (hW.mem_nhds hx)) w
  have hdim : (Fintype.card ι : ℝ) + Fintype.card κ = n := by
    have hh := Fintype.card_congr e
    simp only [Fintype.card_fin,Fintype.card_sum] at hh
    exact_mod_cast hh.symm
  have hden : (Fintype.card ι : ℝ)+Fintype.card κ+2 ≠ 0 := by positivity
  have hc : δ*((n : ℝ)+1) = 1-δ := by
    dsimp only [δ]
    rw [hdim]
    field_simp
    ring
  have hnz : δ*((n : ℝ)+1) ≠ 0 := mul_ne_zero (one_div_ne_zero hden) (by positivity)
  have he := affineMaximal_flat_tube_euler hΩ hcv hu hp hm a L hD hK hzero bS bE
    q₀ hd J hi hJ C hC e hJb hx₀
  change (∑ j, ∑ i, (B x₀).adjugate i j * dirDeriv (v j) (dirDeriv (v i)
      (flatBaseEulerWeight B R δ)) x₀) + (∑ j, ∑ i, (R x₀).adjugate i j *
      dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x₀) = 0 at he
  have hlog := flat_log_euler_of_weighted hW hB hR
    (fun x hx => (hpos x hx).1.det_pos) (fun x hx => (hpos x hx).2.det_pos) v w hc hnz hxW he
  have ht : ContDiffOn ℝ ∞ t W := fun x hx =>
    (contDiffAt_flatLogAreaRatio (hB x hx) (hR x hx)
      (ne_of_gt (hpos x hx).1.det_pos) (ne_of_gt (hpos x hx).2.det_pos) δ).contDiffWithinAt
  have heB (y : Space n) : B y = -flatBlockHessian φ v y := flatBlockHessian_neg φ v y
  have hBd : (-flatBlockHessian φ v x₀).det ≠ 0 := by
    rw [← heB]; exact ne_of_gt (hpos x₀ hxW).1.det_pos
  change flatInverseTrace (B x₀) v t x₀ - ((n : ℝ)+1)*flatInversePair (B x₀) v t t x₀ +
    flatInverseTrace (R x₀) w t x₀ + flatInversePair (R x₀) w t t x₀ = 0 at hlog
  rw [heB] at hlog
  have hf := flat_f_equation_of_log_euler hW hφ ht hφpos v w hxW hBd
    (ne_of_gt (hpos x₀ hxW).2.det_pos) hlog
  change (Fintype.card κ : ℝ) - Fintype.card ι + φ x₀*flatInverseTrace (-flatBlockHessian φ v x₀) v f x₀ -
      φ x₀*flatInversePair (-flatBlockHessian φ v x₀) v p p x₀ -
      ((n : ℝ)+1)*φ x₀*flatInversePair (-flatBlockHessian φ v x₀) v t t x₀ +
      φ x₀*flatInverseTrace (R x₀) w f x₀ + 2*φ x₀*flatInversePair (R x₀) w p f x₀ +
      φ x₀*flatInversePair (R x₀) w f f x₀ = 0 at hf
  rw [← heB] at hf
  change (n : ℝ) - 2*Fintype.card ι + φ x₀*flatInverseTrace (B x₀) v f x₀ -
      φ x₀*flatInversePair (B x₀) v p p x₀ -
      ((n : ℝ)+1)*φ x₀*flatInversePair (B x₀) v t t x₀ +
      φ x₀*flatInverseTrace (R x₀) w f x₀ + 2*φ x₀*flatInversePair (R x₀) w p f x₀ +
      φ x₀*flatInversePair (R x₀) w f f x₀ = 0
  linarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_BlockNewton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section BlockNewton
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adjugate_fromBlocks_scalar (A : Matrix ι ι ℝ) (t : ℝ) (i j : ι) :
    (Matrix.fromBlocks A 0 0 (t • (1 : Matrix Unit Unit ℝ))).adjugate
      (Sum.inl i) (Sum.inl j) = t * A.adjugate i j := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  have hh : (Matrix.fromBlocks A 0 0 (t • (1 : Matrix Unit Unit ℝ))).updateRow
      (Sum.inl j) (Pi.single (Sum.inl i) 1) =
      Matrix.fromBlocks (A.updateRow j (Pi.single i 1)) 0 0 (t • (1 : Matrix Unit Unit ℝ)) := by
    ext l m
    cases l with
    | inl l =>
      cases m with
      | inl m => simp [Matrix.updateRow_apply, Pi.single_apply, Matrix.fromBlocks]
      | inr m => simp [Matrix.updateRow_apply, Matrix.fromBlocks]
    | inr l =>
      cases m <;> simp [Matrix.updateRow_apply, Matrix.fromBlocks]
  rw [hh, Matrix.det_fromBlocks_zero₂₁]
  simp [mul_comm]

end BlockNewton
open scoped Matrix

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_RadialAdjugate
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

lemma adjugate_block_radial (R : Matrix ι ι ℝ) :
    (Matrix.fromBlocks R 0 0 (0 : Matrix Unit Unit ℝ)).adjugate =
      Matrix.fromBlocks 0 0 0 (R.det • (1 : Matrix Unit Unit ℝ)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := adjugate_fromBlocks_scalar R 0 i j
      simpa using hh
    | inr j =>
      cases j
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_column_eq_zero (Sum.inr ())
      intro l
      cases l <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
  | inr i =>
    cases i
    cases j with
    | inl j =>
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inr ())
      intro l
      cases l <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
    | inr j =>
      cases j
      rw [Matrix.adjugate_apply]
      have hh : (Matrix.fromBlocks R 0 0 (0 : Matrix Unit Unit ℝ)).updateRow
          (Sum.inr ()) (Pi.single (Sum.inr ()) 1) = Matrix.fromBlocks R 0 0 (1 : Matrix Unit Unit ℝ) := by
        ext l m
        cases l <;> cases m <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
      rw [hh,Matrix.det_fromBlocks_zero₂₁]
      simp

lemma radialShear_det (e : ι ⊕ Unit → ℝ) : (radialShear e).det = 1 := by
  rw [radialShear,Matrix.det_fromBlocks_zero₂₁]
  simp

omit [Fintype ι] in
lemma radialShear_last (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1) (i : ι ⊕ Unit) :
    radialShear e i (Sum.inr ()) = e i := by
  cases i <;> simp [radialShear,Matrix.fromBlocks,he]

lemma mul_radialShear_left (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (i : ι ⊕ Unit) (j : ι) :
    (A * radialShear e) i (Sum.inl j) = A i (Sum.inl j) := by
  simp [Matrix.mul_apply,Fintype.sum_sum_type,radialShear,Matrix.fromBlocks,Matrix.one_apply]

lemma transpose_radialShear_mul_left (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (i : ι) (j : ι ⊕ Unit) :
    ((radialShear e)ᵀ * A) (Sum.inl i) j = A (Sum.inl i) j := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type,radialShear,
    Matrix.fromBlocks,Matrix.one_apply]

lemma mul_radialShear_last (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1) (i : ι ⊕ Unit) :
    (A * radialShear e) i (Sum.inr ()) = (A *ᵥ e) i := by
  simp only [Matrix.mul_apply,radialShear_last e he,Matrix.mulVec, dotProduct]

lemma radialShear_conjugate {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) :
    (radialShear e)ᵀ * A * radialShear e =
      Matrix.fromBlocks (A.submatrix Sum.inl Sum.inl) 0 0 (0 : Matrix Unit Unit ℝ) := by
  have hs : ((radialShear e)ᵀ * A * radialShear e).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.transpose_mul,Matrix.transpose_transpose,hA.eq,Matrix.mul_assoc]
  have hlast (i : ι ⊕ Unit) : ((radialShear e)ᵀ * A * radialShear e) i (Sum.inr ()) = 0 := by
    rw [Matrix.mul_assoc,Matrix.mul_apply]
    simp [mul_radialShear_last A e he,hz]
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [Matrix.mul_assoc,transpose_radialShear_mul_left,mul_radialShear_left]
      rfl
    | inr j => cases j; exact hlast _
  | inr i =>
    cases i
    cases j with
    | inl j => rw [← hs.apply]; exact hlast _
    | inr j => cases j; exact hlast _

/- A symmetric form with radial null vector has its full adjugate equal to
its transverse principal minor times the radial outer product. This includes
all empty transverse blocks and needs no invertibility of the full matrix. -/
theorem radial_adjugate {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) (i j : ι ⊕ Unit) :
    A.adjugate i j = (A.submatrix Sum.inl Sum.inl).det * e i * e j := by
  let P := radialShear e
  let d := (A.submatrix Sum.inl Sum.inl).det
  have hP : P.det = 1 := radialShear_det e
  have hp : P * P.adjugate = 1 := by rw [Matrix.mul_adjugate,hP,one_smul]
  have hpt : (Pᵀ).adjugate * Pᵀ = 1 := by
    rw [Matrix.adjugate_mul,Matrix.det_transpose,hP,one_smul]
  have hh := congrArg Matrix.adjugate (radialShear_conjugate hA e he hz)
  rw [adjugate_block_radial,Matrix.adjugate_mul_distrib,Matrix.adjugate_mul_distrib] at hh
  have hmul := congrArg (fun M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ => P*M*Pᵀ) hh
  change P * (P.adjugate * (A.adjugate * (Pᵀ).adjugate)) * Pᵀ =
    P*Matrix.fromBlocks 0 0 0 (d • (1 : Matrix Unit Unit ℝ))*Pᵀ at hmul
  have heq : A.adjugate = P*Matrix.fromBlocks 0 0 0 (d • (1 : Matrix Unit Unit ℝ))*Pᵀ := by
    calc
      _ = (P*P.adjugate)*A.adjugate*((Pᵀ).adjugate*Pᵀ) := by rw [hp,hpt,Matrix.one_mul,Matrix.mul_one]
      _ = _ := by simpa only [Matrix.mul_assoc] using hmul
  rw [heq]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,zero_add,
    Fintype.sum_unique,Matrix.smul_apply,Matrix.one_apply,ite_true,smul_eq_mul,mul_one]
  change (P i (Sum.inr ()) * d)*P j (Sum.inr ()) = _
  dsimp only [P,d]
  rw [radialShear_last e he,radialShear_last e he]
  ring

lemma radial_adjugate_trace {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) :
    A.adjugate.trace = (A.submatrix Sum.inl Sum.inl).det * ∑ i, e i * e i := by
  simp only [Matrix.trace,Matrix.diag,radial_adjugate hA e he hz,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonBasis
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
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_symm {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    (tubeFullRadiusMatrix H q b).IsSymm := by
  have hh := hH.isSymmSndFDerivAt (by simp)
  ext i j
  exact hh.eq _ _

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_radial {H : S × E → ℝ} {q : S × E}
    (b : OrthonormalBasis ι ℝ E)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0) :
    tubeFullRadiusMatrix H q b *ᵥ (b.repr q.2) = 0 := by
  ext i
  have hh := hr (b i)
  have he : ((0:S),q.2) = ∑ j, b.repr q.2 j • (0,b j) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' q.2).symm
  rw [he] at hh
  simp only [map_sum,map_smul,smul_eq_mul] at hh
  simpa [Matrix.mulVec,dotProduct,tubeFullRadiusMatrix,map_sum,map_smul,mul_comm] using hh

/- The full cofactor trace recovers the transverse determinant in every flat
normal chart. No unit-normal constraint is imposed away from the chart center. -/
omit [CompleteSpace E] in
lemma tubeAngularDensity_flat {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : inner ℝ q.2 (b (Sum.inr ())) = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0) :
    tubeAngularDensity H q b = (tubeRadiusMatrix H q b).det * inner ℝ q.2 q.2 := by
  have hc : b.repr q.2 (Sum.inr ()) = 1 := by
    simpa [OrthonormalBasis.repr_apply_apply,real_inner_comm] using he
  have hh := radial_adjugate_trace (tubeFullRadiusMatrix_symm hH b)
    (b.repr q.2) hc (tubeFullRadiusMatrix_radial b hr)
  change tubeAngularDensity H q b = (tubeRadiusMatrix H q b).det * _ at hh
  rw [← b.sum_inner_mul_inner q.2 q.2]
  simpa [OrthonormalBasis.repr_apply_apply,real_inner_comm q.2] using hh

omit [CompleteSpace E] in
lemma invariantTubeF_eq_flat {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S)
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : inner ℝ q.2 (b (Sum.inr ())) = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0)
    (hR : (tubeRadiusMatrix H q b).det ≠ 0) (δ : ℝ) :
    invariantTubeF H bS b δ q =
      δ * (Real.log (tubeBaseMatrix H q bS).det - Real.log (tubeRadiusMatrix H q b).det) -
        Real.log (H q) := by
  have hq : q.2 ≠ 0 := by intro hz; simp [hz] at he
  have hh : inner ℝ q.2 q.2 ≠ 0 := (real_inner_self_pos.mpr hq).ne'
  rw [invariantTubeF,tubeAngularDensity_flat hH b he hr,Real.log_mul hR hh]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualInvariantTube
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

lemma affineEpigraph_support_radial {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0) (v : E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hh := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  change ContDiffAt ℝ ∞ H (s,e) at hh
  change fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0
  rw [← second_fderiv_prod_right hh]
  exact homogeneousSupport_hessian_radial (hK s hs) ⟨0,interior_subset (hzero s hs)⟩
    (hh.comp e (contDiffAt_const.prodMk contDiffAt_id)) v

/- The invariant angular determinant is strictly positive on every actual
nonzero fiber conormal, independently of the fixed orthonormal frame. -/

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

lemma flatInverseTrace_affine_pullback {f : F → ℝ} (q₀ : F) (J : E →L[ℝ] F) {x : E}
    (hf : ContDiffAt ℝ ∞ f (q₀+J x)) (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInverseTrace A v (fun y => f (q₀+J y)) x =
      flatInverseTrace A (fun i => J (v i)) f (q₀+J x) := by
  have hh : ContDiffAt ℝ ∞ (fun y => f (q₀+J y)) x :=
    hf.comp x (contDiffAt_const.add J.contDiff.contDiffAt)
  simp only [flatInverseTrace,dirDeriv_eq_second hh,dirDeriv_eq_second hf,
    second_fderiv_affine_comp J q₀ hf]

lemma flatInversePair_affine_pullback {f g : F → ℝ} (q₀ : F) (J : E →L[ℝ] F) {x : E}
    (hf : DifferentiableAt ℝ f (q₀+J x)) (hg : DifferentiableAt ℝ g (q₀+J x))
    (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInversePair A v (fun y => f (q₀+J y)) (fun y => g (q₀+J y)) x =
      flatInversePair A (fun i => J (v i)) f g (q₀+J x) := by
  simp only [flatInversePair,dirDeriv_affine_pullback q₀ J hf,dirDeriv_affine_pullback q₀ J hg]

lemma flatInverseTrace_congr {f g : E → ℝ} {x : E} (hx : f =ᶠ[𝓝 x] g)
    (A : Matrix ι ι ℝ) (v : ι → E) : flatInverseTrace A v f x = flatInverseTrace A v g x := by
  simp only [flatInverseTrace,second_dirDeriv_congr hx]

lemma flatInversePair_congr {f f' g g' : E → ℝ} {x : E}
    (hf : f =ᶠ[𝓝 x] f') (hg : g =ᶠ[𝓝 x] g') (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInversePair A v f g x = flatInversePair A v f' g' x := by
  simp only [flatInversePair,dirDeriv,hf.fderiv_eq,hg.fderiv_eq]

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

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma tubeTangent_linearIndependent (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) : LinearIndependent ℝ (tubeTangent bS bE) := by
  let j : ι ⊕ κ → ι ⊕ (κ ⊕ Unit) := Sum.map id Sum.inl
  have hj : Function.Injective j := Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩
  have hh := (bS.prod bE.toBasis).linearIndependent.comp j hj
  have heq : tubeTangent bS bE = (bS.prod bE.toBasis) ∘ j := by
    funext i
    cases i <;> simp [tubeTangent,j]
  rw [heq]
  exact hh

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
omit [DecidableEq ι] in
lemma exists_flat_tube_chart {n : ℕ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (e : Fin n ≃ ι ⊕ κ) :
    ∃ (J : Space n →L[ℝ] S × E) (C : S × E →L[ℝ] Space n),
      Function.Injective J ∧ (∀ x, C (J x) = x) ∧
      (∀ x, inner ℝ (J x).2 (bE (Sum.inr ())) = 0) ∧
      (∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i)) := by
  let : FiniteDimensional ℝ S := Module.Finite.of_basis bS
  let : FiniteDimensional ℝ E := Module.Finite.of_basis bE.toBasis
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hb (i : Fin n) : b i = coordinateVector n i := by
    exact EuclideanSpace.basisFun_apply (Fin n) ℝ i
  let j := b.constr ℝ (tubeTangent bS bE ∘ e)
  have hj : Function.Injective j := b.injective_constr_of_linearIndependent
    ((tubeTangent_linearIndependent bS bE).comp e e.injective)
  obtain ⟨c,hc⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  let J := j.toContinuousLinearMap
  let C := c.toContinuousLinearMap
  have hJ (i : Fin n) : J (coordinateVector n i) = tubeTangent bS bE (e i) := by
    change j (coordinateVector n i) = _
    rw [← hb]
    exact b.constr_basis ℝ _ i
  refine ⟨J,C,hj,?_,?_,hJ⟩
  · intro x
    exact congrArg (fun l : Space n →ₗ[ℝ] Space n => l x) hc
  · have ht : ((InnerProductSpace.toDual ℝ E (bE (Sum.inr ()))).comp
        ((ContinuousLinearMap.snd ℝ S E).comp J)).toLinearMap = 0 := by
      apply b.ext
      intro i
      change inner ℝ (bE (Sum.inr ())) (J (b i)).2 = 0
      rw [hb i,hJ]
      cases h : e i with
      | inl k => simp [tubeTangent]
      | inr k => simp [tubeTangent,bE.inner_eq_ite]
    intro x
    have hh := congrArg (fun l : Space n →ₗ[ℝ] ℝ => l x) ht
    simpa [real_inner_comm] using hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualAmbientFEquation
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

lemma affineMaximal_flat_invariant_f_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (q₀ : S × E) (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let q := q₀+J x₀
    let B := tubeBaseMatrix H q bS
    let R := tubeRadiusMatrix H q bE
    let V := fun i : ι => ((bS i), (0:E))
    let W := fun i : κ => ((0:S), bE (Sum.inl i))
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let F := invariantTubeF H bS bE δ
    let P := fun y => Real.log (H y)
    let T := fun y => F y+P y
    (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
      H q*flatInversePair B V P P q -
      ((n : ℝ)+1)*H q*flatInversePair B V T T q +
      H q*flatInverseTrace R W F q + 2*H q*flatInversePair R W P F q +
      H q*flatInversePair R W F F q = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let φ := fun x => H (q₀+J x)
  let v := fun i : ι => coordinateVector n (e.symm (Sum.inl i))
  let w := fun i : κ => coordinateVector n (e.symm (Sum.inr i))
  let B := fun y => flatBlockHessian (fun z => -φ z) v y
  let R := fun y => flatBlockHessian φ w y
  let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
  let t := flatLogAreaRatio B R δ
  let p := fun y => Real.log (φ y)
  let f := fun y => t y-p y
  let F := invariantTubeF H bS bE δ
  let P := fun y => Real.log (H y)
  let T := fun y => F y+P y
  let U : Set (Space n) := {x | (q₀+J x).1 ∈ D}
  have hU : IsOpen U := hD.preimage (continuous_const.add J.continuous).fst
  have hxU : x₀ ∈ U := hx₀
  have hv (i : ι) : J (v i) = (bS i,0) := by simp [v,hJb,tubeTangent]
  have hw (i : κ) : J (w i) = (0,bE (Sum.inl i)) := by simp [w,hJb,tubeTangent]
  have hq (x : Space n) : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by
    simp [inner_add_left,hd,hJ]
  have he (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    have hinner := hq x
    simp [hz] at hinner
  have hHs (x : Space n) (hx : x ∈ U) : ContDiffAt ℝ ∞ H (q₀+J x) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hx (he x)).1
  have hfe : f =ᶠ[𝓝 x₀] (fun y => F (q₀+J y)) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    have hpos := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero hy bS bE
      (show inner ℝ (q₀+J y).2 (bE (Sum.inr ())) ≠ 0 by rw [hq]; norm_num)
    have hh := invariantTubeF_eq_flat (hHs y hy) bS bE (hq y)
      (affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hy (he y))
      hpos.2.det_pos.ne' δ
    rw [tubeBaseMatrix_eq_flatBlockHessian q₀ J (hHs y hy) bS v hv,
      tubeRadiusMatrix_eq_flatBlockHessian q₀ J (hHs y hy) bE w hw] at hh
    exact hh.symm
  have hte : t =ᶠ[𝓝 x₀] (fun y => T (q₀+J y)) := by
    filter_upwards [hfe] with y hy
    change t y-p y = F (q₀+J y) at hy
    change t y = F (q₀+J y)+p y
    linarith
  have hF : ContDiffAt ℝ ∞ F (q₀+J x₀) :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hx₀ (he x₀) bS bE δ
  have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hx₀ (he x₀) bS bE
  have hP : ContDiffAt ℝ ∞ P (q₀+J x₀) := (hHs x₀ hxU).log hpos.2.2.ne'
  have hT : ContDiffAt ℝ ∞ T (q₀+J x₀) := hF.add hP
  have hfeq := affineMaximal_flat_tube_f_equation hΩ hcv hu hp hm a L hD hK hzero
    bS bE q₀ hd J hi hJ C hC e hJb hx₀
  change (n : ℝ) - 2*Fintype.card ι + φ x₀*flatInverseTrace (B x₀) v f x₀ -
      φ x₀*flatInversePair (B x₀) v p p x₀ -
      ((n : ℝ)+1)*φ x₀*flatInversePair (B x₀) v t t x₀ +
      φ x₀*flatInverseTrace (R x₀) w f x₀ + 2*φ x₀*flatInversePair (R x₀) w p f x₀ +
      φ x₀*flatInversePair (R x₀) w f f x₀ = 0 at hfeq
  rw [flatInverseTrace_congr hfe (B x₀) v,flatInverseTrace_congr hfe (R x₀) w,
    flatInversePair_congr hte hte (B x₀) v,
    flatInversePair_congr (Filter.EventuallyEq.rfl : p =ᶠ[𝓝 x₀] p) hfe (R x₀) w,
    flatInversePair_congr hfe hfe (R x₀) w] at hfeq
  change (n : ℝ) - 2*Fintype.card ι + H (q₀+J x₀)*flatInverseTrace (B x₀) v (fun y => F (q₀+J y)) x₀ -
      H (q₀+J x₀)*flatInversePair (B x₀) v (fun y => P (q₀+J y)) (fun y => P (q₀+J y)) x₀ -
      ((n : ℝ)+1)*H (q₀+J x₀)*flatInversePair (B x₀) v (fun y => T (q₀+J y)) (fun y => T (q₀+J y)) x₀ +
      H (q₀+J x₀)*flatInverseTrace (R x₀) w (fun y => F (q₀+J y)) x₀ +
      2*H (q₀+J x₀)*flatInversePair (R x₀) w (fun y => P (q₀+J y)) (fun y => F (q₀+J y)) x₀ +
      H (q₀+J x₀)*flatInversePair (R x₀) w (fun y => F (q₀+J y)) (fun y => F (q₀+J y)) x₀ = 0 at hfeq
  rw [flatInverseTrace_affine_pullback q₀ J hF,flatInverseTrace_affine_pullback q₀ J hF,
    flatInversePair_affine_pullback q₀ J (hP.differentiableAt (by simp)) (hP.differentiableAt (by simp)),
    flatInversePair_affine_pullback q₀ J (hT.differentiableAt (by simp)) (hT.differentiableAt (by simp)),
    flatInversePair_affine_pullback q₀ J (hP.differentiableAt (by simp)) (hF.differentiableAt (by simp)),
    flatInversePair_affine_pullback q₀ J (hF.differentiableAt (by simp)) (hF.differentiableAt (by simp))] at hfeq
  have hB : B x₀ = tubeBaseMatrix H (q₀+J x₀) bS :=
    (tubeBaseMatrix_eq_flatBlockHessian q₀ J (hHs x₀ hxU) bS v hv).symm
  have hR : R x₀ = tubeRadiusMatrix H (q₀+J x₀) bE :=
    (tubeRadiusMatrix_eq_flatBlockHessian q₀ J (hHs x₀ hxU) bE w hw).symm
  simp only [hB,hR,hv,hw] at hfeq
  exact hfeq

/- The invariant support f-equation, with all flat-normal chart data produced
from the actual frames. At a unit normal it is the round-sphere equation,
since the actual invariant scalar has zero radial derivative. -/
theorem affineMaximal_invariant_tube_f_equation_oai {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E}
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : bE (Sum.inr ()) = e) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let q := (s,e)
    let B := tubeBaseMatrix H q bS
    let R := tubeRadiusMatrix H q bE
    let V := fun i : ι => ((bS i), (0:E))
    let W := fun i : κ => ((0:S), bE (Sum.inl i))
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let F := invariantTubeF H bS bE δ
    let P := fun y => Real.log (H y)
    let T := fun y => F y+P y
    (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
      H q*flatInversePair B V P P q -
      ((n : ℝ)+1)*H q*flatInversePair B V T T q +
      H q*flatInverseTrace R W F q + 2*H q*flatInversePair R W P F q +
      H q*flatInversePair R W F F q = 0 := by
  obtain ⟨idx⟩ := tube_dimension_equiv bS bE L
  obtain ⟨J,C,hi,hC,hJ,hJb⟩ := exists_flat_tube_chart bS bE idx
  have hd : inner ℝ (s,e).2 (bE (Sum.inr ())) = 1 := by
    rw [← he]
    simp
  have hh := affineMaximal_flat_invariant_f_equation hΩ hcv hu hp hm a L hD hK hzero bS bE
    (s,e) hd J hi hJ C hC idx hJb (x₀ := 0) (by simpa using hs)
  simpa only [map_zero,add_zero] using hh

end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation_oai.{u_1, u_2, u_3, u_4} := @OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation_oai.{u_1, u_2, u_3, u_4}
