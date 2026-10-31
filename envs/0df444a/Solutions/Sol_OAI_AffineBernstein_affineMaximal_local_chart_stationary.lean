-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_local_chart_stationary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:04:05.608137+00:00
-- url     : https://prove2.me/submissions/d9e76091-cdf5-40dc-a611-2e7d52043298

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

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

/-- The exact maximal-graph operator is the double divergence of its variational coefficient. -/
theorem affine_operator_eq_double_divergence {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) {x : Space n} (hx : x ∈ Ω) :
    (∑ j, ∑ i, dirDeriv (coordinateVector n j) (dirDeriv (coordinateVector n i)
      (fun y => affineWeight u y * cofactorHessian u y i j)) x) =
      ∑ i, ∑ j, cofactorHessian u x i j * hessian (affineWeight u) x i j := by
  have hu3 : ContDiffOn ℝ 3 u Ω :=
    hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hdiv := cofactorHessian_divergence hΩ u hu3 hpos
  rw [double_divergence_weighted hΩ (fun y i j => cofactorHessian u y i j)
    (affineWeight u) (coordinateVector n)
    (fun y hy => contDiffAt_cofactorHessian_entry hΩ hu hpos hy)
    (fun y hy => contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hy)) (hpos y hy))
    (fun y hy i => (hdiv y hy i).1) (fun y hy j => (hdiv y hy j).2) hx]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [(cofactorHessian_isSymm u x (hpos x hx)).apply i j]
  rfl

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

/-- Graph-direction stationarity for the source's equation and actual coefficient.
All regularity of `u` is needed only on the original open domain. -/
theorem affineMaximal_weak_stationarity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) :
    (∫ x, ∑ i, ∑ j, affineWeight u x * cofactorHessian u x i j * hessian η x i j) = 0 := by
  have ha (i j : Fin n) (x : Space n) (hx : x ∈ tsupport η) :
      ContDiffAt ℝ ∞ (fun y => affineWeight u y * cofactorHessian u y i j) x :=
    (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds (hηΩ hx))) (hpos x (hηΩ hx))).mul
      (contDiffAt_cofactorHessian_entry hΩ hu hpos (hηΩ hx) i j)
  change (∫ x, ∑ i, ∑ j, affineWeight u x * cofactorHessian u x i j *
    dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j) η) x) = 0
  rw [integral_double_contraction_compact (fun i j x => affineWeight u x * cofactorHessian u x i j)
    (coordinateVector n) η ha hη hηc]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  by_cases hx : η x = 0
  · rw [hx, mul_zero]
    rfl
  · have hxΩ := hηΩ (subset_tsupport η hx)
    rw [affine_operator_eq_double_divergence hΩ hu hpos hxΩ, hmax x hxΩ, zero_mul]
    rfl

/-- The variation coefficient has exactly the exponent in the manuscript. -/
theorem affineWeight_mul_det {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hpos : (hessian u x).PosDef) :
    affineWeight u x * (hessian u x).det = affineAreaDensity u x := by
  unfold affineWeight affineAreaDensity
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add_one (ne_of_gt hpos.det_pos)]
  congr 1
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- `wU` is not a surrogate for the affine-area coefficient. -/
theorem affine_weight_cofactor_entry {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hpos : (hessian u x).PosDef) (i j : Fin n) :
    affineWeight u x * cofactorHessian u x i j =
      affineAreaDensity u x * (hessian u x)⁻¹ i j := by
  change affineWeight u x * ((hessian u x).det * (hessian u x)⁻¹ i j) = _
  rw [← mul_assoc, affineWeight_mul_det hpos]

/-- The source's first-variation integral, over its original open domain. -/
theorem affineMaximal_area_stationarity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) :
    (∫ x in Ω, affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) = 0 := by
  have hzero (x : Space n) (hx : x ∉ Ω) (i j : Fin n) : hessian η x i j = 0 := by
    have hn : x ∉ tsupport η := fun h => hx (hηΩ h)
    unfold hessian
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hn (tsupport_fderiv_apply_subset ℝ _ h))]
    rfl
  calc
    _ = ∫ x in Ω, ∑ i, ∑ j,
        affineWeight u x * cofactorHessian u x i j * hessian η x i j := by
      apply setIntegral_congr_fun hΩ.measurableSet
      intro x hx
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [affine_weight_cofactor_entry (hpos x hx), mul_assoc]
    _ = ∫ x, ∑ i, ∑ j,
        affineWeight u x * cofactorHessian u x i j * hessian η x i j :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp only [hzero x hx, mul_zero, Finset.sum_const_zero]
    _ = 0 := affineMaximal_weak_stationarity hΩ hu hpos hmax η hη hηc hηΩ

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

section DeterminantVariation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Jacobi's formula without assuming invertibility of the varied matrix. -/
theorem hasDerivAt_det_line (A B : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (A + t • B).det)
      (∑ i, ∑ j, A.adjugate j i * B i j) 0 := by
  have hline := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (fun i j => B i j)).const_add
    (fun i j => A i j)
  have hc := (((continuousDetRows (ι := ι)).hasFDerivAt
    ((fun i j => A i j) + (0 : ℝ) • (fun i j => B i j))).comp 0 hline).hasDerivAt
  simp only [zero_smul, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul] at hc
  have hd : continuousDetRows.linearDeriv (fun i j => A i j) (fun i j => B i j) =
      ∑ i, ∑ j, A.adjugate j i * B i j := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    apply Finset.sum_congr rfl
    intro i hi
    change (A.updateRow i (B i)).det = _
    rw [det_updateRow_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Matrix.adjugate_apply, mul_comm]
  rw [hd] at hc
  exact hc

end DeterminantVariation

section RadialCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Away from topological support the test is locally zero, so no extension
of a smooth coefficient across the original boundary is necessary. -/
theorem contDiff_of_contDiffAt_tsupport {f : E → ℝ} {k : ℕ∞ω}
    (hf : ∀ x ∈ tsupport f, ContDiffAt ℝ k f x) : ContDiff ℝ k f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf x hx
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hx)

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

/-- Smoothness of the area density on the original domain. -/
theorem contDiffAt_affineAreaDensity {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef) :
    ContDiffAt ℝ ∞ (affineAreaDensity u) x :=
  (contDiffAt_det_hessian hu).rpow_const_of_ne (ne_of_gt hpos.det_pos)

/-- The exact differential of the affine area coefficient. -/
theorem dirDeriv_affineAreaDensity {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef) (v : Space n) :
    dirDeriv v (affineAreaDensity u) x =
      (1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * dirDeriv v (fun y => hessian u y i j) x) := by
  have hd := ((contDiffAt_det_hessian hu).differentiableAt (by simp)).hasFDerivAt
  have hr := hd.rpow_const (p := 1 / ((n : ℝ) + 2)) (Or.inl (ne_of_gt hpos.det_pos))
  have he : (1 / ((n : ℝ) + 2)) - 1 = -(((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    field_simp
    ring
  have hc : dirDeriv v (affineAreaDensity u) x =
      (1 / ((n : ℝ) + 2)) * affineWeight u x *
        dirDeriv v (fun y => (hessian u y).det) x := by
    unfold dirDeriv affineAreaDensity
    simp only [Real.rpow_eq_pow]
    rw [hr.fderiv]
    simp only [smul_apply, smul_eq_mul, he, affineWeight, Real.rpow_eq_pow]
  rw [hc, dirDeriv_det (hessian u)
    (fun i j => (contDiffAt_hessian_entry hu i j).differentiableAt (by simp))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hcof : (hessian u x).adjugate j i = cofactorHessian u x i j := by
    rw [← cofactorHessian_eq_adjugate u x (ne_of_gt hpos.det_pos)]
    exact (cofactorHessian_isSymm u x hpos).apply i j
  rw [hcof]
  calc
    _ = (1 / ((n : ℝ) + 2)) * (affineWeight u x * cofactorHessian u x i j) *
        dirDeriv v (fun y => hessian u y i j) x := by ring
    _ = _ := by rw [affine_weight_cofactor_entry hpos]; ring

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

/-- A smooth compact test makes a merely locally smooth coefficient globally smooth. -/
theorem contDiff_mul_at_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {k : ℕ∞ω} (hg : ContDiff ℝ k g)
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ k f x) :
    ContDiff ℝ k (fun x => f x * g x) := by
  apply contDiff_of_contDiffAt_tsupport
  intro x hx
  exact (hf x (tsupport_mul_subset_right hx)).mul hg.contDiffAt

/-- Integral of a derivative of a smooth compactly supported scalar field. -/
theorem integral_dirDeriv_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (v : E) :
    (∫ x, dirDeriv v f x ∂μ) = 0 := by
  have he := integral_mul_fderiv_compact (μ := μ) (fun _ : E => (1 : ℝ)) f v
    (fun _ _ => contDiffAt_const)
    (hf.of_le (by simp)) hfc
  simpa [dirDeriv] using he

/-- The actual first-variation density is integrable for a compact local test. -/
theorem integrableOn_area_variation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) :
    IntegrableOn (fun x => affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) Ω := by
  have hi (i j : Fin n) : Integrable (fun x =>
      affineWeight u x * cofactorHessian u x i j * hessian η x i j) := by
    apply integrable_of_support_subset_compact hηc.isCompact
    · exact (Function.support_mul_subset_right _ _).trans
        ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ _).trans
          (tsupport_fderiv_apply_subset ℝ _)))
    · intro x hx
      have hc := (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds (hηΩ hx)))
        (hpos x (hηΩ hx))).mul
          (contDiffAt_cofactorHessian_entry hΩ hu hpos (hηΩ hx) i j)
      exact (hc.mul (contDiffAt_hessian_entry hη.contDiffAt i j)).continuousAt.continuousWithinAt
  have hiSum := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))
  apply hiSum.integrableOn.congr_fun _ hΩ.measurableSet
  intro x hx
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [affine_weight_cofactor_entry (hpos x hx), mul_assoc]

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

lemma contDiffAt_inverse_matrix_entry {A : ℝ → Matrix ι ι ℝ} {t : ℝ}
    (hA : ContDiffAt ℝ ∞ (fun r i j => A r i j) t) (hd : (A t).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ ∞ (fun r => (A r)⁻¹ i j) t := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp t hA).inv hd).mul
    ((contDiff_adjugate_entry i j).contDiffAt.comp t hA)

lemma hasDerivAt_det_entries {A : ℝ → Matrix ι ι ℝ} {D : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun r => A r i j) (D i j) t) :
    HasDerivAt (fun r => (A r).det)
      (∑ i, ∑ j, (A t).adjugate j i * D i j) t := by
  have hd : HasDerivAt (fun r i j => A r i j) (fun i j => D i j) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hA i j
  have hh := (continuousDetRows (ι := ι)).hasFDerivAt (fun i j => A t i j)
    |>.comp_hasDerivAt t hd
  simp only [ContinuousMultilinearMap.linearDeriv_apply] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  symm
  apply Finset.sum_congr rfl
  intro i _
  change ((A t).updateRow i (D i)).det = _
  rw [det_updateRow_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.adjugate_apply, mul_comm]

/- The conormal for the genuine variation (x+t a(x),u(x)+t beta(x)),
written in its first jets, is (-q(t),1). -/

lemma contDiffAt_variationConormal (D : Matrix ι ι ℝ) (g d : ι → ℝ) (k : ι) :
    ContDiffAt ℝ ∞ (fun t => variationConormal D g d t k) 0 := by
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul (by fun_prop)
  apply contDiffAt_inverse_matrix_entry
  · apply contDiffAt_pi.mpr; intro i
    apply contDiffAt_pi.mpr; intro j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  · simp

lemma hasDerivAt_variationSecondForm (H B D : Matrix ι ι ℝ) (g d : ι → ℝ)
    (C : ι → Matrix ι ι ℝ) (i j : ι) :
    HasDerivAt (fun t => variationSecondForm H B D g d C t i j)
      (B i j - ∑ k, g k * C k i j) 0 := by
  have hc : DifferentiableAt ℝ (fun t => ∑ k, variationConormal D g d t k * C k i j) 0 := by
    apply DifferentiableAt.fun_sum
    intro k _
    exact ((contDiffAt_variationConormal D g d k).differentiableAt (by simp)).mul_const _
  have hh := (((hasDerivAt_id (0 : ℝ)).mul_const (B i j)).const_add (H i j)).sub
    ((hasDerivAt_id (0 : ℝ)).mul hc.hasDerivAt)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp

lemma hasDerivAt_variationAreaDensity_raw (H B D : Matrix ι ι ℝ) (hH : H.PosDef)
    (g d : ι → ℝ) (C : ι → Matrix ι ι ℝ) (δ : ℝ) :
    HasDerivAt (variationAreaDensity H B D g d C δ)
      (δ * Real.rpow H.det (δ - 1) *
        (∑ i, ∑ j, H.adjugate j i * (B i j - ∑ k, g k * C k i j)) +
        Real.rpow H.det δ * ((Fintype.card ι : ℝ) * δ * D.trace)) 0 := by
  have hh := (hasDerivAt_det_entries (hasDerivAt_variationSecondForm H B D g d C)).rpow_const
    (p := δ) (Or.inl (by simpa using ne_of_gt hH.det_pos))
  simp only [variationSecondForm_zero] at hh
  have hj : HasDerivAt (fun t : ℝ => (1 + t • D).det) D.trace 0 := by
    simpa [Matrix.adjugate_one, Matrix.one_apply, Matrix.trace] using
      (hasDerivAt_det_line (1 : Matrix ι ι ℝ) D)
  have haj := (hasDerivAt_abs_pos (by simp : 0 < (1 + (0 : ℝ) • D).det)).comp 0 hj
  have hp := haj.rpow_const (p := (Fintype.card ι : ℝ) * δ) (Or.inl (by simp))
  have hhj := hh.mul hp
  convert! hhj using 1
  all_goals try with_reducible_and_instances rfl
  simp [variationSecondForm_zero, mul_assoc, mul_comm, mul_left_comm]

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

lemma trace_hessian_verticalVariation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u η : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hη : ContDiffOn ℝ ∞ η Ω)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (verticalVariation u η a) x i j) =
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j) +
      ∑ k, (a k x * (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n k) (fun y => hessian u y i j) x) +
        dirDeriv (coordinateVector n k) u x * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (a k) x i j) +
        2 * dirDeriv (coordinateVector n k) (a k) x) := by
  have hg (k : Fin n) : ContDiffOn ℝ ∞
      (fun y => dirDeriv (coordinateVector n k) u y * a k y) Ω :=
    (contDiffOn_dirDeriv hΩ hu _).mul (ha k)
  have he (i j : Fin n) : hessian (verticalVariation u η a) x i j =
      hessian η x i j + ∑ k, hessian (fun y => dirDeriv (coordinateVector n k) u y * a k y) x i j := by
    change hessian (fun y => η y + ∑ k, dirDeriv (coordinateVector n k) u y * a k y) x i j = _
    rw [hessian_add_on hΩ hη (ContDiffOn.sum (fun k _ => hg k)) hx,
      Matrix.add_apply, hessian_sum_on hΩ hg hx]
  conv_lhs => simp only [he, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  rw [hessian_product_trace hΩ (contDiffOn_dirDeriv hΩ hu _) (ha k) hx
    (inverseHessian_isSymm hp)]
  simp_rw [hessian_dirDeriv hΩ hu hx]
  congr 2
  change (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian u x i k *
    dirDeriv (coordinateVector n j) (a k) x) = _
  exact inverse_column_contraction hp k _

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
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricFirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma trace_sum_matrices {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (g : κ → ℝ) (C : κ → Matrix ι ι ℝ) :
    (∑ i, ∑ j, A i j * ∑ k, g k * C k i j) =
      ∑ k, g k * ∑ i, ∑ j, A i j * C k i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma hasDerivAt_graphVariationArea_raw {n : ℕ} {u β : Space n → ℝ}
    (a : Fin n → Space n → ℝ) {x : Space n} (hp : (hessian u x).PosDef) :
    HasDerivAt (graphVariationArea u β a x)
      ((1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        ((∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian β x i j) -
          ∑ k, dirDeriv (coordinateVector n k) u x *
            ∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (a k) x i j) +
        affineAreaDensity u x * ((n : ℝ) * (1 / ((n : ℝ) + 2)) *
          ∑ k, dirDeriv (coordinateVector n k) (a k) x)) 0 := by
  have hh := hasDerivAt_variationAreaDensity_raw (hessian u x) (hessian β x)
    (horizontalJacobian a x) hp (fun k => dirDeriv (coordinateVector n k) u x)
    (fun k => dirDeriv (coordinateVector n k) β x) (fun k => hessian (a k) x)
    (1 / ((n : ℝ) + 2))
  have hw : (1 / ((n : ℝ) + 2)) - 1 = -(((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    field_simp
    ring
  have hcof (i j : Fin n) : (hessian u x).adjugate j i = cofactorHessian u x i j := by
    rw [← cofactorHessian_eq_adjugate u x (ne_of_gt hp.det_pos)]
    exact (cofactorHessian_isSymm u x hp).apply i j
  have he (T : Matrix (Fin n) (Fin n) ℝ) :
      (1 / ((n : ℝ) + 2)) * Real.rpow (hessian u x).det ((1 / ((n : ℝ) + 2)) - 1) *
        (∑ i, ∑ j, (hessian u x).adjugate j i * T i j) =
      (1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * T i j) := by
    rw [hw]
    change (1 / ((n : ℝ) + 2)) * affineWeight u x * _ = _
    simp only [Finset.mul_sum, hcof]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (1 / ((n : ℝ) + 2)) * (affineWeight u x * cofactorHessian u x i j) * T i j := by ring
      _ = _ := by rw [affine_weight_cofactor_entry hp]; ring
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  symm
  erw [he (Matrix.of fun i j => hessian β x i j -
    ∑ k, dirDeriv (coordinateVector n k) u x * hessian (a k) x i j)]
  simp only [Matrix.of_apply, mul_sub, Finset.sum_sub_distrib, trace_sum_matrices, Fintype.card_fin]
  rfl

/- The tangential part of the exact parametrized first-variation density is
an ordinary divergence; the remaining part is the genuine graph variation. -/
lemma hasDerivAt_graphVariationArea_normal {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u η : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hη : ContDiffOn ℝ ∞ η Ω)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    HasDerivAt (graphVariationArea u (verticalVariation u η a) a x)
      ((1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j) +
        ∑ k, dirDeriv (coordinateVector n k) (fun y => affineAreaDensity u y * a k y) x) 0 := by
  have hh := hasDerivAt_graphVariationArea_raw (u := u) (β := verticalVariation u η a) a hp
  rw [trace_hessian_verticalVariation hΩ hu hη ha hx hp] at hh
  have hd (k : Fin n) :
      dirDeriv (coordinateVector n k) (fun y => affineAreaDensity u y * a k y) x =
      (1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        (a k x * ∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n k) (fun y => hessian u y i j) x) +
      affineAreaDensity u x * dirDeriv (coordinateVector n k) (a k) x := by
    rw [dirDeriv_mul ((contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds hx)) hp).differentiableAt (by simp))
      (((ha k).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)),
      dirDeriv_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds hx)) hp]
    ring
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [hd, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Every compact smooth parametric velocity has a genuinely smooth compact
normal graph component, without extending the original graph smoothly. -/
lemma normalVariation_compact {n : ℕ} {Ω K : Set (Space n)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {u β : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K) :
    ContDiff ℝ ∞ (normalVariation u β a) ∧
      HasCompactSupport (normalVariation u β a) ∧ tsupport (normalVariation u β a) ⊆ K := by
  have hg (k : Fin n) : ContDiff ℝ ∞
      (fun y => dirDeriv (coordinateVector n k) u y * a k y) :=
    contDiff_mul_at_tsupport (ha k) (fun x hx =>
      contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds (hKΩ (haK k hx)))) _)
  have hs : tsupport (normalVariation u β a) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxn
    have hb : β x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxn (hβK h))
    have ha0 (k : Fin n) : a k x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxn (haK k h))
    exact hx (by simp [normalVariation, hb, ha0])
  exact ⟨hβ.sub (ContDiff.sum (fun k _ => hg k)),
    hK.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩

/- The exact pointwise first variation under every compact smooth parametric
velocity is integrable and has zero integral. The density uses the actual
varying conormal and horizontal Jacobian. -/
theorem affineMaximal_parametric_first_variation {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K) :
    IntegrableOn (fun x => deriv (graphVariationArea u β a x) 0) Ω ∧
      (∫ x in Ω, deriv (graphVariationArea u β a x) 0) = 0 := by
  let η := normalVariation u β a
  have hn := normalVariation_compact hΩ hK hKΩ hu hβ hβK ha haK
  have heβ : verticalVariation u η a = β := by
    funext x
    simp [verticalVariation, η, normalVariation]
  let N := fun x => (1 / ((n : ℝ) + 2)) * (affineAreaDensity u x *
    (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j))
  let F (k : Fin n) (x : Space n) := affineAreaDensity u x * a k x
  let D (k : Fin n) := dirDeriv (coordinateVector n k) (F k)
  have hF (k : Fin n) : ContDiff ℝ ∞ (F k) :=
    contDiff_mul_at_tsupport (ha k) (fun x hx =>
      contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hKΩ (haK k hx))))
        (hp x (hKΩ (haK k hx))))
  have hFs (k : Fin n) : tsupport (F k) ⊆ K := tsupport_mul_subset_right.trans (haK k)
  have hFc (k : Fin n) : HasCompactSupport (F k) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hFs k)
  have hD (k : Fin n) : Integrable (D k) :=
    integrable_of_support_subset_compact (hFc k).isCompact
      ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ _))
      (contDiff_dirDeriv (hF k) _).continuous.continuousOn
  have hD0 (k : Fin n) : (∫ x in Ω, D k x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_dirDeriv_compact _ (hF k) (hFc k) _
    · intro x hx
      change fderiv ℝ (F k) x (coordinateVector n k) = 0
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hKΩ (hFs k h)))]
      rfl
  have hN : IntegrableOn N Ω :=
    (integrableOn_area_variation hΩ hu hp η hn.1 hn.2.1 (hn.2.2.trans hKΩ)).const_mul _
  have hN0 : (∫ x in Ω, N x) = 0 := by
    rw [show N = fun x => (1 / ((n : ℝ) + 2)) * (affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) from rfl, integral_const_mul,
      affineMaximal_area_stationarity hΩ hu hp hm η hn.1 hn.2.1 (hn.2.2.trans hKΩ), mul_zero]
  have hDs : IntegrableOn (fun x => ∑ k, D k x) Ω :=
    (integrable_finsetSum _ (fun k _ => hD k)).integrableOn
  have he (x : Space n) (hx : x ∈ Ω) :
      deriv (graphVariationArea u β a x) 0 = N x + ∑ k, D k x := by
    have hh := hasDerivAt_graphVariationArea_normal hΩ hu hn.1.contDiffOn
      (fun k => (ha k).contDiffOn) hx (hp x hx)
    rw [heβ] at hh
    simpa only [N, F, D, mul_assoc] using hh.deriv
  refine ⟨(hN.add hDs).congr_fun (fun x hx => (he x hx).symm) hΩ.measurableSet, ?_⟩
  rw [setIntegral_congr_fun hΩ.measurableSet he, integral_add hN hDs, hN0,
    integral_finsetSum _ (fun k _ => (hD k).integrableOn)]
  simp only [hD0, Finset.sum_const_zero, add_zero]

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
-- module Solutions.OAIQ22_AB.AffineBernstein_CompactDifferentiation
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
variable {μ : Measure E} [IsLocallyFiniteMeasure μ]

/- Differentiation over a fixed compact set from smoothness in a neighbourhood
of the zero-parameter slice. The uniform bound is obtained by compactness. -/
theorem hasDerivAt_setIntegral_compact {K : Set E} (hK : IsCompact K)
    {U : Set (ℝ × E)} (hU : IsOpen U) (h0K : {0} ×ˢ K ⊆ U)
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    HasDerivAt (fun t : ℝ => ∫ x in K, F (t,x) ∂μ)
      (∫ x in K, fderiv ℝ F (0,x) (1,0) ∂μ) 0 := by
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK hU h0K
  have hv : V ∈ nhds (0 : ℝ) := hV.mem_nhds (h0V (by simp))
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hv
  let I : Set ℝ := Icc (-ε / 2) (ε / 2)
  have hIV : I ⊆ V := by
    intro t ht
    apply hεV
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
    exact ⟨by dsimp [I] at ht; linarith [ht.1], by dsimp [I] at ht; linarith [ht.2]⟩
  have hIU : I ×ˢ K ⊆ U := fun p hp => hVW ⟨hIV hp.1, hKW hp.2⟩
  have hI0 : (0 : ℝ) ∈ I := by
    change -ε / 2 ≤ 0 ∧ 0 ≤ ε / 2
    constructor <;> linarith
  have hIn : I ∈ nhds (0 : ℝ) := Icc_mem_nhds (by linarith) (by linarith)
  let D : ℝ × E → ℝ := fun p => fderiv ℝ F p (1,0)
  have hDc : ContinuousOn D U := by
    intro p hp
    exact (((hF.contDiffAt (hU.mem_nhds hp)).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).continuousWithinAt
  have hFt (t : ℝ) (ht : t ∈ I) : ContinuousOn (fun x => F (t,x)) K :=
    hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => hIU ⟨ht,hx⟩)
  have hDt (t : ℝ) (ht : t ∈ I) : ContinuousOn (fun x => D (t,x)) K :=
    hDc.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => hIU ⟨ht,hx⟩)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hDc.mono hIU)
  have hder (x : E) (hx : x ∈ K) (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun r => F (r,x)) (D (t,x)) t := by
    have hh := ((hF.contDiffAt (hU.mem_nhds (hIU ⟨ht,hx⟩))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  have hi : IntegrableOn (fun _ : E => C) K μ := continuousOn_const.integrableOn_compact hK
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := fun t x => F (t,x)) (F' := fun t x => D (t,x))
    (s := I) (bound := fun _ => C) hIn
    (Filter.eventually_of_mem hIn (fun t ht => ((hFt t ht).integrableOn_compact hK).aestronglyMeasurable))
    ((hFt 0 hI0).integrableOn_compact hK)
    ((hDt 0 hI0).integrableOn_compact hK).aestronglyMeasurable
    (ae_restrict_mem hK.measurableSet |>.mono (fun x hx t ht => hC (t,x) ⟨ht,hx⟩))
    hi (ae_restrict_mem hK.measurableSet |>.mono (fun x hx t ht => hder x hx t ht))).2

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

lemma isOpen_graphVariationRegular {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) :
    IsOpen (graphVariationRegular Ω u β a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hJ := (continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp p
    (contDiffAt_graphVariationJacobian (fun k => (ha k).contDiffAt (hΩ.mem_nhds hp.1)))
  have hH := (continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp p
    (contDiffAt_graphVariationSecond (hu.contDiffAt (hΩ.mem_nhds hp.1))
      (hβ.contDiffAt (hΩ.mem_nhds hp.1))
      (fun k => (ha k).contDiffAt (hΩ.mem_nhds hp.1)) hp.2.1)
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp.1),
    hJ.continuousAt.eventually_ne hp.2.1, hH.continuousAt.eventually_ne hp.2.2] with q hq hj hh
  exact ⟨hq,hj,hh⟩

lemma contDiffOn_graphVariationArea {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Space n => graphVariationArea u β a p.2 p.1)
      (graphVariationRegular Ω u β a) := by
  intro p hp
  have hJ := (continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp p
    (contDiffAt_graphVariationJacobian (fun k => (ha k).contDiffAt (hΩ.mem_nhds hp.1)))
  have hH := (continuousDetRows (ι := Fin n)).contDiff.contDiffAt.comp p
    (contDiffAt_graphVariationSecond (hu.contDiffAt (hΩ.mem_nhds hp.1))
      (hβ.contDiffAt (hΩ.mem_nhds hp.1))
      (fun k => (ha k).contDiffAt (hΩ.mem_nhds hp.1)) hp.2.1)
  exact ((hH.rpow_const_of_ne hp.2.2).mul
    ((hJ.abs hp.2.1).rpow_const_of_ne (abs_ne_zero.mpr hp.2.1))).contDiffWithinAt

lemma zero_mem_graphVariationRegular {n : ℕ} {Ω : Set (Space n)}
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ} {x : Space n}
    (hx : x ∈ Ω) (hp : (hessian u x).PosDef) : (0,x) ∈ graphVariationRegular Ω u β a := by
  refine ⟨hx, ?_, ?_⟩
  · simp [graphVariationJacobian]
  · simpa [graphVariationSecond] using ne_of_gt hp.det_pos

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_IntegratedParametricStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma graphVariationArea_eq_of_notMem {n : ℕ} {K : Set (Space n)}
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hβK : tsupport β ⊆ K) (haK : ∀ k, tsupport (a k) ⊆ K)
    {x : Space n} (hx : x ∉ K) (t : ℝ) :
    graphVariationArea u β a x t = affineAreaDensity u x := by
  have hd (f : Space n → ℝ) (hf : tsupport f ⊆ K) (i : Fin n) :
      dirDeriv (coordinateVector n i) f x = 0 := by
    unfold dirDeriv
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hf h))]
    rfl
  have hh (f : Space n → ℝ) (hf : tsupport f ⊆ K) (i j : Fin n) :
      hessian f x i j = 0 := by
    unfold hessian
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hf (tsupport_fderiv_apply_subset ℝ _ h)))]
    rfl
  have hB : hessian β x = 0 := Matrix.ext (fun i j => hh β hβK i j)
  have hC (k : Fin n) : hessian (a k) x = 0 := Matrix.ext (fun i j => hh (a k) (haK k) i j)
  have hJ : horizontalJacobian a x = 0 := Matrix.ext (fun i j => hd (a i) (haK i) j)
  have hzero : Matrix.of (t • fun (_ _ : Fin n) => (0 : ℝ)) = 0 := by
    ext i j
    simp
  simp [graphVariationArea, variationAreaDensity, variationSecondForm, hB, hC, hJ, hzero,
    affineAreaDensity, smul_zero]

lemma fderiv_param_eq_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × E → ℝ} {x : E} (hF : DifferentiableAt ℝ F (0,x)) :
    fderiv ℝ F (0,x) (1,0) = deriv (fun t => F (t,x)) 0 := by
  have hh := hF.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
  have hh' : HasDerivAt (fun t => F (t,x)) (fderiv ℝ F (0,x) (1,0)) 0 := by
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  exact hh'.deriv.symm

/- Actual differentiation of the compact affine-area functional, not just
an integrated pointwise derivative. -/
theorem affineMaximal_parametric_area_stationary {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K) :
    HasDerivAt (fun t : ℝ => ∫ x in K, graphVariationArea u β a x t) 0 0 := by
  let U := graphVariationRegular Ω u β a
  let F := fun p : ℝ × Space n => graphVariationArea u β a p.2 p.1
  have hU : IsOpen U := isOpen_graphVariationRegular hΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn)
  have hF : ContDiffOn ℝ ∞ F U := contDiffOn_graphVariationArea hΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn)
  have h0 (x : Space n) (hx : x ∈ Ω) : (0,x) ∈ U :=
    zero_mem_graphVariationRegular hx (hp x hx)
  have hD := hasDerivAt_setIntegral_compact (μ := volume) hK hU
    (by rintro ⟨t,x⟩ ⟨ht,hx⟩; simp only [mem_singleton_iff] at ht; subst t; exact h0 x (hKΩ hx)) hF
  have he (x : Space n) (hx : x ∈ K) :
      fderiv ℝ F (0,x) (1,0) = deriv (graphVariationArea u β a x) 0 := by
    exact fderiv_param_eq_deriv ((hF.contDiffAt
      (hU.mem_nhds (h0 x (hKΩ hx)))).differentiableAt (by simp))
  have hz (x : Space n) (hx : x ∉ K) : deriv (graphVariationArea u β a x) 0 = 0 := by
    have heq : graphVariationArea u β a x = fun _ => affineAreaDensity u x :=
      funext (graphVariationArea_eq_of_notMem hβK haK hx)
    rw [heq, deriv_const]
  have hi := affineMaximal_parametric_first_variation hΩ hK hKΩ hu hp hm hβ hβK ha haK
  have hI : (∫ x in K, fderiv ℝ F (0,x) (1,0)) = 0 := by
    rw [setIntegral_congr_fun hK.measurableSet he,
      setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hz x (fun hk => hx (hKΩ hk)))] at hi
    exact hi.2
  simpa only [F, hI] using hD

/- The compact affine-area functional of every arbitrary affine image is
stationary. All derivatives and integrals are the literal geometric density. -/
theorem affineMaximal_affine_parametric_area_stationary {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in K, affineParametricVariationArea L v u β a x t) 0 0 := by
  let c := Real.rpow |LinearMap.det L.toLinearEquiv.toLinearMap| ((n : ℝ) / ((n : ℝ) + 2))
  have he : (fun t : ℝ => ∫ x in K, affineParametricVariationArea L v u β a x t) =
      fun t => c * ∫ x in K, graphVariationArea u β a x t := by
    funext t
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hK.measurableSet (fun x hx =>
      affineParametricVariationArea_eq hΩ hu hβ.contDiffOn (fun k => (ha k).contDiffOn) L v (hKΩ hx) t)
  rw [he]
  simpa using (affineMaximal_parametric_area_stationary hΩ hK hKΩ hu hp hm hβ hβK ha haK).const_mul c

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
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricChartStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- The stationarity functional in any smooth nonsingular injective coordinate
chart. The change of variables uses the literal Lebesgue Jacobian, and positivity
for the full parameter family is derived uniformly from the original Hessian. -/
theorem affineMaximal_coordinate_parametric_area_stationary {n : ℕ}
    {Ω K : Set (Space n)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    {φ : Space n → Space n} (hφ : ∀ x ∈ K, ContDiffAt ℝ ∞ φ x)
    (hinj : InjOn φ K) (hφJ : ∀ x ∈ K, (parametricJacobian φ x).det ≠ 0)
    (hKΩ : φ '' K ⊆ Ω) {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ φ '' K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ φ '' K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in K, coordinateAffineVariationArea L v φ u β a x t) 0 0 := by
  have hKi : IsCompact (φ '' K) := hK.image_of_continuousOn
    (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
  have hstat := affineMaximal_affine_parametric_area_stationary hΩ hKi hKΩ hu hp hm
    hβ hβK ha haK L v
  apply hstat.congr_of_eventuallyEq
  filter_upwards [eventually_graphVariation_positive hΩ hKi hKΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn) hp] with t ht
  calc
    (∫ x in K, coordinateAffineVariationArea L v φ u β a x t) =
        ∫ x in K, |LinearMap.det (fderiv ℝ φ x).toLinearMap| *
          affineParametricVariationArea L v u β a (φ x) t := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      have hh := ht (φ x) (mem_image_of_mem φ hx)
      exact coordinateAffineVariationArea_eq hΩ hu hβ.contDiffOn (fun k => (ha k).contDiffOn)
        L v (hφ x hx) (hKΩ (mem_image_of_mem φ hx)) (hφJ x hx) t hh.1 hh.2.le
    _ = ∫ x in φ '' K, affineParametricVariationArea L v u β a x t := by
      simpa only [smul_eq_mul] using
        (integral_image_eq_integral_abs_det_fderiv_smul volume hK.measurableSet
          (fun x hx => ((hφ x hx).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
          hinj (fun x => affineParametricVariationArea L v u β a x t)).symm

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

lemma contDiff_indicator_vector_of_compact {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    ContDiff ℝ ∞ (U.indicator f) ∧ tsupport (U.indicator f) ⊆ K := by
  have hs : Function.support (U.indicator f) ⊆ K := by
    intro x hx
    by_contra hxK
    by_cases hxU : x ∈ U
    · exact hx (by rw [Set.indicator_of_mem hxU,hz x hxU hxK])
    · exact hx (Set.indicator_of_notMem hxU f)
  have ht : tsupport (U.indicator f) ⊆ K := closure_minimal hs hK.isClosed
  refine ⟨?_,ht⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (U.indicator f)
  · have hxU := hKU (ht hx)
    apply (hf.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact Set.indicator_of_mem hy f
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

/- Push a compactly supported smooth local velocity through a genuine smooth
coordinate inverse and extend by zero. Smoothness at the chart boundary is
proved, not an extra assumption on the transported velocity. -/
lemma smooth_local_velocity_transport {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : OpenPartialHomeomorph E F) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    {K : Set E} (hK : IsCompact K) (hKφ : K ⊆ φ.source)
    {V : E → G} (hV : ContDiffOn ℝ ∞ V φ.source) (hVK : tsupport V ⊆ K) :
    ∃ W : F → G, ContDiff ℝ ∞ W ∧ tsupport W ⊆ φ '' K ∧
      ∀ x ∈ φ.source, W (φ x) = V x := by
  let W := φ.target.indicator (V ∘ φ.symm)
  have hiK : IsCompact (φ '' K) := hK.image_of_continuousOn (φ.continuousOn.mono hKφ)
  have hit : φ '' K ⊆ φ.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact φ.map_source (hKφ hx)
  have hsm : ContDiffOn ℝ ∞ (V ∘ φ.symm) φ.target :=
    hV.comp hψ (fun y hy => φ.map_target hy)
  have hz : ∀ y ∈ φ.target, y ∉ φ '' K → (V ∘ φ.symm) y = 0 := by
    intro y hy hny
    change V (φ.symm y) = 0
    apply notMem_tsupport_iff_eventuallyEq.mp ?_ |>.self_of_nhds
    intro ht
    apply hny
    exact ⟨φ.symm y,hVK ht,φ.right_inv hy⟩
  obtain ⟨hW,hWK⟩ := contDiff_indicator_vector_of_compact φ.open_target hiK hit hsm hz
  refine ⟨W,hW,hWK,?_⟩
  intro x hx
  simp only [W,Set.indicator_of_mem (φ.map_source hx),Function.comp_apply,φ.left_inv hx]

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
theorem affineMaximal_local_chart_stationary_oai {n : ℕ}
    {Ω K : Set (Space n)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    (hKφ : K ⊆ φ.source) (hφΩ : φ.target ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    {V : Space n → Space n × ℝ} (hV : ContDiffOn ℝ ∞ V φ.source)
    (hVK : tsupport V ⊆ K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    ∃ (β : Space n → ℝ) (a : Fin n → Space n → ℝ),
      ContDiff ℝ ∞ β ∧ (∀ i, ContDiff ℝ ∞ (a i)) ∧
      tsupport β ⊆ φ '' K ∧ (∀ i, tsupport (a i) ⊆ φ '' K) ∧
      (∀ x ∈ φ.source, ∀ t : ℝ,
        L (graphParamVariation u β a t (φ x))+v =
          L (φ x,u (φ x))+v+t • V x) ∧
      HasDerivAt (fun t : ℝ => ∫ x in K,
        coordinateAffineVariationArea L v φ u β a x t) 0 0 := by
  obtain ⟨W,hW,hWK,hWe⟩ := smooth_local_velocity_transport φ hψ hK hKφ
    (L.symm.contDiff.comp_contDiffOn hV)
    ((tsupport_comp_subset (map_zero L.symm) V).trans hVK)
  let β : Space n → ℝ := fun x => (W x).2
  let a : Fin n → Space n → ℝ := fun i x => (W x).1 i
  have hβ : ContDiff ℝ ∞ β := hW.snd
  have ha (i : Fin n) : ContDiff ℝ ∞ (a i) :=
    (coordinateProjection n i).contDiff.comp hW.fst
  have hβK : tsupport β ⊆ φ '' K := (tsupport_comp_subset (g := Prod.snd) rfl W).trans hWK
  have haK (i : Fin n) : tsupport (a i) ⊆ φ '' K :=
    (tsupport_comp_subset (g := fun w : Space n × ℝ => w.1 i) rfl W).trans hWK
  refine ⟨β,a,hβ,ha,hβK,haK,?_,?_⟩
  · intro x hx t
    have he : (horizontalVelocity a (φ x),β (φ x)) = L.symm (V x) := by
      have hh := hWe x hx
      change W (φ x) = L.symm (V x) at hh
      rw [← hh]
      rfl
    have hs : graphParamVariation u β a t (φ x) =
        (φ x,u (φ x))+t • L.symm (V x) := by
      rw [← he]
      rfl
    rw [hs,map_add,map_smul,L.apply_symm_apply]
    abel
  · exact affineMaximal_coordinate_parametric_area_stationary hΩ hK
      (fun x hx => hφ.contDiffAt (φ.open_source.mem_nhds (hKφ hx)))
      (φ.injOn.mono hKφ) (fun x hx => smooth_chart_jacobian_ne φ hφ hψ (hKφ hx))
      (by rintro _ ⟨x,hx,rfl⟩; exact hφΩ (φ.map_source (hKφ hx)))
      hu hp hm hβ hβK ha haK L v

end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.affineMaximal_local_chart_stationary_oai := @OAI.AffineBernstein.affineMaximal_local_chart_stationary_oai
