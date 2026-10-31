-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:09:05.725035+00:00
-- url     : https://prove2.me/submissions/10d45df7-03bc-4d81-baba-21915abf8ea9

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

/-- Smoothness holds only locally; the eventual zero argument handles tests. -/
theorem contDiffAt_radialSupport {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (o : E) (c : ℝ) :
    ContDiffAt ℝ ∞ (radialSupport u o c) x :=
  (contDiffAt_const.sub hu).add
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply (contDiffAt_id.sub contDiffAt_const))

/-- The derivative of the radial gradient, including its moving vector argument. -/
theorem dirDeriv_radialGradient {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (o v : E) :
    dirDeriv v (fun y => fderiv ℝ u y (y - o)) x =
      dirDeriv (x - o) (dirDeriv v u) x + dirDeriv v u x := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply ((hasFDerivAt_id x).sub_const o)
  simp only [id_eq] at he
  unfold dirDeriv
  rw [he.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply]
  rw [← dirDeriv_eq_second hu v (x - o), dirDeriv_comm hu v (x - o)]
  exact add_comm _ _

/-- The cancellation `D Z = H(x-o)` with no coordinate or global extension assumption. -/
theorem dirDeriv_radialSupport {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (o : E) (c : ℝ) (v : E) :
    dirDeriv v (radialSupport u o c) x = dirDeriv (x - o) (dirDeriv v u) x := by
  have hdu := hu.differentiableAt (by simp)
  have hdr : DifferentiableAt ℝ (fun y => fderiv ℝ u y (y - o)) x :=
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_id.sub (contDiffAt_const (c := o)))).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (fun y => c - u y) x := by fun_prop
  unfold radialSupport dirDeriv
  rw [fderiv_fun_add hs hdr, fderiv_const_sub]
  simp only [add_apply]
  rw [show fderiv ℝ (fun y => fderiv ℝ u y (y - o)) x v =
      dirDeriv (x - o) (dirDeriv v u) x + dirDeriv v u x from
        dirDeriv_radialGradient hu o v]
  simp only [dirDeriv, neg_apply]
  ring_nf
  rfl

/-- The exact second derivative of the support-plane height. -/
theorem second_dirDeriv_radialSupport {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : E} (hx : x ∈ Ω)
    (o : E) (c : ℝ) (v z : E) :
    dirDeriv z (dirDeriv v (radialSupport u o c)) x =
      dirDeriv z (dirDeriv v u) x +
        dirDeriv (x - o) (dirDeriv z (dirDeriv v u)) x := by
  have he : dirDeriv v (radialSupport u o c) =ᶠ[nhds x]
      (fun y => fderiv ℝ (dirDeriv v u) y (y - o)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_radialSupport (hu.contDiffAt (hΩ.mem_nhds hy)) o c v
  change fderiv ℝ _ x z = _
  rw [he.fderiv_eq]
  exact (dirDeriv_radialGradient
    (contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) v) o z).trans (add_comm _ _)

end RadialCalculus

/-- The coordinate version used in the trace of the cap test. -/
theorem hessian_radialSupport {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (o : Space n) (c : ℝ) (i j : Fin n) :
    hessian (radialSupport u o c) x i j = hessian u x i j +
      dirDeriv (x - o) (fun y => hessian u y i j) x :=
  second_dirDeriv_radialSupport hΩ hu hx o c (coordinateVector n j) (coordinateVector n i)

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

/-- Trace of the identity, in the entry convention used in the manuscript. -/
theorem trace_inverse_mul_self {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) : (∑ i, ∑ j, H⁻¹ i j * H i j) = (n : ℝ) := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hH.isHermitian
  have he : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos))
  calc
    _ = ∑ i, (H⁻¹ * H) i i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hs.apply i j]
    _ = n := by rw [he]; simp

/-- Weighted radial trace, avoiding a logarithm at points outside the domain. -/
theorem weighted_trace_radialSupport {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : Space n} (hx : x ∈ Ω) (hpos : (hessian u x).PosDef)
    (o : Space n) (c : ℝ) :
    affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (radialSupport u o c) x i j) =
        n * affineAreaDensity u x + ((n : ℝ) + 2) * dirDeriv (x - o) (affineAreaDensity u) x := by
  simp_rw [hessian_radialSupport hΩ hu hx o c, mul_add, Finset.sum_add_distrib]
  rw [trace_inverse_mul_self hpos,
    dirDeriv_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds hx)) hpos]
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

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

/-- Scalar composition by its actual one-dimensional derivative. -/
theorem dirDeriv_comp_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E → ℝ} {ψ : ℝ → ℝ} {x : E} (hq : DifferentiableAt ℝ q x)
    (hψ : DifferentiableAt ℝ ψ (q x)) (v : E) :
    dirDeriv v (fun y => ψ (q y)) x = deriv ψ (q x) * dirDeriv v q x := by
  have hd := hψ.hasDerivAt.comp_hasFDerivAt x hq.hasFDerivAt
  change fderiv ℝ (ψ ∘ q) x v = _
  rw [hd.fderiv]
  rfl

/-- The second chain rule used by a cap test. -/
theorem second_dirDeriv_comp_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {q : E → ℝ} {ψ : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q Ω) (hψ : ContDiff ℝ ∞ ψ)
    {x : E} (hx : x ∈ Ω) (v z : E) :
    dirDeriv z (dirDeriv v (fun y => ψ (q y))) x =
      deriv (deriv ψ) (q x) * dirDeriv z q x * dirDeriv v q x +
      deriv ψ (q x) * dirDeriv z (dirDeriv v q) x := by
  have hψ' : ContDiff ℝ ∞ (deriv ψ) := hψ.deriv'
  have he : dirDeriv v (fun y => ψ (q y)) =ᶠ[nhds x]
      (fun y => deriv ψ (q y) * dirDeriv v q y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_comp_scalar ((hq.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      (hψ.differentiable (by simp) (q y)) v
  have hqx := hq.contDiffAt (hΩ.mem_nhds hx)
  have hdq := hqx.differentiableAt (by simp)
  change fderiv ℝ _ x z = _
  rw [he.fderiv_eq]
  change dirDeriv z (fun y => deriv ψ (q y) * dirDeriv v q y) x = _
  have hdc : DifferentiableAt ℝ (fun y => deriv ψ (q y)) x :=
    (hψ'.contDiffAt.comp x hqx).differentiableAt (by simp)
  rw [dirDeriv_mul hdc
    ((contDiffAt_dirDeriv hqx v).differentiableAt (by simp)),
    dirDeriv_comp_scalar hdq (hψ'.differentiable (by simp) (q x))]

theorem contDiffAt_graphAffineFunction {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (a : Space n →L[ℝ] ℝ) (b d : ℝ) :
    ContDiffAt ℝ ∞ (graphAffineFunction u a b d) x := by
  exact (a.contDiff.contDiffAt.add (contDiffAt_const.mul hu)).add contDiffAt_const

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

/-- The radial support gradient cancels exactly against the inverse Hessian. -/
theorem inverseHessian_radialSupport {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef)
    (o : Space n) (c : ℝ) (q : Space n → ℝ) :
    (∑ i, ∑ j, (hessian u x)⁻¹ i j *
      dirDeriv (coordinateVector n i) (radialSupport u o c) x *
      dirDeriv (coordinateVector n j) q x) = dirDeriv (x - o) q x := by
  simp_rw [dirDeriv_radialSupport hu o c]
  have he (i : Fin n) : dirDeriv (x - o) (dirDeriv (coordinateVector n i) u) x =
      ∑ k, (x - o) k * hessian u x k i :=
    dirDeriv_coordinate_sum (dirDeriv (coordinateVector n i) u) x (x - o)
  simp_rw [he]
  rw [inverse_radial_contraction hpos]
  exact (dirDeriv_coordinate_sum q x (x - o)).symm

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

/-- Chain trace in coordinates. -/
theorem hessian_composition_trace {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {q : Space n → ℝ} {ψ : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q Ω) (hψ : ContDiff ℝ ∞ ψ)
    {x : Space n} (hx : x ∈ Ω) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, A i j * hessian (fun y => ψ (q y)) x i j) =
      deriv (deriv ψ) (q x) * (∑ i, ∑ j, A i j *
        dirDeriv (coordinateVector n i) q x * dirDeriv (coordinateVector n j) q x) +
      deriv ψ (q x) * (∑ i, ∑ j, A i j * hessian q x i j) := by
  have he (i j : Fin n) : hessian (fun y => ψ (q y)) x i j =
      deriv (deriv ψ) (q x) * dirDeriv (coordinateVector n i) q x *
        dirDeriv (coordinateVector n j) q x + deriv ψ (q x) * hessian q x i j :=
    second_dirDeriv_comp_scalar hΩ hq hψ hx (coordinateVector n j) (coordinateVector n i)
  simp_rw [he, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> ring

/-- Positivity fixes the inverse-Hessian symmetry employed in a cap test. -/
theorem inverseHessian_isSymm {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hpos : (hessian u x).PosDef) : ((hessian u x)⁻¹).IsSymm :=
  (Matrix.isHermitian_iff_isSymm.mp hpos.isHermitian).inv

/-- Pointwise first-variation integrand of the source cap test. -/
theorem weighted_trace_capTest {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (hpos : (hessian u x).PosDef) (o : Space n) (c : ℝ)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    let q := graphAffineFunction u a b d
    let Z := radialSupport u o c
    affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (fun y => Z y * ψ (q y)) x i j) =
    affineAreaDensity u x *
      (Z x * (∑ i, ∑ j, (hessian u x)⁻¹ i j * dirDeriv (coordinateVector n i) q x *
        dirDeriv (coordinateVector n j) q x) * deriv (deriv ψ) (q x) +
       n * Z x * b * deriv ψ (q x) + 2 * dirDeriv (x - o) q x * deriv ψ (q x) +
       n * ψ (q x)) +
    ((n : ℝ) + 2) * ψ (q x) * dirDeriv (x - o) (affineAreaDensity u) x := by
  dsimp only
  let q := graphAffineFunction u a b d
  let Z := radialSupport u o c
  have hq : ContDiffOn ℝ ∞ q Ω := fun y hy =>
    (contDiffAt_graphAffineFunction (hu.contDiffAt (hΩ.mem_nhds hy)) a b d).contDiffWithinAt
  have hZ : ContDiffOn ℝ ∞ Z Ω := fun y hy =>
    (contDiffAt_radialSupport (hu.contDiffAt (hΩ.mem_nhds hy)) o c).contDiffWithinAt
  have hψq : ContDiffOn ℝ ∞ (fun y => ψ (q y)) Ω :=
    hψ.comp_contDiffOn hq
  have htraceq : (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian q x i j) = n * b := by
    dsimp only [q]
    simp_rw [hessian_graphAffineFunction hΩ hu hx a b d]
    calc
      _ = b * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian u x i j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = n * b := by rw [trace_inverse_mul_self hpos, mul_comm]
  have hcross : (∑ i, ∑ j, (hessian u x)⁻¹ i j * dirDeriv (coordinateVector n i) Z x *
      dirDeriv (coordinateVector n j) (fun y => ψ (q y)) x) =
        deriv ψ (q x) * dirDeriv (x - o) q x := by
    simp_rw [dirDeriv_comp_scalar ((hq.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
      (hψ.differentiable (by simp) (q x))]
    calc
      _ = deriv ψ (q x) * (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n i) Z x * dirDeriv (coordinateVector n j) q x) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [inverseHessian_radialSupport (hu.contDiffAt (hΩ.mem_nhds hx)) hpos]
  change affineAreaDensity u x *
    (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (fun y => Z y * ψ (q y)) x i j) = _
  rw [hessian_product_trace hΩ hZ hψq hx (inverseHessian_isSymm hpos),
    hessian_composition_trace hΩ hq hψ hx, htraceq, hcross]
  have hrad := weighted_trace_radialSupport hΩ hu hx hpos o c
  change affineAreaDensity u x * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian Z x i j) = _ at hrad
  linear_combination ψ (q x) * hrad

/-- Cancellation of the affine coefficients in the first variation. -/
theorem cap_affine_cancellation {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ u x) (o : Space n) (c : ℝ)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) :
    radialSupport u o c x * b - dirDeriv (x - o) (graphAffineFunction u a b d) x =
      (a o + b * c + d) - graphAffineFunction u a b d x := by
  rw [dirDeriv_graphAffineFunction hu]
  simp only [radialSupport, graphAffineFunction, dirDeriv, map_sub]
  ring

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

/-- Radial integration by parts with a compact test and no global extension of `f`.
This formulation gives integrability as well as the identity. -/
theorem integral_radial_divergence_compact {n : ℕ}
    {μ : Measure (Space n)} [μ.IsAddHaarMeasure]
    (f σ : Space n → ℝ) (o : Space n)
    (hσ : ContDiff ℝ ∞ σ) (hσc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x) :
    let D := fun x => dirDeriv (x - o) f x * σ x +
      f x * ((n : ℝ) * σ x + dirDeriv (x - o) σ x)
    Integrable D μ ∧ (∫ x, D x ∂μ) = 0 := by
  dsimp only
  let G (i : Fin n) (x : Space n) : ℝ := (x i - o i) * σ x
  let F (i : Fin n) (x : Space n) : ℝ := f x * G i x
  have hG (i : Fin n) : ContDiff ℝ ∞ (G i) := by
    exact ((coordinateProjection n i).contDiff.sub contDiff_const).mul hσ
  have hsG (i : Fin n) : tsupport (G i) ⊆ tsupport σ := tsupport_mul_subset_right
  have hsF (i : Fin n) : tsupport (F i) ⊆ tsupport σ :=
    tsupport_mul_subset_right.trans (hsG i)
  have hFc (i : Fin n) : HasCompactSupport (F i) :=
    hσc.of_isClosed_subset (isClosed_tsupport _) (hsF i)
  have hF (i : Fin n) : ContDiff ℝ ∞ (F i) :=
    contDiff_mul_at_tsupport (hG i) (fun x hx => hf x (hsG i hx))
  have hcoord (i : Fin n) (x : Space n) :
      dirDeriv (coordinateVector n i) (fun y : Space n => y i - o i) x = 1 := by
    change fderiv ℝ (fun y => coordinateProjection n i y - o i) x (coordinateVector n i) = 1
    rw [fderiv_sub_const, (coordinateProjection n i).fderiv]
    simp [coordinateVector]
  have hderiv (i : Fin n) (x : Space n) :
      dirDeriv (coordinateVector n i) (F i) x =
        dirDeriv (coordinateVector n i) f x * (x i - o i) * σ x +
        f x * (σ x + (x i - o i) * dirDeriv (coordinateVector n i) σ x) := by
    by_cases hx : x ∈ tsupport σ
    · have hdf := (hf x hx).differentiableAt (by simp)
      have hdc : DifferentiableAt ℝ (fun y : Space n => y i - o i) x :=
        ((coordinateProjection n i).differentiableAt.sub_const (o i))
      change dirDeriv (coordinateVector n i) (fun y => f y * G i y) x = _
      rw [dirDeriv_mul hdf ((hG i).differentiable (by simp) x)]
      change dirDeriv (coordinateVector n i) f x * ((x i - o i) * σ x) +
        f x * dirDeriv (coordinateVector n i) (fun y => (y i - o i) * σ y) x = _
      rw [dirDeriv_mul hdc (hσ.differentiable (by simp) x), hcoord]
      ring
    · have hz : σ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hz' : dirDeriv (coordinateVector n i) σ x = 0 := by
        unfold dirDeriv
        rw [fderiv_of_notMem_tsupport ℝ hx]
        rfl
      have hFz : dirDeriv (coordinateVector n i) (F i) x = 0 := by
        unfold dirDeriv
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hsF i h))]
        rfl
      rw [hz, hz', hFz]
      ring
  have hi (i : Fin n) : Integrable (dirDeriv (coordinateVector n i) (F i)) μ :=
    integrable_of_support_subset_compact (hFc i).isCompact
      ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ _))
      (contDiff_dirDeriv (hF i) _).continuous.continuousOn
  have he (x : Space n) :
      dirDeriv (x - o) f x * σ x + f x * ((n : ℝ) * σ x + dirDeriv (x - o) σ x) =
        ∑ i, dirDeriv (coordinateVector n i) (F i) x := by
    simp_rw [hderiv]
    rw [dirDeriv_coordinate_sum f x (x - o), dirDeriv_coordinate_sum σ x (x - o)]
    simp only [PiLp.sub_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    have hsum : (∑ i, (x i - o i) * dirDeriv (coordinateVector n i) f x * σ x) =
        ∑ i, dirDeriv (coordinateVector n i) f x * (x i - o i) * σ x := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hall : (fun x => dirDeriv (x - o) f x * σ x +
      f x * ((n : ℝ) * σ x + dirDeriv (x - o) σ x)) =
      (fun x => ∑ i, dirDeriv (coordinateVector n i) (F i) x) := funext he
  rw [hall]
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_dirDeriv_compact _ (hF _) (hFc _)]
  simp

/-- Zero-extension of a compactly supported local test is genuinely smooth on the
ambient coordinate space; no extension theorem for the graph is needed. -/
theorem contDiff_indicator_of_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {f : E → ℝ} {k : ℕ∞ω} (hf : ContDiffOn ℝ k f Ω)
    (hz : ∀ x ∈ Ω, x ∉ K → f x = 0) :
    ContDiff ℝ k (Ω.indicator f) ∧ HasCompactSupport (Ω.indicator f) ∧
      tsupport (Ω.indicator f) ⊆ K := by
  have hs : Function.support (Ω.indicator f) ⊆ K := by
    intro x hx
    by_contra hxK
    by_cases hxΩ : x ∈ Ω
    · exact hx (by rw [Set.indicator_of_mem hxΩ, hz x hxΩ hxK])
    · exact hx (Set.indicator_of_notMem hxΩ f)
  have ht : tsupport (Ω.indicator f) ⊆ K := closure_minimal hs hK.isClosed
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩
  apply contDiff_of_contDiffAt_tsupport
  intro x hx
  have hxΩ := hKΩ (ht hx)
  apply (hf.contDiffAt (hΩ.mem_nhds hxΩ)).congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hxΩ] with y hy
  exact Set.indicator_of_mem hy f

/-- Hessians depend only on the germ of a function, also with the total derivative
convention at points outside the domain. -/
theorem hessian_eq_of_eventuallyEq {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    (h : f =ᶠ[nhds x] g) : hessian f x = hessian g x := by
  ext i j
  have h' : (fun y => fderiv ℝ f y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ g y (coordinateVector n j)) :=
    (h.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg (fun L => L (coordinateVector n j)) hy
  exact congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinateVector n i)) h'.fderiv_eq

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

/-- The cap identity in the original graph coordinates (source `area.tex`,
Lemma Cap identity). The source assumes compact support of all three displayed
scalar compositions; this proof in fact only needs the first support condition.
The measure here is precisely affine area density times Lebesgue measure. -/
theorem affineMaximal_graph_cap_identity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {K : Set (Space n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hsupport : ∀ x ∈ Ω, x ∉ K → ψ (graphAffineFunction u a b d x) = 0) :
    (∫ x in Ω, affineAreaDensity u x *
      (radialSupport u o c x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n i) (graphAffineFunction u a b d) x *
          dirDeriv (coordinateVector n j) (graphAffineFunction u a b d) x) *
            deriv (deriv ψ) (graphAffineFunction u a b d x) +
       (n : ℝ) * ((a o + b * c + d) - graphAffineFunction u a b d x) *
         deriv ψ (graphAffineFunction u a b d x) -
       (n : ℝ) * ((n : ℝ) + 1) * ψ (graphAffineFunction u a b d x))) = 0 := by
  let q := graphAffineFunction u a b d
  let Z := radialSupport u o c
  let ρ := affineAreaDensity u
  let σ := Ω.indicator (fun x => ψ (q x))
  let η := fun x => Z x * σ x
  let F := fun x => ρ x * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)
  let D := fun x => dirDeriv (x - o) ρ x * σ x +
    ρ x * ((n : ℝ) * σ x + dirDeriv (x - o) σ x)
  have hq : ContDiffOn ℝ ∞ q Ω := fun x hx =>
    (contDiffAt_graphAffineFunction (hu.contDiffAt (hΩ.mem_nhds hx)) a b d).contDiffWithinAt
  have hσpack := contDiff_indicator_of_compact hΩ hK hKΩ (hψ.comp_contDiffOn hq) hsupport
  have hσ : ContDiff ℝ ∞ σ := hσpack.1
  have hσc : HasCompactSupport σ := hσpack.2.1
  have hσΩ : tsupport σ ⊆ Ω := hσpack.2.2.trans hKΩ
  have hηs : tsupport η ⊆ tsupport σ := tsupport_mul_subset_right
  have hη : ContDiff ℝ ∞ η := contDiff_mul_at_tsupport hσ fun x hx =>
    contDiffAt_radialSupport (hu.contDiffAt (hΩ.mem_nhds (hσΩ hx))) o c
  have hηc : HasCompactSupport η := hσc.of_isClosed_subset (isClosed_tsupport _) hηs
  have hηΩ := hηs.trans hσΩ
  have hFint : IntegrableOn F Ω := integrableOn_area_variation hΩ hu hpos η hη hηc hηΩ
  have hFzero : (∫ x in Ω, F x) = 0 :=
    affineMaximal_area_stationarity hΩ hu hpos hmax η hη hηc hηΩ
  have hDpack : Integrable D ∧ (∫ x, D x) = 0 :=
    integral_radial_divergence_compact ρ σ o hσ hσc fun x hx =>
      contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hσΩ hx))) (hpos x (hσΩ hx))
  have hDzero : (∫ x in Ω, D x) = 0 := by
    calc
      _ = ∫ x, D x := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hn : x ∉ tsupport σ := fun h => hx (hσΩ h)
        have hσ0 : σ x = 0 := image_eq_zero_of_notMem_tsupport hn
        have hσ1 : dirDeriv (x - o) σ x = 0 := by
          unfold dirDeriv
          rw [fderiv_of_notMem_tsupport ℝ hn]
          rfl
        simp [D, hσ0, hσ1]
      _ = 0 := hDpack.2
  have he (x : Space n) (hx : x ∈ Ω) :
      ρ x * (Z x * (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n i) q x * dirDeriv (coordinateVector n j) q x) *
          deriv (deriv ψ) (q x) +
        (n : ℝ) * ((a o + b * c + d) - q x) * deriv ψ (q x) -
        (n : ℝ) * ((n : ℝ) + 1) * ψ (q x)) = F x - ((n : ℝ) + 2) * D x := by
    have hσeq : σ =ᶠ[nhds x] (fun y => ψ (q y)) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact Set.indicator_of_mem hy _
    have hηeq : η =ᶠ[nhds x] (fun y => Z y * ψ (q y)) :=
      hσeq.mono fun y hy => congrArg (Z y * ·) hy
    have hσderiv : dirDeriv (x - o) σ x = deriv ψ (q x) * dirDeriv (x - o) q x := by
      unfold dirDeriv
      rw [hσeq.fderiv_eq]
      exact dirDeriv_comp_scalar ((hq.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
        (hψ.differentiable (by simp) (q x)) (x - o)
    -- `F` uses the zero-extension, so transfer its Hessian by equality of germs.
    have hFexp' : F x =
      ρ x * (Z x * (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n i) q x * dirDeriv (coordinateVector n j) q x) *
            deriv (deriv ψ) (q x) +
        n * Z x * b * deriv ψ (q x) + 2 * dirDeriv (x - o) q x * deriv ψ (q x) +
        n * ψ (q x)) + ((n : ℝ) + 2) * ψ (q x) * dirDeriv (x - o) ρ x := by
      dsimp only [F]
      rw [hessian_eq_of_eventuallyEq hηeq]
      exact weighted_trace_capTest hΩ hu hx (hpos x hx) o c a b d hψ
    rw [hFexp']
    dsimp only [D]
    rw [hσeq.eq_of_nhds, hσderiv]
    have hc := cap_affine_cancellation ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt
      (by simp)) o c a b d
    change Z x * b - dirDeriv (x - o) q x = (a o + b * c + d) - q x at hc
    linear_combination -ρ x * (n : ℝ) * deriv ψ (q x) * hc
  calc
    _ = ∫ x in Ω, F x - ((n : ℝ) + 2) * D x :=
      setIntegral_congr_fun hΩ.measurableSet he
    _ = (∫ x in Ω, F x) - ((n : ℝ) + 2) * ∫ x in Ω, D x := by
      rw [integral_sub hFint (hDpack.1.integrableOn.const_mul _), integral_const_mul]
    _ = 0 := by rw [hFzero, hDzero]; ring

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
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothPositivePart
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

lemma smoothPositiveSlope_smooth (ε : ℝ) : ContDiff ℝ ∞ (smoothPositiveSlope ε) := by
  unfold smoothPositiveSlope
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)

lemma smoothPositivePart_hasDeriv (ε t : ℝ) :
    HasDerivAt (smoothPositivePart ε) (smoothPositiveSlope ε t) t := by
  have hc := (smoothPositiveSlope_smooth ε).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma smoothPositivePart_smooth (ε : ℝ) : ContDiff ℝ ∞ (smoothPositivePart ε) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (smoothPositivePart_hasDeriv ε t).differentiableAt, ?_⟩
  have he : deriv (smoothPositivePart ε) = smoothPositiveSlope ε :=
    funext fun t => (smoothPositivePart_hasDeriv ε t).deriv
  rw [he]
  exact smoothPositiveSlope_smooth ε

lemma smoothPositiveSlope_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε) :
    smoothPositiveSlope ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma smoothPositiveSlope_one {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    smoothPositiveSlope ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

lemma smoothPositivePart_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε) :
    smoothPositivePart ε t = 0 := by
  unfold smoothPositivePart
  calc
    _ = ∫ s in (-ε)..t, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_ge ht] at hs
      exact smoothPositiveSlope_zero hε hs.2
    _ = 0 := by simp

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
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothCapTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section SmoothCapTest

lemma smoothCapTest_hasDeriv (ε b t : ℝ) :
    HasDerivAt (smoothCapTest ε b) (-smoothPositivePart ε (b-t)) t := by
  have hc := (smoothPositivePart_smooth ε).continuous
  have hi : HasDerivAt (fun z : ℝ => ∫ s in (-ε)..z, smoothPositivePart ε s)
      (smoothPositivePart ε (b-t)) (b-t) :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  change HasDerivAt (fun x : ℝ => ∫ s in (-ε)..(b-x), smoothPositivePart ε s) _ t
  simpa only [Function.comp_def,zero_sub,smul_eq_mul,neg_mul,one_mul] using
    hi.scomp t ((hasDerivAt_const t b).sub (hasDerivAt_id t))

lemma smoothCapTest_second (ε b : ℝ) :
    deriv (deriv (smoothCapTest ε b)) = fun t => smoothPositiveSlope ε (b-t) := by
  have he : deriv (smoothCapTest ε b) = fun t => -smoothPositivePart ε (b-t) :=
    funext fun t => (smoothCapTest_hasDeriv ε b t).deriv
  rw [he]
  funext t
  have hd := ((smoothPositivePart_hasDeriv ε (b-t)).comp t
    ((hasDerivAt_const t b).sub (hasDerivAt_id t))).neg
  simpa only [Function.comp_def,Pi.neg_def,zero_sub,mul_neg,mul_one,neg_neg] using hd.deriv

lemma smoothCapTest_smooth (ε b : ℝ) : ContDiff ℝ ∞ (smoothCapTest ε b) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (smoothCapTest_hasDeriv ε b t).differentiableAt,?_⟩
  rw [show deriv (smoothCapTest ε b) = fun t => -smoothPositivePart ε (b-t) from
    funext fun t => (smoothCapTest_hasDeriv ε b t).deriv]
  exact ((smoothPositivePart_smooth ε).comp (contDiff_const.sub contDiff_id)).neg

lemma smoothCapTest_second_nonneg (ε b t : ℝ) :
    0 ≤ deriv (deriv (smoothCapTest ε b)) t := by
  rw [smoothCapTest_second]
  exact Real.smoothTransition.nonneg _

lemma smoothCapTest_second_one {ε : ℝ} (hε : 0 < ε) {b t : ℝ} (ht : t ≤ b-ε) :
    deriv (deriv (smoothCapTest ε b)) t = 1 := by
  rw [smoothCapTest_second]
  exact smoothPositiveSlope_one hε (by linarith)

lemma smoothCapTest_vanish {ε : ℝ} (hε : 0 < ε) {b t : ℝ} (ht : b+ε ≤ t) :
    smoothCapTest ε b t = 0 ∧ deriv (smoothCapTest ε b) t = 0 ∧
      deriv (deriv (smoothCapTest ε b)) t = 0 := by
  have hbt : b-t ≤ -ε := by linarith
  refine ⟨?_,?_,?_⟩
  · unfold smoothCapTest
    calc
      _ = ∫ s in (-ε)..(b-t), (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_ge hbt] at hs
        exact smoothPositivePart_zero hε hs.2
      _ = 0 := by simp
  · rw [(smoothCapTest_hasDeriv ε b t).deriv,smoothPositivePart_zero hε hbt,neg_zero]
  · rw [smoothCapTest_second]
    exact smoothPositiveSlope_zero hε hbt

/-- All lower-order terms of the cap identity are bounded by a single
constant fixed by the level interval, center level, dimension and cutoff.
Thus the test construction requires no solution-dependent constant. -/
lemma smoothCapTest_lower_order_bound (n : ℕ) (ε b a q₀ : ℝ) :
    ∃ C > 0, ∀ t ∈ Set.Icc a (b+ε),
      (n:ℝ)*(t-q₀)*deriv (smoothCapTest ε b) t +
        (n:ℝ)*((n:ℝ)+1)*smoothCapTest ε b t ≤ C := by
  let g := fun t => (n:ℝ)*(t-q₀)*deriv (smoothCapTest ε b) t +
        (n:ℝ)*((n:ℝ)+1)*smoothCapTest ε b t
  have hg : Continuous g := by
    have h1 : ContDiff ℝ ∞ (deriv (smoothCapTest ε b)) := (smoothCapTest_smooth ε b).deriv'
    exact ((continuous_const.mul (continuous_id.sub continuous_const)).mul h1.continuous).add
      (continuous_const.mul (smoothCapTest_smooth ε b).continuous)
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hg.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro t ht
  exact (hC ⟨t,ht,rfl⟩).trans (le_max_right _ _)

end SmoothCapTest

/-- The quantitative supporting-plane inequality for an actual interior ball,
valid in any real normed ambient space. -/
lemma ball_support_lower {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ell : V →L[ℝ] ℝ) (o p : V) {r : ℝ} (hr : 0 < r)
    (hs : ∀ z ∈ Metric.closedBall o r, 0 ≤ ell (z-p)) :
    r*‖ell‖ ≤ ell (o-p) := by
  have hZ : 0 ≤ ell (o-p) := hs o (by simp [hr.le])
  have hb (z : V) (hz : ‖z‖ ≤ r) : |ell z| ≤ ell (o-p) := by
    have hp := hs (o+z) (by simpa [Metric.mem_closedBall,dist_eq_norm] using hz)
    have hm := hs (o-z) (by simpa [Metric.mem_closedBall,dist_eq_norm] using hz)
    have hep : ell (o+z-p) = ell (o-p)+ell z := by rw [show o+z-p = o-p+z by abel,map_add]
    have hem : ell (o-z-p) = ell (o-p)-ell z := by rw [show o-z-p = (o-p)-z by abel,map_sub]
    rw [hep] at hp
    rw [hem] at hm
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hn : ‖ell‖ ≤ ell (o-p)/r := by
    apply ell.opNorm_le_bound' (div_nonneg hZ hr.le)
    intro z hz
    have hpz : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hs := hb ((r/‖z‖) • z) (by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hpz),div_mul_cancel₀ _ hz])
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos (div_pos hr hpz)] at hs
    rw [Real.norm_eq_abs]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hr).2
    rw [div_mul_eq_mul_div] at hs
    have hh := (div_le_iff₀ hpz).1 hs
    nlinarith
  simpa only [mul_comm] using (le_div_iff₀ hr).1 hn

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapInverseBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma graphInverseMetric_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (a : Space n →L[ℝ] ℝ) (b d : ℝ) :
    0 ≤ graphInverseMetric u a b d x := by
  let v := fun i => dirDeriv (coordinateVector n i) (graphAffineFunction u a b d) x
  have hh := hp.inv.posSemidef.dotProduct_mulVec_nonneg v
  simpa only [RCLike.re_to_real,star_trivial,graphInverseMetric,v,dotProduct,Matrix.mulVec,
    Finset.mul_sum,mul_left_comm,mul_assoc] using hh

lemma contDiffAt_graphInverseMetric {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) :
    ContDiffAt ℝ ∞ (graphInverseMetric u a b d) x := by
  have hq := contDiffAt_graphAffineFunction hu a b d
  have hi (i j : Fin n) : ContDiffAt ℝ ∞ (fun y => (hessian u y)⁻¹ i j) x := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
    exact ((contDiffAt_det_hessian hu).inv hp.det_pos.ne').mul
      (contDiffAt_adjugate_hessian_entry hu i j)
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((hi i j).mul ((hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)).mul
    ((hq.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedCapInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

theorem affineMaximal_graph_cap_weighted_inverse_bound {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {K Q : Set (Space n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hQ : MeasurableSet Q) (hQK : Q ⊆ K)
    (hs : ∀ x ∈ Ω, x ∉ K →
      ψ (graphAffineFunction u a b d x) = 0 ∧
      deriv ψ (graphAffineFunction u a b d x) = 0 ∧
      deriv (deriv ψ) (graphAffineFunction u a b d x) = 0)
    (hZ : ∀ x ∈ K, 0 ≤ radialSupport u o c x)
    (hρ : ∀ x ∈ K, 0 ≤ deriv (deriv ψ) (graphAffineFunction u a b d x))
    (W : Space n → ℝ) (hW : ContinuousOn W K)
    {r C : ℝ} (hr : 0 ≤ r)
    (hrZ : ∀ x ∈ Q, r*W x ≤ radialSupport u o c x)
    (hρQ : ∀ x ∈ Q, 1 ≤ deriv (deriv ψ) (graphAffineFunction u a b d x))
    (hC : ∀ x ∈ K,
      (n:ℝ) * (graphAffineFunction u a b d x - (a o+b*c+d)) *
        deriv ψ (graphAffineFunction u a b d x) +
      (n:ℝ)*((n:ℝ)+1)*ψ (graphAffineFunction u a b d x) ≤ C) :
    r * (∫ x in Q, affineAreaDensity u x * (W x * graphInverseMetric u a b d x)) ≤
      C * ∫ x in K, affineAreaDensity u x := by
  lift r to NNReal using hr
  let q := graphAffineFunction u a b d
  let V := graphInverseMetric u a b d
  let Z := radialSupport u o c
  let A := affineAreaDensity u
  let F := fun x => A x * (Z x * V x * deriv (deriv ψ) (q x))
  let G := fun x => A x * ((n:ℝ)*(q x-(a o+b*c+d))*deriv ψ (q x) +
    (n:ℝ)*((n:ℝ)+1)*ψ (q x))
  have hAc : ContinuousOn A K := fun x hx =>
    (contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx))).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V K := fun x hx =>
    (contDiffAt_graphInverseMetric (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx)) a b d).continuousAt.continuousWithinAt
  have hzc : ContinuousOn Z K := fun x hx =>
    (contDiffAt_radialSupport (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))) o c).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q K := fun x hx =>
    (contDiffAt_graphAffineFunction (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))) a b d).continuousAt.continuousWithinAt
  have hp0 := hψ.continuous.comp_continuousOn hqc
  have hψ1 : ContDiff ℝ ∞ (deriv ψ) := hψ.deriv'
  have hψ2 : ContDiff ℝ ∞ (deriv (deriv ψ)) := hψ1.deriv'
  have hp1 := hψ1.continuous.comp_continuousOn hqc
  have hp2 := hψ2.continuous.comp_continuousOn hqc
  have hFi : IntegrableOn F K := (hAc.mul ((hzc.mul hVc).mul hp2)).integrableOn_compact hK
  have hGi : IntegrableOn G K :=
    (hAc.mul (((continuousOn_const.mul (hqc.sub continuousOn_const)).mul hp1).add
      (continuousOn_const.mul hp0))).integrableOn_compact hK
  have hAi : IntegrableOn A K := hAc.integrableOn_compact hK
  have hAVi : IntegrableOn (fun x => A x*(W x*V x)) K := (hAc.mul (hW.mul hVc)).integrableOn_compact hK
  have hFG : (∫ x in K, F x-G x) = 0 := by
    have hh := affineMaximal_graph_cap_identity hΩ hu hp hm o c a b d hψ hK hKΩ
      (fun x hx hnot => (hs x hx hnot).1)
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hKΩ] at hh
    · convert hh using 1
      all_goals try with_reducible_and_instances rfl
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      dsimp [F,G,V,graphInverseMetric,A,Z,q]
      ring
    · intro x hx
      obtain ⟨h0,h1,h2⟩ := hs x hx.1 hx.2
      simp only [h0,h1,h2,mul_zero,add_zero,sub_zero]
  have hFG' : (∫ x in K, F x) = ∫ x in K, G x := by
    rw [integral_sub hFi hGi] at hFG
    exact sub_eq_zero.mp hFG
  have hAp (x : Space n) (hx : x ∈ K) : 0 ≤ A x :=
    (Real.rpow_pos_of_pos (hp x (hKΩ hx)).det_pos _).le
  have hVp (x : Space n) (hx : x ∈ K) : 0 ≤ V x :=
    graphInverseMetric_nonneg (hp x (hKΩ hx)) a b d
  have hFp (x : Space n) (hx : x ∈ K) : 0 ≤ F x :=
    mul_nonneg (hAp x hx) (mul_nonneg (mul_nonneg (hZ x hx) (hVp x hx)) (hρ x hx))
  calc
    _ = ∫ x in Q, r*(A x*(W x*V x)) := (integral_const_mul _ _).symm
    _ ≤ ∫ x in Q, F x := by
      apply setIntegral_mono_on ((hAVi.mono_set hQK).const_mul r)
        (hFi.mono_set hQK) hQ
      intro x hx
      have hz := hrZ x hx
      have hv := hVp x (hQK hx)
      have ha := hAp x (hQK hx)
      have hs' := hρQ x hx
      have hz0 : 0 ≤ Z x := hZ x (hQK hx)
      dsimp [F]
      calc
        _ = A x*((r*W x)*V x*1) := by ring
        _ ≤ A x*(Z x*V x*deriv (deriv ψ) (q x)) := by gcongr
    _ ≤ ∫ x in K, F x := setIntegral_mono_set hFi
      (ae_restrict_of_forall_mem hK.measurableSet hFp) (Filter.Eventually.of_forall fun _ hx => hQK hx)
    _ = ∫ x in K, G x := hFG'
    _ ≤ ∫ x in K, C*A x := by
      apply setIntegral_mono_on hGi (hAi.const_mul C) hK.measurableSet
      intro x hx
      dsimp [G]
      calc
        _ ≤ A x*C := mul_le_mul_of_nonneg_left (hC x hx) (hAp x hx)
        _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineInvariantCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma affineGraphConormal_apply {n : ℕ} (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (x : Space n) (z : Space n × ℝ) :
    affineGraphConormal u L x z = (L.symm z).2-fderiv ℝ u x (L.symm z).1 := rfl

lemma continuousAt_affineGraphConormal {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) :
    ContinuousAt (affineGraphConormal u L) x := by
  exact (continuousAt_const.sub
    (((hu.fderiv_right (m := ∞) (by simp)).continuousAt).clm_comp continuousAt_const)).clm_comp
      continuousAt_const

lemma affine_epigraph_support {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : ConvexOn ℝ Ω u) {x : Space n} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {z : Space n × ℝ} (hz : z ∈ (fun p => L p+v) '' sourceEpigraph Ω u) :
    0 ≤ affineGraphConormal u L x (z-(L (x,u x)+v)) := by
  obtain ⟨p,hp,rfl⟩ := hz
  have hs := convex_fderiv_support hc hx hp.1 hd
  rw [show L p+v-(L (x,u x)+v) = L (p-(x,u x)) by simp only [map_sub]; abel,
    affineGraphConormal_apply,L.symm_apply_apply]
  change 0 ≤ p.2-u x-fderiv ℝ u x (p.1-x)
  have ht : u p.1 ≤ p.2 := hp.2
  linarith

/-- The actual inner ball produces the conormal-normalized radial support
bound required in the cap estimate. It is uniform under arbitrary affine maps. -/
lemma affine_inner_ball_radialSupport {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : ConvexOn ℝ Ω u) {x : Space n} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ u x)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (o : Space n) (c : ℝ) {r : ℝ} (hr : 0 < r)
    (hb : Metric.closedBall (L (o,c)+v) r ⊆ (fun p => L p+v) '' sourceEpigraph Ω u) :
    r*‖affineGraphConormal u L x‖ ≤ radialSupport u o c x := by
  have hh := ball_support_lower (affineGraphConormal u L x) (L (o,c)+v)
    (L (x,u x)+v) hr (fun z hz => affine_epigraph_support hc hx hd L v (hb hz))
  have he : affineGraphConormal u L x (L (o,c)+v-(L (x,u x)+v)) = radialSupport u o c x := by
    rw [show L (o,c)+v-(L (x,u x)+v) = L ((o,c)-(x,u x)) by simp only [map_sub]; abel,
      affineGraphConormal_apply,L.symm_apply_apply]
    change c-u x-fderiv ℝ u x (o-x) = c-u x+fderiv ℝ u x (x-o)
    rw [← neg_sub x o,map_neg,sub_neg_eq_add]
  rwa [he] at hh

/-- Uniform affine-image cap estimate, derived from the original PDE.
The scalar is the inverse second-form norm with the actual inward unit
conormal. The determinant on the left is the genuine affine-area covariance.
No transformed-PDE premise or conormal bound is assumed. -/
theorem affineMaximal_uniform_affine_cap_bound (n : ℕ)
    {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R)
    (t₀ t₁ q₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      ∀ (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
        (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ),
      Metric.closedBall (L (o,c)+v) r ⊆ (fun p => L p+v) '' sourceEpigraph Ω u →
      a o+b*c+d = q₀ →
      ∀ {K Q : Set (Space n)}, IsCompact K → K ⊆ Ω → MeasurableSet Q → Q ⊆ K →
      (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ graphAffineFunction u a b d x) →
      (∀ x ∈ K, graphAffineFunction u a b d x ∈ Icc t₀ (t₁+ε)) →
      (∀ x ∈ Q, graphAffineFunction u a b d x ≤ t₁-ε) →
      (∀ x ∈ K, ∀ j, |(L (x,u x)+v).1 j| ≤ R) →
      (∀ x ∈ K, |(L (x,u x)+v).2| ≤ R) →
      Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        (∫ x in Q, affineAreaDensity u x *
          (‖affineGraphConormal u L x‖ * graphInverseMetric u a b d x)) ≤ C := by
  obtain ⟨C₁,hC₁pos,hC₁⟩ := smoothCapTest_lower_order_bound n ε t₁ t₀ q₀
  let B := (graphAreaBoxBound n (2*R)).toReal
  refine ⟨C₁*(B+1)/r,by dsimp [B]; positivity,?_⟩
  intro Ω hΩ hcv u hu hp hm L v o c a b d hball hq₀ K Q hK hKΩ hQ hQK hs hqK hqQ hxR htR
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hZ (x) (hx : x ∈ Ω) : r*‖affineGraphConormal u L x‖ ≤ radialSupport u o c x :=
    affine_inner_ball_radialSupport hcu hx
      ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) L v o c hr hball
  have hZ0 (x) (hx : x ∈ Ω) : 0 ≤ radialSupport u o c x :=
    (mul_nonneg hr.le (norm_nonneg _)).trans (hZ x hx)
  have hW : ContinuousOn (fun x => ‖affineGraphConormal u L x‖) K := fun x hx =>
    (continuousAt_affineGraphConormal (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))) L).norm.continuousWithinAt
  have hb := affineMaximal_graph_cap_weighted_inverse_bound hΩ hu hp hm o c a b d
    (smoothCapTest_smooth ε t₁) hK hKΩ hQ hQK
    (fun x hx hn => smoothCapTest_vanish hε (hs x hx hn))
    (fun x hx => hZ0 x (hKΩ hx))
    (fun x _ => smoothCapTest_second_nonneg ε t₁ (graphAffineFunction u a b d x))
    (fun x => ‖affineGraphConormal u L x‖) hW hr.le
    (fun x hx => hZ x (hKΩ (hQK hx)))
    (fun x hx => le_of_eq (smoothCapTest_second_one hε (hqQ x hx)).symm)
    (fun x hx => by rw [hq₀]; exact hC₁ _ (hqK x hx))
  let J := Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))
  have hJ : 0 ≤ J := Real.rpow_nonneg (abs_nonneg _) _
  have harea := affine_image_graph_area_in_box hΩ hcv hK.measurableSet hKΩ hu hp L v hR hxR htR
  have hi := mul_le_mul_of_nonneg_left hb hJ
  have hi' : r*(J*(∫ x in Q, affineAreaDensity u x *
      (‖affineGraphConormal u L x‖*graphInverseMetric u a b d x))) ≤ C₁*(B+1) := by
    calc
      _ = J*(r*(∫ x in Q, affineAreaDensity u x *
          (‖affineGraphConormal u L x‖*graphInverseMetric u a b d x))) := by ring
      _ ≤ J*(C₁*∫ x in K, affineAreaDensity u x) := hi
      _ = C₁*(J*∫ x in K, affineAreaDensity u x) := by ring
      _ ≤ C₁*B := mul_le_mul_of_nonneg_left harea hC₁pos.le
      _ ≤ C₁*(B+1) := by nlinarith
  exact (le_div_iff₀ hr).mpr (by rwa [mul_comm] at hi')

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineCapLIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- Original-PDE cap bound for the nonnegative integral used by actual chart transport.
Integrability is produced from the compact cap data, not added as a hypothesis. -/
theorem affineMaximal_uniform_affine_cap_lintegral_bound (n : ℕ)
    {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R)
    (t₀ t₁ q₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      ∀ (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
        (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ),
      Metric.closedBall (L (o,c)+v) r ⊆ (fun p => L p+v) '' sourceEpigraph Ω u →
      a o+b*c+d = q₀ →
      ∀ {K Q : Set (Space n)}, IsCompact K → K ⊆ Ω → MeasurableSet Q → Q ⊆ K →
      (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ graphAffineFunction u a b d x) →
      (∀ x ∈ K, graphAffineFunction u a b d x ∈ Icc t₀ (t₁+ε)) →
      (∀ x ∈ Q, graphAffineFunction u a b d x ≤ t₁-ε) →
      (∀ x ∈ K, ∀ j, |(L (x,u x)+v).1 j| ≤ R) →
      (∀ x ∈ K, |(L (x,u x)+v).2| ≤ R) →
      ENNReal.ofReal (Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))) *
        (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖affineGraphConormal u L x‖ * graphInverseMetric u a b d x))) ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := affineMaximal_uniform_affine_cap_bound n hε hr hR t₀ t₁ q₀
  refine ⟨C,hC,?_⟩
  intro Ω hΩ hcv u hu hp hm L v o c a b d hball hq₀ K Q hK hKΩ hQ hQK hs hqK hqQ hxR htR
  have hAc : ContinuousOn (affineAreaDensity u) K := fun x hx =>
    (contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx))).continuousAt.continuousWithinAt
  have hNc : ContinuousOn (fun x => ‖affineGraphConormal u L x‖) K := fun x hx =>
    (continuousAt_affineGraphConormal (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx))) L).norm.continuousWithinAt
  have hVc : ContinuousOn (graphInverseMetric u a b d) K := fun x hx =>
    (contDiffAt_graphInverseMetric (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx)) a b d).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun x => affineAreaDensity u x *
      (‖affineGraphConormal u L x‖ * graphInverseMetric u a b d x)) Q :=
    ((hAc.mul (hNc.mul hVc)).integrableOn_compact hK).mono_set hQK
  have hnn : 0 ≤ᵐ[volume.restrict Q] (fun x => affineAreaDensity u x *
      (‖affineGraphConormal u L x‖ * graphInverseMetric u a b d x)) := by
    filter_upwards [ae_restrict_mem hQ] with x hx
    exact mul_nonneg (Real.rpow_nonneg (hp x (hKΩ (hQK hx))).det_pos.le _)
      (mul_nonneg (norm_nonneg _) (graphInverseMetric_nonneg (hp x (hKΩ (hQK hx))) a b d))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
  rw [← ENNReal.ofReal_mul (p := Real.rpow |L.toContinuousLinearMap.det|
    ((n:ℝ)/((n:ℝ)+2))) (Real.rpow_nonneg (abs_nonneg _) _)]
  exact ENNReal.ofReal_le_ofReal (hbound hΩ hcv hu hp hm L v o c a b d hball hq₀
    hK hKΩ hQ hQK hs hqK hqQ hxR htR)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TargetCapLIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma targetGraphConormal_norm_le {n : ℕ} (u : Space n → ℝ)
    (L T : G ≃L[ℝ] (Space n × ℝ)) (x : Space n) :
    ‖targetGraphConormal u L x‖ ≤
      (‖T.toContinuousLinearMap‖+1)*‖affineGraphConormal u (L.symm.trans T) x‖ := by
  have he : targetGraphConormal u L x =
      (affineGraphConormal u (L.symm.trans T) x).comp T.toContinuousLinearMap := by
    ext z
    simp [targetGraphConormal,affineGraphConormal]
  rw [he]
  calc
    _ ≤ ‖affineGraphConormal u (L.symm.trans T) x‖ * ‖T.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖T.toContinuousLinearMap‖+1)*‖affineGraphConormal u (L.symm.trans T) x‖ := by
      nlinarith [norm_nonneg (affineGraphConormal u (L.symm.trans T) x)]

/-- The uniform cap producer in a fixed normed target. Choosing target coordinates costs
only constants depending on those fixed coordinates, never on the varying affine map.
The nonnegative integral is the exact original inverse second form with actual conormal norm. -/
theorem affineMaximal_uniform_target_cap_lintegral_bound_oai (n : ℕ)
    (T : G ≃L[ℝ] (Space n × ℝ))
    {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R)
    (t₀ t₁ q₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      ∀ (L : G ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
        (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ),
      Metric.closedBall (L.symm ((o,c)-v)) r ⊆
        (fun p => L.symm (p-v)) '' sourceEpigraph Ω u →
      a o+b*c+d = q₀ →
      ∀ {K Q : Set (Space n)}, IsCompact K → K ⊆ Ω → MeasurableSet Q → Q ⊆ K →
      (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ graphAffineFunction u a b d x) →
      (∀ x ∈ K, graphAffineFunction u a b d x ∈ Icc t₀ (t₁+ε)) →
      (∀ x ∈ Q, graphAffineFunction u a b d x ≤ t₁-ε) →
      (∀ x ∈ K, ‖L.symm ((x,u x)-v)‖ ≤ R) →
      ENNReal.ofReal (Real.rpow |(L.symm.trans T).toContinuousLinearMap.det|
        ((n:ℝ)/((n:ℝ)+2))) *
        (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖targetGraphConormal u L x‖ * graphInverseMetric u a b d x))) ≤ ENNReal.ofReal C := by
  let D := ‖T.toContinuousLinearMap‖+1
  let E := ‖T.symm.toContinuousLinearMap‖+1
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  obtain ⟨C,hC,hcap⟩ := affineMaximal_uniform_affine_cap_lintegral_bound n hε
    (div_pos hr hE) (mul_nonneg hD.le hR) t₀ t₁ q₀
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro Ω hΩ hcv u hu hp hm L v o c a b d hball hq₀ K Q hK hKΩ hQ hQK hs hqK hqQ hxR
  let M := L.symm.trans T
  let w := -T (L.symm v)
  have he (p : Space n × ℝ) : M p+w = T (L.symm (p-v)) := by
    simp [M,w,ContinuousLinearEquiv.trans_apply,sub_eq_add_neg]
  have hball' : Metric.closedBall (M (o,c)+w) (r/E) ⊆
      (fun p => M p+w) '' sourceEpigraph Ω u := by
    intro z hz
    have hdist : dist (T.symm z) (L.symm ((o,c)-v)) ≤ r := by
      have hz' : ‖z-T (L.symm ((o,c)-v))‖ ≤ r/E := by
        simpa only [Metric.mem_closedBall,dist_eq_norm,he] using hz
      calc
        _ = ‖T.symm (z-T (L.symm ((o,c)-v)))‖ := by
          simp only [map_sub,T.symm_apply_apply,dist_eq_norm]
        _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖z-T (L.symm ((o,c)-v))‖ :=
          T.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ E*(r/E) := mul_le_mul (by dsimp [E]; linarith) hz' (norm_nonneg _) hE.le
        _ = r := mul_div_cancel₀ r hE.ne'
    obtain ⟨p,hp,hep⟩ := hball hdist
    refine ⟨p,hp,?_⟩
    change M p+w = z
    rw [he,(show L.symm (p-v) = T.symm z from hep),T.apply_symm_apply]
  have hxR' (x : Space n) (hx : x ∈ K) : ‖M (x,u x)+w‖ ≤ D*R := by
    rw [he]
    exact (T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul (by dsimp [D]; linarith) (hxR x hx) (norm_nonneg _) hD.le)
  have hbnd := hcap hΩ hcv hu hp hm M w o c a b d hball' hq₀ hK hKΩ hQ hQK hs hqK hqQ
    (fun x hx j => (le_trans (by simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (p := (2:ℝ≥0∞)) ((M (x,u x)+w).1) j))
      ((norm_fst_le _).trans (hxR' x hx))))
    (fun x hx => by simpa only [Real.norm_eq_abs] using (norm_snd_le _).trans (hxR' x hx))
  have hlin : (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
      (‖targetGraphConormal u L x‖ * graphInverseMetric u a b d x))) ≤
      ENNReal.ofReal D * (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
        (‖affineGraphConormal u M x‖ * graphInverseMetric u a b d x))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' hQ
    intro x hx
    rw [← ENNReal.ofReal_mul hD.le]
    apply ENNReal.ofReal_le_ofReal
    have hA : 0 ≤ affineAreaDensity u x := Real.rpow_nonneg (hp x (hKΩ (hQK hx))).det_pos.le _
    have hV := graphInverseMetric_nonneg (hp x (hKΩ (hQK hx))) a b d
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (targetGraphConormal_norm_le u L T x) hV) hA
    change _ ≤ D * _
    nlinarith only [hh]
  calc
    _ ≤ ENNReal.ofReal (Real.rpow |M.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))) *
        (ENNReal.ofReal D * (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖affineGraphConormal u M x‖ * graphInverseMetric u a b d x)))) := mul_le_mul_right hlin _
    _ = ENNReal.ofReal D * (ENNReal.ofReal (Real.rpow |M.toContinuousLinearMap.det|
        ((n:ℝ)/((n:ℝ)+2))) * (∫⁻ x in Q, ENNReal.ofReal (affineAreaDensity u x *
          (‖affineGraphConormal u M x‖ * graphInverseMetric u a b d x)))) := by ac_rfl
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal C := mul_le_mul_right hbnd _
    _ = ENNReal.ofReal (D*C) := (ENNReal.ofReal_mul hD.le).symm

end AffineBernstein
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound_oai.{u_1} := @OAI.AffineBernstein.affineMaximal_uniform_target_cap_lintegral_bound_oai.{u_1}
