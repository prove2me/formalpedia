-- Prove2me | solution 1 for OAI.AffineBernstein.complete_affineMaximal_positive_cap_area
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:15:04.742591+00:00
-- url     : https://prove2.me/submissions/ac5de6ce-355c-4fe4-9f45-fbbe01bda7a4

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
-- module Solutions.OAIQ22_AB.AffineBernstein_CapGeometry
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
open scoped Topology

/-- A bounded cap quantitatively separates a unit recession direction from
its horizontal hyperplane. This is the ray argument in bounds.tex:45–59. -/
theorem cap_recession_component_lower {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D : Set E} (ell : E →L[ℝ] ℝ) {b R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hcap : ∀ x ∈ D, ell x ≤ b → ‖x‖ ≤ R)
    {o e : E} (ho : o ∈ D) (hgap : ell o ≤ b-ε) (he : ‖e‖ = 1)
    (hrec : ∀ t : ℝ, 0 ≤ t → o+t • e ∈ D) :
    ε/(2*R+1) < ell e := by
  have hT : 0 < 2*R+1 := by positivity
  have hoR : ‖o‖ ≤ R := hcap o ho (by linarith)
  by_contra hn
  have hle : (2*R+1)*ell e ≤ ε := by
    simpa only [mul_comm] using ((le_div_iff₀ hT).mp (not_lt.mp hn))
  have hptop : ell (o+(2*R+1) • e) ≤ b := by
    simp only [map_add,map_smul,smul_eq_mul]
    linarith
  have hpR := hcap (o+(2*R+1) • e) (hrec _ hT.le) hptop
  have htri := norm_sub_le (o+(2*R+1) • e) o
  have hnorm : ‖(o+(2*R+1) • e)-o‖ = 2*R+1 := by
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hT,he,mul_one]
  rw [hnorm] at htri
  linarith

/-- The normalized vertical has uniformly bounded norm. -/
theorem cap_normalized_vertical_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D : Set E} (ell : E →L[ℝ] ℝ) {b R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hcap : ∀ x ∈ D, ell x ≤ b → ‖x‖ ≤ R)
    {o e : E} (ho : o ∈ D) (hgap : ell o ≤ b-ε) (he : ‖e‖ = 1)
    (hrec : ∀ t : ℝ, 0 ≤ t → o+t • e ∈ D) :
    0 < ell e ∧ ell ((ell e)⁻¹ • e) = 1 ∧
      ‖(ell e)⁻¹ • e‖ ≤ (2*R+1)/ε := by
  have hl := cap_recession_component_lower ell hR hε hcap ho hgap he hrec
  have hT : 0 < 2*R+1 := by positivity
  have hp : 0 < ell e := (div_pos hε hT).trans hl
  refine ⟨hp,by simp [hp.ne'],?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),he,mul_one]
  apply (le_div_iff₀ hε).mpr
  have hle : ε ≤ ell e*(2*R+1) := ((div_lt_iff₀ hT).mp hl).le
  have hi := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hp.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hi

/-- Compactness of a closed graph sublevel follows from compactness of the
entire epigraph cap, without a boundary regularity hypothesis. -/
lemma isCompact_graph_sublevel_of_cap {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {b : ℝ}
    (hK : IsCompact {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2 ∧ p.2 ≤ b}) :
    IsCompact {x | x ∈ Ω ∧ u x ≤ b} := by
  have he : Prod.fst '' {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2 ∧ p.2 ≤ b} =
      {x | x ∈ Ω ∧ u x ≤ b} := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨hp.1,hp.2.1.trans hp.2.2⟩
    · intro hx
      exact ⟨(x,u x),⟨hx.1,le_rfl,hx.2⟩,rfl⟩
  rw [← he]
  exact hK.image continuous_fst

/-- A cap radius bounds distances to the center in its base. -/
lemma graph_cap_radius_bound {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {b R : ℝ} {c : Space n} (hc : ‖c‖ ≤ R)
    (hcap : ∀ p : Space n × ℝ, p.1 ∈ Ω → u p.1 ≤ p.2 → p.2 ≤ b → ‖p‖ ≤ R) :
    ∀ x, x ∈ Ω → u x < b → ‖x-c‖ ≤ 2*R := by
  intro x hx hxb
  have hp := hcap (x,u x) hx le_rfl hxb.le
  have hxR : ‖x‖ ≤ R := (norm_fst_le (x,u x)).trans hp
  linarith [norm_sub_le x c]

end AffineBernstein
end

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

/-- Weighted arithmetic-geometric mean for the eigenvalues, with the unused
weight placed at 1. This is the determinant-power supporting inequality at I. -/
theorem det_rpow_le_one_add_trace {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ) (hnδ : (n : ℝ) * δ ≤ 1) :
    H.det ^ δ ≤ 1 + δ * (H.trace - n) := by
  let w : Option (Fin n) → ℝ := fun i => i.elim (1 - (n : ℝ) * δ) (fun _ => δ)
  let z : Option (Fin n) → ℝ := fun i => i.elim 1 hH.isHermitian.eigenvalues
  have hw : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i hi
    cases i with
    | none => exact sub_nonneg.mpr hnδ
    | some i => exact hδ
  have hsum : (∑ i, w i) = 1 := by
    simp [w, Fintype.sum_option]
  have hz : ∀ i ∈ Finset.univ, 0 ≤ z i := by
    intro i hi
    cases i with
    | none => exact zero_le_one
    | some i => exact hH.eigenvalues_nonneg i
  have hg := Real.geom_mean_le_arith_mean_weighted Finset.univ w z hw hsum hz
  simp only [Fintype.prod_option, Fintype.sum_option, w, z, Option.elim_none,
    Option.elim_some, Real.one_rpow, one_mul, mul_one] at hg
  have hd : H.det = ∏ i, hH.isHermitian.eigenvalues i := by
    simpa using hH.isHermitian.det_eq_prod_eigenvalues
  have ht : H.trace = ∑ i, hH.isHermitian.eigenvalues i := by
    simpa using hH.isHermitian.trace_eq_sum_eigenvalues
  rw [Real.finsetProd_rpow _ _ (fun i hi => hH.eigenvalues_nonneg i),
    ← hd, ← Finset.mul_sum, ← ht] at hg
  linarith

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

/-- Concavity in its precise tangent form, for all exponents in [0,1/n]. -/
theorem det_rpow_tangent_inequality {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnδ : (n : ℝ) * δ ≤ 1) :
    B.det ^ δ ≤ A.det ^ δ + δ * A.det ^ δ * (A⁻¹ * (B - A)).trace := by
  obtain ⟨C, hC, hCd, hCt⟩ := exists_normalized_posSemidef hA hB
  have hscalar := det_rpow_le_one_add_trace hC hδ hnδ
  rw [hCd, hCt] at hscalar
  have hpos : 0 < A.det ^ δ := Real.rpow_pos_of_pos hA.det_pos δ
  have htrace : (A⁻¹ * (B - A)).trace = (A⁻¹ * B).trace - n := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos))]
    simp
  calc
    B.det ^ δ = A.det ^ δ * (B.det / A.det) ^ δ := by
      rw [Real.div_rpow hB.det_nonneg hA.det_pos.le]
      field_simp
    _ ≤ A.det ^ δ * (1 + δ * ((A⁻¹ * B).trace - n)) :=
      mul_le_mul_of_nonneg_left hscalar hpos.le
    _ = _ := by rw [htrace]; ring

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

theorem matrix_trace_pair {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm) : (A * B).trace = ∑ i, ∑ j, A i j * B i j := by
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ j, A i j * B j i) = ∑ j, A i j * B i j
  apply Finset.sum_congr rfl
  intro j hj
  rw [hB.apply j i]

/-- The actual determinant density obeys its supporting-hyperplane inequality. -/
theorem affineArea_tangent_inequality {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u η : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hη : ContDiffOn ℝ ∞ η Ω)
    {x : Space n} (hx : x ∈ Ω) (hpos : (hessian u x).PosDef)
    (hpert : (hessian (fun y => u y + η y) x).PosSemidef) :
    affineAreaDensity (fun y => u y + η y) x - affineAreaDensity u x ≤
      (1 / ((n : ℝ) + 2)) * (affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hnd : (n : ℝ) * (1 / ((n : ℝ) + 2)) ≤ 1 := by
    rw [mul_one_div, div_le_one hn]
    linarith
  have hp := det_rpow_tangent_inequality hpos hpert (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2)) hnd
  have he : hessian (fun y => u y + η y) x - hessian u x = hessian η x := by
    rw [hessian_add_on hΩ hu hη hx]
    abel
  rw [he, matrix_trace_pair _ _ (hessian_isSymm (hη.contDiffAt (hΩ.mem_nhds hx)))] at hp
  change _ - _ ≤ _ * (_ * _)
  unfold affineAreaDensity
  simp only [Real.rpow_eq_pow]
  nlinarith [hp]

/-- Density differences for a compactly supported perturbation really are
integrable, although each area on an unbounded domain could be infinite. -/
theorem integrableOn_affineArea_difference {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω)
    (hpert : ∀ y ∈ Ω, (hessian (fun z => u z + η z) y).PosDef) :
    IntegrableOn (fun x => affineAreaDensity (fun y => u y + η y) x - affineAreaDensity u x) Ω := by
  apply Integrable.integrableOn
  apply integrable_of_support_subset_compact hηc.isCompact
  · intro x hx
    by_contra hn
    have he : (fun y => u y + η y) =ᶠ[nhds x] u := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, add_zero]
    exact hx (by
      change affineAreaDensity (fun y => u y + η y) x - affineAreaDensity u x = 0
      unfold affineAreaDensity
      rw [hessian_eq_of_eventuallyEq he]
      exact sub_self _)
  · intro x hx
    have hux := hu.contDiffAt (hΩ.mem_nhds (hηΩ hx))
    exact ((contDiffAt_affineAreaDensity (hux.add hη.contDiffAt) (hpert x (hηΩ hx))).sub
      (contDiffAt_affineAreaDensity hux (hpos x (hηΩ hx)))).continuousAt.continuousWithinAt

/-- Local maximization of graph affine area, deduced from the PDE rather than
assumed as stability. -/
theorem affineMaximal_local_area_maximization {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω)
    (hpert : ∀ y ∈ Ω, (hessian (fun z => u z + η z) y).PosDef) :
    (∫ x in Ω, affineAreaDensity (fun y => u y + η y) x - affineAreaDensity u x) ≤ 0 := by
  have hi := integrableOn_affineArea_difference hΩ hu hpos η hη hηc hηΩ hpert
  have hv := integrableOn_area_variation hΩ hu hpos η hη hηc hηΩ
  calc
    _ ≤ ∫ x in Ω, (1 / ((n : ℝ) + 2)) * (affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) := by
      apply integral_mono_ae hi (hv.const_mul _)
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      exact affineArea_tangent_inequality hΩ hu hη.contDiffOn hx (hpos x hx) (hpert x hx).posSemidef
    _ = 0 := by
      rw [integral_const_mul, affineMaximal_area_stationarity hΩ hu hpos hmax η hη hηc hηΩ, mul_zero]

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

/-- The trace contraction is invariant under simultaneous congruence, with the
exact scalar ratio. This is the algebra behind covariance of the affine PDE. -/
theorem trace_inverse_congruence {n : ℕ} {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c)
    (K : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ((c • (B.transpose * H * B))⁻¹ * (t • (B.transpose * K * B))).trace =
    (c⁻¹ * t) * (H⁻¹ * K).trace := by
  let : Invertible c := invertibleOfNonzero (ne_of_gt hc)
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBt : IsUnit B.transpose.det := by simpa using hBu
  have hPu : IsUnit (B.transpose * H * B).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hB (ne_of_gt hH.det_pos)) hB
  rw [Matrix.inv_smul _ c hPu, invOf_eq_inv, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  suffices hs : (((B.transpose * H * B)⁻¹) * (B.transpose * K * B)).trace =
      (H⁻¹ * K).trace by rw [hs]; ring
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have he : (B⁻¹ * (H⁻¹ * B.transpose⁻¹)) * (B.transpose * K * B) =
      B⁻¹ * (H⁻¹ * K) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B.transpose⁻¹ B.transpose, Matrix.nonsing_inv_mul _ hBt, one_mul]
  rw [he, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hBu, one_mul]

/-- The classical PDE is equivalent to the inverse-Hessian trace formulation
wherever its coefficients are the actual positive-definite Hessian. -/
theorem affineMaximalOn_iff_trace {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) :
    AffineMaximalOn Ω u ↔ ∀ x ∈ Ω,
      ((hessian u x)⁻¹ * hessian (affineWeight u) x).trace = 0 := by
  apply forall₂_congr
  intro x hx
  have hw := hessian_isSymm (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hx)) (hpos x hx))
  rw [matrix_trace_pair _ _ hw]
  change (∑ i, ∑ j, (hessian u x).det * (hessian u x)⁻¹ i j * hessian (affineWeight u) x i j) = 0 ↔ _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  exact mul_eq_zero_iff_left (ne_of_gt (hpos x hx).det_pos)

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

/-- The actual determinant weight transforms by its exact positive constant. -/
theorem affineWeight_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    affineWeight (affineGraphPullback u B d a c e) x =
      Real.rpow (c ^ n * B.det ^ 2) (-(((n : ℝ) + 1) / ((n : ℝ) + 2))) *
        affineWeight u (affineBaseMap B d x) := by
  unfold affineWeight
  rw [hessian_affineGraphPullback hΩ hu B d a c e hx, det_affine_congruence]
  exact Real.mul_rpow (mul_nonneg (pow_nonneg hc.le _) (sq_pos_of_ne_zero hB).le)
    (hpos _ hx).det_pos.le

/-- Hessians are local, including their inner derivative. -/
theorem hessian_congr_nhds {n : ℕ} {u v : Space n → ℝ} {x : Space n}
    (he : u =ᶠ[nhds x] v) : hessian u x = hessian v x := by
  ext i j
  have hd : (fun y => fderiv ℝ u y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ v y (coordinateVector n j)) :=
    he.fderiv.mono (fun _ hy => congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n j)) hy)
  exact congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n i)) hd.fderiv_eq

/-- Exact, classical affine-maximal PDE covariance for section normalization.
No transformed PDE is assumed: it follows from the original one by the actual
Hessian and determinant chain rules. -/
theorem affineMaximalOn_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ) :
    AffineMaximalOn (affineBaseMap B d ⁻¹' Ω) (affineGraphPullback u B d a c e) := by
  have hΩ' := hΩ.preimage (contDiff_affineBaseMap B d).continuous
  have hv := contDiffOn_affineGraphPullback hu B d a c e
  have hpv : ∀ x ∈ affineBaseMap B d ⁻¹' Ω,
      (hessian (affineGraphPullback u B d a c e) x).PosDef :=
    fun _ hx => posDef_hessian_affineGraphPullback hΩ hu hpos hB d a hc e hx
  apply (affineMaximalOn_iff_trace hΩ' hv hpv).mpr
  intro x hx
  let t := Real.rpow (c ^ n * B.det ^ 2) (-(((n : ℝ) + 1) / ((n : ℝ) + 2)))
  have hw : ContDiffOn ℝ ∞ (affineWeight u) Ω := by
    intro y hy
    exact (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hy)) (hpos y hy)).contDiffWithinAt
  have hwt : ContDiffOn ℝ ∞ (fun y => affineWeight u (affineBaseMap B d y))
      (affineBaseMap B d ⁻¹' Ω) :=
    hw.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  have hew : affineWeight (affineGraphPullback u B d a c e) =ᶠ[nhds x]
      (fun y => t * affineWeight u (affineBaseMap B d y)) := by
    filter_upwards [hΩ'.mem_nhds hx] with y hy
    exact affineWeight_affineGraphPullback hΩ hu hpos hB d a hc e hy
  rw [hessian_congr_nhds hew, hessian_const_mul hΩ' hwt t hx,
    hessian_comp_affine hΩ hw B d hx, hessian_affineGraphPullback hΩ hu B d a c e hx,
    trace_inverse_congruence (hpos _ hx) hB hc,
    (affineMaximalOn_iff_trace hΩ hu hpos).mp hmax _ hx, mul_zero]

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

lemma cleGraphPullback_regular {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (B : Space n ≃L[ℝ] Space n) (d : Space n) (a : Space n →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (e : ℝ) :
    IsOpen {x | B x+d ∈ Ω} ∧ ContDiffOn ℝ ∞ (cleGraphPullback u B d a c e)
      {x | B x+d ∈ Ω} ∧
    (∀ x ∈ {x | B x+d ∈ Ω}, (hessian (cleGraphPullback u B d a c e) x).PosDef) ∧
    AffineMaximalOn {x | B x+d ∈ Ω} (cleGraphPullback u B d a c e) := by
  have he : {x | B x+d ∈ Ω} = affineBaseMap (equivMatrix B) d ⁻¹' Ω := by
    ext x
    change (B x+d ∈ Ω) ↔ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (equivMatrix B) x+d ∈ Ω)
    rw [toEuclideanCLM_equivMatrix]
    rfl
  rw [cleGraphPullback_eq,he]
  exact ⟨hΩ.preimage (contDiff_affineBaseMap _ _).continuous,
    contDiffOn_affineGraphPullback hu _ _ _ _ _,
    fun x hx => posDef_hessian_affineGraphPullback hΩ hu hp (equivMatrix_det_ne B) d a hc e hx,
    affineMaximalOn_affineGraphPullback hΩ hu hp hm (equivMatrix_det_ne B) d a hc e⟩

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

lemma smoothTransition_reflect (x : ℝ) :
    Real.smoothTransition (1-x) = 1 - Real.smoothTransition x := by
  unfold Real.smoothTransition
  rw [show 1-(1-x) = x by ring]
  have h : expNegInvGlue x + expNegInvGlue (1-x) ≠ 0 :=
    (Real.smoothTransition.pos_denom x).ne'
  rw [add_comm (expNegInvGlue (1-x))]
  field_simp
  ring

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

lemma smoothPositivePart_deriv_bounds (ε t : ℝ) :
    0 ≤ deriv (smoothPositivePart ε) t ∧ deriv (smoothPositivePart ε) t ≤ 1 := by
  rw [(smoothPositivePart_hasDeriv ε t).deriv]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma smoothPositiveSlope_monotone {ε : ℝ} (hε : 0 < ε) :
    Monotone (smoothPositiveSlope ε) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

lemma smoothPositivePart_second_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ deriv (deriv (smoothPositivePart ε)) t := by
  rw [show deriv (smoothPositivePart ε) = smoothPositiveSlope ε from
    funext fun t => (smoothPositivePart_hasDeriv ε t).deriv]
  exact (smoothPositiveSlope_monotone hε).deriv_nonneg

lemma smoothPositiveSlope_zero {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ -ε) :
    smoothPositiveSlope ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma smoothPositiveSlope_one {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    smoothPositiveSlope ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

lemma smoothPositiveSlope_reflect {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    smoothPositiveSlope ε (-t) = 1 - smoothPositiveSlope ε t := by
  unfold smoothPositiveSlope
  rw [show (-t+ε)/(2*ε) = 1 - (t+ε)/(2*ε) by field_simp; ring]
  exact smoothTransition_reflect _

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

lemma smoothPositivePart_at_right {ε : ℝ} (hε : 0 < ε) :
    smoothPositivePart ε ε = ε := by
  have hc := (smoothPositiveSlope_smooth ε).continuous
  have hr : (∫ t in (-ε)..ε, smoothPositiveSlope ε (-t)) = smoothPositivePart ε ε := by
    have hh := intervalIntegral.integral_comp_sub_left (a := -ε) (b := ε)
      (smoothPositiveSlope ε) 0
    simp [smoothPositivePart]
  have he : (∫ t in (-ε)..ε, smoothPositiveSlope ε (-t)) =
      2*ε - smoothPositivePart ε ε := by
    simp_rw [smoothPositiveSlope_reflect hε]
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    simp [smoothPositivePart]
    ring
  linarith

lemma smoothPositivePart_identity {ε t : ℝ} (hε : 0 < ε) (ht : ε ≤ t) :
    smoothPositivePart ε t = t := by
  have hc := (smoothPositiveSlope_smooth ε).continuous
  have hi : (∫ s in ε..t, smoothPositiveSlope ε s) = t-ε := by
    calc
      _ = ∫ s in ε..t, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht] at hs
        exact smoothPositiveSlope_one hε hs.1
      _ = t-ε := by simp
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (a := -ε) (b := ε) (c := t) (μ := volume) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  change smoothPositivePart ε ε + _ = smoothPositivePart ε t at ha
  rw [smoothPositivePart_at_right hε, hi] at ha
  linarith

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

lemma hessian_convex_smooth_max {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u q : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (ε : ℝ) {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => u y + smoothPositivePart ε (q y-u y)) x =
      (1-deriv (smoothPositivePart ε) (q x-u x)) • hessian u x +
      deriv (smoothPositivePart ε) (q x-u x) • hessian q x +
      deriv (deriv (smoothPositivePart ε)) (q x-u x) •
        Matrix.vecMulVec (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x)
          (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x) := by
  have hs : ContDiffOn ℝ ∞ (fun y => smoothPositivePart ε (q y-u y)) Ω :=
    (smoothPositivePart_smooth ε).comp_contDiffOn (hq.sub hu)
  rw [hessian_add_on hΩ hu hs hx]
  ext i j
  have hc := second_dirDeriv_comp_scalar hΩ (hq.sub hu) (smoothPositivePart_smooth ε)
    hx (coordinateVector n j) (coordinateVector n i)
  change hessian u x i j + _ = _
  change hessian u x i j + dirDeriv (coordinateVector n i)
    (dirDeriv (coordinateVector n j) (fun y => smoothPositivePart ε (q y-u y))) x = _
  rw [hc]
  change hessian u x i j + (_ + _ * hessian (fun y => q y-u y) x i j) = _
  rw [hessian_sub_on hΩ hq hu hx]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.vecMulVec_apply]
  ring

lemma posDef_convex_combination {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : ((1-t) • A + t • B).PosDef := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    simpa using hA
  · exact Matrix.PosDef.posSemidef_add (hA.posSemidef.smul (sub_nonneg.mpr ht1)) (hB.smul hp)

lemma hessian_convex_smooth_max_posDef {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u q : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    {ε : ℝ} (hε : 0 < ε) {x : Space n} (hx : x ∈ Ω)
    (hpu : (hessian u x).PosDef) (hpq : (hessian q x).PosDef) :
    (hessian (fun y => u y + smoothPositivePart ε (q y-u y)) x).PosDef := by
  rw [hessian_convex_smooth_max hΩ hu hq ε hx]
  have hb := smoothPositivePart_deriv_bounds ε (q x-u x)
  have hr : (Matrix.vecMulVec
      (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x)
      (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x)).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star
      (fun i => dirDeriv (coordinateVector n i) (fun y => q y-u y) x)
  exact (posDef_convex_combination hpu hpq hb.1 hb.2).add_posSemidef
    (hr.smul (smoothPositivePart_second_nonneg hε _))

lemma capQuadratic_smooth {n : ℕ} (c : Space n) (b α : ℝ) :
    ContDiff ℝ ∞ (capQuadratic c b α) := by
  unfold capQuadratic
  exact contDiff_const.add (contDiff_const.mul ((contDiff_norm_sq ℝ : ContDiff ℝ ∞ (fun y : Space n => ‖y‖^2)).comp
    (contDiff_id.sub contDiff_const)))

lemma dirDeriv_capQuadratic {n : ℕ} (c : Space n) (b α : ℝ) (x v : Space n) :
    dirDeriv v (capQuadratic c b α) x = 2*α*inner ℝ (x-c) v := by
  have hd := ((((hasFDerivAt_id x).sub_const c).norm_sq).const_mul α).const_add b
  change fderiv ℝ (fun y => b+α*‖y-c‖^2) x v = _
  simp only [id_eq] at hd
  rw [hd.fderiv]
  simp [inner_sub_left, mul_assoc, mul_comm]

lemma hessian_capQuadratic {n : ℕ} (c : Space n) (b α : ℝ) (x : Space n) :
    hessian (capQuadratic c b α) x = (2*α) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  change dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j) (capQuadratic c b α)) x = _
  have he : dirDeriv (coordinateVector n j) (capQuadratic c b α) =
      (fun y => 2*α*(inner ℝ (coordinateVector n j) y-inner ℝ (coordinateVector n j) c)) := by
    funext y
    rw [dirDeriv_capQuadratic, real_inner_comm, inner_sub_right]
  rw [he]
  have hd := (((innerSL ℝ (coordinateVector n j)).hasFDerivAt (x := x)).sub_const
    (inner ℝ (coordinateVector n j) c)).const_mul (2*α)
  change fderiv ℝ _ x (coordinateVector n i) = _
  have heq := congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinateVector n i)) hd.fderiv
  convert! heq using 1
  all_goals try with_reducible_and_instances rfl
  simp [coordinateVector, EuclideanSpace.inner_single_left, eq_comm]

lemma hessian_capQuadratic_posDef {n : ℕ} (c : Space n) (b : ℝ) {α : ℝ}
    (hα : 0 < α) (x : Space n) : (hessian (capQuadratic c b α) x).PosDef := by
  rw [hessian_capQuadratic]
  exact Matrix.PosDef.one.smul (by positivity)

lemma affineAreaDensity_capQuadratic {n : ℕ} (c : Space n) (b : ℝ) {α : ℝ}
    (hα : 0 < α) (x : Space n) :
    affineAreaDensity (capQuadratic c b α) x =
      Real.rpow (2*α) ((n : ℝ)/((n : ℝ)+2)) := by
  unfold affineAreaDensity
  rw [hessian_capQuadratic, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rw [← Real.rpow_natCast]
  change ((2*α)^(n : ℝ))^(1/((n : ℝ)+2)) = (2*α)^((n : ℝ)/((n : ℝ)+2))
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapPerturbation
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

lemma isOpen_graphSublevel {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) (b : ℝ) :
    IsOpen {x | x ∈ Ω ∧ u x < b} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hg := (hu.continuousAt (hΩ.mem_nhds hx.1)).preimage_mem_nhds (Iio_mem_nhds hx.2)
  exact Filter.inter_mem (hΩ.mem_nhds hx.1) hg

lemma isCompact_lower_graphSublevel {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) {b d : ℝ} (hdb : d ≤ b)
    (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b}) :
    IsCompact {x | x ∈ Ω ∧ u x ≤ d} := by
  have hc : ContinuousOn u {x | x ∈ Ω ∧ u x ≤ b} := hu.mono fun _ hx => hx.1
  have hi := hc.lowerSemicontinuousOn.isCompact_inter_preimage_Iic hK d
  have he : {x | x ∈ Ω ∧ u x ≤ b} ∩ u ⁻¹' Iic d = {x | x ∈ Ω ∧ u x ≤ d} := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1,hx.2.trans hdb⟩,hx.2⟩⟩
  simpa only [he] using hi

/-- A genuine compact smooth convex-cap replacement, with no stationarity or
area conclusion assumed. -/
theorem exists_cap_perturbation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u q : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) {b ε : ℝ} (hε : 0 < ε)
    (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b})
    (hqtop : ∀ x, x ∈ Ω → u x < b → q x ≤ b-2*ε)
    (hqp : ∀ x, x ∈ Ω → u x < b → (hessian q x).PosDef) :
    ∃ η : Space n → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ {x | x ∈ Ω ∧ u x < b} ∧
      (∀ x ∈ Ω, (hessian (fun y => u y+η y) x).PosDef) ∧
      ∀ x, x ∈ Ω → u x < b → ε ≤ q x-u x → u x+η x = q x := by
  let E : Set (Space n) := {x | x ∈ Ω ∧ u x < b}
  let K : Set (Space n) := {x | x ∈ Ω ∧ u x ≤ b-ε}
  let η := E.indicator (fun x => smoothPositivePart ε (q x-u x))
  have hE : IsOpen E := isOpen_graphSublevel hΩ hu.continuousOn b
  have hKE : K ⊆ E := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩
  have hKc : IsCompact K := isCompact_lower_graphSublevel hu.continuousOn (by linarith) hK
  have hEΩ : E ⊆ Ω := fun _ hx => hx.1
  have hsm : ContDiffOn ℝ ∞ (fun x => smoothPositivePart ε (q x-u x)) E :=
    (smoothPositivePart_smooth ε).comp_contDiffOn ((hq.sub hu).mono hEΩ)
  have hzero : ∀ x ∈ E, x ∉ K → smoothPositivePart ε (q x-u x) = 0 := by
    intro x hx hxn
    have hl : b-ε < u x := lt_of_not_ge (fun hl => hxn ⟨hx.1,hl⟩)
    exact smoothPositivePart_zero hε (by linarith [hqtop x hx.1 hx.2])
  obtain ⟨hη,hηc,hηK⟩ := contDiff_indicator_of_compact hE hKc hKE hsm hzero
  change ContDiff ℝ ∞ η at hη
  change HasCompactSupport η at hηc
  change tsupport η ⊆ K at hηK
  have hηE := hηK.trans hKE
  refine ⟨η,hη,hηc,hηE,?_,?_⟩
  · intro x hx
    by_cases hxE : x ∈ E
    · have he : (fun y => u y+η y) =ᶠ[𝓝 x]
          (fun y => u y+smoothPositivePart ε (q y-u y)) := by
        filter_upwards [hE.mem_nhds hxE] with y hy
        simp only [η, Set.indicator_of_mem hy]
      rw [hessian_eq_of_eventuallyEq he]
      exact hessian_convex_smooth_max_posDef hΩ hu hq hε hx (hp x hx) (hqp x hx hxE.2)
    · have hn : x ∉ tsupport η := fun hh => hxE (hηE hh)
      have he : (fun y => u y+η y) =ᶠ[𝓝 x] u := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
        simp only [Pi.zero_apply] at hy
        simp only [hy,add_zero]
      rw [hessian_eq_of_eventuallyEq he]
      exact hp x hx
  · intro x hx hxb hbar
    have hxE : x ∈ E := ⟨hx,hxb⟩
    simp only [η, Set.indicator_of_mem hxE, smoothPositivePart_identity hε hbar]
    ring

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

lemma triangularGraphFunction_image {n : ℕ} (u : Space n → ℝ)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcn : c ≠ 0) (v : Space n × ℝ) (p : Space n × ℝ) :
    triangularGraphFunction u M hc hcn v (M p+v).1 =
      triangularLinearHeight M p.1+c*u p.1+v.2 := by
  rw [triangularGraphFunction_eval]
  have he : (triangularBaseEquiv M hc hcn).symm ((M p+v).1-v.1) = p.1 := by
    change (triangularBaseEquiv M hc hcn).symm ((M p).1+v.1-v.1) = _
    rw [add_sub_cancel_right,triangular_fst M hc]
    exact (triangularBaseEquiv M hc hcn).symm_apply_apply p.1
  rw [he]

lemma triangularGraph_regular {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) :
    let Ω' := {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω}
    let g := triangularGraphFunction u M hc hcp.ne' v
    IsOpen Ω' ∧ ContDiffOn ℝ ∞ g Ω' ∧
      (∀ y ∈ Ω', (hessian g y).PosDef) ∧ AffineMaximalOn Ω' g := by
  dsimp only
  unfold triangularGraphFunction
  simpa only [map_sub,sub_eq_add_neg,map_add,map_neg] using
    cleGraphPullback_regular hΩ hu hp hm (triangularBaseEquiv M hc hcp.ne').symm
      (-((triangularBaseEquiv M hc hcp.ne').symm v.1))
      ((triangularLinearHeight M).comp (triangularBaseEquiv M hc hcp.ne').symm.toContinuousLinearMap)
      hcp (v.2-((triangularLinearHeight M).comp
        (triangularBaseEquiv M hc hcp.ne').symm.toContinuousLinearMap) v.1)

/-- The affine image is literally the epigraph of the derived graph; no new
solution or geometric stationary surrogate is assumed. -/
lemma triangular_sourceEpigraph_image {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) :
    (fun p => M p+v) '' sourceEpigraph Ω u =
      sourceEpigraph {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω}
        (triangularGraphFunction u M hc hcp.ne' v) := by
  have hi (p : Space n × ℝ) :
      (M p+v ∈ sourceEpigraph
        {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω}
        (triangularGraphFunction u M hc hcp.ne' v)) ↔ p ∈ sourceEpigraph Ω u := by
    have he : (triangularBaseEquiv M hc hcp.ne').symm ((M p+v).1-v.1) = p.1 := by
      change (triangularBaseEquiv M hc hcp.ne').symm ((M p).1+v.1-v.1) = _
      rw [add_sub_cancel_right,triangular_fst M hc]
      exact (triangularBaseEquiv M hc hcp.ne').symm_apply_apply p.1
    change (_ ∈ Ω ∧ _ ≤ (M p+v).2) ↔ (p.1 ∈ Ω ∧ u p.1 ≤ p.2)
    rw [he,triangularGraphFunction_image]
    have hs := triangular_snd M hc p.1 p.2
    change (p.1 ∈ Ω ∧ triangularLinearHeight M p.1+c*u p.1+v.2 ≤ (M p).2+v.2) ↔ _
    rw [hs,triangularLinearHeight_apply,add_le_add_iff_right,add_le_add_iff_left,
      mul_le_mul_iff_right₀ hcp]
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact (hi p).mpr hp
  · intro hz
    refine ⟨M.symm (z-v),?_,by simp⟩
    exact (hi _).mp (by simpa using hz)

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

/-- The true cap integral is identical in the sheared graph coordinates. -/
theorem triangular_graph_cap_area {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) (b : ℝ) :
    (∫ y in {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω ∧
        triangularGraphFunction u M hc hcp.ne' v y < b},
       affineAreaDensity (triangularGraphFunction u M hc hcp.ne' v) y) =
      affineImageCapArea Ω u M v b := by
  let P := triangularBaseEquiv M hc hcp.ne'
  let a := (triangularLinearHeight M).comp P.symm.toContinuousLinearMap
  let E : Set (Space n) := {x | x ∈ Ω ∧ (M (x,u x)+v).2 < b}
  have hE : MeasurableSet E := by
    apply IsOpen.measurableSet
    exact isOpen_graphSublevel hΩ
      (continuous_snd.comp_continuousOn
        ((M.continuous.comp_continuousOn (continuousOn_id.prodMk hu.continuousOn)).add_const v)) b
  have he (y : Space n) : (M ((P.symm y-P.symm v.1),u (P.symm y-P.symm v.1))+v).2 =
      triangularGraphFunction u M hc hcp.ne' v y := by
    rw [triangularGraphFunction_eval]
    change (M (_, _)).2+v.2 = _
    rw [triangular_snd M hc,map_sub]
    rfl
  have hset : {y | P.symm y+(-P.symm v.1) ∈ E} =
      {y | P.symm (y-v.1) ∈ Ω ∧ triangularGraphFunction u M hc hcp.ne' v y < b} := by
    ext y
    simp only [E,mem_ofPred_eq,sub_eq_add_neg,map_add,map_neg] at he ⊢
    rw [← he]
  have hi := affine_area_pullback_integral hΩ hu hp hE (fun x hx => hx.1)
    P.symm (-P.symm v.1) a hcp (v.2-a v.1)
  change |(equivMatrix P.symm).det| * (∫ y in {y | P.symm y+(-P.symm v.1) ∈ E},
      affineAreaDensity (triangularGraphFunction u M hc hcp.ne' v) y) = _ at hi
  rw [hset,triangular_area_scaling M hc hcp] at hi
  apply mul_left_cancel₀ (abs_pos.mpr (equivMatrix_det_ne P.symm)).ne'
  exact hi.trans (by simp only [affineImageCapArea,E,P,mul_assoc])

lemma affineImageCapArea_shear {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) (b : ℝ)
    (p : Space n) :
    affineImageCapArea Ω u (L.trans (verticalShear p)) (verticalShear p v) b =
      affineImageCapArea Ω u L v b := by
  have hd : (L.trans (verticalShear p)).toContinuousLinearMap.det = L.toContinuousLinearMap.det := by
    change LinearMap.det ((verticalShear p).toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap) = _
    rw [LinearMap.det_comp]
    change (verticalShear p).toContinuousLinearMap.det*L.toContinuousLinearMap.det = _
    rw [det_verticalShear,one_mul]
  simp only [affineImageCapArea,hd,ContinuousLinearEquiv.trans_apply,verticalShear_apply,
    Prod.snd_add]

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

section AffineCapGeometry
open Metric

lemma sourceEpigraph_vertical_ray {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {z : Space n × ℝ} (hz : z ∈ sourceEpigraph Ω u) {t : ℝ} (ht : 0 ≤ t) :
    z+t • ((0 : Space n),1) ∈ sourceEpigraph Ω u := by
  change z.1+ t • (0 : Space n) ∈ Ω ∧ u (z.1+t • (0 : Space n)) ≤ z.2+t*1
  have hz' : u z.1 ≤ z.2 := hz.2
  simpa using And.intro hz.1 (by linarith : u z.1 ≤ z.2+t)

end AffineCapGeometry
open Metric

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineCapGeometry
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

open Metric

lemma affineEpigraph_vertical_ray {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {o : Space n × ℝ} (ho : o ∈ (fun z => L z+v) '' sourceEpigraph Ω u)
    {t : ℝ} (ht : 0 ≤ t) : o+t • L ((0 : Space n),1) ∈
      (fun z => L z+v) '' sourceEpigraph Ω u := by
  obtain ⟨z,hz,rfl⟩ := ho
  refine ⟨z+t • ((0 : Space n),1),sourceEpigraph_vertical_ray hz ht,?_⟩
  dsimp only
  rw [map_add,map_smul]
  abel

lemma affineEpigraph_positive_vertical {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {b R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hcap : ∀ z ∈ (fun z => L z+v) '' sourceEpigraph Ω u, z.2 ≤ b → ‖z‖ ≤ R)
    {o : Space n × ℝ} (ho : o ∈ (fun z => L z+v) '' sourceEpigraph Ω u)
    (hgap : o.2 ≤ b-ε) :
    0 < (L (0,1)).2 ∧ ‖((L (0,1)).2)⁻¹ • (L (0,1)).1‖ ≤ (2*R+1)/ε := by
  let q : Space n × ℝ := L (0,1)
  have hq : q ≠ 0 := by
    intro hz
    have h : ((0 : Space n),(1:ℝ)) = 0 := L.injective (hz.trans (map_zero L).symm)
    have := congrArg Prod.snd h
    norm_num at this
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let e : Space n × ℝ := ‖q‖⁻¹ • q
  have he : ‖e‖ = 1 := by
    simp only [e, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hrec (t : ℝ) (ht : 0 ≤ t) : o+t • e ∈
      (fun z => L z+v) '' sourceEpigraph Ω u := by
    simpa only [e,smul_smul] using affineEpigraph_vertical_ray L v ho
      (mul_nonneg ht (inv_nonneg.mpr hn.le))
  obtain ⟨hepos,_,hebound⟩ := cap_normalized_vertical_bound
    (ContinuousLinearMap.snd ℝ (Space n) ℝ) hR hε hcap ho hgap he hrec
  change 0 < e.2 at hepos
  have hqp : 0 < q.2 := by
    have heq : e.2 = ‖q‖⁻¹*q.2 := rfl
    rw [heq] at hepos
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hepos
  have hnorm := (norm_fst_le (e.2⁻¹ • e)).trans hebound
  have heq : (e.2⁻¹ • e).1 = q.2⁻¹ • q.1 := by
    simp only [e,Prod.smul_snd,Prod.smul_fst,smul_eq_mul,mul_inv_rev,inv_inv,smul_smul]
    congr 1
    field_simp [hn.ne']
  rw [heq] at hnorm
  exact ⟨hqp,hnorm⟩

lemma norm_verticalShear_le {n : ℕ} (p : Space n) (z : Space n × ℝ) :
    ‖verticalShear p z‖ ≤ (1+‖p‖)*‖z‖ := by
  rw [verticalShear_apply,Prod.norm_def]
  apply max_le
  · calc
      _ ≤ ‖z.1‖+‖z.2 • p‖ := norm_sub_le _ _
      _ ≤ ‖z‖+‖z‖*‖p‖ := add_le_add (norm_fst_le z)
        (by rw [norm_smul]; exact mul_le_mul_of_nonneg_right (norm_snd_le z) (norm_nonneg p))
      _ = _ := by ring
  · calc
      ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
      _ ≤ (1+‖p‖)*‖z‖ := by nlinarith [norm_nonneg p,norm_nonneg z]

lemma shear_image_cap {n : ℕ} (p : Space n) (D : Set (Space n × ℝ)) (b : ℝ) :
    {z | z ∈ verticalShear p '' D ∧ z.2 ≤ b} =
      verticalShear p '' {z | z ∈ D ∧ z.2 ≤ b} := by
  ext z
  constructor
  · rintro ⟨⟨y,hy,rfl⟩,hb⟩
    exact ⟨y,⟨hy,hb⟩,rfl⟩
  · rintro ⟨y,⟨hy,hb⟩,rfl⟩
    exact ⟨⟨y,hy,rfl⟩,hb⟩

lemma shear_horizontal_ball {n : ℕ} (p : Space n) {D : Set (Space n × ℝ)}
    {o : Space n × ℝ} {r : ℝ} (hball : Metric.ball o r ⊆ D) :
    ∀ x ∈ Metric.ball (verticalShear p o).1 r,
      (x,o.2) ∈ verticalShear p '' D := by
  intro x hx
  let y : Space n × ℝ := (x+o.2 • p,o.2)
  have hy : dist y o = dist x (verticalShear p o).1 := by
    rw [Prod.dist_eq]
    simp only [y,verticalShear_apply,dist_self]
    rw [max_eq_left dist_nonneg,dist_eq_norm,dist_eq_norm]
    congr 1
    abel
  refine ⟨y,hball (by rwa [mem_ball,hy]),?_⟩
  simp [y]

lemma affine_image_after_shear {n : ℕ} (p : Space n)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) (D : Set (Space n × ℝ)) :
    (fun z => (L.trans (verticalShear p)) z+verticalShear p v) '' D =
      verticalShear p '' ((fun z => L z+v) '' D) := by
  rw [Set.image_image]
  congr 1
  funext z
  exact (map_add (verticalShear p) (L z) v).symm

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapArea
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

lemma integrableOn_affineArea_sublevel {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hv : ContDiffOn ℝ ∞ v Ω)
    (hp : ∀ x ∈ Ω, (hessian v x).PosDef) {b : ℝ}
    (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b}) :
    IntegrableOn (affineAreaDensity v) {x | x ∈ Ω ∧ u x < b} := by
  have hc : ContinuousOn (affineAreaDensity v) {x | x ∈ Ω ∧ u x ≤ b} := by
    intro x hx
    exact (contDiffAt_affineAreaDensity (hv.contDiffAt (hΩ.mem_nhds hx.1))
      (hp x hx.1)).continuousAt.continuousWithinAt
  exact (hc.integrableOn_compact hK).mono_set (fun _ hx => ⟨hx.1,hx.2.le⟩)

/-- Local weak maximization and a smooth convex replacement give the cap
comparison on its actual open base. -/
theorem affineMaximal_cap_area_comparison {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u q : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hq : ContDiffOn ℝ ∞ q Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmax : AffineMaximalOn Ω u)
    {b ε : ℝ} (hε : 0 < ε) (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b})
    (hqtop : ∀ x, x ∈ Ω → u x < b → q x ≤ b-2*ε)
    (hqp : ∀ x, x ∈ Ω → u x < b → (hessian q x).PosDef)
    {B : Set (Space n)} (hB : IsOpen B)
    (hBE : ∀ x ∈ B, x ∈ Ω ∧ u x < b ∧ ε ≤ q x-u x) :
    (∫ x in B, affineAreaDensity q x) ≤
      ∫ x in {x | x ∈ Ω ∧ u x < b}, affineAreaDensity u x := by
  let E : Set (Space n) := {x | x ∈ Ω ∧ u x < b}
  have hE : IsOpen E := isOpen_graphSublevel hΩ hu.continuousOn b
  have hEΩ : E ⊆ Ω := fun _ hx => hx.1
  obtain ⟨η,hη,hηc,hηE,hpert,heq⟩ := exists_cap_perturbation hΩ hu hq hp hε hK hqtop hqp
  let v : Space n → ℝ := fun x => u x+η x
  have hv : ContDiffOn ℝ ∞ v Ω := hu.add hη.contDiffOn
  have hiu := integrableOn_affineArea_sublevel hΩ hu hp hK
  have hiv := integrableOn_affineArea_sublevel hΩ hv hpert hK
  have hmaxi := affineMaximal_local_area_maximization hΩ hu hp hmax η hη hηc
    (hηE.trans hEΩ) hpert
  have hrestrict : (∫ x in Ω, affineAreaDensity v x-affineAreaDensity u x) =
      ∫ x in E, affineAreaDensity v x-affineAreaDensity u x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hEΩ
    intro x hx
    have hn : x ∉ tsupport η := fun hh => hx.2 (hηE hh)
    have he : v =ᶠ[𝓝 x] u := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [v,hy,add_zero]
    unfold affineAreaDensity
    rw [hessian_eq_of_eventuallyEq he,sub_self]
  change (∫ x in Ω, affineAreaDensity v x-affineAreaDensity u x) ≤ 0 at hmaxi
  rw [hrestrict,integral_sub hiv hiu] at hmaxi
  have hev : (∫ x in B, affineAreaDensity q x) = ∫ x in B, affineAreaDensity v x := by
    apply setIntegral_congr_fun hB.measurableSet
    intro x hx
    have he : v =ᶠ[𝓝 x] q := by
      filter_upwards [hB.mem_nhds hx] with y hy
      exact heq y (hBE y hy).1 (hBE y hy).2.1 (hBE y hy).2.2
    unfold affineAreaDensity
    rw [hessian_eq_of_eventuallyEq he]
  rw [hev]
  refine le_trans (setIntegral_mono_set hiv ?_ ?_) (sub_nonpos.mp hmaxi)
  · filter_upwards [ae_restrict_mem hE.measurableSet] with x hx
    exact Real.rpow_nonneg (hpert x hx.1).det_pos.le _
  · exact Filter.Eventually.of_forall fun x hx => ⟨(hBE x hx).1,(hBE x hx).2.1⟩

/-- The graph-coordinate positive cap estimate, with a quantitative uniform
constant. The original PDE, not an area lower bound, is the hypothesis. -/
theorem affineMaximal_positive_cap_area {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmax : AffineMaximalOn Ω u)
    {b ε α r : ℝ} (hε : 0 < ε) (hα : 0 < α) (_hr : 0 < r)
    (c : Space n) (hK : IsCompact {x | x ∈ Ω ∧ u x ≤ b})
    (hball : ∀ x ∈ Metric.ball c r, x ∈ Ω ∧ u x ≤ b-6*ε)
    (hradius : ∀ x, x ∈ Ω → u x < b → α*‖x-c‖^2 ≤ 2*ε) :
    volume.real (Metric.ball (0 : Space n) r) * Real.rpow (2*α) ((n : ℝ)/((n : ℝ)+2)) ≤
      ∫ x in {x | x ∈ Ω ∧ u x < b}, affineAreaDensity u x := by
  have hcomp := affineMaximal_cap_area_comparison hΩ hu
    (capQuadratic_smooth c (b-4*ε) α).contDiffOn hp hmax hε hK
    (q := capQuadratic c (b-4*ε) α) (B := Metric.ball c r) ?_ ?_ Metric.isOpen_ball ?_
  · simpa only [affineAreaDensity_capQuadratic _ _ hα, integral_const,
      measureReal_restrict_apply_univ, smul_eq_mul, Measure.addHaar_real_ball_center] using hcomp
  · intro x hx hxb
    unfold capQuadratic
    linarith [hradius x hx hxb]
  · intro x hx hxb
    exact hessian_capQuadratic_posDef c (b-4*ε) hα x
  · intro x hx
    obtain ⟨hxΩ,hxu⟩ := hball x hx
    refine ⟨hxΩ,by linarith,?_⟩
    unfold capQuadratic
    nlinarith [sq_nonneg ‖x-c‖]

lemma cap_area_constant_pos (n : ℕ) {r α : ℝ} (hr : 0 < r) (hα : 0 < α) :
    0 < volume.real (Metric.ball (0 : Space n) r) *
      Real.rpow (2*α) ((n : ℝ)/((n : ℝ)+2)) := by
  apply mul_pos
  · exact ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume _ hr))
      (ne_of_lt (measure_ball_lt_top))
  · exact Real.rpow_pos_of_pos (by positivity) _

/-- Uniform nonvanishing in uniformly bounded graph caps, without assumptions
on boundary regularity or uniform Hessian bounds. -/
theorem exists_uniform_positive_graph_cap_area (n : ℕ) {ε r R : ℝ}
    (hε : 0 < ε) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set (Space n)) (u : Space n → ℝ)
      (b : ℝ) (c : Space n), IsOpen Ω → ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      IsCompact {x | x ∈ Ω ∧ u x ≤ b} →
      (∀ x ∈ Metric.ball c r, x ∈ Ω ∧ u x ≤ b-6*ε) →
      (∀ x, x ∈ Ω → u x < b → ‖x-c‖ ≤ R) →
      C ≤ ∫ x in {x | x ∈ Ω ∧ u x < b}, affineAreaDensity u x := by
  let α : ℝ := ε/(R^2+1)
  have hd : 0 < R^2+1 := by positivity
  have ha : 0 < α := div_pos hε hd
  refine ⟨_,cap_area_constant_pos n hr ha,?_⟩
  intro Ω u b c hΩ hu hp hmax hK hball hbound
  apply affineMaximal_positive_cap_area hΩ hu hp hmax hε ha hr c hK hball
  intro x hx hxb
  have hb := hbound x hx hxb
  have hsq : ‖x-c‖^2 ≤ R^2 := by nlinarith [norm_nonneg (x-c)]
  have he : α*(R^2+1) = ε := div_mul_cancel₀ ε (ne_of_gt hd)
  have hh := mul_le_mul_of_nonneg_left hsq ha.le
  nlinarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineCapArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section AffineCapArea

/- Uniform positive area for genuine affine images of the original solution.
The only uniform geometric data are a bounded compact cap and an interior ball
strictly below its top. This joins the source ray, shear and smooth-cap arguments. -/
theorem exists_uniform_positive_affine_cap_area (n : ℕ) {ε r R : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set (Space n)) (u : Space n → ℝ)
      (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v o : Space n × ℝ) (b : ℝ),
      IsOpen Ω → ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      IsCompact {z | z ∈ (fun p => L p+v) '' sourceEpigraph Ω u ∧ z.2 ≤ b} →
      (∀ z ∈ (fun p => L p+v) '' sourceEpigraph Ω u, z.2 ≤ b → ‖z‖ ≤ R) →
      (Metric.ball o r ⊆ (fun p => L p+v) '' sourceEpigraph Ω u) →
      o.2 ≤ b-6*ε → C ≤ affineImageCapArea Ω u L v b := by
  let P : ℝ := (2*R+1)/(6*ε)
  let R' : ℝ := (1+P)*R
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨C,hC,huniform⟩ := exists_uniform_positive_graph_cap_area n (R := 2*R') hε hr
  refine ⟨C,hC,?_⟩
  intro Ω u L v o b hΩ hu hp hm hK hcap hball hgap
  let D := (fun p => L p+v) '' sourceEpigraph Ω u
  have ho : o ∈ D := hball (Metric.mem_ball_self hr)
  obtain ⟨hcpos,hpbound⟩ := affineEpigraph_positive_vertical L v hR
    (show 0 < 6*ε by positivity) hcap ho hgap
  let c := (L (0,1)).2
  let p := c⁻¹ • (L (0,1)).1
  let S := verticalShear p
  let M := L.trans S
  let w := S v
  have hMV : M (0,1) = ((0 : Space n),c) :=
    verticalShear_straightens (L (0,1)) hcpos.ne'
  let B := triangularBaseEquiv M hMV hcpos.ne'
  let Ω' := {y | B.symm (y-w.1) ∈ Ω}
  let g := triangularGraphFunction u M hMV hcpos.ne' w
  have hepi : sourceEpigraph Ω' g = S '' D := by
    rw [← triangular_sourceEpigraph_image Ω u M hMV hcpos w]
    exact affine_image_after_shear p L v (sourceEpigraph Ω u)
  obtain ⟨hΩ',hg,hpg,hmg⟩ := triangularGraph_regular hΩ hu hp hm M hMV hcpos w
  have hcapS : ∀ z ∈ sourceEpigraph Ω' g, z.2 ≤ b → ‖z‖ ≤ R' := by
    intro z hz hzb
    rw [hepi] at hz
    obtain ⟨y,hy,rfl⟩ := hz
    have hyb : y.2 ≤ b := hzb
    calc
      ‖S y‖ ≤ (1+‖p‖)*‖y‖ := norm_verticalShear_le p y
      _ ≤ (1+P)*R := mul_le_mul (by change 1+‖p‖ ≤ 1+P; linarith [hpbound])
        (hcap y hy hyb) (norm_nonneg y) (by linarith)
  have hKS : IsCompact {z | z ∈ sourceEpigraph Ω' g ∧ z.2 ≤ b} := by
    rw [hepi,shear_image_cap]
    exact hK.image S.continuous
  have hgK : IsCompact {x | x ∈ Ω' ∧ g x ≤ b} :=
    isCompact_graph_sublevel_of_cap (by simpa only [sourceEpigraph, Set.mem_ofPred_eq, and_assoc] using hKS)
  have hbase : ∀ x ∈ Metric.ball (S o).1 r, x ∈ Ω' ∧ g x ≤ b-6*ε := by
    intro x hx
    have hz := shear_horizontal_ball p hball x hx
    rw [← hepi] at hz
    exact ⟨hz.1,hz.2.trans hgap⟩
  have hocap : ‖(S o).1‖ ≤ R' := by
    apply (norm_fst_le (S o)).trans
    apply hcapS
    · rw [hepi]; exact ⟨o,ho,rfl⟩
    · change o.2 ≤ b
      linarith
  have hbound := graph_cap_radius_bound hocap
    (fun z hz hgz hzb => hcapS z ⟨hz,hgz⟩ hzb)
  have h := huniform Ω' g b (S o).1 hΩ' hg hpg hmg hgK hbase hbound
  have heq := triangular_graph_cap_area hΩ hu hp M hMV hcpos w b
  change (∫ x in {x | x ∈ Ω' ∧ g x < b}, affineAreaDensity g x) = _ at heq
  rw [heq] at h
  simpa only [M,w,S,affineImageCapArea_shear] using h

end AffineCapArea

open Filter Metric
open scoped Topology

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

open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportCoordinates
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

section SupportCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A nonzero real functional has full range. -/
theorem real_functional_surjective (ell : E →L[ℝ] ℝ) (hne : ell ≠ 0) :
    Function.Surjective ell := by
  have hx : ∃ x, ell x ≠ 0 := by
    by_contra h
    apply hne
    ext x
    simpa using not_exists.mp h x
  obtain ⟨x, hx⟩ := hx
  intro r
  refine ⟨(r / ell x) • x, ?_⟩
  simp [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]

/- A nonzero support is strictly positive at every interior point. -/

end SupportCoordinates

/- Append one real base coordinate, placing it first in Fin (k+1). -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GeneralCapCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GeneralCapCoordinates

/- A fixed genuine invertible coordinate map with the prescribed height
functional. The product max norm is retained; no artificial inner-product
instance is introduced on these coordinates. -/
lemma exists_height_coordinates {n : ℕ}
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hne : ell ≠ 0) :
    ∃ A : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ), ∀ z, (A z).2 = ell z := by
  obtain ⟨w,hw⟩ := real_functional_surjective ell hne 1
  let T := splitFunctionalEquiv ell w hw
  have hd := T.toLinearEquiv.finrank_eq
  have hk : Module.finrank ℝ ell.ker = Module.finrank ℝ (Space n) := by
    change Module.finrank ℝ (Space n × ℝ) = Module.finrank ℝ (ℝ × ell.ker) at hd
    simp only [Module.finrank_prod,Module.finrank_self] at hd
    omega
  let Q : ell.ker ≃L[ℝ] Space n := (LinearEquiv.ofFinrankEq ell.ker (Space n) hk).toContinuousLinearEquiv
  let A := (T.trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr Q)).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ (Space n))
  exact ⟨A,fun _ => rfl⟩

/- The affine-area cap for an arbitrary linear height, in the original
literal graph chart. -/

lemma affineImageCapArea_height_coordinates {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (L A : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hA : ∀ z, (A z).2 = ell z) (b : ℝ) :
    affineImageCapArea Ω u (L.trans A) (A v) b =
      Real.rpow |A.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        affineImageLinearCapArea Ω u L v ell b := by
  have hd : (L.trans A).toContinuousLinearMap.det =
      A.toContinuousLinearMap.det*L.toContinuousLinearMap.det := by
    change LinearMap.det (A.toLinearEquiv.toLinearMap.comp L.toLinearEquiv.toLinearMap) = _
    rw [LinearMap.det_comp]
    rfl
  have hz (x : Space n) : ((L.trans A) (x,u x)+A v).2 = ell (L (x,u x)+v) := by
    rw [ContinuousLinearEquiv.trans_apply,← map_add,hA]
  simp only [affineImageCapArea,affineImageLinearCapArea,hd,hz,abs_mul, Real.rpow_eq_pow]
  rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _),mul_assoc]

lemma image_height_cap {n : ℕ} (A : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hA : ∀ z, (A z).2 = ell z)
    (C : Set (Space n × ℝ)) (b : ℝ) :
    (A '' C) ∩ {z | z.2 ≤ b} = A '' (C ∩ {z | ell z ≤ b}) := by
  ext z
  constructor
  · rintro ⟨⟨y,hy,rfl⟩,hb⟩
    exact ⟨y,⟨hy,by change (A y).2 ≤ b at hb; change ell y ≤ b; rwa [hA] at hb⟩,rfl⟩
  · rintro ⟨y,⟨hy,hb⟩,rfl⟩
    exact ⟨mem_image_of_mem A hy,by change (A y).2 ≤ b; rw [hA]; exact hb⟩

end GeneralCapCoordinates

open Filter Metric
open scoped Topology

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormedInteriorLimits
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
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- Normed-space inner containment. In particular this applies to the literal
product coordinates used for the epigraph, whose norm is not a Hilbert norm. -/
omit [ProperSpace E] in
theorem normed_ball_subset_of_infDist_lt {K : Set E} (hcl : IsClosed K)
    (hcv : Convex ℝ K) (hne : K.Nonempty) (a : E) {r : ℝ} (hr : 0 < r)
    (happ : ∀ y ∈ Metric.closedBall a r, infDist y K < r/4) :
    Metric.ball a (r/4) ⊆ K := by
  intro x hx
  by_contra hxn
  obtain ⟨f,s,hsep,hfx⟩ := geometric_hahn_banach_closed_point hcv hcl hxn
  have hf : 0 < ‖f‖ := by
    apply norm_pos_iff.mpr
    intro he
    obtain ⟨z,hz⟩ := hne
    have hh := (hsep z hz).trans hfx
    simp [he] at hh
  obtain ⟨v,hv,hfv⟩ := f.exists_lt_apply_of_lt_opNorm (show ‖f‖/2 < ‖f‖ by linarith)
  obtain ⟨v,hv,hfv⟩ : ∃ v : E, ‖v‖ < 1 ∧ ‖f‖/2 < f v := by
    by_cases hh : 0 ≤ f v
    · exact ⟨v,hv,by simpa only [Real.norm_eq_abs,abs_of_nonneg hh] using hfv⟩
    · exact ⟨-v,by simpa using hv,by simpa only [map_neg,Real.norm_eq_abs,abs_of_neg (lt_of_not_ge hh)] using hfv⟩
  let y := a+r • v
  have hy : y ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    simpa only [y,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_one]
      using (mul_le_mul_of_nonneg_left hv.le hr.le)
  obtain ⟨z,hz,hyz⟩ := (infDist_lt_iff hne).mp (happ y hy)
  have hyz' : ‖y-z‖ < r/4 := by simpa only [dist_eq_norm] using hyz
  have hx' : ‖x-a‖ < r/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hfxy : f y-f x ≤ ‖f‖*‖y-z‖ := by
    have hb : f y-f z ≤ ‖f‖*‖y-z‖ := by
      rw [← map_sub]
      exact (le_abs_self _).trans (f.le_opNorm (y-z))
    linarith [hsep z hz]
  have hfxa : f x-f a ≤ ‖f‖*‖x-a‖ := by
    rw [← map_sub]
    exact (le_abs_self _).trans (f.le_opNorm (x-a))
  have hfy : f y = f a+r*f v := by simp only [y,map_add,map_smul,smul_eq_mul]
  have h1 := mul_lt_mul_of_pos_left hyz' hf
  have h2 := mul_lt_mul_of_pos_left hx' hf
  have h3 := mul_lt_mul_of_pos_left hfv hr
  nlinarith

theorem LocalDistanceConverges.eventually_normed_ball_subset
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {a : E} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ C) :
    ∀ᶠ j in atTop, Metric.ball a (r/4) ⊆ Cj j := by
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp h (Metric.closedBall a r)
    (isCompact_closedBall a r)
  have he := Metric.tendstoUniformlyOn_iff.mp hU (r/4) (by positivity)
  filter_upwards [he] with j hj
  apply normed_ball_subset_of_infDist_lt (hclj j) (hcvj j) (hnej j) a hr
  intro y hy
  have he := hj y hy
  rw [infDist_zero_of_mem (hball hy),dist_zero_left,Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at he
  exact he

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveLimitCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section PositiveLimitCap
open Filter Metric

/- Positive cap area for a local limit of genuine affine images. This is
bounds.tex, Lemma positive-cap-area, with a strict height cutoff (hence it also
bounds the closed cap whenever that area is expressed as a measure). -/
theorem positive_cap_area_of_affine_local_limit {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    (hclj : ∀ j, IsClosed ((fun p => L j p+v j) '' sourceEpigraph Ω u))
    (hcvj : ∀ j, Convex ℝ ((fun p => L j p+v j) '' sourceEpigraph Ω u))
    (hnej : ∀ j, ((fun p => L j p+v j) '' sourceEpigraph Ω u).Nonempty)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | z.2 ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : o.2 < b) :
    ∃ c > 0, ∀ᶠ j in atTop, c ≤ affineImageCapArea Ω u (L j) (v j) b := by
  let D := fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u
  obtain ⟨R,hR,hcaps⟩ := hlim.eventually_bounded_caps hC hclj hcvj hnej
    (ContinuousLinearMap.snd ℝ (Space n) ℝ) b hcapC (interior_subset ho) hob
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior o ho
  have hclosedball : Metric.closedBall o (r/2) ⊆ C :=
    (Metric.closedBall_subset_ball (by linarith)).trans (hball.trans interior_subset)
  have hballs := hlim.eventually_normed_ball_subset hclj hcvj hnej (half_pos hr) hclosedball
  let ε := (b-o.2)/6
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : o.2 ≤ b-6*ε := by dsimp [ε]; linarith
  obtain ⟨c,hc,huniform⟩ := exists_uniform_positive_affine_cap_area n (r := (r/2)/4)
    (R := R) hε (by positivity) hR.le
  refine ⟨c,hc,?_⟩
  filter_upwards [hcaps,hballs] with j hj hjball
  have hK : IsCompact {z | z ∈ D j ∧ z.2 ≤ b} := by
    exact (isCompact_iff_isClosed_bounded).mpr
      ⟨(hclj j).inter (isClosed_le continuous_snd continuous_const),
        (isBounded_ball (x := (0 : Space n × ℝ)) (r := R)).subset hj⟩
  apply huniform Ω u (L j) (v j) o b hΩ hu hp hm hK _ hjball hgap
  intro z hz hzb
  exact (show ‖z‖ < R by simpa only [Metric.mem_ball,dist_zero_right] using hj ⟨hz,hzb⟩).le

end PositiveLimitCap

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GeneralPositiveCap
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

section GeneralPositiveCap
open Filter Metric

lemma affine_image_after_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L A : E ≃L[ℝ] E) (v : E) (D : Set E) :
    (fun z => (L.trans A) z+A v) '' D = A '' ((fun z => L z+v) '' D) := by
  rw [Set.image_image]
  congr 1
  funext z
  exact (map_add A (L z) v).symm

/- The positive-cap-area lemma for every nonzero height functional, with
no orthogonality or vertical-preserving assumption on the affine images. -/
theorem positive_linear_cap_area_of_affine_local_limit {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    (hclj : ∀ j, IsClosed ((fun p => L j p+v j) '' sourceEpigraph Ω u))
    (hcvj : ∀ j, Convex ℝ ((fun p => L j p+v j) '' sourceEpigraph Ω u))
    (hnej : ∀ j, ((fun p => L j p+v j) '' sourceEpigraph Ω u).Nonempty)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hell : ell ≠ 0)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | ell z ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : ell o < b) :
    ∃ c > 0, ∀ᶠ j in atTop, c ≤ affineImageLinearCapArea Ω u (L j) (v j) ell b := by
  obtain ⟨A,hA⟩ := exists_height_coordinates ell hell
  have hset (j : ℕ) := affine_image_after_linear (L j) A (v j) (sourceEpigraph Ω u)
  have hlimA := hlim.homeomorph hC ⟨o,interior_subset ho⟩ hclj hnej A.toHomeomorph
  have hclA : IsClosed (A '' C) := A.toHomeomorph.isClosed_image.mpr hC
  have hcapA : Bornology.IsBounded ((A '' C) ∩ {z | z.2 ≤ b}) := by
    rw [image_height_cap A ell hA]
    exact hcapC.image A.toContinuousLinearMap
  have hoA : A o ∈ interior (A '' C) := by
    change A.toHomeomorph o ∈ interior (A.toHomeomorph '' C)
    rw [← A.toHomeomorph.image_interior C]
    exact mem_image_of_mem A ho
  have hclAj (j : ℕ) : IsClosed ((fun p => (L j |>.trans A) p+A (v j)) '' sourceEpigraph Ω u) := by
    rw [hset]
    exact A.toHomeomorph.isClosed_image.mpr (hclj j)
  have hcvAj (j : ℕ) : Convex ℝ ((fun p => (L j |>.trans A) p+A (v j)) '' sourceEpigraph Ω u) := by
    rw [hset]
    exact (hcvj j).linear_image A.toLinearEquiv.toLinearMap
  have hneAj (j : ℕ) : ((fun p => (L j |>.trans A) p+A (v j)) '' sourceEpigraph Ω u).Nonempty := by
    rw [hset]
    exact (hnej j).image A
  have hlimA' : LocalDistanceConverges
      (fun j => (fun p => (L j |>.trans A) p+A (v j)) '' sourceEpigraph Ω u) (A '' C) := by
    simp only [hset]
    exact hlimA
  obtain ⟨c,hc,hbound⟩ := positive_cap_area_of_affine_local_limit hΩ hu hp hm
    (fun j => (L j).trans A) (fun j => A (v j)) hclAj hcvAj hneAj hclA hlimA'
    hcapA hoA (by rwa [hA])
  let a := Real.rpow |A.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))
  have ha : 0 < a := Real.rpow_pos_of_pos (abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero) _
  refine ⟨c/a,div_pos hc ha,?_⟩
  filter_upwards [hbound] with j hj
  rw [affineImageCapArea_height_coordinates Ω u (L j) A (v j) ell hA b] at hj
  exact (div_le_iff₀ ha).mpr (by simpa only [a,mul_comm] using hj)

end GeneralPositiveCap

/- Every admissible graph path has at least the Euclidean length of its
base displacement. This uses the literal C¹-path definition of completeness. -/
/- A straight base segment has constant velocity, including its endpoints
for the closed-interval derivative used in the metric. -/
/- Length estimate on a segment on which the graph height is nondecreasing. -/
/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
/- The straight-segment estimate in its geometric form. Both possible
orientations of a monotone height are included. -/
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
theorem complete_affineMaximal_positive_cap_area_oai {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (hc : EuclideanGraphComplete Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hell : ell ≠ 0)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | ell z ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : ell o < b) :
    ∃ c > 0, ∀ᶠ j in atTop, c ≤ affineImageLinearCapArea Ω u (L j) (v j) ell b := by
  apply positive_linear_cap_area_of_affine_local_limit hΩ hu hp hm L v
    (fun index => affineSourceEpigraph_closed hΩ hne hcv hu hp hc (L index) (v index))
    (fun index => affineSourceEpigraph_convex hΩ hcv hu hp (L index) (v index))
    _ hC hlim ell hell hcapC ho hob
  intro j
  obtain ⟨x,hx⟩ := hne
  exact ⟨L j (x,u x)+v j,mem_image_of_mem _ ⟨hx,le_rfl⟩⟩

/- Positive-definiteness of the derivative makes a map injective on a convex
set, by strict monotonicity along every segment. -/

/- The actual gradient of a strictly positive-Hessian function is injective;
in particular this applies to every principal-coordinate slice in the source. -/
/- The true Euclidean gradient has Jacobian determinant equal to the
coordinate Hessian determinant, including dimension zero. -/
/- Exact change of variables for the convex gradient map. This is the
principal-minor argument used in bounds.tex; applying this result on each
coordinate slice gives the claimed integral bound for that minor. -/
/- A uniformly bounded gradient image gives a uniformly bounded Hessian
Jacobian integral. No bound on the Hessian itself is needed. -/

/- Reciprocal projective chart of the Gauss covector. In the chart where
coordinate `i` dominates the normal, its image lies in a fixed cube. -/

/- Projection to the coordinate hyperplane omitting the i-th original
base coordinate, represented in its standard n coordinates. -/

/- Holder interpolation, with weights rather than reciprocal exponents.
The endpoint masses may be infinite; no hidden integrability premise is used. -/
/- Real positive densities can be interpolated before or after `ofReal`. -/

/- A dimension/radius-only bound for the literal affine area on any measurable
part of a smooth strictly convex graph with |x_i|,|u| ≤ R. This proves the
area-in-a-ball producer without assuming a surface-area or Gauss-map theorem:
two injective coordinate projections supply its Jacobians directly. -/

/- A determinant-one-in-absolute-value coordinate change straightens any nonzero
vector upwards, with a uniform factor two bound on coordinate boxes. No Euclidean
structure is falsely assigned to the max-norm product. -/

/- Genuine affine area of every bounded measurable patch of an arbitrary
invertible affine image of the original convex graph. The constant depends
only on dimension and the physical coordinate radius, not on the affine map. -/

end AffineBernstein

end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.complete_affineMaximal_positive_cap_area_oai := @OAI.AffineBernstein.complete_affineMaximal_positive_cap_area_oai
