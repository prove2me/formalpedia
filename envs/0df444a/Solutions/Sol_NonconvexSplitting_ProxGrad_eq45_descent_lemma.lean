-- Prove2me | solution 1 for NonconvexSplitting.ProxGrad.eq45_descent_lemma
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:13:38.759857+00:00
-- url     : https://prove2.me/submissions/de71f042-3760-4e91-a72a-73525d84a198

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
import Definitions.Def_NonconvexSplitting_ProxGrad_HessianSandwich
open scoped RealInnerProductSpace
open NonconvexSplitting.ProxGrad

private theorem grad_diff {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
    (hfder.differentiable (by norm_num))

private theorem descent_local {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ) (ℓ : ℝ)
    (hh : ContDiff ℝ 2 h) (hq : ContDiff ℝ 2 q) (hℓ : 0 < ℓ) (h44 : HessianSandwich h q ℓ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    h v + q v ≤ h u + q u + ⟪gradient h u + gradient q u, v-u⟫ + ℓ/2*‖v-u‖^2 := by
  let d := v-u
  let g : ℝ → ℝ := fun t => h (u+t • d)+q (u+t • d)-ℓ/2*t^2*‖d‖^2
  let g' : ℝ → ℝ := fun t => ⟪gradient h (u+t • d)+gradient q (u+t • d),d⟫-ℓ*t*‖d‖^2
  have hdh : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hdq : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u+s • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add u
  have hg : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have hc1 := (hdh (u+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    have hc2 := (hdq (u+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [← inner_gradient_left] at hc1 hc2
    convert! (hc1.add hc2).sub (((hasDerivAt_id t).pow 2).const_mul (ℓ/2) |>.mul_const (‖d‖^2)) using 1 <;>
      dsimp only [g,g',id_eq] <;> simp only [inner_add_left] <;> ring
  have hg' : ∀ t, HasDerivAt g'
      (⟪(hess h (u+t • d)+hess q (u+t • d)) d,d⟫-ℓ*‖d‖^2) t := by
    intro t
    have hc1 := (grad_diff h hh (u+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    have hc2 := (grad_diff q hq (u+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    convert! ((hc1.add hc2).inner ℝ (hasDerivAt_const t d)).sub
      (((hasDerivAt_id t).const_mul ℓ).mul_const (‖d‖^2)) using 1 <;> simp [g',hess]
  have hanti : Antitone g' := antitone_of_hasDerivAt_nonpos hg' (by
    intro t
    have hu := ((ContinuousLinearMap.le_def _ _).mp (h44 (u+t • d)).2).inner_nonneg_left d
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left,smul_apply,
      ContinuousLinearMap.one_apply,real_inner_smul_left,real_inner_self_eq_norm_sq] at hu
    change ⟪(hess h (u+t • d)+hess q (u+t • d)) d,d⟫-ℓ*‖d‖^2 ≤ 0
    linarith)
  have hconc : ConcaveOn ℝ Set.univ g :=
    (show Antitone (deriv g) from fun x y hxy => by
      rw [(hg x).deriv,(hg y).deriv]; exact hanti hxy).antitoneOn (interior Set.univ) |>.concaveOn_of_deriv
      convex_univ (fun t _ => (hg t).continuousAt.continuousWithinAt)
      (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
  have hh := hconc.slope_le_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0:ℝ)<1) (hg 0)
  simp [g,g',slope_def_field,d] at hh
  linarith

theorem solution {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ) (ℓ : ℝ)
    (hh : ContDiff ℝ 2 h) (hq : ContDiff ℝ 2 q) (hℓ : 0 < ℓ) (h44 : HessianSandwich h q ℓ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    h v + q v ≤ h u + q u + ⟪gradient h u + gradient q u, v-u⟫ + ℓ/2*‖v-u‖^2 :=
  descent_local h q ℓ hh hq hℓ h44 u v
