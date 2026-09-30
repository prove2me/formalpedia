-- Prove2me | solution 1 for NonconvexSplitting.ProxGrad.summed_decrease
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:20:56.641586+00:00
-- url     : https://prove2.me/submissions/893137b9-c83e-4d0a-86b8-db3a2c659df8

import Definitions.Def_NonconvexSplitting_ProxGrad_IsProxGradSeq
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

private theorem convex_gradient {n : ℕ} (q : EuclideanSpace ℝ (Fin n) → ℝ)
    (hq : Differentiable ℝ q) (hc : ConvexOn ℝ Set.univ q) (u v : EuclideanSpace ℝ (Fin n)) :
    q u+⟪gradient q u,v-u⟫ ≤ q v := by
  have hline : HasDerivAt (fun t : ℝ => u+t • (v-u)) (v-u) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (v-u)).const_add u
  have hd := (hq (u+(0:ℝ) • (v-u))).hasFDerivAt.comp_hasDerivAt (0:ℝ) hline
  simp only [zero_smul,add_zero] at hd
  rw [← inner_gradient_left] at hd
  have hc' : ConvexOn ℝ Set.univ (fun t : ℝ => q (u+t • (v-u))) := by
    simpa [Function.comp_def,AffineMap.lineMap_apply_module',add_comm] using hc.comp_affineMap (AffineMap.lineMap (k := ℝ) u v)
  have hh := hc'.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num : (0:ℝ)<1) hd
  simpa [slope_def_field,le_sub_iff_add_le,add_comm] using hh

private theorem prox_finite {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) (β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hp : IsProperFn P) (hx : IsProxGradSeq h P β x) (t : ℕ) : P (x (t+1)) ≠ ⊤ := by
  obtain ⟨z,hz⟩ := hp.2
  have hh := hx t z
  rw [← EReal.coe_toReal hz (hp.1 z)] at hh
  intro he
  simp [he,← EReal.coe_add] at hh

private theorem decrease_local {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) (ℓ β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hSA : StandingAssumptions h P) (hq : ContDiff ℝ 2 q) (hqc : ConvexOn ℝ Set.univ q)
    (hℓ : 0 < ℓ) (h44 : HessianSandwich h q ℓ) (hβ : 0 < β)
    (hx : IsProxGradSeq h P β x) (t : ℕ) :
    (h (x (t+1)) : EReal)+P (x (t+1)) ≤ (h (x t) : EReal)+P (x t)+
      (((ℓ/2-1/(2*β))*‖x (t+1)-x t‖^2 : ℝ) : EReal) := by
  by_cases ht : P (x t)=⊤
  · simp only [ht,EReal.coe_add_top,EReal.top_add_coe,le_top]
  have ht' := prox_finite h P β x hSA.P_proper hx t
  have hpr := hx t (x t)
  simp only [sub_self,inner_zero_right,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero,
    EReal.coe_zero,zero_add] at hpr
  rw [← EReal.coe_toReal ht (hSA.P_proper.1 (x t)),← EReal.coe_toReal ht' (hSA.P_proper.1 (x (t+1)))] at hpr ⊢
  simp only [← EReal.coe_add,EReal.coe_le_coe_iff] at hpr ⊢
  have hd := descent_local h q ℓ hSA.h_contDiff hq hℓ h44 (x t) (x (t+1))
  have hc := convex_gradient q (hq.differentiable (by norm_num)) hqc (x t) (x (t+1))
  rw [inner_add_left] at hd
  linarith

private theorem summed_local {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) (ℓ β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hSA : StandingAssumptions h P) (hq : ContDiff ℝ 2 q) (hqc : ConvexOn ℝ Set.univ q)
    (hℓ : 0 < ℓ) (h44 : HessianSandwich h q ℓ) (hβ : 0 < β)
    (hx : IsProxGradSeq h P β x) (N : ℕ) :
    (((1/(2*β)-ℓ/2)*∑ t ∈ Finset.range N,‖x (t+1)-x t‖^2 : ℝ) : EReal)+
      (h (x N) : EReal)+P (x N) ≤ (h (x 0) : EReal)+P (x 0) := by
  by_cases h0 : P (x 0)=⊤
  · simp only [h0,EReal.coe_add_top,le_top]
  have hfin : ∀ t,P (x t) ≠ ⊤ := by
    intro t
    cases t with
    | zero => exact h0
    | succ t => exact prox_finite h P β x hSA.P_proper hx t
  have hd : ∀ t,h (x (t+1))+(P (x (t+1))).toReal ≤
      h (x t)+(P (x t)).toReal+(ℓ/2-1/(2*β))*‖x (t+1)-x t‖^2 := by
    intro t
    have hh := decrease_local h q P ℓ β x hSA hq hqc hℓ h44 hβ hx t
    rw [← EReal.coe_toReal (hfin t) (hSA.P_proper.1 (x t)),
      ← EReal.coe_toReal (hfin (t+1)) (hSA.P_proper.1 (x (t+1)))] at hh
    simpa only [← EReal.coe_add,EReal.coe_le_coe_iff] using hh
  rw [← EReal.coe_toReal (hfin N) (hSA.P_proper.1 (x N)),
    ← EReal.coe_toReal (hfin 0) (hSA.P_proper.1 (x 0))]
  simp only [← EReal.coe_add,EReal.coe_le_coe_iff]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hh := hd N
    nlinarith

theorem solution {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin n) → EReal) (ℓ β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hSA : StandingAssumptions h P) (hq : ContDiff ℝ 2 q) (hq_convex : ConvexOn ℝ Set.univ q)
    (hℓ : 0 < ℓ) (h44 : HessianSandwich h q ℓ) (hβ : 0 < β)
    (hx : IsProxGradSeq h P β x) (N : ℕ) (hN : 1 < N) :
    (((1 / (2 * β) - ℓ / 2) * ∑ t ∈ Finset.range N, ‖x (t + 1) - x t‖ ^ 2 : ℝ) : EReal) +
        ((h (x N) : ℝ) : EReal) + P (x N) ≤
      ((h (x 0) : ℝ) : EReal) + P (x 0) := by
  exact summed_local h q P ℓ β x hSA hq hq_convex hℓ h44 hβ hx N
