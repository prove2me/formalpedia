-- Prove2me | solution 1 for NonconvexSplitting.ProxGrad.P_tendsto_along_subseq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:29:39.53295+00:00
-- url     : https://prove2.me/submissions/d239d676-2b07-4826-851e-4e66ba019dbc

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

open Filter Topology
private theorem step_limit {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) (ℓ β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hSA : StandingAssumptions h P) (hq : ContDiff ℝ 2 q) (hqc : ConvexOn ℝ Set.univ q)
    (hℓ : 0 < ℓ) (h44 : HessianSandwich h q ℓ) (hβ : 0 < β) (hβℓ : β < 1/ℓ)
    (hx : IsProxGradSeq h P β x)
    (hclu : ∃ xs,∃ φ : ℕ → ℕ,StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 xs)) :
    Tendsto (fun t => ‖x (t+1)-x t‖) atTop (𝓝 0) := by
  let c := 1/(2*β)-ℓ/2
  have hc : 0 < c := by
    have hh := (lt_div_iff₀ hℓ).mp hβℓ
    dsimp [c]
    apply (mul_pos_iff_of_pos_right (show 0 < 2*β by positivity)).mp
    field_simp
    nlinarith
  have hfin : ∀ t,1 ≤ t → P (x t) ≠ ⊤ := by
    intro t ht
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    exact prox_finite h P β x hSA.P_proper hx k
  let E : ℕ → ℝ := fun t => h (x (t+1))+(P (x (t+1))).toReal
  have hstep : ∀ t, E (t+1)+c*‖x (t+1+1)-x (t+1)‖^2 ≤ E t := by
    intro t
    have hh := decrease_local h q P ℓ β x hSA hq hqc hℓ h44 hβ hx (t+1)
    rw [← EReal.coe_toReal (hfin (t+1) (by omega)) (hSA.P_proper.1 _),
      ← EReal.coe_toReal (hfin (t+1+1) (by omega)) (hSA.P_proper.1 _)] at hh
    simp only [← EReal.coe_add,EReal.coe_le_coe_iff] at hh
    dsimp [E,c]
    linarith
  have hanti : Antitone E := antitone_nat_of_succ_le (fun t => by
    have hh := hstep t
    have hp := mul_nonneg hc.le (sq_nonneg ‖x (t+1+1)-x (t+1)‖)
    linarith)
  obtain ⟨xs,φ,hφ,hlim⟩ := hclu
  obtain ⟨r,_,hr⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr (hSA.P_proper.1 xs))
  have hp : ∀ᶠ i in atTop,(r:EReal)<P (x (φ i)) := hlim.eventually (hSA.P_closed xs (r:EReal) hr)
  have hhlim : Tendsto (fun i => h (x (φ i))) atTop (𝓝 (h xs)) :=
    (hSA.h_contDiff.continuous.tendsto xs).comp hlim
  have hh : ∀ᶠ i in atTop,h xs-1 < h (x (φ i)) := (tendsto_order.mp hhlim).1 _ (by linarith)
  have hb : BddBelow (Set.range E) := by
    refine ⟨r+h xs-1,?_⟩
    rintro _ ⟨t,rfl⟩
    have hg : ∀ᶠ i in atTop,t+1 ≤ φ i := hφ.tendsto_atTop.eventually_ge_atTop (t+1)
    obtain ⟨i,hpi,hhi,hgi⟩ := (hp.and (hh.and hg)).exists
    have hfi := hfin (φ i) (by omega)
    rw [← EReal.coe_toReal hfi (hSA.P_proper.1 _),EReal.coe_lt_coe_iff] at hpi
    have hm := hanti (show t ≤ φ i-1 by omega)
    dsimp [E] at hm
    rw [show φ i-1+1=φ i by omega] at hm
    linarith
  have hElim := tendsto_atTop_ciInf hanti hb
  have hdiff : Tendsto (fun t => (E t-E (t+1))/c) atTop (𝓝 0) := by
    have hh := (hElim.sub (hElim.comp (tendsto_add_atTop_nat 1))).div_const c
    simpa using hh
  have hsq : Tendsto (fun t => ‖x (t+1+1)-x (t+1)‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun t => sq_nonneg _) (fun t => ?_) hdiff
    apply (le_div_iff₀ hc).mpr
    nlinarith [hstep t]
  have hn : Tendsto (fun t => ‖x (t+1+1)-x (t+1)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsq.sqrt
  exact (tendsto_add_atTop_iff_nat 1).mp hn

private theorem prox_values_limit {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) (β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hSA : StandingAssumptions h P) (hx : IsProxGradSeq h P β x)
    (xs : EuclideanSpace ℝ (Fin n)) (φ : ℕ → ℕ)
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 xs))
    (hdiff : Tendsto (fun i => x (φ i+1)-x (φ i)) atTop (𝓝 0)) :
    P xs ≠ ⊤ ∧ Tendsto (fun i => P (x (φ i+1))) atTop (𝓝 (P xs)) := by
  let m : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun i w =>
    ⟪gradient h (x (φ i)),w-x (φ i)⟫+1/(2*β)*‖w-x (φ i)‖^2
  let mlim : EuclideanSpace ℝ (Fin n) → ℝ := fun w =>
    ⟪gradient h xs,w-xs⟫+1/(2*β)*‖w-xs‖^2
  have hg : Tendsto (fun i => gradient h (x (φ i))) atTop (𝓝 (gradient h xs)) :=
    ((grad_diff h hSA.h_contDiff).continuous.tendsto xs).comp hlim
  have hm (w : EuclideanSpace ℝ (Fin n)) : Tendsto (fun i => m i w) atTop (𝓝 (mlim w)) := by
    have hd : Tendsto (fun i => w-x (φ i)) atTop (𝓝 (w-xs)) := tendsto_const_nhds.sub hlim
    exact (hg.inner hd).add ((hd.norm.pow 2).const_mul (1/(2*β)))
  have hmn : Tendsto (fun i => m i (x (φ i+1))) atTop (𝓝 0) := by
    have hh := (hg.inner hdiff).add ((hdiff.norm.pow 2).const_mul (1/(2*β)))
    simpa only [inner_zero_right,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] using hh
  have hnext : Tendsto (fun i => x (φ i+1)) atTop (𝓝 xs) := by
    simpa only [Function.comp_apply,sub_add_cancel,zero_add] using hdiff.add hlim
  have hupper (w : EuclideanSpace ℝ (Fin n)) (hw : P w ≠ ⊤) : ∀ i,
      P (x (φ i+1)) ≤ (((P w).toReal+m i w-m i (x (φ i+1)) : ℝ) : EReal) := by
    intro i
    have hn := prox_finite h P β x hSA.P_proper hx (φ i)
    have hh := hx (φ i) w
    rw [← EReal.coe_toReal hw (hSA.P_proper.1 w),
      ← EReal.coe_toReal hn (hSA.P_proper.1 _)] at hh
    rw [← EReal.coe_toReal hn (hSA.P_proper.1 _)]
    simp only [← EReal.coe_add,EReal.coe_le_coe_iff] at hh ⊢
    dsimp [m]
    linarith
  have huplim (w : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun i => (P w).toReal+m i w-m i (x (φ i+1))) atTop
        (𝓝 ((P w).toReal+mlim w)) := by
    simpa using (tendsto_const_nhds.add (hm w)).sub hmn
  have hfin : P xs ≠ ⊤ := by
    obtain ⟨w,hw⟩ := hSA.P_proper.2
    have hb : P xs ≤ (((P w).toReal+mlim w : ℝ) : EReal) :=
      hSA.P_closed.isClosed_epigraph.mem_of_tendsto
        (hnext.prodMk_nhds (EReal.tendsto_coe.mpr (huplim w))) (Eventually.of_forall (hupper w hw))
    intro he
    simp only [he,top_le_iff,EReal.coe_ne_top] at hb
  refine ⟨hfin,tendsto_order.mpr ⟨?_,?_⟩⟩
  · intro a ha
    exact hnext.eventually (hSA.P_closed xs a ha)
  · intro b hb
    obtain ⟨r,hr1,hr2⟩ := EReal.exists_between_coe_real hb
    have hr : (P xs).toReal < r := by
      rwa [← EReal.coe_toReal hfin (hSA.P_proper.1 xs),EReal.coe_lt_coe_iff] at hr1
    have hu : Tendsto (fun i => (P xs).toReal+m i xs-m i (x (φ i+1))) atTop (𝓝 (P xs).toReal) := by
      simpa [mlim] using huplim xs
    filter_upwards [(tendsto_order.mp hu).2 r hr] with i hi
    exact lt_of_le_of_lt (hupper xs hfin i) ((EReal.coe_lt_coe_iff.mpr hi).trans hr2)

theorem solution {n : ℕ} (h q : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin n) → EReal) (ℓ β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hSA : StandingAssumptions h P) (hq : ContDiff ℝ 2 q) (hq_convex : ConvexOn ℝ Set.univ q)
    (hℓ : 0 < ℓ) (h44 : HessianSandwich h q ℓ) (hβ : 0 < β)
    (hβℓ : β < 1 / ℓ) (hx : IsProxGradSeq h P β x)
    (xs : EuclideanSpace ℝ (Fin n)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 xs)) :
    Tendsto (fun i => P (x (φ i + 1))) atTop (𝓝 (P xs)) := by
  have hn := (step_limit h q P ℓ β x hSA hq hq_convex hℓ h44 hβ hβℓ hx ⟨xs,φ,hφ,hlim⟩).comp hφ.tendsto_atTop
  have hd : Tendsto (fun i => x (φ i+1)-x (φ i)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  exact (prox_values_limit h P β x hSA hx xs φ hlim hd).2
