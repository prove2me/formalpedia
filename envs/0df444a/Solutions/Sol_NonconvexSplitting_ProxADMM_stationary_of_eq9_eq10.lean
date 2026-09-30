-- Prove2me | solution 1 for NonconvexSplitting.ProxADMM.stationary_of_eq9_eq10
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:39:53.623983+00:00
-- url     : https://prove2.me/submissions/5ed199f0-445d-475c-9d53-9830c1842165

import Definitions.Def_NonconvexSplitting_Shared_IsStationary
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_NonconvexSplitting_Shared_IsProxADMMSeq
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic
open Filter Topology NonconvexSplitting.Shared
open scoped RealInnerProductSpace

private theorem y_finite {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin m) → EReal) (phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hp : IsProperFn P) (hseq : IsProxADMMSeq h P phi M β x y z) (t : ℕ) : P (y (t+1)) ≠ ⊤ := by
  obtain ⟨w,hw⟩:=hp.2
  have hh:=(hseq t).1 w
  unfold augLag at hh
  rw [← EReal.coe_toReal hw (hp.1 w)] at hh
  intro he
  simp [he,← EReal.coe_add] at hh

private theorem y_subgrad {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin m) → EReal) (phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hp : IsProperFn P) (hb : 0 < β) (hseq : IsProxADMMSeq h P phi M β x y z) (t : ℕ) :
    -z t+β • (M (x t)-y (t+1)) ∈ LimitingSubdiff P (y (t+1)) := by
  let a:=y (t+1)
  let b:=M (x t)
  let v:= -z t+β • (b-a)
  have hfin : P a ≠ ⊤ := y_finite h P phi M β x y z hp hseq t
  have hreg : IsRegularSubgrad P a v := by
    refine ⟨hfin,?_⟩
    intro ε he
    filter_upwards [Metric.ball_mem_nhds a (by positivity : 0 < 2*ε/β)] with w hw
    have hwn : ‖w-a‖ < 2*ε/β := by simpa [Metric.mem_ball,dist_eq_norm] using hw
    by_cases hwt : P w=⊤
    · rw [hwt];exact le_top
    have hmin:=(hseq t).1 w
    unfold augLag at hmin
    rw [← EReal.coe_toReal hfin (hp.1 a),← EReal.coe_toReal hwt (hp.1 w)] at hmin ⊢
    simp only [← EReal.coe_add,EReal.coe_le_coe_iff] at hmin ⊢
    have hquad : (-⟪z t,b-w⟫+β/2*‖b-w‖^2)-(-⟪z t,b-a⟫+β/2*‖b-a‖^2)=
        -⟪v,w-a⟫+β/2*‖w-a‖^2 := by
      have he : b-w=(b-a)-(w-a) := by abel
      rw [he,norm_sub_sq_real]
      dsimp [v]
      simp only [inner_sub_right,inner_add_left,inner_neg_left,real_inner_smul_left]
      ring
    have hrem : β/2*‖w-a‖^2 ≤ ε*‖w-a‖ := by
      have hsmall := (lt_div_iff₀ hb).mp hwn
      nlinarith [mul_nonneg (norm_nonneg (w-a)) (show 0 ≤ 2*ε-β*‖w-a‖ by linarith)]
    change h (x t)+(P a).toReal+(-⟪z t,b-a⟫+β/2*‖b-a‖^2) ≤
      h (x t)+(P w).toReal+(-⟪z t,b-w⟫+β/2*‖b-w‖^2) at hmin
    linarith
  exact ⟨hfin,(fun _ => a),(fun _ => v),tendsto_const_nhds,tendsto_const_nhds,tendsto_const_nhds,(fun _ => hreg)⟩

private theorem x_optimality {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin m) → EReal) (phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hstd : StandingAssumptions h P phi β) (hseq : IsProxADMMSeq h P phi M β x y z) (t : ℕ) :
    gradient h (x (t+1))-ContinuousLinearMap.adjoint M (z (t+1))=
      -gradient phi (x (t+1))+gradient phi (x t) := by
  let a:=x (t+1)
  let b:=x t
  let yy:=y (t+1)
  let zz:=z t
  let F:=fun w => h w-⟪zz,M w-yy⟫+β/2*‖M w-yy‖^2+phi w-phi b-⟪gradient phi b,w-b⟫
  let G:=gradient h a-ContinuousLinearMap.adjoint M zz+
    β • ContinuousLinearMap.adjoint M (M a-yy)+gradient phi a-gradient phi b
  have hfin := y_finite h P phi M β x y z hstd.P_proper hseq t
  have hmin (w : EuclideanSpace ℝ (Fin n)) : F a ≤ F w := by
    have hh:=(hseq t).2.1 w
    unfold augLag bregman at hh
    rw [← EReal.coe_toReal hfin (hstd.P_proper.1 (y (t+1)))] at hh
    simp only [← EReal.coe_add,EReal.coe_le_coe_iff] at hh
    dsimp [F,a,b,yy,zz]
    linarith
  have hzero (d : EuclideanSpace ℝ (Fin n)) : ⟪G,d⟫=0 := by
    have hl : HasDerivAt (fun q : ℝ => a+q • d) d 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add a
    have hh:=(hstd.h_contDiff.differentiable (by norm_num) (a+(0:ℝ) • d)).hasFDerivAt.comp_hasDerivAt 0 hl
    have hp:=(hstd.phi_contDiff.differentiable (by norm_num) (a+(0:ℝ) • d)).hasFDerivAt.comp_hasDerivAt 0 hl
    have hM:=M.hasFDerivAt.comp_hasDerivAt 0 hl
    rw [← inner_gradient_left] at hh hp
    simp only [zero_smul,add_zero] at hh hp hM
    have hlin:=(hasDerivAt_const 0 zz).inner ℝ (hM.sub_const yy)
    have hnorm:=(hM.sub_const yy).norm_sq.const_mul (β/2)
    have hphi:=(hasDerivAt_const 0 (gradient phi b)).inner ℝ (hl.sub_const b)
    have hd : HasDerivAt (fun q : ℝ => F (a+q • d)) ⟪G,d⟫ 0 := by
      convert! ((((hh.sub hlin).add hnorm).add hp).sub_const (phi b)).sub hphi using 1 <;>
        simp [F,G,inner_add_left,inner_sub_left,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left] <;> ring
    have hm : IsLocalMin (fun q : ℝ => F (a+q • d)) 0 := by
      apply Filter.Eventually.of_forall
      intro q
      simpa using hmin (a+q • d)
    exact hm.hasDerivAt_eq_zero hd
  have hG : G=0 := (inner_self_eq_zero.mp (hzero G))
  rw [(hseq t).2.2,map_sub,map_smul]
  dsimp [G,a,b,yy,zz] at hG
  linear_combination (norm := module) hG

private theorem optimality {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z) (t : ℕ) :
    -(z (t + 1)) - β • M (x (t + 1) - x t) ∈ LimitingSubdiff P (y (t + 1)) ∧
    gradient h (x (t + 1)) - ContinuousLinearMap.adjoint M (z (t + 1)) =
      -(gradient phi (x (t + 1))) + gradient phi (x t) ∧
    M (x (t + 1)) - y (t + 1) = (1 / β) • (z t - z (t + 1))  := by
  refine ⟨?_,x_optimality h P phi M β x y z hstd hseq t,?_⟩
  · have hh:=y_subgrad h P phi M β x y z hstd.P_proper hstd.beta_pos hseq t
    convert! hh using 1
    rw [(hseq t).2.2,map_sub]
    module
  · rw [(hseq t).2.2]
    have hb : β ≠ 0 := ne_of_gt hstd.beta_pos
    rw [sub_sub_cancel,smul_smul]
    simp [hb]

private theorem grad_diff {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
    (hfder.differentiable (by norm_num))


private theorem subdiff_robust {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : IsProperFn f) (x v : EuclideanSpace ℝ (Fin n)) (hx : f x ≠ ⊤)
    (xs vs : ℕ → EuclideanSpace ℝ (Fin n))
    (hxs : Tendsto xs atTop (𝓝 x)) (hfxs : Tendsto (fun t => f (xs t)) atTop (𝓝 (f x)))
    (hvs : Tendsto vs atTop (𝓝 v)) (hmem : ∀ t, vs t ∈ LimitingSubdiff f (xs t)) :
    v ∈ LimitingSubdiff f x := by
  let R : Set (EuclideanSpace ℝ (Fin n) × EReal × EuclideanSpace ℝ (Fin n)) :=
    {z | f z.1 = z.2.1 ∧ IsRegularSubgrad f z.1 z.2.2}
  have hC : ∀ t, (xs t,f (xs t),vs t) ∈ closure R := by
    intro t
    obtain ⟨_,ys,ws,hys,hfys,hws,hreg⟩ := hmem t
    apply mem_closure_iff_seq_limit.mpr
    exact ⟨fun k => (ys k,f (ys k),ws k),fun k => ⟨rfl,hreg k⟩,by simpa only [nhds_prod_eq] using hys.prodMk (hfys.prodMk hws)⟩
  have hcl : (x,f x,v) ∈ closure R :=
    isClosed_closure.mem_of_tendsto (by simpa only [nhds_prod_eq] using hxs.prodMk (hfxs.prodMk hvs)) (Eventually.of_forall hC)
  obtain ⟨z,hz,hzt⟩ := mem_closure_iff_seq_limit.mp hcl
  simp only [nhds_prod_eq] at hzt
  refine ⟨hx,fun t => (z t).1,fun t => (z t).2.2,hzt.fst,?_,hzt.snd.snd,?_⟩
  · have he : (fun t => f (z t).1) = (fun t => (z t).2.1) := funext fun t => (hz t).1
    rw [he]
    exact hzt.snd.fst
  · intro t
    exact (hz t).2

private theorem step_vanish_of_sum {X : Type*} [NormedAddCommGroup X]
    (u : ℕ → X) (F : ℕ → ℝ) (hF : Tendsto F atTop (𝓝 0))
    (hle : ∀ t,‖u (t+1)-u t‖^2 ≤ F t) :
    Tendsto (fun t => u (t+1)-u t) atTop (𝓝 0) := by
  have hs : Tendsto (fun t => ‖u (t+1)-u t‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun t => sq_nonneg _) hle hF
  have hh:=Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

theorem solution {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (s : ℕ → ℕ) (hs : StrictMono s) (xs : EuclideanSpace ℝ (Fin n)) (ys zs : EuclideanSpace ℝ (Fin m))
    (hconv : Tendsto (fun i => (x (s i), y (s i), z (s i))) atTop (𝓝 (xs, ys, zs)))
    (h9 : Tendsto (fun t => ‖y (t + 1) - y t‖ ^ 2 + ‖x (t + 1) - x t‖ ^ 2 + ‖z (t + 1) - z t‖ ^ 2)
      atTop (𝓝 0))
    (h10 : Tendsto (fun i => P (y (s i + 1))) atTop (𝓝 (P ys))) (h10fin : P ys ≠ ⊤) :
    (gradient h xs = ContinuousLinearMap.adjoint M zs ∧ -zs ∈ LimitingSubdiff P ys ∧ ys = M xs) ∧
    IsStationary h P M xs  := by
  simp only [nhds_prod_eq] at hconv
  have hx:=hconv.fst
  have hy:=hconv.snd.fst
  have hz:=hconv.snd.snd
  have hdx:=step_vanish_of_sum x _ h9 (fun t => by nlinarith [sq_nonneg ‖y (t+1)-y t‖,sq_nonneg ‖z (t+1)-z t‖])
  have hdy:=step_vanish_of_sum y _ h9 (fun t => by nlinarith [sq_nonneg ‖x (t+1)-x t‖,sq_nonneg ‖z (t+1)-z t‖])
  have hdz:=step_vanish_of_sum z _ h9 (fun t => by nlinarith [sq_nonneg ‖y (t+1)-y t‖,sq_nonneg ‖x (t+1)-x t‖])
  have hx1 : Tendsto (fun i => x (s i+1)) atTop (𝓝 xs) := by
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hdx.comp hs.tendsto_atTop).add hx
  have hy1 : Tendsto (fun i => y (s i+1)) atTop (𝓝 ys) := by
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hdy.comp hs.tendsto_atTop).add hy
  have hz1 : Tendsto (fun i => z (s i+1)) atTop (𝓝 zs) := by
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hdz.comp hs.tendsto_atTop).add hz
  have hgh:=(grad_diff h hstd.h_contDiff).continuous
  have hgp:=(grad_diff phi hstd.phi_contDiff).continuous
  have hegrad : gradient h xs=ContinuousLinearMap.adjoint M zs := by
    have hl:=(hgh.tendsto xs |>.comp hx1).sub ((ContinuousLinearMap.adjoint M).continuous.tendsto zs |>.comp hz1)
    have hr:=(hgp.tendsto xs |>.comp hx1).neg.add (hgp.tendsto xs |>.comp hx)
    have he : (fun i => gradient h (x (s i+1))-(ContinuousLinearMap.adjoint M) (z (s i+1)))=
        (fun i => -gradient phi (x (s i+1))+gradient phi (x (s i))) :=
      funext (fun i => (optimality h P phi M β hstd x y z hseq (s i)).2.1)
    dsimp only [Function.comp_def] at hl hr
    rw [he] at hl
    have hh:=tendsto_nhds_unique hl hr
    simp only [neg_add_cancel] at hh
    exact sub_eq_zero.mp hh
  have heym : ys=M xs := by
    have hl:=(M.continuous.tendsto xs |>.comp hx1).sub hy1
    have hr:=(hz.sub hz1).const_smul (1/β)
    have he : (fun i => M (x (s i+1))-y (s i+1))=(fun i => (1/β) • (z (s i)-z (s i+1))) :=
      funext (fun i => (optimality h P phi M β hstd x y z hseq (s i)).2.2)
    dsimp only [Function.comp_def] at hl hr
    rw [he] at hl
    have hh:=tendsto_nhds_unique hl hr
    simp only [sub_self,smul_zero] at hh
    exact (sub_eq_zero.mp hh).symm
  have hmem : -zs ∈ LimitingSubdiff P ys := by
    apply subdiff_robust P hstd.P_proper ys (-zs) h10fin (fun i => y (s i+1))
      (fun i => -z (s i+1)-β • M (x (s i+1)-x (s i))) hy1 h10
    · have hh:=hz1.neg.sub ((M.continuous.tendsto 0 |>.comp (hdx.comp hs.tendsto_atTop)).const_smul β)
      simpa only [Function.comp_def,map_zero,smul_zero,sub_zero] using hh
    · intro i
      exact (optimality h P phi M β hstd x y z hseq (s i)).1
  refine ⟨⟨hegrad,hmem,heym⟩,-zs,?_,?_⟩
  · simpa only [heym] using hmem
  · rw [map_neg,hegrad]
    module
