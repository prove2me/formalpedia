-- Prove2me | solution 1 for NonconvexSplitting.ProxADMM.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:13:17.42506+00:00
-- url     : https://prove2.me/submissions/b644e7d1-227a-4b1b-8d96-14a83d8db901

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_NonconvexSplitting_Shared_IsStationary
import Definitions.Def_NonconvexSplitting_Shared_Assumption1
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


private theorem adjoint_lower {n m : ℕ}
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (σ : ℝ)
    (hM : σ • (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) ≤ M.comp (ContinuousLinearMap.adjoint M))
    (v : EuclideanSpace ℝ (Fin m)) : σ*‖v‖^2 ≤ ‖(ContinuousLinearMap.adjoint M) v‖^2 := by
  have hh:=((ContinuousLinearMap.le_def _ _).mp hM).inner_nonneg_left v
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,inner_sub_left,
    smul_apply,one_apply_eq_self,real_inner_smul_left,real_inner_self_eq_norm_sq] at hh
  rw [← ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq] at hh
  linarith

private theorem grad_diff {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
    (hfder.differentiable (by norm_num))


private theorem hessian_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → ℝ) (hF : ContDiff ℝ 2 F) (x : E) :
    (fderiv ℝ (gradient F) x).toLinearMap.IsSymmetric := by
  have hG : Differentiable ℝ (gradient F) := by
    have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.differentiable.comp
      (hfder.differentiable (by norm_num))
  have he := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp x
    (hG x).hasFDerivAt
  change HasFDerivAt ((InnerProductSpace.toDual ℝ E) ∘ gradient F) _ x at he
  rw [toDual_comp_gradient] at he
  intro u v
  have hs := ((hF.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num)).eq u v
  rw [he.fderiv] at hs
  change ⟪fderiv ℝ (gradient F) x u,v⟫ = ⟪fderiv ℝ (gradient F) x v,u⟫ at hs
  exact hs.trans (real_inner_comm _ _)


private theorem vector_diff_bound {n : ℕ}
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hder : ∀ x,HasFDerivAt G (A x) x) (hsym : ∀ x,(A x).toLinearMap.IsSymmetric)
    (hbound : ∀ x,A x*A x ≤ Q) (u v : EuclideanSpace ℝ (Fin n)) :
    ‖G v-G u‖^2 ≤ wnormSq Q (v-u) := by
  let d:=v-u
  let q:=wnormSq Q d
  have hnorm (x : EuclideanSpace ℝ (Fin n)) : ‖A x d‖^2 ≤ q := by
    have hh:=((ContinuousLinearMap.le_def _ _).mp (hbound x)).inner_nonneg_left d
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left,mul_apply_eq_comp] at hh
    have he : ⟪A x (A x d),d⟫=‖A x d‖^2 := by
      exact (hsym x (A x d) d).trans (real_inner_self_eq_norm_sq _)
    rw [he] at hh
    change ‖A x d‖^2 ≤ ⟪d,Q d⟫
    rw [real_inner_comm]
    linarith
  have hq : 0 ≤ q := le_trans (sq_nonneg _) (hnorm u)
  have hderline (t : ℝ) : HasDerivAt (fun a : ℝ => G (u+a • d)) (A (u+t • d) d) t := by
    have hl : HasDerivAt (fun a : ℝ => u+a • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add u
    exact (hder _).comp_hasDerivAt t hl
  have hh:=norm_image_sub_le_of_norm_deriv_le_segment_01' (fun t ht => (hderline t).hasDerivWithinAt)
    (fun t ht => show ‖A (u+t • d) d‖ ≤ Real.sqrt q by
      nlinarith [hnorm (u+t • d),Real.sq_sqrt hq,Real.sqrt_nonneg q,norm_nonneg (A (u+t • d) d)])
  have hdiff : ‖G v-G u‖ ≤ Real.sqrt q := by simpa [d] using hh
  change ‖G v-G u‖^2 ≤ q
  nlinarith [Real.sq_sqrt hq,Real.sqrt_nonneg q,norm_nonneg (G v-G u)]

private theorem young_norm {E : Type*} [NormedAddCommGroup E] (u v : E)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ‖u-v‖^2 ≤ (1/γ)*‖u‖^2+(1/(1-γ))*‖v‖^2 := by
  have hnorm:=norm_sub_le u v
  have hsq : ‖u-v‖^2 ≤ (‖u‖+‖v‖)^2 := by nlinarith [norm_nonneg (u-v),norm_nonneg u,norm_nonneg v]
  apply hsq.trans
  have hg : γ ≠ 0 := ne_of_gt hγ0
  have h1g : 1-γ ≠ 0 := ne_of_gt (sub_pos.mpr hγ1)
  have hid : ((1/γ)*‖u‖^2+(1/(1-γ))*‖v‖^2-(‖u‖+‖v‖)^2)*(γ*(1-γ))=
      ((1-γ)*‖u‖-γ*‖v‖)^2 := by field_simp;ring
  by_contra hn
  have hd := sub_neg.mpr (lt_of_not_ge hn)
  have hh:=mul_neg_of_neg_of_pos hd (mul_pos hγ0 (sub_pos.mpr hγ1))
  rw [hid] at hh
  exact not_lt_of_ge (sq_nonneg _) hh



private theorem square_order {n : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsq : B*B ≤ A*A) : B ≤ A := by
  have hAp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hA
  have hBp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hB
  let C:=A-B
  have hC : C.toLinearMap.IsSymmetric := hAp.toLinearMap.isSymmetric.sub hBp.toLinearMap.isSymmetric
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=n := by simp
  let e:=hC.eigenvalues hdim
  let v:=hC.eigenvectorBasis hdim
  have hev (i : Fin n) : C (v i)=e i • v i := hC.apply_eigenvectorBasis hdim i
  have henonneg (i : Fin n) : 0 ≤ e i := by
    have hi:=hev i
    have ha : A (v i)=B (v i)+e i • v i := by change A (v i)-B (v i)=_ at hi;linear_combination (norm := module) hi
    have hpos:=hAp.inner_nonneg_left (v i)
    rw [ha,inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,v.norm_eq_one] at hpos
    have hnorm:=((ContinuousLinearMap.le_def _ _).mp hsq).inner_nonneg_left (v i)
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left,mul_apply_eq_comp] at hnorm
    have hea : ⟪A (A (v i)),v i⟫=‖A (v i)‖^2 :=
      (hAp.isSymmetric (A (v i)) (v i)).trans (real_inner_self_eq_norm_sq _)
    have heb : ⟪B (B (v i)),v i⟫=‖B (v i)‖^2 :=
      (hBp.isSymmetric (B (v i)) (v i)).trans (real_inner_self_eq_norm_sq _)
    rw [hea,heb,ha,norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,v.norm_eq_one,real_inner_smul_right] at hnorm
    by_contra hn
    have he : e i < 0 := lt_of_not_ge hn
    have hmul:=mul_nonpos_of_nonpos_of_nonneg he.le hpos
    nlinarith
  apply (ContinuousLinearMap.le_def _ _).mpr
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨hC,?_⟩
  intro x
  have he : ⟪C x,x⟫=∑ i,e i*⟪v i,x⟫^2 := by
    rw [← v.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro i hi
    have hix : ⟪v i,C x⟫=e i*⟪v i,x⟫ := by
      calc ⟪v i,C x⟫=⟪C (v i),x⟫ := (hC (v i) x).symm
           _ = _ := by rw [hev,real_inner_smul_left]
    rw [real_inner_comm (v i) (C x),hix]
    ring
  change 0 ≤ ⟪C x,x⟫
  rw [he]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (henonneg i) (sq_nonneg _))

private theorem hessian_nonneg {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (hc : ConvexOn ℝ Set.univ F) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ hess F x := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨hessian_symmetric F hF x,?_⟩
  intro d
  let g:=fun t : ℝ => F (x+t • d)
  let gp:=fun t : ℝ => ⟪gradient F (x+t • d),d⟫
  have hl (t : ℝ) : HasDerivAt (fun a : ℝ => x+a • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hg (t : ℝ) : HasDerivAt g (gp t) t := by
    have hh:=(hF.differentiable (by norm_num) (x+t • d)).hasFDerivAt.comp_hasDerivAt t (hl t)
    rw [← inner_gradient_left] at hh
    exact hh
  have hgp (t : ℝ) : HasDerivAt gp ⟪hess F (x+t • d) d,d⟫ t := by
    simpa [gp,hess] using ((grad_diff F hF (x+t • d)).hasFDerivAt.comp_hasDerivAt t (hl t)).inner ℝ (hasDerivAt_const t d)
  have hgc : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ,?_⟩
    intro a ha b hb u v hu hv huv
    have hh:=hc.2 (Set.mem_univ (x+a • d)) (Set.mem_univ (x+b • d)) hu hv huv
    have hae : x+(u*a+v*b) • d=u • (x+a • d)+v • (x+b • d) := by
      calc x+(u*a+v*b) • d=(u+v) • x+(u*a+v*b) • d := by rw [huv,one_smul]
           _ = _ := by module
    change F (x+(u*a+v*b) • d) ≤ u*F (x+a • d)+v*F (x+b • d)
    rw [hae]
    exact hh
  have hmono : Monotone gp := by
    intro a b hab
    have hh:=hgc.monotoneOn_deriv (fun t _ => (hg t).differentiableAt) (Set.mem_univ a) (Set.mem_univ b) hab
    simpa only [(hg a).deriv,(hg b).deriv] using hh
  have hh:=hmono.deriv_nonneg (x:=0)
  rw [(hgp 0).deriv] at hh
  simpa [hess] using hh

private theorem taylor_lower {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ x,A ≤ hess F x) (u v : EuclideanSpace ℝ (Fin n)) :
    F u+⟪gradient F u,v-u⟫+(1/2)*wnormSq A (v-u) ≤ F v := by
  let d:=v-u
  let g:=fun t : ℝ => F (u+t • d)-(1/2)*t^2*wnormSq A d
  let gp:=fun t : ℝ => ⟪gradient F (u+t • d),d⟫-t*wnormSq A d
  have hl (t : ℝ) : HasDerivAt (fun a : ℝ => u+a • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add u
  have hg (t : ℝ) : HasDerivAt g (gp t) t := by
    have hh:=(hF.differentiable (by norm_num) (u+t • d)).hasFDerivAt.comp_hasDerivAt t (hl t)
    rw [← inner_gradient_left] at hh
    convert! hh.sub (((hasDerivAt_id t).pow 2).const_mul (1/2) |>.mul_const (wnormSq A d)) using 1 <;> dsimp [g,gp,id_eq] <;> ring
  have hgp (t : ℝ) : HasDerivAt gp (⟪hess F (u+t • d) d,d⟫-wnormSq A d) t := by
    convert! (((grad_diff F hF (u+t • d)).hasFDerivAt.comp_hasDerivAt t (hl t)).inner ℝ (hasDerivAt_const t d)).sub
      ((hasDerivAt_id t).mul_const (wnormSq A d)) using 1 <;> simp [gp,hess]
  have hm : Monotone gp := monotone_of_hasDerivAt_nonneg hgp (fun t => by
    have hh:=((ContinuousLinearMap.le_def _ _).mp (hA (u+t • d))).inner_nonneg_left d
    simp only [ContinuousLinearMap.sub_apply,inner_sub_left] at hh
    change 0 ≤ ⟪hess F (u+t • d) d,d⟫-wnormSq A d
    simpa only [wnormSq,real_inner_comm d (A d)] using hh)
  have hc : ConvexOn ℝ Set.univ g :=
    (show Monotone (deriv g) from fun x y hxy => by rw [(hg x).deriv,(hg y).deriv];exact hm hxy).monotoneOn (interior Set.univ) |>.convexOn_of_deriv
      convex_univ (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
  have hh:=hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num : (0:ℝ)<1) (hg 0)
  simp [g,gp,slope_def_field,d] at hh
  rw [inner_gradient_left,map_sub]
  linarith


private theorem wnorm_neg {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n)) :
    wnormSq A (-u)=wnormSq A u := by simp [wnormSq]

private theorem step_base {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin m) → EReal) (phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z) (t : ℕ) (w : EuclideanSpace ℝ (Fin m)) :
    augLag h P M β (x (t+1)) (y (t+1)) (z (t+1)) ≤ augLag h P M β (x t) w (z t)+
      (((1/β)*‖z (t+1)-z t‖^2-(1/2)*wnormSq (δ • 1+T2) (x (t+1)-x t) : ℝ) : EReal) := by
  have hT (u : EuclideanSpace ℝ (Fin n)) : T2 ≤ hess phi u :=
    square_order (hess phi u) T2 (hessian_nonneg phi hstd.phi_contDiff hstd.phi_convex u)
      hA.2.2.2.1.1 (hA.2.2.2.1.2.2 u).1
  have hyfin:=y_finite h P phi M β x y z hstd.P_proper hseq t
  by_cases hwfin : P w=⊤
  · simp only [augLag,hwfin,EReal.coe_add_top,EReal.top_add_coe,le_top]
  let L:=fun a b c => h a+(P b).toReal-⟪c,M a-b⟫+β/2*‖M a-b‖^2
  have lag_coe (a : EuclideanSpace ℝ (Fin n)) (b c : EuclideanSpace ℝ (Fin m)) (hb : P b ≠ ⊤) :
      augLag h P M β a b c=(L a b c : EReal) := by
    unfold augLag
    rw [← EReal.coe_toReal hb (hstd.P_proper.1 b)]
    simp only [← EReal.coe_add]
    congr 1
    dsimp [L]
    ring
  have hymin : L (x t) (y (t+1)) (z t) ≤ L (x t) w (z t) := by
    have hh:=(hseq t).1 w
    rw [lag_coe _ _ _ hyfin,lag_coe _ _ _ hwfin,EReal.coe_le_coe_iff] at hh
    exact hh
  let dx:=x (t+1)-x t
  have hprim : L (x (t+1)) (y (t+1)) (z t) ≤ L (x t) (y (t+1)) (z t)-(1/2)*wnormSq (δ • 1+T2) dx := by
    have hh:=taylor_lower h hstd.h_contDiff Q2 (fun u => (hA.2.1 u).1) (x (t+1)) (x t)
    have hpf:=taylor_lower phi hstd.phi_contDiff T2 hT (x t) (x (t+1))
    have hpr:=taylor_lower phi hstd.phi_contDiff T2 hT (x (t+1)) (x t)
    have hn : x t-x (t+1)= -dx := by dsimp [dx];module
    rw [hn,inner_neg_right,wnorm_neg] at hh hpr
    change phi (x t)+⟪gradient phi (x t),dx⟫+(1/2)*wnormSq T2 dx ≤ phi (x (t+1)) at hpf
    have hop:=x_optimality h P phi M β x y z hstd hseq t
    rw [(hseq t).2.2,map_sub,map_smul] at hop
    have hi:=congrArg (fun a => ⟪a,dx⟫) hop
    simp only [inner_sub_left,inner_add_left,inner_neg_left,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left] at hi
    have hd:=((ContinuousLinearMap.le_def _ _).mp hA.2.2.2.2.1.2).inner_nonneg_left dx
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,smul_apply,one_apply_eq_self,
      ContinuousLinearMap.comp_apply,inner_sub_left,inner_add_left,real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq] at hd
    have hq : ⟪Q2 dx,dx⟫=wnormSq Q2 dx := real_inner_comm _ _
    have ht : ⟪T2 dx,dx⟫=wnormSq T2 dx := real_inner_comm _ _
    rw [hq,ht] at hd
    have hsum : wnormSq (δ • 1+T2) dx=δ*‖dx‖^2+wnormSq T2 dx := by
      simp [wnormSq,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    have hm : M (x t)-y (t+1)=(M (x (t+1))-y (t+1))-M dx := by dsimp [dx];rw [map_sub];module
    dsimp [L]
    rw [hm,hsum]
    simp only [norm_sub_sq_real,inner_sub_right,inner_sub_left]
    linarith
  have hdual : L (x (t+1)) (y (t+1)) (z (t+1))-L (x (t+1)) (y (t+1)) (z t)=
      (1/β)*‖z (t+1)-z t‖^2 := by
    have hz : z (t+1)-z t= -β • (M (x (t+1))-y (t+1)) := by rw [(hseq t).2.2];module
    rw [hz]
    dsimp [L]
    rw [(hseq t).2.2,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,norm_smul,
      Real.norm_eq_abs,abs_neg,abs_of_pos hstd.beta_pos]
    field_simp
    ring
  rw [lag_coe _ _ _ hyfin,lag_coe _ _ _ hwfin,← EReal.coe_add,EReal.coe_le_coe_iff]
  change L (x (t+1)) (y (t+1)) (z (t+1)) ≤ L (x t) w (z t)+((1/β)*‖z (t+1)-z t‖^2-(1/2)*wnormSq (δ • 1+T2) dx)
  linarith

private theorem dual_step {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (t : ℕ) (ht : 1 ≤ t) :
    σ * ‖z (t + 1) - z t‖ ^ 2 ≤
      (1 / γ) * wnormSq Q3 (x (t + 1) - x t) +
        (1 / (1 - γ)) * wnormSq (T1 * T1) (x t - x (t - 1))  := by
  have hg0 := hA.2.2.2.2.2.2.1
  have hg1 := hA.2.2.2.2.2.2.2.1
  let u:=gradient h (x (t+1))+gradient phi (x (t+1))-(gradient h (x t)+gradient phi (x t))
  let v:=gradient phi (x t)-gradient phi (x (t-1))
  have hu : ‖u‖^2 ≤ wnormSq Q3 (x (t+1)-x t) := by
    apply vector_diff_bound (fun w => gradient h w+gradient phi w)
      (fun w => hess h w+hess phi w) Q3 _ _ hA.2.2.2.2.2.1 (x t) (x (t+1))
    · intro w
      exact (grad_diff h hstd.h_contDiff w).hasFDerivAt.add (grad_diff phi hstd.phi_contDiff w).hasFDerivAt
    · intro w a b
      simp only [ContinuousLinearMap.coe_add,LinearMap.add_apply,inner_add_left,inner_add_right]
      exact congrArg₂ (·+·) (hessian_symmetric h hstd.h_contDiff w a b) (hessian_symmetric phi hstd.phi_contDiff w a b)
  have hv : ‖v‖^2 ≤ wnormSq (T1*T1) (x t-x (t-1)) := by
    exact vector_diff_bound (gradient phi) (hess phi) (T1*T1)
      (fun w => (grad_diff phi hstd.phi_contDiff w).hasFDerivAt)
      (hessian_symmetric phi hstd.phi_contDiff)
      (fun w => (hA.2.2.2.1.2.2 w).2) (x (t-1)) (x t)
  have he : (ContinuousLinearMap.adjoint M) (z (t+1)-z t)=u-v := by
    have h1:=(optimality h P phi M β hstd x y z hseq t).2.1
    have h0:=(optimality h P phi M β hstd x y z hseq (t-1)).2.1
    rw [Nat.sub_add_cancel ht] at h0
    rw [map_sub]
    dsimp [u,v]
    linear_combination (norm := module) h0-h1
  calc
    σ*‖z (t+1)-z t‖^2 ≤ ‖(ContinuousLinearMap.adjoint M) (z (t+1)-z t)‖^2 := adjoint_lower M σ hA.1.2 _
    _ = ‖u-v‖^2 := by rw [he]
    _ ≤ (1/γ)*‖u‖^2+(1/(1-γ))*‖v‖^2 := young_norm u v γ hA.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.1
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 1/γ))
      (mul_le_mul_of_nonneg_left hv (by have := hA.2.2.2.2.2.2.2.1; positivity : 0 ≤ 1/(1-γ)))

private theorem one_step {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (t : ℕ) (ht : 1 ≤ t) :
    augLag h P M β (x (t + 1)) (y (t + 1)) (z (t + 1)) ≤
      augLag h P M β (x t) (y t) (z t) +
        ((1 / 2 * wnormSq ((2 / (σ * β * γ)) • Q3 - δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) - T2) (x (t + 1) - x t) +
          1 / 2 * wnormSq ((2 / (σ * β * (1 - γ))) • (T1 * T1)) (x t - x (t - 1)) : ℝ) : EReal)  := by
  have hσ := hA.1.1
  have hβ := hstd.beta_pos
  have hγ := hA.2.2.2.2.2.2.1
  have hγ1 := hA.2.2.2.2.2.2.2.1
  have hd:=dual_step h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq t ht
  have hb : (1/β)*‖z (t+1)-z t‖^2 ≤
      (1/(σ*β*γ))*wnormSq Q3 (x (t+1)-x t)+
      (1/(σ*β*(1-γ)))*wnormSq (T1*T1) (x t-x (t-1)) := by
    have hh:=mul_le_mul_of_nonneg_left hd (show 0 ≤ 1/(σ*β) by positivity)
    convert! hh using 1 <;> field_simp <;> ring
  have hs:=step_base h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq t (y t)
  apply hs.trans
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.mpr
  simp only [wnormSq,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,smul_apply,
    one_apply_eq_self,inner_sub_right,inner_add_right,real_inner_smul_right]
  simp only [wnormSq] at hb
  ring_nf at hb ⊢
  linarith

private theorem telescope (L : ℕ → EReal) (r b : ℕ → ℝ)
    (hstep : ∀ t, 1 ≤ t → L (t+1) ≤ L t+↑(-r t-b t+b (t-1)))
    (a N : ℕ) (ha : 1 ≤ a) (hN : a ≤ N) :
    L N ≤ L a+↑(-(∑ t ∈ Finset.Ico a N,r t)+b (a-1)-b (N-1)) := by
  induction N,hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hs:=hstep N (ha.trans hN)
    apply hs.trans
    have hh:=add_le_add ih (le_refl (((-r N-b N+b (N-1) : ℝ) : EReal)))
    convert! hh using 1
    rw [add_assoc,← EReal.coe_add,Finset.sum_Ico_succ_top hN,Nat.add_sub_cancel]
    congr 2
    ring

private theorem forms_pos {n m : ℕ} (h phi : EuclideanSpace ℝ (Fin n) → ℝ)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β σ δ γ : ℝ)
    (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ) :
    (∀ u, 0 ≤ wnormSq ((2/(σ*β*(1-γ))) • (T1*T1)) u) ∧
    (∀ u, u ≠ 0 → 0 < wnormSq (δ • 1+T2-(2/(σ*β)) • ((1/γ) • Q3+(1/(1-γ)) • (T1*T1))) u) := by
  constructor
  · intro u
    have hp:=(ContinuousLinearMap.nonneg_iff_isPositive T1).mp (hA.2.2.2.1.1.trans hA.2.2.2.1.2.1)
    have he : wnormSq (T1*T1) u=‖T1 u‖^2 := by
      dsimp [wnormSq]
      change ⟪u,T1 (T1 u)⟫=_
      exact (hp.isSymmetric u (T1 u)).symm.trans (real_inner_self_eq_norm_sq _)
    simp only [wnormSq,smul_apply,real_inner_smul_right]
    change (2/(σ*β*(1-γ)))*wnormSq (T1*T1) u ≥ 0
    rw [he]
    have := hA.1.1
    have := hA.2.2.1
    have := hA.2.2.2.2.2.2.2.1
    positivity
  · intro u hu
    simpa only [wnormSq,real_inner_comm] using hA.2.2.2.2.2.2.2.2.2 u hu

private theorem positive_coercive {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hR : R.toLinearMap.IsSymmetric) (hpos : ∀ u, u ≠ 0 → 0 < wnormSq R u) :
    ∃ c : ℝ, 0 < c ∧ ∀ u,c*‖u‖^2 ≤ wnormSq R u := by
  classical
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=n := by simp
  let e:=hR.eigenvalues hdim
  let v:=hR.eigenvectorBasis hdim
  have hev (i : Fin n) : R (v i)=e i • v i := hR.apply_eigenvectorBasis hdim i
  have hepos (i : Fin n) : 0 < e i := by
    have hv : v i ≠ 0 := by
      intro hh
      have hn:=v.norm_eq_one i
      rw [hh,norm_zero] at hn
      norm_num at hn
    have hh:=hpos (v i) hv
    dsimp [wnormSq] at hh
    rw [hev,real_inner_smul_right,real_inner_self_eq_norm_sq,v.norm_eq_one] at hh
    simpa using hh
  have hfinite (s : Finset (Fin n)) : ∃ c : ℝ,0 < c ∧ ∀ i ∈ s,c ≤ e i := by
    induction s using Finset.induction with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨c,hc,hci⟩:=ih
      refine ⟨min c (e a),lt_min hc (hepos a),?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hci i hi)
  obtain ⟨c,hc,hci⟩:=hfinite Finset.univ
  refine ⟨c,hc,?_⟩
  intro u
  have he : wnormSq R u=∑ i,e i*⟪v i,u⟫^2 := by
    rw [wnormSq,← v.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro i hi
    have hh : ⟪v i,R u⟫=e i*⟪v i,u⟫ := by
      calc
        _ = ⟪R (v i),u⟫ := (hR (v i) u).symm
        _ = _ := by rw [hev,real_inner_smul_left]
    have hc : ⟪u,v i⟫=⟪v i,u⟫ := real_inner_comm _ _
    rw [hh,hc]
    ring
  rw [he,← v.sum_sq_inner_right,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hci i hi) (sq_nonneg _))
private theorem primal_step_limit {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (hcl : ∃ (s : ℕ → ℕ) (xs : EuclideanSpace ℝ (Fin n)) (ys zs : EuclideanSpace ℝ (Fin m)), StrictMono s ∧
      Tendsto (fun i => (x (s i), y (s i), z (s i))) atTop (𝓝 (xs, ys, zs))) :
    Tendsto (fun t => ‖x (t + 1) - x t‖) atTop (𝓝 0) := by
  let R:=δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))+T2-(2/(σ*β)) • ((1/γ) • Q3+(1/(1-γ)) • (T1*T1))
  let B:=(2/(σ*β*(1-γ))) • (T1*T1)
  let r:=fun t => (1/2)*wnormSq R (x (t+1)-x t)
  let b:=fun t => (1/2)*wnormSq B (x (t+1)-x t)
  have hp:=forms_pos h phi M β σ δ γ Q1 Q2 T1 T2 Q3 hA
  have hRs : R.toLinearMap.IsSymmetric := ((ContinuousLinearMap.le_def _ _).mp hA.2.2.2.2.2.2.2.2.1).toLinearMap.isSymmetric
  obtain ⟨c,hc,hcr⟩:=positive_coercive R hRs hp.2
  have hr (t : ℕ) : (c/2)*‖x (t+1)-x t‖^2 ≤ r t := by
    have hh:=hcr (x (t+1)-x t)
    dsimp [r]
    linarith
  have hr0 (t : ℕ) : 0 ≤ r t := (mul_nonneg (by positivity) (sq_nonneg _)).trans (hr t)
  have hb (t : ℕ) : 0 ≤ b t := mul_nonneg (by norm_num) (hp.1 _)
  have hfin : ∀ t,1 ≤ t → P (y t) ≠ ⊤ := by
    intro t ht
    obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    exact y_finite h P phi M β x y z hstd.P_proper hseq k
  let C : ℕ → ℝ := fun t => h (x t)-⟪z t,M (x t)-y t⟫+β/2*‖M (x t)-y t‖^2
  let E : ℕ → ℝ := fun t => C (t+1)+(P (y (t+1))).toReal+b t
  have hstep (t : ℕ) : E (t+1)+r (t+1) ≤ E t := by
    have hh:=one_step h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq (t+1) (by omega)
    unfold augLag at hh
    rw [← EReal.coe_toReal (hfin (t+1) (by omega)) (hstd.P_proper.1 _),
      ← EReal.coe_toReal (hfin (t+1+1) (by omega)) (hstd.P_proper.1 _)] at hh
    simp only [← EReal.coe_mul,← EReal.coe_neg,← EReal.coe_add,EReal.coe_le_coe_iff,Nat.add_sub_cancel] at hh
    dsimp [E,C,r,b,R,B]
    simp only [wnormSq,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,smul_apply,
      one_apply_eq_self,inner_sub_right,inner_add_right,real_inner_smul_right,
      div_eq_mul_inv,mul_inv_rev] at hh ⊢
    ring_nf at hh ⊢
    linarith
  have hanti : Antitone E := antitone_nat_of_succ_le (fun t => by have hh:=hstep t;have hh0:=hr0 (t+1);linarith)
  obtain ⟨s,xs,ys,zs,hs,hconv⟩:=hcl
  simp only [nhds_prod_eq] at hconv
  have hx:=hconv.fst
  have hy:=hconv.snd.fst
  have hz:=hconv.snd.snd
  let cs:=h xs-⟪zs,M xs-ys⟫+β/2*‖M xs-ys‖^2
  have hC : Tendsto (fun i => C (s i)) atTop (𝓝 cs) := by
    have hd:=(M.continuous.tendsto xs |>.comp hx).sub hy
    exact ((hstd.h_contDiff.continuous.tendsto xs |>.comp hx).sub (hz.inner hd)).add ((hd.norm.pow 2).const_mul (β/2))
  obtain ⟨q,_,hq⟩:=EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr (hstd.P_proper.1 ys))
  have hP : ∀ᶠ i in atTop,(q:EReal)<P (y (s i)) := hy.eventually (hstd.P_closed ys (q:EReal) hq)
  have hCe : ∀ᶠ i in atTop,cs-1 < C (s i) := (tendsto_order.mp hC).1 _ (by linarith)
  have hbelow : BddBelow (Set.range E) := by
    refine ⟨q+cs-1,?_⟩
    rintro _ ⟨t,rfl⟩
    have hg : ∀ᶠ i in atTop,t+1 ≤ s i := hs.tendsto_atTop.eventually_ge_atTop (t+1)
    obtain ⟨i,hpi,hci,hgi⟩ := (hP.and (hCe.and hg)).exists
    rw [← EReal.coe_toReal (hfin (s i) (by omega)) (hstd.P_proper.1 _),EReal.coe_lt_coe_iff] at hpi
    have hm:=hanti (show t ≤ s i-1 by omega)
    dsimp [E] at hm
    rw [show s i-1+1=s i by omega] at hm
    have hb0:=hb (s i-1)
    linarith
  have hElim:=tendsto_atTop_ciInf hanti hbelow
  have hdiff : Tendsto (fun t => (E t-E (t+1))/(c/2)) atTop (𝓝 0) := by
    have hh:=(hElim.sub (hElim.comp (tendsto_add_atTop_nat 1))).div_const (c/2)
    simpa using hh
  have hsq : Tendsto (fun t => ‖x (t+1+1)-x (t+1)‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun t => sq_nonneg _) (fun t => ?_) hdiff
    apply (le_div_iff₀ (show 0 < c/2 by positivity)).mpr
    have hh:=hstep t
    have hh2:=hr (t+1)
    nlinarith
  have hn : Tendsto (fun t => ‖x (t+1+1)-x (t+1)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsq.sqrt
  exact (tendsto_add_atTop_iff_nat 1).mp hn
private theorem all_steps {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (hcl : ∃ (s : ℕ → ℕ) (xs : EuclideanSpace ℝ (Fin n)) (ys zs : EuclideanSpace ℝ (Fin m)), StrictMono s ∧
      Tendsto (fun i => (x (s i), y (s i), z (s i))) atTop (𝓝 (xs, ys, zs))) :
    Tendsto (fun t => ‖y (t+1)-y t‖^2+‖x (t+1)-x t‖^2+‖z (t+1)-z t‖^2) atTop (𝓝 0) := by
  have hxn:=primal_step_limit h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq hcl
  have hdx:=tendsto_zero_iff_norm_tendsto_zero.mpr hxn
  have hquad (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun t => wnormSq A (x (t+1)-x t)) atTop (𝓝 0) := by
    have hh:=hdx.inner (𝕜 := ℝ) (A.continuous.tendsto 0 |>.comp hdx)
    simpa only [map_zero,inner_zero_left,wnormSq,Function.comp_def] using hh
  have hF : Tendsto (fun t => ((1/γ)*wnormSq Q3 (x (t+1+1)-x (t+1))+
      (1/(1-γ))*wnormSq (T1*T1) (x (t+1)-x t))/σ) atTop (𝓝 0) := by
    have h1:=((hquad Q3).comp (tendsto_add_atTop_nat 1)).const_mul (1/γ)
    have h2:=(hquad (T1*T1)).const_mul (1/(1-γ))
    simpa using (h1.add h2).div_const σ
  have hzsq : Tendsto (fun t => ‖z (t+1+1)-z (t+1)‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun t => sq_nonneg _) (fun t => ?_) hF
    apply (le_div_iff₀ hA.1.1).mpr
    have hh:=dual_step h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq (t+1) (by omega)
    simpa only [Nat.add_sub_cancel,mul_comm] using hh
  have hzn : Tendsto (fun t => ‖z (t+1)-z t‖) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hzsq.sqrt
  have hdz:=tendsto_zero_iff_norm_tendsto_zero.mpr hzn
  have hgap : Tendsto (fun t => M (x (t+1))-y (t+1)) atTop (𝓝 0) := by
    have he : (fun t => M (x (t+1))-y (t+1))=(fun t => (1/β) • (-(z (t+1)-z t))) := by
      funext t
      rw [neg_sub]
      exact (optimality h P phi M β hstd x y z hseq t).2.2
    rw [he]
    simpa using hdz.neg.const_smul (1/β)
  have hdy : Tendsto (fun t => y (t+1)-y t) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    have hh:=((M.continuous.tendsto 0 |>.comp hdx).comp (tendsto_add_atTop_nat 1)).sub
      ((hgap.comp (tendsto_add_atTop_nat 1)).sub hgap)
    simp only [map_zero,sub_zero] at hh
    convert! hh using 1
    funext t
    simp only [Function.comp_def,map_sub,Nat.add_assoc]
    module
  simpa using ((hdy.norm.pow 2).add (hdx.norm.pow 2)).add (hdz.norm.pow 2)

private theorem step_vanish_of_sum {X : Type*} [NormedAddCommGroup X]
    (u : ℕ → X) (F : ℕ → ℝ) (hF : Tendsto F atTop (𝓝 0))
    (hle : ∀ t,‖u (t+1)-u t‖^2 ≤ F t) :
    Tendsto (fun t => u (t+1)-u t) atTop (𝓝 0) := by
  have hs : Tendsto (fun t => ‖u (t+1)-u t‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun t => sq_nonneg _) hle hF
  have hh:=Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

private theorem values_limit {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (s : ℕ → ℕ) (hs : StrictMono s) (xs : EuclideanSpace ℝ (Fin n)) (ys zs : EuclideanSpace ℝ (Fin m))
    (hconv : Tendsto (fun i => (x (s i), y (s i), z (s i))) atTop (𝓝 (xs, ys, zs))) :
    Tendsto (fun i => P (y (s i + 1))) atTop (𝓝 (P ys)) ∧ P ys ≠ ⊤ := by
  have h9:=all_steps h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq ⟨s,xs,ys,zs,hs,hconv⟩
  simp only [nhds_prod_eq] at hconv
  have hx:=hconv.fst
  have hy:=hconv.snd.fst
  have hz:=hconv.snd.snd
  have hdy:=step_vanish_of_sum y _ h9 (fun t => by nlinarith [sq_nonneg ‖x (t+1)-x t‖,sq_nonneg ‖z (t+1)-z t‖])
  have hy1 : Tendsto (fun i => y (s i+1)) atTop (𝓝 ys) := by
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hdy.comp hs.tendsto_atTop).add hy
  let cost : ℕ → EuclideanSpace ℝ (Fin m) → ℝ := fun i w =>
    -⟪z (s i),M (x (s i))-w⟫+β/2*‖M (x (s i))-w‖^2
  let mlim : EuclideanSpace ℝ (Fin m) → ℝ := fun w =>
    -⟪zs,M xs-w⟫+β/2*‖M xs-w‖^2
  have hm (w : EuclideanSpace ℝ (Fin m)) : Tendsto (fun i => cost i w) atTop (𝓝 (mlim w)) := by
    have hd:=(M.continuous.tendsto xs |>.comp hx).sub (tendsto_const_nhds (x:=w))
    exact (hz.inner hd).neg.add ((hd.norm.pow 2).const_mul (β/2))
  have hmn : Tendsto (fun i => cost i (y (s i+1))) atTop (𝓝 (mlim ys)) := by
    have hd:=(M.continuous.tendsto xs |>.comp hx).sub hy1
    exact (hz.inner hd).neg.add ((hd.norm.pow 2).const_mul (β/2))
  have hupper (w : EuclideanSpace ℝ (Fin m)) (hw : P w ≠ ⊤) : ∀ i,
      P (y (s i+1)) ≤ (((P w).toReal+cost i w-cost i (y (s i+1)) : ℝ) : EReal) := by
    intro i
    have hn:=y_finite h P phi M β x y z hstd.P_proper hseq (s i)
    have hh:=(hseq (s i)).1 w
    unfold augLag at hh
    rw [← EReal.coe_toReal hw (hstd.P_proper.1 w),
      ← EReal.coe_toReal hn (hstd.P_proper.1 _)] at hh
    rw [← EReal.coe_toReal hn (hstd.P_proper.1 _)]
    simp only [← EReal.coe_mul,← EReal.coe_neg,← EReal.coe_add,EReal.coe_le_coe_iff] at hh ⊢
    dsimp [cost]
    linarith
  have huplim (w : EuclideanSpace ℝ (Fin m)) :
      Tendsto (fun i => (P w).toReal+cost i w-cost i (y (s i+1))) atTop
        (𝓝 ((P w).toReal+mlim w-mlim ys)) :=
    (tendsto_const_nhds.add (hm w)).sub hmn
  have hfin : P ys ≠ ⊤ := by
    obtain ⟨w,hw⟩:=hstd.P_proper.2
    have hb : P ys ≤ (((P w).toReal+mlim w-mlim ys : ℝ) : EReal) :=
      hstd.P_closed.isClosed_epigraph.mem_of_tendsto
        (hy1.prodMk_nhds (EReal.tendsto_coe.mpr (huplim w))) (Eventually.of_forall (hupper w hw))
    intro he
    simp only [he,top_le_iff,EReal.coe_ne_top] at hb
  refine ⟨tendsto_order.mpr ⟨?_,?_⟩,hfin⟩
  · intro a ha
    exact hy1.eventually (hstd.P_closed ys a ha)
  · intro b hb
    obtain ⟨q,hq1,hq2⟩:=EReal.exists_between_coe_real hb
    have hq : (P ys).toReal < q := by
      rwa [← EReal.coe_toReal hfin (hstd.P_proper.1 ys),EReal.coe_lt_coe_iff] at hq1
    have hu : Tendsto (fun i => (P ys).toReal+cost i ys-cost i (y (s i+1))) atTop (𝓝 (P ys).toReal) := by
      simpa using huplim ys
    filter_upwards [(tendsto_order.mp hu).2 q hq] with i hi
    exact lt_of_le_of_lt (hupper ys hfin i) ((EReal.coe_lt_coe_iff.mpr hi).trans hq2)

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


private theorem stationary_of_limits {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
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

private theorem summed {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (M₀ N : ℕ) (hM₀ : 1 ≤ M₀) (hN : M₀ < N) :
    augLag h P M β (x N) (y N) (z N) ≤
      augLag h P M β (x M₀) (y M₀) (z M₀) +
        ((-(1 / 2) * ∑ t ∈ Finset.Ico M₀ (N - 1),
            wnormSq (δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + T2 - (2 / (σ * β)) • ((1 / γ) • Q3 + (1 / (1 - γ)) • (T1 * T1))) (x (t + 1) - x t) +
          1 / 2 * wnormSq ((2 / (σ * β * (1 - γ))) • (T1 * T1)) (x M₀ - x (M₀ - 1)) : ℝ) : EReal) := by
  let R:=δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))+T2-(2/(σ*β)) • ((1/γ) • Q3+(1/(1-γ)) • (T1*T1))
  let B:=(2/(σ*β*(1-γ))) • (T1*T1)
  let r:=fun t => (1/2)*wnormSq R (x (t+1)-x t)
  let b:=fun t => (1/2)*wnormSq B (x (t+1)-x t)
  have hp:=forms_pos h phi M β σ δ γ Q1 Q2 T1 T2 Q3 hA
  have hr (t : ℕ) : 0 ≤ r t := by
    dsimp [r,R]
    by_cases hh : x (t+1)-x t=0
    · simp [hh,wnormSq]
    · exact mul_nonneg (by norm_num) (hp.2 _ hh).le
  have hb (t : ℕ) : 0 ≤ b t := mul_nonneg (by norm_num) (hp.1 _)
  have hstep (t : ℕ) (ht : 1 ≤ t) :
      augLag h P M β (x (t+1)) (y (t+1)) (z (t+1)) ≤
      augLag h P M β (x t) (y t) (z t)+↑(-r t-b t+b (t-1)) := by
    have hh:=one_step h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq t ht
    convert! hh using 2
    congr 1
    dsimp [r,b,R,B]
    rw [Nat.sub_add_cancel ht]
    simp only [wnormSq,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,smul_apply,
      one_apply_eq_self,inner_sub_right,inner_add_right,real_inner_smul_right]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hh:=telescope (fun t => augLag h P M β (x t) (y t) (z t)) r b hstep M₀ N hM₀ hN.le
  have hsum : (∑ t ∈ Finset.Ico M₀ N,r t)=(∑ t ∈ Finset.Ico M₀ (N-1),r t)+r (N-1) := by
    convert! Finset.sum_Ico_succ_top (show M₀ ≤ N-1 by omega) (f:=r) using 1
    congr 2
    omega
  apply hh.trans
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.mpr
  rw [hsum]
  have hbr:=hb (N-1)
  have hrr:=hr (N-1)
  have hsume : (∑ t ∈ Finset.Ico M₀ (N-1),r t)=(1/2)*∑ t ∈ Finset.Ico M₀ (N-1),wnormSq R (x (t+1)-x t) := by
    simp only [r,Finset.mul_sum]
  rw [hsume]
  have hbe : b (M₀-1)=(1/2)*wnormSq B (x M₀-x (M₀-1)) := by
    simp only [b,Nat.sub_add_cancel hM₀]
  rw [hbe]
  change _ ≤ -(1/2)*(∑ t ∈ Finset.Ico M₀ (N-1),wnormSq R (x (t+1)-x t))+(1/2)*wnormSq B (x M₀-x (M₀-1))
  linarith

private theorem first_step {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (hz0 : ContinuousLinearMap.adjoint M (z 0) = gradient h (x 0)) :
    augLag h P M β (x 1) (y 1) (z 1) ≤
      augLag h P M β (x 0) (M (x 0)) (z 0) +
        ((1 / 2 * wnormSq ((2 / (σ * β * γ)) • Q3 - δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) - T2) (x 1 - x 0) : ℝ) : EReal)  := by
  have hσ:=hA.1.1
  have hβ:=hstd.beta_pos
  have hγ:=hA.2.2.2.2.2.2.1
  have hγ1:=hA.2.2.2.2.2.2.2.1
  let u:=gradient h (x 1)+gradient phi (x 1)-(gradient h (x 0)+gradient phi (x 0))
  have hu : ‖u‖^2 ≤ wnormSq Q3 (x 1-x 0) := by
    apply vector_diff_bound (fun w => gradient h w+gradient phi w)
      (fun w => hess h w+hess phi w) Q3 _ _ hA.2.2.2.2.2.1 (x 0) (x 1)
    · intro w
      exact (grad_diff h hstd.h_contDiff w).hasFDerivAt.add (grad_diff phi hstd.phi_contDiff w).hasFDerivAt
    · intro w a b
      simp only [ContinuousLinearMap.coe_add,LinearMap.add_apply,inner_add_left,inner_add_right]
      exact congrArg₂ (·+·) (hessian_symmetric h hstd.h_contDiff w a b) (hessian_symmetric phi hstd.phi_contDiff w a b)
  have he : (ContinuousLinearMap.adjoint M) (z 1-z 0)=u := by
    have hh:=(optimality h P phi M β hstd x y z hseq 0).2.1
    simp only [Nat.zero_add] at hh
    rw [map_sub,hz0]
    dsimp [u]
    linear_combination (norm := module) -hh
  have hd : σ*‖z 1-z 0‖^2 ≤ (1/γ)*wnormSq Q3 (x 1-x 0) := by
    have hh:=adjoint_lower M σ hA.1.2 (z 1-z 0)
    rw [he] at hh
    apply (hh.trans hu).trans
    have hi : 1 ≤ 1/γ := (le_div_iff₀ hγ).mpr (by linarith)
    simpa using mul_le_mul_of_nonneg_right hi ((sq_nonneg ‖u‖).trans hu)
  have hb : (1/β)*‖z 1-z 0‖^2 ≤ (1/(σ*β*γ))*wnormSq Q3 (x 1-x 0) := by
    have hh:=mul_le_mul_of_nonneg_left hd (show 0 ≤ 1/(σ*β) by positivity)
    convert! hh using 1 <;> field_simp <;> ring
  have hs:=step_base h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq 0 (M (x 0))
  simp only [Nat.zero_add] at hs
  apply hs.trans
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.mpr
  simp only [wnormSq,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,smul_apply,
    one_apply_eq_self,inner_sub_right,inner_add_right,real_inner_smul_right]
  simp only [wnormSq] at hb
  ring_nf at hb ⊢
  linarith

private theorem first_nonzero {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (hz0 : ContinuousLinearMap.adjoint M (z 0) = gradient h (x 0))
    (hns : ¬ IsStationary h P M (x 0))
    (hfin : ((h (x 0) : ℝ) : EReal) + P (M (x 0)) ≠ ⊤) :
    x 1 ≠ x 0  := by
  intro hx
  apply hns
  have ho:=optimality h P phi M β hstd x y z hseq 0
  simp only [Nat.zero_add] at ho
  have he:=ho.2.1
  rw [hx] at he
  have hadj : (ContinuousLinearMap.adjoint M) (z 1-z 0)=0 := by
    rw [map_sub,hz0]
    linear_combination (norm := module) -he
  have hz : z 1=z 0 := by
    have hh:=adjoint_lower M σ hA.1.2 (z 1-z 0)
    rw [hadj,norm_zero,zero_pow (by norm_num)] at hh
    have hzero : σ*‖z 1-z 0‖^2=0 := le_antisymm hh (mul_nonneg hA.1.1.le (sq_nonneg _))
    have hsq : ‖z 1-z 0‖^2=0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hA.1.1)
    have hn : ‖z 1-z 0‖=0 := sq_eq_zero_iff.mp hsq
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hym : y 1=M (x 0) := by
    have hh:=ho.2.2
    rw [hx,hz,sub_self,smul_zero] at hh
    exact (sub_eq_zero.mp hh).symm
  refine ⟨-z 0,?_,?_⟩
  · simpa only [hx,hz,hym,sub_self,map_zero,smul_zero,sub_zero] using ho.1
  · rw [map_neg,hz0]
    module

private theorem strict_decrease {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (hz0 : ContinuousLinearMap.adjoint M (z 0) = gradient h (x 0))
    (hns : ¬ IsStationary h P M (x 0))
    (hfin : ((h (x 0) : ℝ) : EReal) + P (M (x 0)) ≠ ⊤) :
    (∀ N : ℕ, 1 < N →
      augLag h P M β (x N) (y N) (z N) ≤
        augLag h P M β (x 0) (M (x 0)) (z 0) +
          ((-(1 / 2) * wnormSq (δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + T2 - (2 / (σ * β)) • ((1 / γ) • Q3 + (1 / (1 - γ)) • (T1 * T1))) (x 1 - x 0) : ℝ) : EReal)) ∧
    0 < wnormSq (δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) + T2 - (2 / (σ * β)) • ((1 / γ) • Q3 + (1 / (1 - γ)) • (T1 * T1))) (x 1 - x 0) := by
  let R:=δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))+T2-(2/(σ*β)) • ((1/γ) • Q3+(1/(1-γ)) • (T1*T1))
  have hp:=forms_pos h phi M β σ δ γ Q1 Q2 T1 T2 Q3 hA
  have hr (t : ℕ) : 0 ≤ wnormSq R (x (t+1)-x t) := by
    by_cases hh : x (t+1)-x t=0
    · simp [hh,wnormSq]
    · exact (hp.2 _ hh).le
  constructor
  · intro N hN
    have hh:=summed h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq 1 N le_rfl hN
    have hf:=first_step h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq hz0
    have hs : 0 ≤ ∑ t ∈ Finset.Ico 1 (N-1),wnormSq R (x (t+1)-x t) := Finset.sum_nonneg (fun t ht => hr t)
    apply hh.trans
    apply (add_le_add hf le_rfl).trans
    rw [add_assoc,← EReal.coe_add]
    apply add_le_add le_rfl
    apply EReal.coe_le_coe_iff.mpr
    simp only [Nat.sub_self] 
    change (1/2)*wnormSq _ (x 1-x 0)+(-(1/2)*(∑ t ∈ Finset.Ico 1 (N-1),wnormSq R (x (t+1)-x t))+(1/2)*wnormSq _ (x 1-x 0)) ≤ -(1/2)*wnormSq R (x 1-x 0)
    have he : (1/2)*wnormSq ((2/(σ*β*γ)) • Q3-δ • 1-T2) (x 1-x 0)+(1/2)*wnormSq ((2/(σ*β*(1-γ))) • (T1*T1)) (x 1-x 0)=-(1/2)*wnormSq R (x 1-x 0) := by
      dsimp [R]
      simp only [wnormSq,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,smul_apply,
        one_apply_eq_self,inner_sub_right,inner_add_right,real_inner_smul_right]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    linarith
  · exact hp.2 _ (sub_ne_zero.mpr (first_nonzero h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq hz0 hns hfin))

theorem solution {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z) :
    -- (i) global subsequential convergence
    (∀ (s : ℕ → ℕ) (xs : EuclideanSpace ℝ (Fin n)) (ys zs : EuclideanSpace ℝ (Fin m)), StrictMono s →
      Tendsto (fun i => (x (s i), y (s i), z (s i))) atTop (𝓝 (xs, ys, zs)) →
      Tendsto (fun t => ‖y (t + 1) - y t‖ ^ 2 + ‖x (t + 1) - x t‖ ^ 2 + ‖z (t + 1) - z t‖ ^ 2)
      atTop (𝓝 0) ∧
      (gradient h xs = ContinuousLinearMap.adjoint M zs ∧ -zs ∈ LimitingSubdiff P ys ∧ ys = M xs) ∧
      IsStationary h P M xs) ∧
    -- (ii) strict improvement in objective values
    (ContinuousLinearMap.adjoint M (z 0) = gradient h (x 0) →
      ¬ IsStationary h P M (x 0) →
      ((h (x 0) : ℝ) : EReal) + P (M (x 0)) ≠ ⊤ →
      ∀ (s : ℕ → ℕ) (xs : EuclideanSpace ℝ (Fin n)) (ys zs : EuclideanSpace ℝ (Fin m)), StrictMono s →
        Tendsto (fun i => (x (s i), y (s i), z (s i))) atTop (𝓝 (xs, ys, zs)) →
        ((h xs : ℝ) : EReal) + P (M xs) < ((h (x 0) : ℝ) : EReal) + P (M (x 0))) := by
  have hpart (s : ℕ → ℕ) (xs : EuclideanSpace ℝ (Fin n)) (ys zs : EuclideanSpace ℝ (Fin m))
      (hs : StrictMono s) (hconv : Tendsto (fun i => (x (s i),y (s i),z (s i))) atTop (𝓝 (xs,ys,zs))) :
      Tendsto (fun t => ‖y (t+1)-y t‖^2+‖x (t+1)-x t‖^2+‖z (t+1)-z t‖^2) atTop (𝓝 0) ∧
      (gradient h xs=ContinuousLinearMap.adjoint M zs ∧ -zs ∈ LimitingSubdiff P ys ∧ ys=M xs) ∧ IsStationary h P M xs := by
    have h9:=all_steps h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq ⟨s,xs,ys,zs,hs,hconv⟩
    have h10:=values_limit h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq s hs xs ys zs hconv
    exact ⟨h9,stationary_of_limits h P phi M β hstd x y z hseq s hs xs ys zs hconv h9 h10.1 h10.2⟩
  refine ⟨hpart,?_⟩
  intro hz0 hns hfin s xs ys zs hs hconv
  have hres:=hpart s xs ys zs hs hconv
  have hdecr:=strict_decrease h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq hz0 hns hfin
  have hP0 : P (M (x 0)) ≠ ⊤ := by
    intro hh
    simp only [hh,EReal.coe_add_top] at hfin
    exact hfin rfl
  let F0:=h (x 0)+(P (M (x 0))).toReal
  let q:=wnormSq (δ • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))+T2-(2/(σ*β)) • ((1/γ) • Q3+(1/(1-γ)) • (T1*T1))) (x 1-x 0)
  have hq : 0 < q := hdecr.2
  have heym : ys=M xs := hres.2.1.2.2
  simp only [nhds_prod_eq] at hconv
  have hx:=hconv.fst
  have hy:=hconv.snd.fst
  have hz:=hconv.snd.snd
  have hdx:=step_vanish_of_sum x _ hres.1 (fun t => by nlinarith [sq_nonneg ‖y (t+1)-y t‖,sq_nonneg ‖z (t+1)-z t‖])
  have hdy:=step_vanish_of_sum y _ hres.1 (fun t => by nlinarith [sq_nonneg ‖x (t+1)-x t‖,sq_nonneg ‖z (t+1)-z t‖])
  have hdz:=step_vanish_of_sum z _ hres.1 (fun t => by nlinarith [sq_nonneg ‖y (t+1)-y t‖,sq_nonneg ‖x (t+1)-x t‖])
  have hx1 : Tendsto (fun i => x (s i+1)) atTop (𝓝 xs) := by
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hdx.comp hs.tendsto_atTop).add hx
  have hy1 : Tendsto (fun i => y (s i+1)) atTop (𝓝 ys) := by
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hdy.comp hs.tendsto_atTop).add hy
  have hz1 : Tendsto (fun i => z (s i+1)) atTop (𝓝 zs) := by
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using (hdz.comp hs.tendsto_atTop).add hz
  let C:=fun i => h (x (s i+1))-⟪z (s i+1),M (x (s i+1))-y (s i+1)⟫+β/2*‖M (x (s i+1))-y (s i+1)‖^2
  have hC : Tendsto C atTop (𝓝 (h xs)) := by
    have hd:=(M.continuous.tendsto xs |>.comp hx1).sub hy1
    have hh:=((hstd.h_contDiff.continuous.tendsto xs |>.comp hx1).sub (hz1.inner (𝕜 := ℝ) hd)).add ((hd.norm.pow 2).const_mul (β/2))
    simpa only [C,Function.comp_def,← heym,sub_self,inner_zero_right,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero,add_zero] using hh
  have hu : ∀ᶠ i in atTop,P (y (s i+1)) ≤ ((F0-q/2-C i : ℝ) : EReal) := by
    filter_upwards [hs.tendsto_atTop.eventually_ge_atTop 1] with i hi
    have hh:=hdecr.1 (s i+1) (by omega)
    have hpn:=y_finite h P phi M β x y z hstd.P_proper hseq (s i)
    unfold augLag at hh
    rw [← EReal.coe_toReal hP0 (hstd.P_proper.1 _),
      ← EReal.coe_toReal hpn (hstd.P_proper.1 _)] at hh
    rw [← EReal.coe_toReal hpn (hstd.P_proper.1 _)]
    simp only [sub_self,inner_zero_right,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,neg_zero,add_zero,
      ← EReal.coe_mul,← EReal.coe_neg,← EReal.coe_add,EReal.coe_le_coe_iff] at hh ⊢
    change h (x (s i+1))+(P (y (s i+1))).toReal+(-⟪z (s i+1),M (x (s i+1))-y (s i+1)⟫+β/2*‖M (x (s i+1))-y (s i+1)‖^2) ≤ F0+(-(1/2)*q) at hh
    dsimp [C]
    linarith
  have hb : P ys ≤ ((F0-q/2-h xs : ℝ) : EReal) :=
    hstd.P_closed.isClosed_epigraph.mem_of_tendsto
      (hy1.prodMk_nhds (EReal.tendsto_coe.mpr (tendsto_const_nhds.sub hC))) hu
  have hysfin : P ys ≠ ⊤ := by
    intro hh
    simp only [hh,top_le_iff,EReal.coe_ne_top] at hb
  rw [← EReal.coe_toReal hysfin (hstd.P_proper.1 _),EReal.coe_le_coe_iff] at hb
  rw [← heym,← EReal.coe_toReal hysfin (hstd.P_proper.1 _),
    ← EReal.coe_toReal hP0 (hstd.P_proper.1 _),← EReal.coe_add,← EReal.coe_add,EReal.coe_lt_coe_iff]
  change h xs+(P ys).toReal < F0
  linarith
