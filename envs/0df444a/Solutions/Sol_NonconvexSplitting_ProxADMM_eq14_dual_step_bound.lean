-- Prove2me | solution 1 for NonconvexSplitting.ProxADMM.eq14_dual_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:41:41.402104+00:00
-- url     : https://prove2.me/submissions/b6055950-91da-4d5b-b50c-88665a2a4f9f

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


theorem solution {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
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
