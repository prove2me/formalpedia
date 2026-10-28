-- Prove2me | solution 2 for NonconvexSplitting.ADMMBounded.theorem2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:57:31.463796+00:00
-- url     : https://prove2.me/submissions/67da3e22-d56b-44e8-8025-899196b5176e

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_IsStationary
import Definitions.Def_NonconvexSplitting_Shared_Assumption1
import Definitions.Def_NonconvexSplitting_Shared_IsProxADMMSeq
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Theorems.Thm_NonconvexSplitting_ProxADMM_eq20_one_step

-- carved verbatim out of submission 5441819e-0556-4689-aa74-9daf341e7b4e, lines 772-860

section
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

private theorem merit_bound {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (t : ℕ) (ht : 1 ≤ t) :
    augLag h P M β (x t) (y t) (z t) +
        ((1 / 2 * wnormSq ((2 / (σ * β * (1 - γ))) • (T1 * T1)) (x t - x (t - 1)) : ℝ) : EReal) ≤
      augLag h P M β (x 1) (y 1) (z 1) +
        ((1 / 2 * wnormSq ((2 / (σ * β * (1 - γ))) • (T1 * T1)) (x 1 - x 0) : ℝ) : EReal) := by
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
    have hh:=NonconvexSplitting.ProxADMM.eq20_one_step h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq t ht
    convert! hh using 2
    congr 1
    dsimp [r,b,R,B]
    rw [Nat.sub_add_cancel ht]
    simp only [wnormSq,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,smul_apply,
      one_apply_eq_self,inner_sub_right,inner_add_right,real_inner_smul_right]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hh:=telescope (fun t => augLag h P M β (x t) (y t) (z t)) r b hstep 1 t (by omega) ht
  have hadd:=add_le_add hh (le_refl (((b (t-1) : ℝ) : EReal)))
  rw [add_assoc,← EReal.coe_add] at hadd
  have hbt : b (t-1)=(1/2)*wnormSq B (x t-x (t-1)) := by simp only [b,Nat.sub_add_cancel ht]
  change augLag h P M β (x t) (y t) (z t)+↑((1/2)*wnormSq B (x t-x (t-1))) ≤
    augLag h P M β (x 1) (y 1) (z 1)+↑(b 0)
  rw [←hbt]
  apply hadd.trans
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.mpr
  have hs:=Finset.sum_nonneg (fun k (_ : k∈Finset.Ico 1 t) => hr k)
  norm_num only [Nat.reduceSub]
  linarith

private theorem dual_bound {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (t : ℕ) (ht : 1 ≤ t) :
    σ * ‖z t‖ ^ 2 ≤
      (1 / γ) * ‖gradient h (x t)‖ ^ 2 +
        (1 / (1 - γ)) * wnormSq (T1 * T1) (x t - x (t - 1)) := by
  have hγ:=hA.2.2.2.2.2.2.1
  have hγ1:=hA.2.2.2.2.2.2.2.1
  let u:=gradient h (x t)
  let v:=gradient phi (x t)-gradient phi (x (t-1))
  have hv : ‖v‖^2≤wnormSq (T1*T1) (x t-x (t-1)) :=
    vector_diff_bound (gradient phi) (hess phi) (T1*T1)
      (fun w => (grad_diff phi hstd.phi_contDiff w).hasFDerivAt)
      (hessian_symmetric phi hstd.phi_contDiff)
      (fun w => (hA.2.2.2.1.2.2 w).2) (x (t-1)) (x t)
  have he : (ContinuousLinearMap.adjoint M) (z t)=u-(-v) := by
    have hh:=x_optimality h P phi M β x y z hstd hseq (t-1)
    rw [Nat.sub_add_cancel ht] at hh
    dsimp [u,v]
    linear_combination (norm := module) -hh
  calc
    σ*‖z t‖^2≤‖(ContinuousLinearMap.adjoint M) (z t)‖^2 := adjoint_lower M σ hA.1.2 _
    _ = ‖u-(-v)‖^2 := by rw [he]
    _ ≤ (1/γ)*‖u‖^2+(1/(1-γ))*‖-v‖^2 := young_norm u (-v) γ hγ hγ1
    _ ≤ _ := by
      rw [norm_neg]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hv (by positivity))

private theorem lower_bound {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (ζ h₀ : ℝ) (hζ : 0 < ζ ∧ ζ < 2 * β * γ)
    (h29 : ∀ x, h₀ ≤ h x - 1 / (σ * ζ) * ‖gradient h x‖ ^ 2)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z)
    (μ : ℝ) (hμ : 0 < μ ∧ μ < 1) (hμβ : ζ / (2 * γ) < (1 - μ) * β)
    (t : ℕ) (ht : 1 ≤ t) :
    ((μ * h (x t) + (1 - μ) * h₀ +
          ((1 - μ) / ζ - 1 / (2 * β * γ)) / σ * ‖gradient h (x t)‖ ^ 2 : ℝ) : EReal) +
        P (y t) +
        ((β / 2 * ‖M (x t) - y t - (1 / β) • z t‖ ^ 2 +
          1 / 2 * wnormSq ((1 / (σ * β * (1 - γ))) • (T1 * T1)) (x t - x (t - 1)) : ℝ) : EReal) ≤
      augLag h P M β (x 1) (y 1) (z 1) +
        ((1 / 2 * wnormSq ((2 / (σ * β * (1 - γ))) • (T1 * T1)) (x 1 - x 0) : ℝ) : EReal) := by
  have hσ:=hA.1.1
  have hβ:=hstd.beta_pos
  have hγ:=hA.2.2.2.2.2.2.1
  have hγ1:=hA.2.2.2.2.2.2.2.1
  have hd:=dual_bound h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq t ht
  have hd' : (1/(2*β))*‖z t‖^2 ≤ (1/(2*σ*β*γ))*‖gradient h (x t)‖^2+
      (1/(2*σ*β*(1-γ)))*wnormSq (T1*T1) (x t-x (t-1)) := by
    have hh:=mul_le_mul_of_nonneg_left hd (show 0≤1/(2*σ*β) by positivity)
    convert! hh using 1 <;> field_simp <;> ring
  have he (d v : EuclideanSpace ℝ (Fin m)) :
      β/2*‖d-(1/β) • v‖^2 = β/2*‖d‖^2-inner ℝ v d+(1/(2*β))*‖v‖^2 := by
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_comm v d]
    field_simp <;> ring
  have hh:=mul_le_mul_of_nonneg_left (h29 (x t)) (show 0≤1-μ by linarith [hμ.2])
  have hreal : μ*h (x t)+(1-μ)*h₀+((1-μ)/ζ-1/(2*β*γ))/σ*‖gradient h (x t)‖^2+
      (β/2*‖M (x t)-y t-(1/β) • z t‖^2+
        1/2*wnormSq ((1/(σ*β*(1-γ))) • (T1*T1)) (x t-x (t-1))) ≤
      h (x t)-inner ℝ (z t) (M (x t)-y t)+β/2*‖M (x t)-y t‖^2+
        1/2*wnormSq ((2/(σ*β*(1-γ))) • (T1*T1)) (x t-x (t-1)) := by
    rw [he]
    simp only [wnormSq,smul_apply,real_inner_smul_right] at hd' ⊢
    simp only [div_eq_mul_inv,mul_inv_rev] at hh hd' ⊢
    ring_nf at hh hd' ⊢
    linarith
  have hfin : P (y t) ≠ ⊤ := by
    obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : t≠0)
    exact y_finite h P phi M β x y z hstd.P_proper hseq k
  have hmerit:=merit_bound h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq t ht
  apply le_trans _ hmerit
  unfold augLag
  rw [←EReal.coe_toReal hfin (hstd.P_proper.1 _)]
  simp only [←EReal.coe_neg,←EReal.coe_mul,←EReal.coe_add,EReal.coe_le_coe_iff]
  linarith

private theorem component_bounds {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (ζ h₀ : ℝ) (hζ : 0 < ζ ∧ ζ < 2 * β * γ)
    (h29 : ∀ x, h₀ ≤ h x - 1 / (σ * ζ) * ‖gradient h x‖ ^ 2)
    (p₀ : ℝ) (hp₀ : ∀ w,(p₀:EReal)≤P w)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z) :
    ∃ A B C : ℝ,∀ t : ℕ,1≤t →
      h (x t)≤A ∧ P (y t)≤(A:EReal) ∧ ‖z t‖≤B ∧ ‖M (x t)-y t-(1/β) • z t‖≤C := by
  have hσ:=hA.1.1
  have hβ:=hstd.beta_pos
  have hγ:=hA.2.2.2.2.2.2.1
  have hγ1:=hA.2.2.2.2.2.2.2.1
  have hq : ζ/(2*γ)<β := (div_lt_iff₀ (by positivity : 0<2*γ)).mpr (by nlinarith [hζ.2])
  obtain ⟨q,hq0,hqβ⟩:=exists_between hq
  have hqp : 0<q := lt_trans (div_pos hζ.1 (by positivity)) hq0
  let μ:=1-q/β
  have hμ : 0<μ ∧ μ<1 := by
    have hdiv : q/β<1 := (div_lt_one hβ).mpr hqβ
    have hdiv0 : 0<q/β := div_pos hqp hβ
    dsimp [μ]
    constructor <;> linarith
  have hμq : (1-μ)*β=q := by dsimp [μ]; field_simp; ring
  have hμβ : ζ/(2*γ)<(1-μ)*β := by rw [hμq]; exact hq0
  let a:=((1-μ)/ζ-1/(2*β*γ))/σ
  let d:=1/(2*σ*β*(1-γ))
  have ha : 0<a := by
    apply div_pos _ hσ
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ (by positivity : 0<2*β*γ) hζ.1).mpr
    have hh:=(div_lt_iff₀ (by positivity : 0<2*γ)).mp hμβ
    nlinarith
  have hd : 0<d := by dsimp [d]; positivity
  let C := h (x 1)-inner ℝ (z 1) (M (x 1)-y 1)+β/2*‖M (x 1)-y 1‖^2+
    (P (y 1)).toReal+1/2*wnormSq ((2/(σ*β*(1-γ))) • (T1*T1)) (x 1-x 0)
  let B:=C-h₀-p₀
  have hfin : ∀ t,1≤t → P (y t)≠⊤ := by
    intro t ht
    obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : t≠0)
    exact y_finite h P phi M β x y z hstd.P_proper hseq k
  have hinit : augLag h P M β (x 1) (y 1) (z 1)+
      ((1/2*wnormSq ((2/(σ*β*(1-γ))) • (T1*T1)) (x 1-x 0) : ℝ) : EReal) = (C:EReal) := by
    unfold augLag
    rw [←EReal.coe_toReal (hfin 1 (by omega)) (hstd.P_proper.1 _)]
    simp only [←EReal.coe_add]
    congr 1
    dsimp [C]
    ring
  have hlow : ∀ t,h₀≤h (x t) := by
    intro t
    have hh:=h29 (x t)
    have hn:=mul_nonneg (show 0≤1/(σ*ζ) by have := hζ.1; positivity) (sq_nonneg ‖gradient h (x t)‖)
    linarith
  have hW : ∀ v,0≤wnormSq (T1*T1) v := by
    intro v
    have hp:=(ContinuousLinearMap.nonneg_iff_isPositive T1).mp (hA.2.2.2.1.1.trans hA.2.2.2.1.2.1)
    have he : wnormSq (T1*T1) v=‖T1 v‖^2 := by
      dsimp [wnormSq]
      change inner ℝ v (T1 (T1 v))=_
      exact (hp.isSymmetric v (T1 v)).symm.trans (real_inner_self_eq_norm_sq _)
    rw [he]
    exact sq_nonneg _
  have hline : ∀ t,1≤t → μ*(h (x t)-h₀)+a*‖gradient h (x t)‖^2+
      ((P (y t)).toReal-p₀)+(β/2)*‖M (x t)-y t-(1/β) • z t‖^2+
      d*wnormSq (T1*T1) (x t-x (t-1))≤B := by
    intro t ht
    have hh:=lower_bound h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA ζ h₀ hζ h29 x y z hseq μ hμ hμβ t ht
    rw [hinit,←EReal.coe_toReal (hfin t ht) (hstd.P_proper.1 _)] at hh
    simp only [←EReal.coe_add,EReal.coe_le_coe_iff] at hh
    dsimp [a,d,B]
    simp only [wnormSq,smul_apply,real_inner_smul_right] at hh ⊢
    simp only [div_eq_mul_inv,mul_inv_rev] at hh ⊢
    ring_nf at hh ⊢
    linarith
  refine ⟨max (h₀+B/μ) (p₀+B),((1/γ)*(B/a)+(1/(1-γ))*(B/d))/σ+1,B/(β/2)+1,?_⟩
  intro t ht
  have hh:=hline t ht
  have hh0:=mul_nonneg hμ.1.le (sub_nonneg.mpr (hlow t))
  have hg0:=mul_nonneg ha.le (sq_nonneg ‖gradient h (x t)‖)
  have hr0:=mul_nonneg (show 0≤β/2 by positivity) (sq_nonneg ‖M (x t)-y t-(1/β) • z t‖)
  have hW0:=mul_nonneg hd.le (hW (x t-x (t-1)))
  have hp0 : p₀≤(P (y t)).toReal := by
    have hh:=hp₀ (y t)
    rw [←EReal.coe_toReal (hfin t ht) (hstd.P_proper.1 _),EReal.coe_le_coe_iff] at hh
    exact hh
  have hgB : ‖gradient h (x t)‖^2≤B/a := (le_div_iff₀ ha).mpr (by nlinarith)
  have hWB : wnormSq (T1*T1) (x t-x (t-1))≤B/d := (le_div_iff₀ hd).mpr (by nlinarith)
  have hrB : ‖M (x t)-y t-(1/β) • z t‖^2≤B/(β/2) := (le_div_iff₀ (by positivity : 0<β/2)).mpr (by nlinarith)
  have hzB : ‖z t‖^2≤((1/γ)*(B/a)+(1/(1-γ))*(B/d))/σ := by
    apply (le_div_iff₀ hσ).mpr
    have hz:=dual_bound h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA x y z hseq t ht
    have h1:=mul_le_mul_of_nonneg_left hgB (show 0≤1/γ by positivity)
    have h2:=mul_le_mul_of_nonneg_left hWB (show 0≤1/(1-γ) by positivity)
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · apply le_trans _ (le_max_left _ _)
    have hh' : h (x t)-h₀≤B/μ := (le_div_iff₀ hμ.1).mpr (by nlinarith)
    linarith
  · rw [←EReal.coe_toReal (hfin t ht) (hstd.P_proper.1 _),EReal.coe_le_coe_iff]
    apply le_trans _ (le_max_right _ _)
    linarith
  · nlinarith only [hzB,sq_nonneg (‖z t‖-1)]
  · nlinarith only [hrB,sq_nonneg (‖M (x t)-y t-(1/β) • z t‖-1)]

end

section
open Filter Topology NonconvexSplitting.Shared
open scoped RealInnerProductSpace
open Set

private theorem coercive_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : E → EReal) (hlsc : LowerSemicontinuous P) (hbot : ∀ x,P x≠⊥)
    (hco : ∀ r : ℝ,∃ R : ℝ,∀ w : E,R<‖w‖ → (r:EReal)<P w) :
    ∃ c : ℝ,∀ w : E,(c:EReal)≤P w := by
  obtain ⟨R,hR⟩:=hco 0
  let S:=Metric.closedBall (0:E) (max R 0)
  have hS : S.Nonempty := ⟨0,by simp [S]⟩
  obtain ⟨v,hv,hmin⟩:=LowerSemicontinuousOn.exists_isMinOn hS (isCompact_closedBall _ _) (hlsc.lowerSemicontinuousOn S)
  obtain ⟨c,_,hc⟩:=EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr (hbot v))
  refine ⟨min c 0,?_⟩
  intro w
  by_cases hw : w∈S
  · have hh : ((min c 0 : ℝ) : EReal) ≤ (c:EReal) := EReal.coe_le_coe_iff.mpr (min_le_left _ _)
    exact hh.trans (hc.le.trans (hmin hw))
  · have hnorm : R<‖w‖ := by
      have hn : max R 0<‖w‖ := by simpa only [S,Metric.mem_closedBall,dist_zero_right,not_le] using hw
      exact lt_of_le_of_lt (le_max_left _ _) hn
    have hh : ((min c 0 : ℝ) : EReal) ≤ (0:EReal) := by exact_mod_cast min_le_right c 0
    exact hh.trans (hR w hnorm).le

theorem solution {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (phi : EuclideanSpace ℝ (Fin n) → ℝ) (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (hstd : StandingAssumptions h P phi β)
    (σ δ γ : ℝ) (Q1 Q2 T1 T2 Q3 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Assumption1 h phi M β σ Q1 Q2 T1 T2 δ Q3 γ)
    (ζ h₀ : ℝ) (hζ : 0 < ζ ∧ ζ < 2 * β * γ)
    (h29 : ∀ x, h₀ ≤ h x - 1 / (σ * ζ) * ‖gradient h x‖ ^ 2)
    (hcase :
      (Function.Bijective M ∧
          ∀ r : ℝ, ∃ R : ℝ, ∀ w : EuclideanSpace ℝ (Fin m), R < ‖w‖ → (r : EReal) < P w) ∨
        ((∀ r : ℝ, ∃ R : ℝ, ∀ v : EuclideanSpace ℝ (Fin n), R < ‖v‖ → r < h v) ∧
          ∃ c : ℝ, ∀ w : EuclideanSpace ℝ (Fin m), (c : EReal) ≤ P w))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (hseq : IsProxADMMSeq h P phi M β x y z) :
    ∃ R : ℝ, ∀ t : ℕ, ‖x t‖ ≤ R ∧ ‖y t‖ ≤ R ∧ ‖z t‖ ≤ R := by
  have hpbelow : ∃ p₀ : ℝ,∀ w,(p₀:EReal)≤P w := by
    rcases hcase with hc | hc
    · exact coercive_lower P hstd.P_closed hstd.P_proper.1 hc.2
    · exact hc.2
  obtain ⟨p₀,hp₀⟩:=hpbelow
  obtain ⟨A,B,C,hbounds⟩:=component_bounds h P phi M β hstd σ δ γ Q1 Q2 T1 T2 Q3 hA ζ h₀ hζ h29 p₀ hp₀ x y z hseq
  have hβ:=hstd.beta_pos
  let D:=C+(1/β)*B
  have hres : ∀ t,1≤t → ‖M (x t)-y t‖≤D := by
    intro t ht
    have hh:=norm_add_le (M (x t)-y t-(1/β) • z t) ((1/β) • z t)
    rw [sub_add_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos zero_lt_one hβ)] at hh
    have hb:=mul_le_mul_of_nonneg_left (hbounds t ht).2.2.1 (show 0≤1/β by positivity)
    dsimp [D]
    linarith [(hbounds t ht).2.2.2]
  have hxy : ∃ Rx Ry : ℝ,∀ t,1≤t → ‖x t‖≤Rx ∧ ‖y t‖≤Ry := by
    rcases hcase with hc | hc
    · obtain ⟨Ry,hRy⟩:=hc.2 A
      have hy : ∀ t,1≤t → ‖y t‖≤Ry := by
        intro t ht
        by_contra! hn
        exact not_lt_of_ge (hbounds t ht).2.1 (hRy (y t) hn)
      let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
        (LinearEquiv.ofBijective M.toLinearMap hc.1).toContinuousLinearEquiv
      refine ⟨‖e.symm.toContinuousLinearMap‖*(D+Ry),Ry,?_⟩
      intro t ht
      refine ⟨?_,hy t ht⟩
      have hm : ‖M (x t)‖≤D+Ry := by
        have hh:=norm_add_le (M (x t)-y t) (y t)
        rw [sub_add_cancel] at hh
        linarith [hres t ht,hy t ht]
      have hi:=e.symm.toContinuousLinearMap.le_opNorm (M (x t))
      have he : e.symm (M (x t))=x t := e.symm_apply_apply (x t)
      change ‖e.symm (M (x t))‖≤_ at hi
      rw [he] at hi
      exact hi.trans (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
    · obtain ⟨Rx,hRx⟩:=hc.1 A
      have hx : ∀ t,1≤t → ‖x t‖≤Rx := by
        intro t ht
        by_contra! hn
        exact not_lt_of_ge (hbounds t ht).1 (hRx (x t) hn)
      refine ⟨Rx,‖M‖*Rx+D,?_⟩
      intro t ht
      refine ⟨hx t ht,?_⟩
      have hm : ‖M (x t)‖≤‖M‖*Rx := (M.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hx t ht) (norm_nonneg _))
      have hh:=norm_sub_le (M (x t)) (M (x t)-y t)
      rw [sub_sub_cancel] at hh
      linarith [hres t ht]
  obtain ⟨Rx,Ry,hxy⟩:=hxy
  refine ⟨|Rx|+|Ry|+|B|+‖x 0‖+‖y 0‖+‖z 0‖,?_⟩
  intro t
  have hRxa:=abs_nonneg Rx
  have hRya:=abs_nonneg Ry
  have hBa:=abs_nonneg B
  have hx0:=norm_nonneg (x 0)
  have hy0:=norm_nonneg (y 0)
  have hz0:=norm_nonneg (z 0)
  by_cases ht : t=0
  · subst t
    constructor
    · nlinarith
    constructor <;> nlinarith
  · have ht' : 1≤t := by omega
    have hxt:=(hxy t ht').1
    have hyt:=(hxy t ht').2
    have hzt:=(hbounds t ht').2.2.1
    have hRx:=le_abs_self Rx
    have hRy:=le_abs_self Ry
    have hB:=le_abs_self B
    constructor
    · nlinarith
    constructor <;> nlinarith

end
