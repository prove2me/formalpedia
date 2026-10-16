-- Prove2me | solution 1 for NAPPAL.Rate.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:39:17.340983+00:00
-- url     : https://prove2.me/submissions/d7dc2777-35e9-4fca-b1ca-3ba8e690b51e

import Definitions.Def_NAPPAL_Rate_Setting
set_option autoImplicit false
open NAPPAL.KL NAPPAL.Rate Filter Topology
open scoped InnerProductSpace
namespace QueeliusNappalDual

theorem quadratic_minimum {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (B : X →L[ℝ] Y) (g : X) (q : Y) (γ : ℝ) (v y : X)
    (hmin : ∀ z, ⟪g,y⟫_ℝ+⟪q,B y⟫_ℝ+γ/2*‖B (y-v)‖^2 ≤
      ⟪g,z⟫_ℝ+⟪q,B z⟫_ℝ+γ/2*‖B (z-v)‖^2) :
    g + ContinuousLinearMap.adjoint B q + γ • ContinuousLinearMap.adjoint B (B (y-v)) = 0 := by
  let z := g + ContinuousLinearMap.adjoint B q + γ • ContinuousLinearMap.adjoint B (B (y-v))
  have hd := (((innerSL ℝ g).hasFDerivAt).add
    (((innerSL ℝ q).comp B).hasFDerivAt)).add
    (((B.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const v)).norm_sq).const_mul (γ/2))
  have hm : IsLocalMin (fun z => ⟪g,z⟫_ℝ+⟪q,B z⟫_ℝ+γ/2*‖B (z-v)‖^2) y :=
    Filter.Eventually.of_forall hmin
  have hh := congrArg (fun f : X →L[ℝ] ℝ => f z) (hd.fderiv.symm.trans hm.fderiv_eq_zero)
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change ⟪z,z⟫_ℝ=0
  calc
    _ = ⟪g,z⟫_ℝ+⟪q,B z⟫_ℝ+γ*⟪B (y-v),B z⟫_ℝ := by
      simp only [z,inner_add_left,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
    _ = 0 := by
      simp only [add_apply,smul_apply,
        ContinuousLinearMap.coe_comp,Function.comp_apply,ContinuousLinearMap.id_apply,
        zero_apply,innerSL_apply_apply,smul_eq_mul,nsmul_eq_mul,id_eq] at hh
      nlinarith only [hh]

theorem rayleigh {n d m : ℕ} (P : Problem n d m) (v : E d) :
    lamMin P * ‖v‖^2 ≤ ‖P.B v‖^2 := by
  by_cases hv : v=0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnorm : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hn]
  have hmem : ‖P.B (‖v‖⁻¹ • v)‖^2 ∈ (fun x => ‖P.B x‖^2) '' Metric.sphere (0 : E d) 1 :=
    ⟨‖v‖⁻¹ • v,by simpa only [Metric.mem_sphere,dist_zero_right] using hnorm,rfl⟩
  have hbb : BddBelow ((fun x : E d => ‖P.B x‖^2) '' Metric.sphere (0 : E d) 1) := by
    refine ⟨0,?_⟩
    rintro _ ⟨x,_,rfl⟩
    positivity
  have hh : lamMin P ≤ ‖P.B (‖v‖⁻¹ • v)‖^2 := csInf_le hbb hmem
  rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hh
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖v‖)
  field_simp [hn] at hm
  nlinarith only [hm]

theorem adjoint_range_bound {n d m : ℕ} (P : Problem n d m) (hlam : 0 ≤ lamMin P)
    (z : E m) (hz : z ∈ Set.range P.B) :
    lamMin P*‖z‖^2 ≤ ‖ContinuousLinearMap.adjoint P.B z‖^2 := by
  obtain ⟨v,rfl⟩ := hz
  by_cases hb : P.B v=0
  · simp [hb]
  have hbpos : 0 < ‖P.B v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
  have hinner : ‖P.B v‖^2 ≤ ‖v‖*‖ContinuousLinearMap.adjoint P.B (P.B v)‖ := by
    rw [P.B.apply_norm_sq_eq_inner_adjoint_right]
    exact real_inner_le_norm v (ContinuousLinearMap.adjoint P.B (P.B v))
  have hs := mul_self_le_mul_self (sq_nonneg ‖P.B v‖) hinner
  have h1 := mul_le_mul_of_nonneg_left hs hlam
  have h2 := mul_le_mul_of_nonneg_right (rayleigh P v)
    (sq_nonneg ‖ContinuousLinearMap.adjoint P.B (P.B v)‖)
  apply (mul_le_mul_iff_right₀ hbpos).mp
  nlinarith only [h1,h2]

theorem dual_identity {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) :
    ContinuousLinearMap.adjoint P.B (p (k+1)) =
      -gradV P (u k) (v k)-gradient P.H (v k)+
        γ • ContinuousLinearMap.adjoint P.B (Theta P (u (k+1))-Theta P (u k)) := by
  have hk := hrun.2.2.2 k
  have hq := quadratic_minimum P.B (gradV P (u k) (v k)+gradient P.H (v k))
    (qseq P γ u v p k) γ (v k) (v (k+1)) hk.2.2.1
  rw [hk.2.2.2]
  simp only [qseq,map_add,map_smul,map_sub] at hq ⊢
  apply sub_eq_zero.mp
  convert hq using 1
  module


theorem dual_step_lower {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ σ LG LH L0 : ℝ) (LOmj : Fin m → ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hA1 : Assumption1 P LG LH L0 LOmj)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) :
    lamMin P*‖p k-p (k+1)‖^2 ≤ ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖^2 := by
  apply adjoint_range_bound P hA1.2.2.2.2.2.1.2.le
  obtain ⟨z,hz⟩ := hA1.2.2.2.2.2.1.1 (Set.mem_range_self (u (k+1)))
  refine ⟨(-γ) • (z+v (k+1)),?_⟩
  rw [(hrun.2.2.2 k).2.2.2]
  simp only [map_smul,map_add,hz]
  module

theorem gradV_bound {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u u' : E n) (v v' : E d) :
    ‖gradV P u v-gradV P u' v'‖ ≤ LG*(‖u-u'‖+‖v-v'‖) := by
  have h := hA1.1.2.2 u v u' v'
  have hnn := mul_nonneg (sq_nonneg LG) (mul_nonneg (norm_nonneg (u-u')) (norm_nonneg (v-v')))
  have hLG := hA1.1.2.1
  have hp : 0 ≤ LG*(‖u-u'‖+‖v-v'‖) := mul_nonneg hLG (add_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith only [h,hnn,hp,norm_nonneg (gradV P u v-gradV P u' v'),sq_nonneg ‖gradU P u v-gradU P u' v'‖]

theorem adjoint_theta_bound {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u u' : E n) :
    ‖ContinuousLinearMap.adjoint P.B (Theta P u-Theta P u')‖ ≤ ‖P.B‖*L0*‖u-u'‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint P.B‖*‖Theta P u-Theta P u'‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖P.B‖*‖Theta P u-Theta P u'‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖P.B‖*(L0*‖u-u'‖) := mul_le_mul_of_nonneg_left (hA1.2.2.2.1.2.2.2 u u') (norm_nonneg _)
    _ = _ := by ring

theorem dual_step_norm {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ σ LG LH L0 : ℝ) (LOmj : Fin m → ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hA1 : Assumption1 P LG LH L0 LOmj)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) (hk : 1 ≤ k) :
    ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖ ≤
      γ*‖P.B‖*L0*‖u k-u (k+1)‖ + (LG+γ*‖P.B‖*L0)*‖u (k-1)-u k‖+
        (LG+LH)*‖v (k-1)-v k‖ := by
  have hprev := dual_identity P K γ σ δ ε u v p hrun (k-1)
  rw [Nat.sub_add_cancel hk] at hprev
  have hnext := dual_identity P K γ σ δ ε u v p hrun k
  let a := gradV P (u k) (v k)-gradV P (u (k-1)) (v (k-1))
  let b := gradient P.H (v k)-gradient P.H (v (k-1))
  let c := γ • ContinuousLinearMap.adjoint P.B (Theta P (u k)-Theta P (u (k+1)))
  let d' := γ • ContinuousLinearMap.adjoint P.B (Theta P (u k)-Theta P (u (k-1)))
  have hid : ContinuousLinearMap.adjoint P.B (p k-p (k+1)) = a+b+c+d' := by
    rw [map_sub,hprev,hnext]
    dsimp [a,b,c,d']
    simp only [map_sub]
    module
  have htri : ‖a+b+c+d'‖ ≤ ‖a‖+‖b‖+‖c‖+‖d'‖ := by
    linarith only [norm_add_le (a+b+c) d',norm_add_le (a+b) c,norm_add_le a b]
  have ha : ‖a‖ ≤ LG*(‖u (k-1)-u k‖+‖v (k-1)-v k‖) := by
    simpa only [a,norm_sub_rev] using gradV_bound P LG LH L0 LOmj hA1 (u k) (u (k-1)) (v k) (v (k-1))
  have hb : ‖b‖ ≤ LH*‖v (k-1)-v k‖ := by
    simpa only [b,norm_sub_rev] using hA1.2.1.2.2 (v k) (v (k-1))
  have hc : ‖c‖ ≤ γ*‖P.B‖*L0*‖u k-u (k+1)‖ := by
    dsimp [c]
    rw [norm_smul,Real.norm_of_nonneg hrun.1.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (adjoint_theta_bound P LG LH L0 LOmj hA1 (u k) (u (k+1))) hrun.1.le
  have hd : ‖d'‖ ≤ γ*‖P.B‖*L0*‖u (k-1)-u k‖ := by
    dsimp [d']
    rw [norm_smul,Real.norm_of_nonneg hrun.1.le]
    simpa only [mul_assoc,norm_sub_rev] using mul_le_mul_of_nonneg_left (adjoint_theta_bound P LG LH L0 LOmj hA1 (u k) (u (k-1))) hrun.1.le
  rw [hid]
  nlinarith only [htri,ha,hb,hc,hd]

end QueeliusNappalDual
#print axioms QueeliusNappalDual.quadratic_minimum
#print axioms QueeliusNappalDual.rayleigh
#print axioms QueeliusNappalDual.adjoint_range_bound
#print axioms QueeliusNappalDual.dual_identity

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Zhu, Zhao and Zhang, arXiv:2007.12219v1, Lemma 4.1.
theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 LK β γ σ : ℝ)
    (LOmj : Fin m → ℝ) (K : NAPPAL.KL.E n → ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hA1 : NAPPAL.KL.Assumption1 P LG LH L0 LOmj)
    (_hA2 : NAPPAL.KL.Assumption2 P K β LK γ LG LH)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) :
    (∀ k : ℕ, ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖^2 ≥
      NAPPAL.KL.lamMin P*‖p k-p (k+1)‖^2) ∧
    (∀ k : ℕ, 1 ≤ k → ContinuousLinearMap.adjoint P.B (p k) =
      -NAPPAL.KL.gradV P (u (k-1)) (v (k-1))-gradient P.H (v (k-1))+
        γ • ContinuousLinearMap.adjoint P.B (NAPPAL.KL.Theta P (u k)-NAPPAL.KL.Theta P (u (k-1)))) ∧
    (∀ k : ℕ, 1 ≤ k → ‖p k-p (k+1)‖^2 ≤
      3*γ^2*‖P.B‖^2*L0^2/NAPPAL.KL.lamMin P*‖u k-u (k+1)‖^2+
      3*(LG+γ*‖P.B‖*L0)^2/NAPPAL.KL.lamMin P*‖u (k-1)-u k‖^2+
      3*(LG+LH)^2/NAPPAL.KL.lamMin P*‖v (k-1)-v k‖^2) := by
  constructor
  · intro k
    exact QueeliusNappalDual.dual_step_lower P K γ σ LG LH L0 LOmj δ ε u v p hA1 hrun k
  constructor
  · intro k hk
    have hh := QueeliusNappalDual.dual_identity P K γ σ δ ε u v p hrun (k-1)
    simpa only [Nat.sub_add_cancel hk] using hh
  · intro k hk
    let a := γ*‖P.B‖*L0*‖u k-u (k+1)‖
    let b := (LG+γ*‖P.B‖*L0)*‖u (k-1)-u k‖
    let c := (LG+LH)*‖v (k-1)-v k‖
    have hnorm := QueeliusNappalDual.dual_step_norm P K γ σ LG LH L0 LOmj δ ε u v p hA1 hrun k hk
    change ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖ ≤ a+b+c at hnorm
    have hquad : ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖^2 ≤ (a+b+c)^2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hnorm
    have hthree : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
      nlinarith only [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
    have hlow := QueeliusNappalDual.dual_step_lower P K γ σ LG LH L0 LOmj δ ε u v p hA1 hrun k
    have hlam := hA1.2.2.2.2.2.1.2
    calc
      _ ≤ (3*(a^2+b^2+c^2))/lamMin P := (le_div_iff₀ hlam).2 (by
        simpa only [mul_comm] using hlow.trans (hquad.trans hthree))
      _ = _ := by
        dsimp [a,b,c]
        field_simp

#print axioms solution
