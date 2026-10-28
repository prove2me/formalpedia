-- Prove2me | solution 1 for OAI.ElasticityODE.fundamental_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:20:06.091005+00:00
-- url     : https://prove2.me/submissions/776f77aa-16f2-4234-8ff5-93f381ae70a3

import Mathlib
import Definitions.Def_OAIQ6El005

section
-- module Solutions.OAIQ6_Elast.Elasticity_ODE
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma extend_apply (f : C(Time,F)) (t : Time) : extend f t=f t := by
  exact ContinuousMap.IccExtendCM_of_mem t.property
lemma weightedCLM_norm (k : ℝ) (hk : 0<k) : ‖weightedCLM (F := F) k hk‖ ≤ k⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hk.le) (fun f => weighted_bound k hk f)

end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma pointwiseCLM_apply (b : C(Time,F →L[ℝ] F)) (f : C(Time,F)) (t : Time) :
    pointwiseCLM b f t=b t (f t) := rfl
omit [CompleteSpace F] in
lemma pointwiseCLM_norm (b : C(Time,F →L[ℝ] F)) : ‖pointwiseCLM b‖ ≤ ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b) (pointwise_bound b)

lemma volterra_unit (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F)) (hb : ‖b‖<k) :
    IsUnit (1-weightedCLM k hk*pointwiseCLM b) := by
  apply isUnit_one_sub_of_norm_lt_one (R := C(Time,F) →L[ℝ] C(Time,F))
  calc
    ‖weightedCLM k hk*pointwiseCLM b‖ ≤ ‖weightedCLM (F := F) k hk‖*‖pointwiseCLM b‖ := norm_mul_le (weightedCLM (F := F) k hk) (pointwiseCLM b)
    _ ≤ k⁻¹*‖b‖ := mul_le_mul (weightedCLM_norm k hk) (pointwiseCLM_norm b)
      (norm_nonneg (pointwiseCLM b)) (inv_nonneg.mpr hk.le)
    _ < 1 := by rw [mul_comm,← div_eq_mul_inv]; exact (div_lt_one hk).mpr hb

lemma evolution_integral (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F)) (hb : ‖b‖<k)
    (y : F) (t : Time) :
    evolution k hk b y t=y+∫ s in (0:ℝ)..(t:ℝ), extend b s (extend (evolution k hk b y) s) := by
  let q : C(Time,F) := expScale (-k) (ContinuousMap.const Time y)
  let w : C(Time,F) := (Ring.inverse ((1 : C(Time,F) →L[ℝ] C(Time,F))-weightedCLM k hk*pointwiseCLM b) : C(Time,F) →L[ℝ] C(Time,F)) q
  have hw : w-weightedCLM k hk (pointwiseCLM b w)=q := by
    have h := congrArg (fun L : C(Time,F) →L[ℝ] C(Time,F) => L q)
      (Ring.mul_inverse_cancel _ (volterra_unit k hk b hb))
    simpa only [mul_apply_eq_comp,sub_apply,one_apply_eq_self] using h
  have hwt := congrArg (fun f : C(Time,F) => f t) hw
  change w t-Real.exp (-k*(t:ℝ)) •
    (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend (pointwiseCLM b w) s)=
      Real.exp (-k*(t:ℝ)) • y at hwt
  have he : Real.exp (k*(t:ℝ))*Real.exp (-k*(t:ℝ))=1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hscaled := congrArg (fun z : F => Real.exp (k*(t:ℝ)) • z) hwt
  rw [smul_sub,smul_smul,he,one_smul,smul_smul,he,one_smul] at hscaled
  have hint : (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend (pointwiseCLM b w) s)=
      ∫ s in (0:ℝ)..(t:ℝ), extend b s (extend (evolution k hk b y) s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsi : s∈Icc (0:ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hs
      exact ⟨hs.1,hs.2.trans t.property.2⟩
    have hs' : s=(⟨s,hsi⟩ : Time) := rfl
    change Real.exp (k*s) • extend (pointwiseCLM b w) s =
      extend b s (extend (evolution k hk b y) s)
    rw [hs',extend_apply,extend_apply,extend_apply,pointwiseCLM_apply]
    change Real.exp (k*s) • b ⟨s,hsi⟩ (w ⟨s,hsi⟩)=
      b ⟨s,hsi⟩ (Real.exp (k*s) • w ⟨s,hsi⟩)
    exact (map_smul (b ⟨s,hsi⟩) (Real.exp (k*s)) (w ⟨s,hsi⟩)).symm
  rw [hint] at hscaled
  change Real.exp (k*(t:ℝ)) • w t=_
  exact sub_eq_iff_eq_add.mp hscaled

end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Integral solutions are genuine classical solutions, including one-sided
endpoint derivatives. -/
lemma evolution_hasDerivWithinAt (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F))
    (hb : ‖b‖<k) (y : F) (t : Time) :
    HasDerivWithinAt (extend (evolution k hk b y)) (b t (evolution k hk b y t)) Time t := by
  let u := evolution k hk b y
  have hc : Continuous (fun s : ℝ => extend b s (extend u s)) :=
    (extend b).continuous.clm_apply (extend u).continuous
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 (t:ℝ))
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add y
  have he : ∀ s∈Time, y+(∫ r in (0:ℝ)..s, extend b r (extend u r))=extend u s := by
    intro s hs
    change _=extend u (⟨s,hs⟩ : Time)
    rw [extend_apply]
    exact (evolution_integral k hk b hb y ⟨s,hs⟩).symm
  have ht := h.hasDerivWithinAt.congr_of_mem (fun s hs => (he s hs).symm) t.property
  simpa only [extend_apply] using ht

lemma evolution_initial (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F))
    (hb : ‖b‖<k) (y : F) : evolution k hk b y ⟨0,by simp [Time]⟩=y := by
  simpa only [intervalIntegral.integral_same,add_zero] using
    evolution_integral k hk b hb y ⟨0,by simp [Time]⟩

omit [CompleteSpace F] in
/-- Uniqueness on the entire time interval, with no smallness hypothesis. -/
lemma linear_ode_unique (b : C(Time,F →L[ℝ] F)) (u v : C(Time,F))
    (hu : ∀ t : Time, HasDerivWithinAt (extend u) (b t (u t)) Time t)
    (hv : ∀ t : Time, HasDerivWithinAt (extend v) (b t (v t)) Time t)
    (hzero : u ⟨0,by simp [Time]⟩=v ⟨0,by simp [Time]⟩) : u=v := by
  have hLip (t : ℝ) : LipschitzWith ‖b‖₊ (extend b t) :=
    (extend b t).lipschitz.weaken (by exact_mod_cast extend_norm_le b t)
  have he := ODE_solution_unique_of_mem_Icc_right
    (v := fun t x => extend b t x) (s := fun _ => univ) (K := ‖b‖₊)
    (fun t _ => (hLip t).lipschitzOnWith) (extend u).continuous.continuousOn
    (fun t ht => by
      have h := (hu ⟨t,mem_Icc_of_Ico ht⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
      simpa only [extend_apply b ⟨t,mem_Icc_of_Ico ht⟩,
        extend_apply u ⟨t,mem_Icc_of_Ico ht⟩] using h)
    (fun _ _ => mem_univ _) (extend v).continuous.continuousOn
    (fun t ht => by
      have h := (hv ⟨t,mem_Icc_of_Ico ht⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
      simpa only [extend_apply b ⟨t,mem_Icc_of_Ico ht⟩,
        extend_apply v ⟨t,mem_Icc_of_Ico ht⟩] using h)
    (fun _ _ => mem_univ _) (by
      change extend u (⟨0,by simp [Time]⟩ : Time)=extend v (⟨0,by simp [Time]⟩ : Time)
      simpa only [extend_apply u ⟨0,by simp [Time]⟩,extend_apply v ⟨0,by simp [Time]⟩] using hzero)
  ext t
  have h := he t.property
  simpa only [extend_apply] using h

lemma flow_hasDerivWithinAt (b : C(Time,F →L[ℝ] F)) (y : F) (t : Time) :
    HasDerivWithinAt (extend (flow b y)) (b t (flow b y t)) Time t :=
  evolution_hasDerivWithinAt _ _ b (by linarith) y t
lemma flow_initial (b : C(Time,F →L[ℝ] F)) (y : F) :
    flow b y ⟨0,by simp [Time]⟩=y := evolution_initial _ _ b (by linarith) y
end ElasticityODE

end
end
section
noncomputable section
open Set
namespace ElasticityODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
lemma fundamental_deriv (b : C(Time,R)) (t : Time) :
    HasDerivWithinAt (extend (fundamental b)) (b t*fundamental b t) Time t :=
  flow_hasDerivWithinAt (leftCoeff b) 1 t
lemma reciprocal_deriv (b : C(Time,R)) (t : Time) :
    HasDerivWithinAt (extend (reciprocal b)) (-(reciprocal b t*b t)) Time t :=
  flow_hasDerivWithinAt (-rightCoeff b) 1 t
lemma fundamental_initial (b : C(Time,R)) : fundamental b ⟨0,by simp [Time]⟩=1 :=
  flow_initial (leftCoeff b) 1
lemma reciprocal_initial (b : C(Time,R)) : reciprocal b ⟨0,by simp [Time]⟩=1 :=
  flow_initial (-rightCoeff b) 1
lemma reciprocal_mul_fundamental (b : C(Time,R)) (t : Time) :
    reciprocal b t*fundamental b t=1 := by
  let f : ℝ → R := fun s => extend (reciprocal b) s*extend (fundamental b) s
  have hder (s : Time) : HasDerivWithinAt f 0 Time s := by
    have h := (reciprocal_deriv b s).mul (fundamental_deriv b s)
    simpa only [f,Pi.mul_def,extend_apply,neg_mul,mul_assoc,neg_add_cancel] using h
  have he := constant_of_has_deriv_right_zero
    ((extend (reciprocal b)).continuous.mul (extend (fundamental b)).continuous).continuousOn
    (fun s hs => (hder ⟨s,mem_Icc_of_Ico hs⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)) t t.property
  change f t=f (⟨0,by simp [Time]⟩ : Time) at he
  have hz : f (⟨0,by simp [Time]⟩ : Time)=1 := by
    change extend (reciprocal b) (⟨0,by simp [Time]⟩ : Time)*
      extend (fundamental b) (⟨0,by simp [Time]⟩ : Time)=1
    rw [extend_apply,extend_apply,reciprocal_initial,fundamental_initial,mul_one]
  have hh := he.trans hz
  simpa only [f,extend_apply] using hh
lemma fundamental_mul_reciprocal (b : C(Time,R)) (t : Time) :
    fundamental b t*reciprocal b t=1 := by
  let a := leftCoeff b-rightCoeff b
  let u := fundamental b*reciprocal b
  let v : C(Time,R) := ContinuousMap.const Time 1
  have hu (s : Time) : HasDerivWithinAt (extend u) (a s (u s)) Time s := by
    have h := (fundamental_deriv b s).mul (reciprocal_deriv b s)
    have hh : HasDerivWithinAt (fun x => extend (fundamental b) x*extend (reciprocal b) x)
        (b s*(fundamental b s*reciprocal b s)-(fundamental b s*reciprocal b s)*b s) Time s := by
      simpa only [Pi.mul_def,extend_apply,mul_neg,mul_assoc,sub_eq_add_neg] using h
    exact hh.congr_of_mem (fun x hx => by
      change extend u (⟨x,hx⟩ : Time)=_
      rw [extend_apply]
      change fundamental b ⟨x,hx⟩*reciprocal b ⟨x,hx⟩=_
      rw [← extend_apply (fundamental b) ⟨x,hx⟩,← extend_apply (reciprocal b) ⟨x,hx⟩]) s.property
  have hv (s : Time) : HasDerivWithinAt (extend v) (a s (v s)) Time s := by
    have h : a s (v s)=0 := by change b s*1-1*b s=0; simp
    rw [h]
    have hh : HasDerivWithinAt (fun _ : ℝ => (1:R)) 0 Time s := hasDerivWithinAt_const _ _ _
    exact hh.congr_of_mem (fun x hx => by
      change extend v (⟨x,hx⟩ : Time)=1
      rw [extend_apply]
      rfl) s.property
  have hi : u ⟨0,by simp [Time]⟩=v ⟨0,by simp [Time]⟩ := by
    change fundamental b ⟨0,by simp [Time]⟩*reciprocal b ⟨0,by simp [Time]⟩=1
    rw [fundamental_initial,reciprocal_initial,mul_one]
  exact congrArg (fun f : C(Time,R) => f t) (linear_ode_unique a u v hu hv hi)
theorem fundamental_isUnit_oai (b : C(Time,R)) (t : Time) : IsUnit (fundamental b t) :=
  ⟨⟨fundamental b t,reciprocal b t,fundamental_mul_reciprocal b t,reciprocal_mul_fundamental b t⟩,rfl⟩
end ElasticityODE

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityODE.fundamental_isUnit_oai.{u_1} := @OAI.ElasticityODE.fundamental_isUnit_oai.{u_1}
