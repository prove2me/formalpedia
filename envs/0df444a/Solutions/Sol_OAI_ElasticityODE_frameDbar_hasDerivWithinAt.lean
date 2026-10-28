-- Prove2me | solution 1 for OAI.ElasticityODE.frameDbar_hasDerivWithinAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:19:20.805743+00:00
-- url     : https://prove2.me/submissions/3160869f-54b9-48c2-bcbb-cd86917ef64b

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

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
/-- Strong smooth parameter dependence of the entire continuous trajectory. -/
theorem evolution_contDiffAt (k : ℝ) (hk : 0<k)
    (b : P → C(Time,F →L[ℝ] F)) (y : P → F) (p : P)
    (hb : ContDiffAt ℝ (⊤ : ℕ∞) b p) (hy : ContDiffAt ℝ (⊤ : ℕ∞) y p)
    (hsmall : ‖b p‖<k) : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => evolution k hk (b p) (y p)) p := by
  have hB : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => pointwiseCLM (b q)) p := by
    exact (ContinuousLinearMap.contDiff (E := C(Time,F →L[ℝ] F))
      (F := C(Time,F) →L[ℝ] C(Time,F)) (pointwiseCLM (F := F))).contDiffAt.comp p hb
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => (1 : C(Time,F) →L[ℝ] C(Time,F))-
      weightedCLM k hk*pointwiseCLM (b p)) p :=
    by
      apply ContDiffAt.sub contDiffAt_const
      exact ContDiffAt.mul (𝕜 := ℝ) (f := fun _ : P => weightedCLM (F := F) k hk)
        (g := fun q => pointwiseCLM (b q)) contDiffAt_const hB
  obtain ⟨a,ha⟩ := volterra_unit k hk (b p) hsmall
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) Ring.inverse
      ((1 : C(Time,F) →L[ℝ] C(Time,F))-weightedCLM k hk*pointwiseCLM (b p)) := by
    rw [← ha]
    exact contDiffAt_ringInverse (R := C(Time,F) →L[ℝ] C(Time,F)) ℝ a
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => expScale (-k) (ContinuousMap.const Time (y p))) p :=
    (expScale (F := F) (-k)).contDiff.contDiffAt.comp p ((ContinuousLinearMap.contDiff (E := F) (F := C(Time,F))
      (ContinuousLinearMap.const ℝ Time)).contDiffAt.comp p hy)
  have hic := hi.comp p hA
  exact (expScale (F := F) k).contDiff.contDiffAt.comp p (hic.clm_apply hq)
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
lemma flow_eq_evolution (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F))
    (hb : ‖b‖<k) (y : F) : flow b y=evolution k hk b y := by
  apply linear_ode_unique b _ _ (flow_hasDerivWithinAt b y) (evolution_hasDerivWithinAt k hk b hb y)
  rw [flow_initial,evolution_initial k hk b hb y]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
theorem flow_contDiff (b : P → C(Time,F →L[ℝ] F)) (y : P → F)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hy : ContDiff ℝ (⊤ : ℕ∞) y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => flow (b p) (y p)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let k : ℝ := ‖b p‖+1
  have hk : 0<k := by dsimp [k]; positivity
  have hsmall : ‖b p‖<k := by dsimp [k]; linarith
  apply (evolution_contDiffAt k hk b y p hb.contDiffAt hy.contDiffAt hsmall).congr_of_eventuallyEq
  have hbc : ContinuousAt b p := hb.continuous.continuousAt
  have hn : ContinuousAt (fun q => ‖b q‖) p := ContinuousAt.norm (f := b) hbc
  filter_upwards [hn.eventually_lt_const hsmall] with q hq
  exact flow_eq_evolution k hk (b q) hq (y q)
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma integral_curve_hasDerivWithinAt (u f : C(Time,F)) (y : F)
    (he : u=ContinuousMap.const Time y+integrateCLM f) (t : Time) :
    HasDerivWithinAt (extend u) (f t) Time t := by
  have hc := (extend f).continuous
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 (t:ℝ))
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add y
  apply (h.hasDerivWithinAt.congr_of_mem ?_ t.property).congr_deriv (extend_apply f t)
  intro s hs
  change extend u (⟨s,hs⟩ : Time)=_
  rw [extend_apply,he]
  rfl
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma integral_family_variation (b : P → C(Time,F →L[ℝ] F)) (u : P → C(Time,F)) (y : P → F)
    (p : P) (b' : P →L[ℝ] C(Time,F →L[ℝ] F)) (u' : P →L[ℝ] C(Time,F)) (y' : P →L[ℝ] F)
    (hb : HasFDerivAt b b' p) (hu : HasFDerivAt u u' p) (hy : HasFDerivAt y y' p)
    (he : ∀ q, u q=ContinuousMap.const Time (y q)+integrateCLM (pointwiseCLM (b q) (u q))) (v : P) :
    u' v=ContinuousMap.const Time (y' v)+
      integrateCLM (pointwiseCLM (b p) (u' v)+pointwiseCLM (b' v) (u p)) := by
  have hB : HasFDerivAt (fun q => pointwiseCLM (b q))
      ((pointwiseCLM (F := F)).comp b') p := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (f := b) (g := pointwiseCLM (F := F))
      (f' := b') (g' := pointwiseCLM (F := F)) p
      (pointwiseCLM (F := F)).hasFDerivAt hb
  have hprod := hB.clm_apply hu
  have hI := (integrateCLM (F := F)).hasFDerivAt.comp p hprod
  have hyc := (ContinuousLinearMap.const ℝ Time : F →L[ℝ] C(Time,F)).hasFDerivAt.comp p hy
  have hall := (hyc.add hI).congr_of_eventuallyEq (Filter.Eventually.of_forall he)
  have hd := hu.unique hall
  have h := congrArg (fun L : P →L[ℝ] C(Time,F) => L v) hd
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply] at h
  exact h

lemma integral_family_variation_hasDerivWithinAt
    (b : P → C(Time,F →L[ℝ] F)) (u : P → C(Time,F)) (y : P → F)
    (p : P) (b' : P →L[ℝ] C(Time,F →L[ℝ] F)) (u' : P →L[ℝ] C(Time,F)) (y' : P →L[ℝ] F)
    (hb : HasFDerivAt b b' p) (hu : HasFDerivAt u u' p) (hy : HasFDerivAt y y' p)
    (he : ∀ q, u q=ContinuousMap.const Time (y q)+integrateCLM (pointwiseCLM (b q) (u q)))
    (v : P) (t : Time) :
    HasDerivWithinAt (extend (u' v)) (b p t (u' v t)+b' v t (u p t)) Time t := by
  have h := integral_curve_hasDerivWithinAt (u' v) _ (y' v)
    (integral_family_variation b u y p b' u' y' hb hu hy he v) t
  simpa only [ContinuousMap.add_apply,pointwiseCLM_apply] using h
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
lemma flow_integral_curve (b : C(Time,F →L[ℝ] F)) (y : F) :
    flow b y=ContinuousMap.const Time y+integrateCLM (pointwiseCLM b (flow b y)) := by
  ext t
  have h := evolution_integral (‖b‖+1) (by positivity) b (by linarith) y t
  change flow b y t=y+∫ s in (0:ℝ)..(t:ℝ), extend b s (extend (flow b y) s) at h
  rw [h]
  rfl
variable {R P : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
omit [CompleteSpace R] in
lemma leftCoeffCLM_eq (b : C(Time,R)) : leftCoeffCLM b=leftCoeff b := rfl
lemma fundamental_contDiff (b : P → C(Time,R)) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => fundamental (b p)) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (leftCoeffCLM (R := R)) :=
    ContinuousLinearMap.contDiff (E := C(Time,R)) (F := C(Time,R →L[ℝ] R)) _
  have hcomp := hL.comp hb
  have hcoeff : ContDiff ℝ (⊤ : ℕ∞) (fun p => leftCoeff (b p)) := by
    simpa only [Function.comp_def,leftCoeffCLM_eq] using hcomp
  exact flow_contDiff (fun p => leftCoeff (b p)) (fun _ => 1) hcoeff contDiff_const
lemma fundamental_variation_hasDerivWithinAt (b : P → C(Time,R))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p v : P) (t : Time) :
    HasDerivWithinAt (extend (fderiv ℝ (fun p => fundamental (b p)) p v))
      (b p t*(fderiv ℝ (fun p => fundamental (b p)) p v t)+
        fderiv ℝ b p v t*fundamental (b p) t) Time t := by
  have hL : HasFDerivAt (leftCoeffCLM (R := R)) (leftCoeffCLM (R := R)) (b p) :=
    ContinuousLinearMap.hasFDerivAt _
  have hc := HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := C(Time,R))
    (G := C(Time,R →L[ℝ] R)) (f := b) (g := leftCoeffCLM (R := R))
    (f' := fderiv ℝ b p) (g' := leftCoeffCLM (R := R)) p hL
    (hb.differentiable (by simp) p).hasFDerivAt
  have hb' : HasFDerivAt (fun q => leftCoeff (b q))
      ((leftCoeffCLM (R := R)).comp (fderiv ℝ b p)) p := by
    simpa only [Function.comp_def,leftCoeffCLM_eq] using hc
  have hu := ((fundamental_contDiff b hb).differentiable (by simp) p).hasFDerivAt
  have hy : HasFDerivAt (fun _ : P => (1:R)) 0 p := hasFDerivAt_const (𝕜 := ℝ) _ _
  exact integral_family_variation_hasDerivWithinAt (fun q => leftCoeff (b q))
    (fun q => fundamental (b q)) (fun _ => 1) p _ _ _ hb' hu hy
    (fun q => flow_integral_curve (leftCoeff (b q)) 1) v t
end ElasticityODE

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Homotopy
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
namespace ElasticityODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
lemma frameDbar_hasDerivWithinAt_oai (b : ℂ → C(Time,R))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p : ℂ) (t : Time) :
    HasDerivWithinAt (extend (frameDbar b p))
      (b p t*frameDbar b p t+coefficientDbar b p t*fundamental (b p) t) Time t := by
  have h1 := fundamental_variation_hasDerivWithinAt b hb p 1 t
  have hi := (fundamental_variation_hasDerivWithinAt b hb p Complex.I t).const_smul Complex.I
  have h := h1.add hi
  have he :
      b p t*fderiv ℝ (fun p => fundamental (b p)) p 1 t+fderiv ℝ b p 1 t*fundamental (b p) t+
        Complex.I • (b p t*fderiv ℝ (fun p => fundamental (b p)) p Complex.I t+
          fderiv ℝ b p Complex.I t*fundamental (b p) t)=
      b p t*frameDbar b p t+coefficientDbar b p t*fundamental (b p) t := by
    simp only [frameDbar,coefficientDbar,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      smul_add,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
    abel
  rw [he] at h
  exact h.congr_of_mem (fun x hx => by
    change extend (frameDbar b p) (⟨x,hx⟩ : Time)=_
    rw [extend_apply]
    change _=extend (fderiv ℝ (fun p => fundamental (b p)) p 1) (⟨x,hx⟩ : Time)+
      Complex.I • extend (fderiv ℝ (fun p => fundamental (b p)) p Complex.I) (⟨x,hx⟩ : Time)
    rw [extend_apply,extend_apply]
    rfl) t.property
end ElasticityODE

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityODE.frameDbar_hasDerivWithinAt_oai.{u_1} := @OAI.ElasticityODE.frameDbar_hasDerivWithinAt_oai.{u_1}
