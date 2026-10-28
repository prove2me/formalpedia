-- Prove2me | solution 1 for OAI.ElasticityPlanar.dbar_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:21:12.98344+00:00
-- url     : https://prove2.me/submissions/bcc45955-8bc1-4ffc-a184-24aa0ff3c23a

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
open Set Complex Module
namespace ElasticityPlanar
open ElasticityODE ElasticityCompact
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
omit [CompleteSpace R] in
lemma dbar_evaluation (b : ℂ → C(Time,R)) (hb : Differentiable ℝ b) (z : ℂ) (t : Time) :
    classicalDbar (fun z => b z t) z=coefficientDbar b z t := by
  have h := (ContinuousMap.evalCLM ℝ t : C(Time,R) →L[ℝ] R).hasFDerivAt.comp z (hb z).hasFDerivAt
  change HasFDerivAt (fun z => b z t) _ z at h
  rw [classicalDbar,h.fderiv]
  rfl
lemma dbar_fundamental_oai (b : ℂ → C(Time,R)) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (z : ℂ) (t : Time) :
    classicalDbar (fun z => fundamental (b z) t) z=frameDbar b z t :=
  dbar_evaluation (fun z => fundamental (b z))
    ((fundamental_contDiff b hb).differentiable (by simp)) z t
end ElasticityPlanar

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityPlanar.dbar_fundamental_oai.{u_1} := @OAI.ElasticityPlanar.dbar_fundamental_oai.{u_1}
