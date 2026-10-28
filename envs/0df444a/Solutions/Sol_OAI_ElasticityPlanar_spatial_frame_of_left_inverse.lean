-- Prove2me | solution 1 for OAI.ElasticityPlanar.spatial_frame_of_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:23:31.007997+00:00
-- url     : https://prove2.me/submissions/68f45655-9ada-4305-9ca0-87a765ccb4d5

import Mathlib
import Definitions.Def_OAIQ6El005
import Theorems.Thm_OAI_ElasticityODE_fundamental_isUnit
import Theorems.Thm_OAI_ElasticityODE_fundamental_transport
import Theorems.Thm_OAI_ElasticityPlanar_dbar_fundamental
import Theorems.Thm_OAI_ElasticityPlanar_exists_algebra_variable_homotopy

section
-- module Solutions.OAIQ6_Elast.Elasticity_Compact
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Topology
namespace ElasticityCompact
variable {A P F : Type*} [TopologicalSpace A] [CompactSpace A]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hasFDerivAt_compact (f : P → C(A,F)) (q : P → C(A,P →L[ℝ] F))
    (hq : Continuous q)
    (hd : ∀ p a, HasFDerivAt (fun p => f p a) (q p a) p) (p : P) :
    HasFDerivAt f (flipLinear (q p)) p := by
  rw [hasFDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨r,hr,he⟩ := (Metric.continuousAt_iff (f := q) (a := p)).mp hq.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds p hr] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro a
  have hb (z : P) (hz : z∈Metric.ball p r) : ‖q z a-q p a‖ ≤ ε := by
    have hh := le_of_lt (he hz)
    simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist (f := q z) (g := q p) a).trans hh
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hd z a).hasFDerivWithinAt) hb (convex_ball p r)
    (Metric.mem_ball_self hr) hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [CompactSpace A] [NormedSpace ℝ P] [NormedSpace ℝ F] [NormedSpace ℝ E] in
lemma curryCompact_continuous (f : P × E → F) (hf : Continuous f) (j : A → E) (hj : Continuous j) :
    Continuous (curryCompact f hf j hj) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hf.comp (continuous_fst.prodMk (hj.comp continuous_snd))

lemma curryCompact_hasFDerivAt (f : P × E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : A → E) (hj : Continuous j) (p : P) :
    HasFDerivAt (curryCompact f hf.continuous j hj)
      (flipLinear ⟨fun a => (fderiv ℝ f (p,j a)).comp (ContinuousLinearMap.inl ℝ P E),
        ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp (continuous_const.prodMk hj)).clm_comp continuous_const⟩) p := by
  let q : P → C(A,P →L[ℝ] F) := fun p =>
    ⟨fun a => (fderiv ℝ f (p,j a)).comp (ContinuousLinearMap.inl ℝ P E),
      ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp (continuous_const.prodMk hj)).clm_comp continuous_const⟩
  apply hasFDerivAt_compact _ q ?_ ?_ p
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.comp
      (continuous_fst.prodMk (hj.comp continuous_snd))).clm_comp continuous_const
  · intro p a
    exact (hf.differentiable (by simp) (p,j a)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).prodMk (hasFDerivAt_const (j a) p))

/-- Smooth currying over a compact set. This supplies the Banach-space parameter
regularity needed for the actual coefficient multipliers and linear ODE. -/
theorem curryCompact_contDiff [FiniteDimensional ℝ P]
    (f : P × E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : A → E) (hj : Continuous j) :
    ContDiff ℝ (⊤ : ℕ∞) (curryCompact f hf.continuous j hj) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing f with
  | zero =>
    simp only [Nat.cast_zero,contDiff_zero]
    exact curryCompact_continuous f hf.continuous j hj
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv_apply]
    refine ⟨fun p => (curryCompact_hasFDerivAt f hf j hj p).differentiableAt,by simp,fun v => ?_⟩
    let f' : P × E → F := fun q => fderiv ℝ f q (v,0)
    have hf' : ContDiff ℝ (⊤ : ℕ∞) f' := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    have he : (fun p => fderiv ℝ (curryCompact f hf.continuous j hj) p v)=
        curryCompact f' hf'.continuous j hj := by
      funext p
      ext a
      rw [(curryCompact_hasFDerivAt f hf j hj p).fderiv]
      rfl
    rw [he]
    exact ih f' hf'
end ElasticityCompact

end
end

end OAI
end

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
end ElasticityPlanar

end
end
section
noncomputable section
open Set Complex Module
namespace ElasticityPlanar
open ElasticityODE ElasticityCompact
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
  [FiniteDimensional ℂ R] {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
/-- A genuine jointly smooth global planar frame with arbitrary transverse
parameters. Invertibility holds everywhere, not only at a chosen base point. -/
theorem exists_variable_planar_frame {S Ω Ω' K : Set ℂ} (hS : IsCompact S)
    (hΩS : Ω ⊆ S) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (hK : IsCompact K) (q : Basis n ℂ R) (A : P × ℂ → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAc : ∀ p z, z∉K → A (p,z)=0) {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ V : P × ℂ → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ w, IsUnit (V w)) ∧
      ∀ p z, z∈Ω' → classicalDbar (fun z => V (p,z)) z=A (p,z)*V (p,z) := by
  obtain ⟨B,hB,he⟩ := exists_algebra_variable_homotopy hS hΩS hΩ' hsub hK q A hA hAc hg hc hs h1
  let f : (P × ℂ) × ℝ → R := fun w => B ((w.2,w.1.1),w.1.2)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hB.comp
    ((contDiff_snd.prodMk (contDiff_fst.comp contDiff_fst)).prodMk (contDiff_snd.comp contDiff_fst))
  let b : P × ℂ → C(Time,R) := curryCompact f hf.continuous (fun t : Time => (t:ℝ)) continuous_subtype_val
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := curryCompact_contDiff f hf _ continuous_subtype_val
  let t : Time := ⟨1,by simp [Time]⟩
  let V : P × ℂ → R := fun w => fundamental (b w) t
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := by
    have hL : ContDiff ℝ (⊤ : ℕ∞) (ContinuousMap.evalCLM ℝ t : C(Time,R) →L[ℝ] R) :=
      ContinuousLinearMap.contDiff (E := C(Time,R)) (F := R) _
    exact hL.comp (fundamental_contDiff b hb)
  refine ⟨V,hV,fun w => fundamental_isUnit (b w) t,fun p z hz => ?_⟩
  let bp : ℂ → C(Time,R) := fun z => b (p,z)
  have hbp : ContDiff ℝ (⊤ : ℕ∞) bp := hb.comp (contDiff_const.prodMk contDiff_id)
  have hcoeff (s : Time) : coefficientDbar bp z s=A (p,z)+(s:ℝ) • (A (p,z)*bp z s-bp z s*A (p,z)) := by
    rw [← dbar_evaluation bp (hbp.differentiable (by simp)) z s]
    exact he (s:ℝ) p z hz
  have ht := fundamental_transport bp hbp z (A (p,z)) hcoeff t
  rw [← dbar_fundamental bp hbp] at ht
  simpa only [t,one_smul] using ht
end ElasticityPlanar

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open Set Complex Module
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R] [FiniteDimensional ℂ R]
variable {n : Type*} [Fintype n]

/-- A smooth frame for the actual constant complex characteristic direction
in ambient space. Transverse coordinates are obtained by a proved continuous
left inverse, not assumed to exist. Arbitrary smooth coefficients are allowed. -/
theorem spatial_frame_of_left_inverse_oai (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ)
    (hK : Function.LeftInverse K J)
    {S Ω Ω' : Set ℂ} (hS : IsCompact S) (hΩS : Ω ⊆ S)
    (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) (q : Basis n ℂ R)
    (A : E → R) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ V : E → R, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x, IsUnit (V x)) ∧
        ∀ x, K x∈Ω' → fderiv ℝ V x (J 1)+I • fderiv ℝ V x (J I)=A x*V x := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-J.comp K
  have hPJ (z : ℂ) : P (J z)=0 := by
    change J z-J (K (J z))=0
    rw [hK z,sub_self]
  have hrec (x : E) : P x+J (K x)=x := sub_add_cancel x (J (K x))
  let B : E × ℂ → R := fun w => g w.2 • A (w.1+J w.2)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B :=
    (hg.comp contDiff_snd).smul (hA.comp (contDiff_fst.add (J.contDiff.comp contDiff_snd)))
  have hBc (p : E) (z : ℂ) (hz : z∉tsupport g) : B (p,z)=0 := by
    simp only [B,image_eq_zero_of_notMem_tsupport hz,zero_smul]
  obtain ⟨W,hW,hunit,he⟩ := exists_variable_planar_frame hS hΩS hΩ' hsub hc q B hB hBc hg hc hs h1
  let L := P.prod K
  let V : E → R := W ∘ L
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := hW.comp L.contDiff
  refine ⟨V,hV,fun x => hunit (L x),fun x hx => ?_⟩
  have hd (v : ℂ) : fderiv ℝ V x (J v)=fderiv ℝ (fun z => W (P x,z)) (K x) v := by
    have hw := ((hW.differentiable (by simp)) (L x)).hasFDerivAt.comp x L.hasFDerivAt
    have ht : HasFDerivAt (fun z : ℂ => (P x,z)) (ContinuousLinearMap.inr ℝ E ℂ) (K x) := by
      simpa only [ContinuousLinearMap.inr,id] using
        (hasFDerivAt_const (P x) (K x)).prodMk (hasFDerivAt_id (K x))
    have hw' := ((hW.differentiable (by simp)) (L x)).hasFDerivAt.comp (K x) ht
    change HasFDerivAt V _ x at hw
    change HasFDerivAt (fun z => W (P x,z)) _ (K x) at hw'
    rw [hw.fderiv,hw'.fderiv]
    change fderiv ℝ W (L x) (P (J v),K (J v))=fderiv ℝ W (L x) (0,v)
    rw [hPJ v,hK v]
  rw [hd 1,hd I]
  have hh := he (P x) (K x) hx
  change classicalDbar (fun z => W (P x,z)) (K x)=_
  rw [hh]
  change (g (K x) • A (P x+J (K x)))*W (P x,K x)=A x*W (P x,K x)
  rw [h1 hx,hrec]
  simp only [Pi.one_apply,one_smul]
end

end ElasticityPlanar

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElasticityPlanar.spatial_frame_of_left_inverse_oai.{u_1, u_2, u_3} := @OAI.ElasticityPlanar.spatial_frame_of_left_inverse_oai.{u_1, u_2, u_3}
