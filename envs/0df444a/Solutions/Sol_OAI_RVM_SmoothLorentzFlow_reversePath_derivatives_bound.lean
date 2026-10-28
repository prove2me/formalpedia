-- Prove2me | solution 1 for OAI.RVM.SmoothLorentzFlow.reversePath_derivatives_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:08:07.592966+00:00
-- url     : https://prove2.me/submissions/a28f0f71-f16f-4ad5-90e8-8dcac8e34d0f

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Definitions.Def_OAIQ073V001

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma hasDerivAt_particle_energy {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) K) s := by
  have hp : 1+‖V s‖^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hV.norm_sq).const_add 1).sqrt hp
  convert h using 1 <;> try rfl
  rw [velocity, dot_smul_left, dot_eq_inner]
  dsimp [q]
  have hq : Real.sqrt (1+‖V s‖^2) ≠ 0 := ne_of_gt (q_pos (V s))
  field_simp

lemma hasDerivAt_particle_velocity {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => velocity (V t))
      ((q (V s))⁻¹ • (K-dot (velocity (V s)) K • velocity (V s))) s := by
  have hq := hasDerivAt_particle_energy hV
  have h := (hq.inv (ne_of_gt (q_pos (V s)))).smul hV
  convert h using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply, velocity, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop

lemma fderiv_velocity_apply (v h : Vec) :
    fderiv ℝ velocity v h = (q v)⁻¹ • (h-dot (velocity v) h • velocity v) := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt velocity (fderiv ℝ velocity v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_velocity hc
  have he := h₁.unique h₂
  simpa using he

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma fderiv_q_apply (v h : Vec) : fderiv ℝ q v h = dot (velocity v) h := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt q (fderiv ℝ q v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_q.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_energy hc
  have he := h₁.unique h₂
  simpa using he

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ExtendedField
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

lemma contDiff_lorentzField {E B : Field} {k : ℕ∞ω}
    (hE : ContDiff ℝ k E) (hB : ContDiff ℝ k B) : ContDiff ℝ k (lorentzField E B) := by
  have hx : ContDiff ℝ k (fun z : ℝ × Phase => (z.1,z.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hu : ContDiff ℝ k (fun z : ℝ × Phase => velocity z.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.prodMk ((hE.comp hx).add (contDiff_cross.comp (hu.prodMk (hB.comp hx))))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_CurvatureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

lemma SmoothLorentzFlow.reversePath_deriv {E B : Field} (F : SmoothLorentzFlow E B)
    (t u : ℝ) (z : Phase) :
    HasDerivAt (F.reversePath t z) (-lorentzField E B (t-u,F.reversePath t z u)) u := by
  change HasDerivAt (fun r => F.forward (F.backward (t,z)) (t-r))
    (-lorentzField E B (t-u,F.forward (F.backward (t,z)) (t-u))) u
  have hh := (F.ode (F.backward (t,z)) (t-u)).scomp u ((hasDerivAt_id u).const_sub t)
  simpa only [Function.comp_def,one_smul,neg_smul] using hh

end


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SmoothIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u v

section SpatialDerivatives
variable {A E W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiff_iteratedFDeriv_slice {F : A × E → W} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E W).symm.contDiff.comp hF
  | succ n ih =>
    let G : A × E → (E [×n]→L[ℝ] W) := fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2
    change ContDiff ℝ ∞ G at ih
    have he (p : A × E) : fderiv ℝ (fun x => G (p.1,x)) p.2 =
        (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ A E) := by
      have hin : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ A E) p.2 := by
        convert (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1 <;> rfl
      exact ((ih.differentiable (by simp) p).hasFDerivAt.comp p.2 hin).fderiv
    simp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    change ContDiff ℝ ∞ (fun p : A × E =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm (fderiv ℝ (fun x => G (p.1,x)) p.2))
    simp_rw [he]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm.contDiff.comp
      ((ih.fderiv_right (m:=∞) (by simp)).clm_comp contDiff_const)

end SpatialDerivatives

section CompactFamily
variable {α : Type v} {E : Type u} [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma SmoothCompactFamily.ofJoint {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {G : A × E → W} (hG : ContDiff ℝ ∞ G) {ι : α → A} (hι : Continuous ι) :
    SmoothCompactFamily (fun a x => G (ι a,x)) := by
  refine ⟨fun a => hG.comp (contDiff_const.prodMk contDiff_id),fun n => ?_⟩
  exact (contDiff_iteratedFDeriv_slice hG n).continuous.comp
    ((hι.comp continuous_snd).prodMk continuous_fst)

lemma SmoothCompactFamily.continuous {F : α → E → W} (hF : SmoothCompactFamily F) :
    Continuous (fun p : E × α => F p.2 p.1) := by
  have h := (continuousMultilinearCurryFin0 ℝ E W).continuous.comp (hF.2 0)
  simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,LinearIsometryEquiv.apply_symm_apply] using h

lemma SmoothCompactFamily.derivFamily {F : α → E → W} (hF : SmoothCompactFamily F) :
    SmoothCompactFamily (fun a => fderiv ℝ (F a)) := by
  refine ⟨fun a => (hF.1 a).fderiv_right (m:=∞) (by simp),fun n => ?_⟩
  have he (p : E × α) : iteratedFDeriv ℝ n (fderiv ℝ (F p.2)) p.1 =
      continuousMultilinearCurryRightEquiv' ℝ n E W (iteratedFDeriv ℝ (n+1) (F p.2) p.1) := by
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  simp_rw [he]
  exact (continuousMultilinearCurryRightEquiv' ℝ n E W).continuous.comp (hF.2 (n+1))

variable [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α]
  [ProperSpace E] [CompleteSpace W]

omit [CompleteSpace W] in
lemma hasFDerivAt_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) (x : E) :
    HasFDerivAt (fun y => ∫ a, F a y ∂μ) (∫ a, fderiv ℝ (F a) x ∂μ) x := by
  have hD := hF.derivFamily.continuous
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall x 1) (bound:=fun _ => C) (F':=fun y a => fderiv ℝ (F a) y)
    (closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y => (hF.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun a y hy => hC _ ⟨(y,a),⟨hy,mem_univ a⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun a y _ => ((hF.1 a).differentiable (by simp) y).hasFDerivAt)

lemma contDiff_integral_smoothFamily_nat (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ContDiff ℝ n (fun x => ∫ a, F a x ∂μ) := by
  induction n with
  | zero =>
    intro W _ _ _ F hF
    apply contDiff_zero.mpr
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hF.continuous.continuousOn
    intro x a _ ha
    exact (ha (mem_univ a)).elim
  | succ n ih =>
    intro W _ _ _ F hF
    rw [show (↑(n+1) : ℕ∞ω) = ↑n+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_smoothFamily μ hF x).differentiableAt,by simp,?_⟩
    have he : fderiv ℝ (fun x => ∫ a, F a x ∂μ) = (fun x => ∫ a, fderiv ℝ (F a) x ∂μ) := by
      funext x
      exact (hasFDerivAt_integral_smoothFamily μ hF x).fderiv
    rw [he]
    exact ih hF.derivFamily

lemma contDiff_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) : ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) := by
  rw [contDiff_infty]
  exact fun n => contDiff_integral_smoothFamily_nat μ n hF

lemma norm_iteratedFDeriv_integral_le (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x‖ ≤
        ∫ a, ‖iteratedFDeriv ℝ n (F a) x‖ ∂μ := by
  induction n with
  | zero =>
    intro W _ _ _ F hF x
    simpa only [norm_iteratedFDeriv_zero] using norm_integral_le_integral_norm (fun a => F a x)
  | succ n ih =>
    intro W _ _ _ F hF x
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun y => ∫ a, F a y ∂μ) = (fun y => ∫ a, fderiv ℝ (F a) y ∂μ) := by
      funext y
      exact (hasFDerivAt_integral_smoothFamily μ hF y).fderiv
    rw [he]
    simpa only [norm_iteratedFDeriv_fderiv] using ih hF.derivFamily x

end CompactFamily

variable {E W : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

attribute [local instance] Measure.Subtype.measureSpace in
lemma norm_iteratedFDeriv_intervalIntegral_le {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) {a b : ℝ} (hab : a≤b) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ r in a..b, F (r,y)) x‖ ≤
      ∫ r in a..b, ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖ := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := norm_iteratedFDeriv_integral_le
    (E:=E) (W:=W) (volume : Measure (Icc a b)) n
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val) x
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  have he' : (∫ r : Icc a b, ‖iteratedFDeriv ℝ n (fun y => F ((r:ℝ),y)) x‖) =
      ∫ r in a..b, ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖ := by
    rw [integral_subtype measurableSet_Icc (fun r => ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖),
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
  simp_rw [he] at hh
  rwa [he'] at hh

attribute [local instance] Measure.Subtype.measureSpace in
lemma contDiff_spatial_intervalIntegral {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    {a b : ℝ} (hab : a≤b) : ContDiff ℝ ∞ (fun y => ∫ r in a..b, F (r,y)) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := contDiff_integral_smoothFamily (volume : Measure (Icc a b))
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val)
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  simpa only [he] using hh

lemma integral_gronwall_bound {f : ℝ → ℝ} (hf : Continuous f) {a b T : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hn : ∀ t∈Icc 0 T, 0≤f t)
    (hbound : ∀ t∈Icc 0 T, f t≤a+b*∫ r in 0..t, f r) :
    ∀ t∈Icc 0 T, f t≤a*Real.exp (b*t) := by
  let g := fun t => a+b*∫ r in 0..t, f r
  have hg : Continuous g := continuous_const.add
    (continuous_const.mul (intervalIntegral.continuous_primitive hf.intervalIntegrable 0))
  have hnG (t : ℝ) (ht : t∈Icc 0 T) : 0≤g t := by
    exact le_trans (hn t ht) (hbound t ht)
  have hd (t : ℝ) : HasDerivAt g (b*f t) t := by
    convert ((intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt).const_mul b).const_add a using 1
    all_goals try with_reducible_and_instances rfl
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hg.continuousOn
    (fun t _ => (hd t).hasDerivWithinAt) (a:=0) (b:=T) (δ:=a) (K:=b) (ε:=0)
    (by simp only [g,intervalIntegral.integral_same,mul_zero,add_zero,Real.norm_eq_abs,abs_of_nonneg ha]; exact le_rfl)

    (by
      intro t ht
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hb (hn t ⟨ht.1,ht.2.le⟩)),
        Real.norm_eq_abs,abs_of_nonneg (hnG t ⟨ht.1,ht.2.le⟩),add_zero]
      exact mul_le_mul_of_nonneg_left (hbound t ⟨ht.1,ht.2.le⟩) hb)
  intro t ht
  exact (hbound t ht).trans ((le_abs_self (g t)).trans (by
    simpa only [Real.norm_eq_abs,gronwallBound_ε0,sub_zero] using hh t ht))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_TameDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma tame_iteratedFDeriv_comp (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : F → G) (f : E → F), ContDiff ℝ ∞ g  →  ContDiff ℝ ∞ f  →
      ∀ x, (∀ i : ℕ, 1 ≤ i  →  i ≤ n  →  ‖iteratedFDeriv ℝ i g (f x)‖ ≤ A)  →
        (∀ i : ℕ, 1 ≤ i  →  i ≤ n  →  ‖iteratedFDeriv ℝ i f x‖ ≤ A)  →
        ‖iteratedFDeriv ℝ (n+1) (g ∘ f) x‖ ≤
          C*(1+‖iteratedFDeriv ℝ (n+1) g (f x)‖+‖iteratedFDeriv ℝ (n+1) f x‖) := by
  let c : ℕ → ℝ := fun i => (n.choose i : ℝ)*i.factorial*A^(i+1)
  let S := ∑ i∈Finset.range (n+1), c i
  refine ⟨A+S*(A+1),by dsimp [S,c]; positivity,?_⟩
  intro g f hg hf x hgl hfl
  let Mg := ‖iteratedFDeriv ℝ (n+1) g (f x)‖
  let Mf := ‖iteratedFDeriv ℝ (n+1) f x‖
  have hMg : 0 ≤ Mg := norm_nonneg _
  have hMf : 0 ≤ Mf := norm_nonneg _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hcn (i : ℕ) : 0 ≤ c i := by dsimp [c]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hcn i)
  have hfg : fderiv ℝ (g ∘ f) =
      (fun y => ContinuousLinearMap.compL ℝ E F G (fderiv ℝ g (f y)) (fderiv ℝ f y)) := by
    funext y
    exact fderiv_comp y (hg.differentiable (by simp) (f y)) (hf.differentiable (by simp) y)
  have hcomp (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fderiv ℝ g ∘ f) x‖ ≤ i.factorial*(A+Mg)*A^i := by
    apply norm_iteratedFDeriv_comp_le (n:=i) (hg.fderiv_right (m:=∞) (by simp)) hf (by exact_mod_cast le_top) x
    · intro j hj
      rw [norm_iteratedFDeriv_fderiv]
      by_cases hjn : j+1 ≤ n
      · exact (hgl (j+1) (by omega) hjn).trans (le_add_of_nonneg_right hMg)
      · have he : j+1=n+1 := by omega
        rw [he]
        exact le_add_of_nonneg_left hA0
    · intro j hj hj'
      exact (hfl j hj (hj'.trans hi)).trans (le_self_pow₀ hA (by omega))
  have hh := (ContinuousLinearMap.compL ℝ E F G).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    ((hg.fderiv_right (m:=∞) (by simp)).comp hf) (hf.fderiv_right (m:=∞) (by simp)) x (n:=n) (by exact_mod_cast le_top)
    (ContinuousLinearMap.norm_compL_le ℝ E F G)
  have hterm (i : ℕ) (hi : i∈Finset.range (n+1)) :
      (n.choose i : ℝ)*‖iteratedFDeriv ℝ i (fderiv ℝ g ∘ f) x‖*
        ‖iteratedFDeriv ℝ (n-i) (fderiv ℝ f) x‖  ≤
      c i*(A+Mg)+(if i=0 then A*Mf else 0) := by
    have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
    rw [norm_iteratedFDeriv_fderiv]
    by_cases hi0 : i=0
    · subst i
      simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,norm_iteratedFDeriv_zero,Function.comp_apply,
        Nat.sub_zero,ite_true]
      have hg1 : ‖fderiv ℝ g (f x)‖ ≤ A := by simpa only [norm_iteratedFDeriv_one] using hgl 1 le_rfl hn
      exact (mul_le_mul_of_nonneg_right hg1 hMf).trans (le_add_of_nonneg_left (mul_nonneg (hcn 0) (add_nonneg hA0 hMg)))
    · rw [ite_eq_right hi0,add_zero]
      have hlow := hfl (n-i+1) (by omega) (by omega)
      calc
        _  ≤  (n.choose i : ℝ)*(i.factorial*(A+Mg)*A^i)*A := by
          gcongr
          exact hcomp i hi'
        _ = c i*(A+Mg) := by dsimp [c]; rw [pow_succ]; ring
  rw [← norm_iteratedFDeriv_fderiv,hfg]
  refine hh.trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show 0<n+1 by omega,ite_true]
  change S*(A+Mg)+A*Mf ≤ (A+S*(A+1))*(1+Mg+Mf)
  nlinarith [mul_nonneg hS hMg,mul_nonneg hS hMf,mul_nonneg (mul_nonneg hS hA0) hMg,
    mul_nonneg (mul_nonneg hS hA0) hMf,mul_nonneg hA0 hMg]

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {U V W Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma norm_iteratedFDeriv_precomp_contraction (f : V → W) (hf : ContDiff ℝ ∞ f)
    (L : U →L[ℝ] V) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  exact ((iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le _).trans (by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hL) (norm_nonneg _)).trans_eq (mul_one _))

lemma norm_iteratedFDeriv_pair_le {f : U → V} {g : U → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : U) {C : ℝ}
    (hb : ‖iteratedFDeriv ℝ n f x‖ ≤ C) (hc : ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun z => (f z,g z)) x‖ ≤ C := by
  rw [iteratedFDeriv_prodMk hf.contDiffAt hg.contDiffAt (by exact_mod_cast le_top)]
  apply ContinuousMultilinearMap.opNorm_le_bound ((norm_nonneg _).trans hb)
  intro m
  rw [ContinuousMultilinearMap.prod_apply,Prod.norm_mk]
  exact max_le ((ContinuousMultilinearMap.le_opNorm _ m).trans
    (mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun _ _ => norm_nonneg _)))
    ((ContinuousMultilinearMap.le_opNorm _ m).trans
    (mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg fun _ _ => norm_nonneg _)))

lemma bounded_derivatives_comp_on_compact {g : V → W} (hg : ContDiff ℝ ∞ g) {K : Set V}
    (hK : IsCompact K) (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : U → V), ContDiff ℝ ∞ f → ∀ x, f x∈K →
      (∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ A) →
      ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i (g ∘ f) x‖ ≤ C := by
  have hb (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x∈K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hK.image (hg.continuous_iteratedFDeriv (by exact_mod_cast le_top))).isBounded.exists_norm_le
    exact ⟨max C 0,le_max_right _ _,fun x hx => (hC _ ⟨x,hx,rfl⟩).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  let D := ∑ i, B i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hB i)
  have hiD (i : Fin (n+1)) : B i ≤ D := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
  let c : Fin (n+1) → ℝ := fun i => i.val.factorial*D*A^i.val
  have hc (i : Fin (n+1)) : 0 ≤ c i := by dsimp [c]; positivity
  refine ⟨∑ i, c i,Finset.sum_nonneg (fun i _ => hc i),?_⟩
  intro f hf x hx hlow i hi
  have hcomp : ‖iteratedFDeriv ℝ i (g ∘ f) x‖ ≤ i.factorial*D*A^i := by
    apply norm_iteratedFDeriv_comp_le hg hf (by exact_mod_cast le_top)
    · intro j hj
      exact (hbound ⟨j,by omega⟩ _ hx).trans (hiD _)
    · intro j hj hj'
      exact (hlow j hj (hj'.trans hi)).trans (le_self_pow₀ hA (by omega))
  exact hcomp.trans (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ (⟨i,by omega⟩ : Fin (n+1))))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_VelocityDerivatives
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma bounded_iteratedFDeriv_of_factor
    {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {g : W → (U →L[ℝ] W)} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {K : Set W} (hK : IsCompact K) (himage : ∀ x, f x ∈ K) (he : fderiv ℝ f=g ∘ f) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      obtain ⟨C,hC⟩ := hK.isBounded.exists_norm_le
      exact ⟨max C 0,le_max_right _ _,fun x => by
        simpa only [norm_iteratedFDeriv_zero] using (hC (f x) (himage x)).trans (le_max_left _ _)⟩
    | succ n =>
      have hb (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
        ih i (by omega)
      choose B hB hbound using hb
      have hc (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x∈K, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
        obtain ⟨C,hC⟩ := (hK.image ((hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)))).isBounded.exists_norm_le
        exact ⟨max C 0,le_max_right _ _,fun x hx => (hC _ ⟨x,hx,rfl⟩).trans (le_max_left _ _)⟩
      choose G hG hgbound using hc
      let D : ℝ := 1+∑ i, B i
      let C : ℝ := 1+∑ i, G i
      have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
      have hC : 0 ≤ C := add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => hG i))
      have hBD (i : Fin (n+1)) : B i ≤ D :=
        (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
      have hGC (i : Fin (n+1)) : G i ≤ C :=
        (Finset.single_le_sum (fun j _ => hG j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
      refine ⟨n.factorial*C*D^n,by positivity,fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv,he]
      apply norm_iteratedFDeriv_comp_le (n:=n) hg hf (by exact_mod_cast le_top) x
      · intro i hi
        exact (hgbound ⟨i,by omega⟩ (f x) (himage x)).trans (hGC _)
      · intro i hi hi'
        exact (hbound ⟨i,by omega⟩ x).trans ((hBD _).trans (le_self_pow₀ hD (by omega)))

private lemma velocityAugment_smooth : ContDiff ℝ ∞ velocityAugment :=
  (contDiff_q.inv (fun v => (q_pos v).ne')).prodMk contDiff_velocity

private lemma velocityJet_smooth : ContDiff ℝ ∞ velocityJet := by
  have hinner : ContDiff ℝ ∞ (fun w : ℝ × Vec => innerSL ℝ w.2) :=
    (innerSL ℝ (E:=Vec)).contDiff.comp contDiff_snd
  exact (ContinuousLinearMap.prodₗᵢ ℝ (E:=Vec) (F:=ℝ) (G:=Vec)).contDiff.comp
    (((contDiff_fst.pow 2).neg.smul hinner).prodMk
      (contDiff_fst.smul (contDiff_const.sub (hinner.smulRight contDiff_snd))))

private lemma velocityAugment_deriv : fderiv ℝ velocityAugment=velocityJet ∘ velocityAugment := by
  funext v
  have hq := (hasFDerivAt_inv (q_pos v).ne').comp v
    ((contDiff_q.differentiable (by simp : (∞:ℕ∞ω)≠0) v).hasFDerivAt)
  have hu := (contDiff_velocity.differentiable (by simp : (∞:ℕ∞ω)≠0) v).hasFDerivAt
  have hh := (hq.prodMk hu).fderiv
  change fderiv ℝ velocityAugment v=_ at hh
  rw [hh]
  ext h
  · simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_comp,Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,velocityJet,velocityAugment,
      smul_apply,innerSL_apply_apply,← dot_eq_inner,fderiv_q_apply]
    ring
  · simp only [ContinuousLinearMap.prod_apply,Function.comp_apply,velocityJet,velocityAugment,
      smul_apply,sub_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,← dot_eq_inner,fderiv_velocity_apply]

theorem velocity_derivatives_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖iteratedFDeriv ℝ n velocity v‖ ≤ C := by
  have himage (v : Vec) : velocityAugment v∈closedBall (0:ℝ × Vec) 1 := by
    rw [mem_closedBall_zero_iff,Prod.norm_mk]
    refine max_le ?_ (norm_velocity_lt_one v).le
    change ‖(q v)⁻¹‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (q_pos v).le)]
    apply (inv_le_one₀ (q_pos v)).mpr
    nlinarith [q_sq v,q_pos v,sq_nonneg ‖v‖]
  obtain ⟨C,hC,hb⟩ := bounded_iteratedFDeriv_of_factor velocityAugment_smooth velocityJet_smooth
    (isCompact_closedBall (0:ℝ × Vec) 1) himage velocityAugment_deriv n
  refine ⟨C,hC,fun v => ?_⟩
  have hh := (ContinuousLinearMap.snd ℝ ℝ Vec).norm_iteratedFDeriv_comp_left
    velocityAugment_smooth.contDiffAt (x:=v) (n:=n) (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ n velocity v‖ ≤ _ at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ ℝ Vec)
    (norm_nonneg _)).trans ((by simpa only [one_mul] using hb v)))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_HighFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace E]

omit [ProperSpace E] [CompleteSpace E] in
lemma iteratedFDeriv_id_high (n : ℕ) (hn : 1 ≤ n) (x : E) :
    iteratedFDeriv ℝ (n+1) (id : E → E) x=0 := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp only [fderiv_id,iteratedFDeriv_const_of_ne (by omega : n≠0),Function.comp_apply,
    Pi.zero_apply,map_zero]

lemma tame_flow_iteratedFDeriv (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V Y : ℝ × E → E), ContDiff ℝ ∞ V → ContDiff ℝ ∞ Y →
      ∀ T ∈ Icc (0:ℝ) 1, ∀ H : ℝ, 0 ≤ H →
      (∀ t ∈ Icc 0 T, ∀ x, Y (t,x)=x+∫ r in 0..t, V (r,Y (r,x))) →
      (∀ t ∈ Icc 0 T, ∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun z => V (t,z)) (Y (t,x))‖ ≤ A ∧
        ‖iteratedFDeriv ℝ i (fun z => Y (t,z)) x‖ ≤ A) →
      (∀ t ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun z => V (t,z)) (Y (t,x))‖ ≤ H) →
      ∀ t ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun z => Y (t,z)) x‖ ≤ C*(1+H) := by
  obtain ⟨K,hK,hcomp⟩ := tame_iteratedFDeriv_comp (E:=E) (F:=E) (G:=E) n hn A hA
  refine ⟨K*Real.exp K,by positivity,?_⟩
  intro V Y hV hY T hT H hH heq hlow htop t ht x
  let Z : ℝ × E → E := fun p => V (p.1,Y p)
  have hZ : ContDiff ℝ ∞ Z := hV.comp (contDiff_fst.prodMk hY)
  let f : ℝ → ℝ := fun r => ‖iteratedFDeriv ℝ (n+1) (fun z => Y (r,z)) x‖
  have hf : Continuous f := ((contDiff_iteratedFDeriv_slice hY (n+1)).continuous.comp
    (continuous_id.prodMk continuous_const)).norm
  have hb (r : ℝ) (hr : r ∈ Icc 0 T) : f r ≤ K*(1+H)+K*∫ v in 0..r, f v := by
    have hfun : (fun z => Y (r,z)) = (fun z => z+∫ v in 0..r, Z (v,z)) := funext (heq r hr)
    have hint := (contDiff_spatial_intervalIntegral hZ hr.1).of_le (by exact_mod_cast le_top : (n+1:ℕ) ≤ (∞:ℕ∞ω))
    have hder := fun_iteratedFDeriv_add (contDiff_id : ContDiff ℝ (n+1) (id : E → E)) hint
    have hid := iteratedFDeriv_id_high (E:=E) n hn x
    have hzbound (v : ℝ) (hv : v ∈ Icc 0 r) :
        ‖iteratedFDeriv ℝ (n+1) (fun z => Z (v,z)) x‖ ≤ K*(1+H+f v) := by
      have hvT : v ∈ Icc 0 T := ⟨hv.1,hv.2.trans hr.2⟩
      have hh := hcomp (fun z => V (v,z)) (fun z => Y (v,z))
        (hV.comp (contDiff_const.prodMk contDiff_id)) (hY.comp (contDiff_const.prodMk contDiff_id)) x
        (fun i hi hi' => (hlow v hvT x i hi hi').1)
        (fun i hi hi' => (hlow v hvT x i hi hi').2)
      exact hh.trans (mul_le_mul_of_nonneg_left (by gcongr; exact htop v hvT x) hK)
    have hzi : Continuous (fun v => ‖iteratedFDeriv ℝ (n+1) (fun z => Z (v,z)) x‖) :=
      ((contDiff_iteratedFDeriv_slice hZ (n+1)).continuous.comp
        (continuous_id.prodMk continuous_const)).norm
    have hi := intervalIntegral.integral_mono_on (μ:=volume) hr.1 (hzi.intervalIntegrable 0 r)
      ((continuous_const.mul ((continuous_const.add continuous_const).add hf)).intervalIntegrable 0 r) hzbound
    have hcint : (∫ v in 0..r, K*(1+H+f v))=K*(1+H)*r+K*∫ v in 0..r, f v := by
      simp_rw [mul_add]
      rw [intervalIntegral.integral_add (intervalIntegrable_const) ((hf.intervalIntegrable 0 r).const_mul K),
        intervalIntegral.integral_const,intervalIntegral.integral_const_mul]
      simp only [sub_zero,smul_eq_mul]
      ring
    calc
      f r = ‖iteratedFDeriv ℝ (n+1) (fun z => ∫ v in 0..r, Z (v,z)) x‖ := by
        dsimp [f]
        rw [hfun]
        have hd : iteratedFDeriv ℝ (n+1) (fun z => z+∫ v in 0..r, Z (v,z)) x =
            iteratedFDeriv ℝ (n+1) (id : E → E) x+
              iteratedFDeriv ℝ (n+1) (fun z => ∫ v in 0..r, Z (v,z)) x := congrFun hder x
        rw [hd,hid,zero_add]
      _  ≤  ∫ v in 0..r, ‖iteratedFDeriv ℝ (n+1) (fun z => Z (v,z)) x‖ :=
        norm_iteratedFDeriv_intervalIntegral_le hZ (n+1) hr.1 x
      _  ≤  K*(1+H)*r+K*∫ v in 0..r, f v := hi.trans_eq hcint
      _  ≤  K*(1+H)+K*∫ v in 0..r, f v := by
        have hh := mul_le_mul_of_nonneg_left (hr.2.trans hT.2) (mul_nonneg hK (by linarith : 0≤1+H))
        nlinarith only [hh]
  have hg := integral_gronwall_bound hf (mul_nonneg hK (by linarith)) hK
    (fun r _ => norm_nonneg _) hb t ht
  exact hg.trans (by
    calc
      K*(1+H)*Real.exp (K*t)  ≤  K*(1+H)*Real.exp K := by
        gcongr
        nlinarith [ht.2.trans hT.2]
      _ = K*Real.exp K*(1+H) := by ring)

end

private lemma lorentzNonlinearity_smooth : ContDiff ℝ ∞ lorentzNonlinearity :=
  contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).add
    (contDiff_cross.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))))

private lemma lorentzArgument_smooth {E B : Vec → Vec}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (lorentzArgument E B) :=
  (contDiff_velocity.comp contDiff_snd).prodMk ((hE.comp contDiff_fst).prodMk (hB.comp contDiff_fst))

private lemma lorentzArgument_derivative_le {E B : Vec → Vec}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (i : ℕ) (z : Phase) {C : ℝ}
    (hv : ‖iteratedFDeriv ℝ i velocity z.2‖ ≤ C)
    (he : ‖iteratedFDeriv ℝ i E z.1‖ ≤ C) (hb : ‖iteratedFDeriv ℝ i B z.1‖ ≤ C) :
    ‖iteratedFDeriv ℝ i (lorentzArgument E B) z‖ ≤ C := by
  apply norm_iteratedFDeriv_pair_le (contDiff_velocity.comp contDiff_snd)
    ((hE.comp contDiff_fst).prodMk (hB.comp contDiff_fst))
  · exact (norm_iteratedFDeriv_precomp_contraction velocity contDiff_velocity
      (ContinuousLinearMap.snd ℝ Vec Vec) (ContinuousLinearMap.norm_snd_le ℝ Vec Vec) i z).trans hv
  · apply norm_iteratedFDeriv_pair_le (hE.comp contDiff_fst) (hB.comp contDiff_fst)
    · exact (norm_iteratedFDeriv_precomp_contraction E hE
        (ContinuousLinearMap.fst ℝ Vec Vec) (ContinuousLinearMap.norm_fst_le ℝ Vec Vec) i z).trans he
    · exact (norm_iteratedFDeriv_precomp_contraction B hB
        (ContinuousLinearMap.fst ℝ Vec Vec) (ContinuousLinearMap.norm_fst_le ℝ Vec Vec) i z).trans hb

private lemma lorentzArgument_mem {E B : Vec → Vec} {A : ℝ} (hA : 1 ≤ A)
    (he : ∀ x, ‖E x‖ ≤ A) (hb : ∀ x, ‖B x‖ ≤ A) (z : Phase) :
    lorentzArgument E B z∈closedBall (0:Vec × (Vec × Vec)) A := by
  rw [mem_closedBall_zero_iff]
  exact max_le ((norm_velocity_lt_one z.2).le.trans hA) (max_le (he z.1) (hb z.1))

lemma lorentzField_derivatives_bound (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ T, SpatialJetBound n T A E B → ∀ t∈Icc 0 T, ∀ z, ∀ i : ℕ, i ≤ n →
        ‖iteratedFDeriv ℝ i (fun w => lorentzField E B (t,w)) z‖ ≤ C := by
  have hv (i : Fin (n+1)) := velocity_derivatives_bounded i
  choose V hV hbV using hv
  let D := A+∑ i, V i
  have hAD : A ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hV i))
  have hVD (i : Fin (n+1)) : V i ≤ D :=
    (Finset.single_le_sum (fun j _ => hV j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le_one.trans hA))
  obtain ⟨C,hC,hcomp⟩ := bounded_derivatives_comp_on_compact (U:=Phase) lorentzNonlinearity_smooth
    (isCompact_closedBall (0:Vec × (Vec × Vec)) A) n D (hA.trans hAD)
  refine ⟨C,hC,?_⟩
  intro E B hE hB T hbound t ht z i hi
  have he : ContDiff ℝ ∞ (fun x => E (t,x)) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hb : ContDiff ℝ ∞ (fun x => B (t,x)) := hB.comp (contDiff_const.prodMk contDiff_id)
  apply hcomp (lorentzArgument (fun x => E (t,x)) (fun x => B (t,x))) (lorentzArgument_smooth he hb) z
  · apply lorentzArgument_mem hA
    · intro x; simpa only [norm_iteratedFDeriv_zero] using (hbound t ht x 0 (Nat.zero_le _)).1
    · intro x; simpa only [norm_iteratedFDeriv_zero] using (hbound t ht x 0 (Nat.zero_le _)).2
  · intro j hj hj'
    exact lorentzArgument_derivative_le he hb j z ((hbV ⟨j,by omega⟩ z.2).trans (hVD _))
      ((hbound t ht z.1 j hj').1.trans hAD) ((hbound t ht z.1 j hj').2.trans hAD)
  · exact hi

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace E]

lemma flow_first_derivative_bound {V Y : ℝ × E → E}
    (hV : ContDiff ℝ ∞ V) (hY : ContDiff ℝ ∞ Y) {T : ℝ} (hT : T∈Icc (0:ℝ) 1)
    {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀ t∈Icc 0 T, ∀ x, Y (t,x)=x+∫ r in 0..t, V (r,Y (r,x)))
    (hbound : ∀ t∈Icc 0 T, ∀ x, ‖fderiv ℝ (fun z => V (t,z)) (Y (t,x))‖ ≤ A)
    {t : ℝ} (ht : t∈Icc 0 T) (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun z => Y (t,z)) x‖ ≤ Real.exp A := by
  let Z : ℝ × E → E := fun p => V (p.1,Y p)
  have hZ : ContDiff ℝ ∞ Z := hV.comp (contDiff_fst.prodMk hY)
  let f : ℝ → ℝ := fun r => ‖iteratedFDeriv ℝ 1 (fun z => Y (r,z)) x‖
  have hf : Continuous f := ((contDiff_iteratedFDeriv_slice hY 1).continuous.comp
    (continuous_id.prodMk continuous_const)).norm
  have hb (r : ℝ) (hr : r∈Icc 0 T) : f r ≤ 1+A*∫ v in 0..r, f v := by
    have hfun : (fun z => Y (r,z))=(fun z => z+∫ v in 0..r, Z (v,z)) := funext (heq r hr)
    have hint := (contDiff_spatial_intervalIntegral hZ hr.1).of_le (by simp : (1:ℕ∞ω) ≤ ∞)
    have hder : iteratedFDeriv ℝ 1 (fun z => z+∫ v in 0..r, Z (v,z)) x =
        iteratedFDeriv ℝ 1 (id : E → E) x+iteratedFDeriv ℝ 1 (fun z => ∫ v in 0..r, Z (v,z)) x :=
      congrFun (fun_iteratedFDeriv_add (contDiff_id : ContDiff ℝ 1 (id : E → E)) hint) x
    have hzi : Continuous (fun v => ‖iteratedFDeriv ℝ 1 (fun z => Z (v,z)) x‖) :=
      ((contDiff_iteratedFDeriv_slice hZ 1).continuous.comp (continuous_id.prodMk continuous_const)).norm
    have hg (v : ℝ) (hv : v∈Icc 0 r) : ‖iteratedFDeriv ℝ 1 (fun z => Z (v,z)) x‖ ≤ A*f v := by
      dsimp [Z,f]
      simp only [norm_iteratedFDeriv_one]
      have he : (fun z => V (v,Y (v,z)))=(fun z => V (v,z)) ∘ (fun z => Y (v,z)) := rfl
      have hvD : Differentiable ℝ (fun z => V (v,z)) :=
        (hV.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
      have hyD : Differentiable ℝ (fun z => Y (v,z)) :=
        (hY.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
      rw [he,fderiv_comp x (hvD _) (hyD _)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hbound v ⟨hv.1,hv.2.trans hr.2⟩ x) (norm_nonneg _))
    have hi := intervalIntegral.integral_mono_on (μ:=volume) hr.1 (hzi.intervalIntegrable 0 r)
      ((continuous_const.mul hf).intervalIntegrable 0 r) hg
    calc
      f r = ‖iteratedFDeriv ℝ 1 (fun z => z+∫ v in 0..r, Z (v,z)) x‖ := by dsimp [f]; rw [hfun]
      _ ≤ ‖iteratedFDeriv ℝ 1 (id : E → E) x‖+
          ‖iteratedFDeriv ℝ 1 (fun z => ∫ v in 0..r, Z (v,z)) x‖ := by rw [hder]; exact norm_add_le _ _
      _ ≤ 1+∫ v in 0..r, ‖iteratedFDeriv ℝ 1 (fun z => Z (v,z)) x‖ := by
        apply add_le_add
        · simp only [norm_iteratedFDeriv_one,fderiv_id]; exact ContinuousLinearMap.norm_id_le
        · exact norm_iteratedFDeriv_intervalIntegral_le hZ 1 hr.1 x
      _ ≤ 1+A*∫ v in 0..r, f v := by
        have hi' : (∫ v in 0..r, ‖iteratedFDeriv ℝ 1 (fun z => Z (v,z)) x‖) ≤ A*∫ v in 0..r, f v := by
          simpa only [Pi.mul_apply,intervalIntegral.integral_const_mul] using hi
        exact add_le_add le_rfl hi'
  have hh := integral_gronwall_bound hf zero_le_one hA (fun r _ => norm_nonneg _) hb t ht
  apply hh.trans
  simp only [one_mul]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left (ht.2.trans hT.2) hA).trans_eq (mul_one _)

lemma flow_derivatives_bound (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V Y : ℝ × E → E), ContDiff ℝ ∞ V → ContDiff ℝ ∞ Y →
      ∀ T∈Icc (0:ℝ) 1,
      (∀ t∈Icc 0 T, ∀ x, Y (t,x)=x+∫ r in 0..t, V (r,Y (r,x))) →
      (∀ t∈Icc 0 T, ∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun z => V (t,z)) (Y (t,x))‖ ≤ A) →
      ∀ t∈Icc 0 T, ∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun z => Y (t,z)) x‖ ≤ C := by
  induction n with
  | zero => exact ⟨0,le_rfl,fun V Y hV hY T hT heq hb t ht x i hi hin => by omega⟩
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      refine ⟨Real.exp A,(Real.exp_pos _).le,?_⟩
      intro V Y hV hY T hT heq hb t ht x i hi hi'
      have he : i=1 := by omega
      subst i
      exact flow_first_derivative_bound hV hY hT (zero_le_one.trans hA) heq
        (fun r hr z => by simpa only [norm_iteratedFDeriv_one] using hb r hr z 1 le_rfl le_rfl) ht x
    · obtain ⟨D,hD,hd⟩ := ih
      obtain ⟨C,hC,hhigh⟩ := tame_flow_iteratedFDeriv (E:=E) n (by omega) (max A D) (hA.trans (le_max_left _ _))
      refine ⟨max D (C*(1+A)),le_max_of_le_left hD,?_⟩
      intro V Y hV hY T hT heq hb t ht x i hi hi'
      have hy := hd V Y hV hY T hT heq (fun r hr z j hj hj' => hb r hr z j hj (by omega))
      by_cases hin : i ≤ n
      · exact (hy t ht x i hi hin).trans (le_max_left _ _)
      · have he : i=n+1 := by omega
        subst i
        exact (hhigh V Y hV hY T hT A (zero_le_one.trans hA) heq
          (fun r hr z j hj hj' => ⟨(hb r hr z j hj (by omega)).trans (le_max_left _ _),
            (hy r hr z j hj hj').trans (le_max_right _ _)⟩)
          (fun r hr z => hb r hr z (n+1) (by omega) le_rfl) t ht x).trans (le_max_right _ _)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma SmoothLorentzFlow.reversePath_smooth {E B : Field} (F : SmoothLorentzFlow E B) (t : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Phase => F.reversePath t p.2 p.1) := by
  exact F.smooth_forward.comp ((contDiff_const.sub contDiff_fst).prodMk
    (F.smooth_backward.comp (contDiff_const.prodMk contDiff_snd)))

lemma SmoothLorentzFlow.reversePath_integral {E B : Field} (F : SmoothLorentzFlow E B)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (t u : ℝ) (z : Phase) :
    F.reversePath t z u=z+∫ r in 0..u, -lorentzField E B (t-r,F.reversePath t z r) := by
  have hc : Continuous (fun r => -lorentzField E B (t-r,F.reversePath t z r)) :=
    ((contDiff_lorentzField hE hB).continuous.comp ((continuous_const.sub continuous_id).prodMk
      ((F.reversePath_smooth t).continuous.comp (continuous_id.prodMk continuous_const)))).neg
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => F.reversePath_deriv t r z)
    (hc.intervalIntegrable 0 u)
  rw [F.reversePath_zero] at hh
  rw [hh]
  abel

lemma SmoothLorentzFlow.reversePath_derivatives_bound_oai (n : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ (F : SmoothLorentzFlow E B) (T : ℝ), T∈Icc (0:ℝ) 1 → SpatialJetBound n T A E B →
      ∀ t∈Icc 0 T, ∀ u∈Icc 0 t, ∀ z, ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun w => F.reversePath t w u) z‖ ≤ C := by
  obtain ⟨L,hL,hLor⟩ := lorentzField_derivatives_bound n A hA
  obtain ⟨C,hC,hflow⟩ := flow_derivatives_bound (E:=Phase) n (max 1 L) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro E B hE hB F T hT hbound t ht u hu z i hi hi'
  let V : ℝ × Phase → Phase := fun p => -lorentzField E B (t-p.1,p.2)
  let Y : ℝ × Phase → Phase := fun p => F.reversePath t p.2 p.1
  have hV : ContDiff ℝ ∞ V := ((contDiff_lorentzField hE hB).comp
    ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)).neg
  have hY : ContDiff ℝ ∞ Y := F.reversePath_smooth t
  apply hflow V Y hV hY t ⟨ht.1,ht.2.trans hT.2⟩
    (fun r hr x => F.reversePath_integral hE hB t r x) ?_ u hu z i hi hi'
  intro r hr x j hj hj'
  dsimp only [V]
  rw [show (fun z => -lorentzField E B (t-r,z)) = -(fun z => lorentzField E B (t-r,z)) from rfl,
      iteratedFDeriv_neg_apply,norm_neg]
  exact (hLor E B hE hB T hbound (t-r) ⟨by linarith [hr.2],by linarith [hr.1,ht.2]⟩ _ j hj').trans
    (le_max_right _ _)

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.SmoothLorentzFlow.reversePath_derivatives_bound_oai := @OAI.RVM.SmoothLorentzFlow.reversePath_derivatives_bound_oai
