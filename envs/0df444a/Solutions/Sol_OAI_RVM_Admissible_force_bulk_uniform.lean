-- Prove2me | solution 1 for OAI.RVM.Admissible.force_bulk_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:03:30.273366+00:00
-- url     : https://prove2.me/submissions/fb5b6efc-817e-4113-b24b-f617267dad6b

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direct_source_absolute_uniform
import Theorems.Thm_OAI_RVM_Admissible_direct_transport_uniform
import Theorems.Thm_OAI_RVM_Admissible_force_bulk_receiver_residual_uniform
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_multiplier_retarded_force_integrable
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_retarded_force_source_polar

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

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_add_left (a b c : Vec) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_add_right (a b c : Vec) : dot a (b + c) = dot a b + dot a c := by
  rw [dot_comm, dot_add_left, dot_comm b a, dot_comm c a]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

lemma velocity_self (v : Vec) : dot (velocity v) (velocity v) = 1 - (q v)⁻¹ ^ 2 := by
  rw [velocity, dot_smul_left, dot_smul_right, dot_self]
  have hq := q_sq v
  have hn := ne_of_gt (q_pos v)
  field_simp
  nlinarith

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

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeArgument
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma sphere_norm (n : Sphere) : ‖n.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using n.2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_BallCutoff
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma continuous_dot : Continuous (fun p : Vec × Vec => dot p.1 p.2) := by
  simp only [dot_eq_inner]
  exact continuous_fst.inner continuous_snd

end RVM
end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma hasFDerivAt_integral_sphere
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ 1 F) (p : H) :
    HasFDerivAt (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure)
      (∫ n : Sphere, (fderiv ℝ F (p,n.1)).comp (ContinuousLinearMap.inl ℝ H Vec)
        ∂sphereMeasure) p := by
  let D : H × Sphere → H →L[ℝ] W := fun z =>
    (fderiv ℝ F (z.1,z.2.1)).comp (ContinuousLinearMap.inl ℝ H Vec)
  have hD : Continuous D := by
    exact ((hF.continuous_fderiv (by simp)).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall p 1) (bound:=fun _ => C) (F':=fun x n => D (x,n))
    (closedBall_mem_nhds p (by norm_num))
  · exact Eventually.of_forall (fun x => (hF.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun n x hx => hC _ ⟨(x,n),⟨hx,mem_univ n⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun n x _ => (hF.differentiable (by simp) (x,n.1)).hasFDerivAt.comp x
      (by convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const n.1 x) using 1 <;> rfl))

lemma continuous_integral_sphere
    {H W : Type*} [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : H × Vec → W} (hF : Continuous F) :
    Continuous (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  have hc : Continuous (fun p : H × Sphere => F (p.1,p.2.1)) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hc.continuousOn
  intro x n _ hn
  exact (hn (mem_univ n)).elim

lemma contDiff_integral_sphere_nat
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    (k : ℕ) : ∀ {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W}, ContDiff ℝ k F →
      ContDiff ℝ k (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  induction k with
  | zero =>
    intro W _ _ _ F hF
    exact contDiff_zero.mpr (continuous_integral_sphere hF.continuous)
  | succ k ih =>
    intro W _ _ _ F hF
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.succ_pos k)
    let D : H × Vec → H →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H Vec)
    have hD : ContDiff ℝ k D :=
      ((contDiff_succ_iff_fderiv.mp hF).2.2).clm_comp contDiff_const
    have he : fderiv ℝ (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) =
        (fun x => ∫ n : Sphere, D (x,n.1) ∂sphereMeasure) := by
      funext x
      exact (hasFDerivAt_integral_sphere hF1 x).fderiv
    rw [show (↑(k+1) : ℕ∞ω) = ↑k+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_sphere hF1 x).differentiableAt,?_,?_⟩
    · simp
    · rw [he]
      exact ih hD

lemma contDiff_integral_sphere
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_integral_sphere_nat k (contDiff_infty.mp hF k)

lemma contDiff_sphereSum {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (sphereSum g) := by
  apply contDiff_integral_sphere (F:=fun p : (ℝ × Vec) × Vec => g (p.1.2+p.1.1 • p.2))
  exact hg.comp ((contDiff_snd.comp contDiff_fst).add
    ((contDiff_fst.comp contDiff_fst).smul contDiff_snd))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_LabelOccupationDurationMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.position_lipschitz {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) :
    LipschitzOnWith 1 (fun t => (F.flow z t).1) (Icc 0 T) := by
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (F.ode z t ht).fst)
  intro t _
  exact_mod_cast (norm_velocity_lt_one (F.flow z t).2).le

lemma PhaseFlowOn.continuousOn_joint {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T)
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContinuousOn B (Icc 0 T ×ˢ (univ : Set Vec))) :
    ContinuousOn (fun p : ℝ × Phase => F.flow p.2 p.1)
      (Icc 0 T ×ˢ (univ : Set Phase)) := by
  intro p hp
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall p.2.1 (T+1))).bddAbove_image
    ((hE.norm.add hB.norm).mono (prod_mono Subset.rfl (subset_univ _)))
  let L : ℝ≥0 := ⟨max 1 M, zero_le_one.trans (le_max_left _ _)⟩
  have hpos (z : Phase) (hz : z ∈ ball p.2 (1/2:ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (F.flow z t).1 ∈ closedBall p.2.1 (T+1) := by
    have hh := (F.position_lipschitz z).dist_le_mul t ht 0 ⟨le_rfl,hT⟩
    simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
    have hz' : dist z.1 p.2.1 < (1/2:ℝ) := (le_max_left _ _).trans_lt hz
    exact (dist_triangle _ z.1 _).trans (add_le_add hh hz'.le) |>.trans (by linarith [ht.2])
  have hLip (z : Phase) (hz : z ∈ ball p.2 (1/2:ℝ)) :
      LipschitzOnWith L (F.flow z) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (F.ode z)
    intro t ht
    apply NNReal.coe_le_coe.mp
    change ‖lorentzField E B (t,F.flow z t)‖ ≤ max 1 M
    rw [lorentzField,lorentzPhase,Prod.norm_def]
    apply max_le
    · exact (norm_velocity_lt_one _).le.trans (le_max_left _ _)
    · calc
        _ ≤ ‖E (t,(F.flow z t).1)‖+‖B (t,(F.flow z t).1)‖ := by
          exact (norm_add_le _ _).trans (add_le_add le_rfl
            ((norm_cross_le _ _).trans
              (mul_le_of_le_one_left (norm_nonneg _) (norm_velocity_lt_one _).le)))
        _ ≤ M := hM ⟨(t,(F.flow z t).1),⟨ht,hpos z hz t ht⟩,rfl⟩
        _ ≤ _ := le_max_right _ _
  have hc : ContinuousAt (fun z => F.flow z p.1) p.2 := (F.label p.2 p.1 hp.1).continuousAt
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hlabel⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  refine ⟨min (1/2:ℝ) (min δ (ε/(2*((L:ℝ)+1)))),by positivity,?_⟩
  intro q hq hdist
  have hd₁ : dist q.1 p.1 < ε/(2*((L:ℝ)+1)) :=
    (le_max_left _ _).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hd₂ : dist q.2 p.2 < δ :=
    (le_max_right _ _).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hqball : q.2 ∈ ball p.2 (1/2:ℝ) :=
    (le_max_right _ _).trans_lt (hdist.trans_le (min_le_left _ _))
  have hh : (L:ℝ)*dist q.1 p.1 < ε/2 := by
    have hh := (lt_div_iff₀ (show 0<2*((L:ℝ)+1) by positivity)).mp hd₁
    nlinarith [dist_nonneg (x := q.1) (y := p.1)]
  exact (dist_triangle _ (F.flow q.2 p.1) _).trans_lt
    (add_lt_add_of_le_of_lt ((hLip q.2 hqball).dist_le_mul q.1 hq.1 p.1 hp.1)
      (hlabel hd₂) |>.trans_le (by linarith))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma prefixClamp_mem {T : ℝ} (hT : 0≤T) (t : ℝ) : prefixClamp T t∈Icc 0 T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩

lemma prefixClamp_eq {T t : ℝ} (ht : t∈Icc 0 T) : prefixClamp T t=t := by
  simp [prefixClamp,min_eq_right ht.2,max_eq_right ht.1]

lemma PhaseFlowOn.continuous_prefixFlow {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) :
    Continuous (fun p : ℝ × Phase => prefixFlow F.flow T p.2 p.1) := by
  apply (F.continuousOn_joint hT hs.E_smooth.continuousOn hs.B_smooth.continuousOn).comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
  intro p
  exact ⟨prefixClamp_mem hT p.1,mem_univ _⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixParticle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma EnergyPrefix.continuous_prefixParticle {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) : Continuous (prefixParticle s T) :=
  hs.f_smooth.continuousOn.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

lemma continuous_prefixField {E : Field} {T : ℝ}
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec))) (hT : 0 ≤ T) :
    Continuous (prefixField E T) :=
  hE.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverQ
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
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma receiverQ_add (a n h k : Vec) : receiverQ a n (h+k)=receiverQ a n h+receiverQ a n k := by
  simp only [receiverQ,dot_add_right,smul_add,add_smul]
  module

lemma receiverQ_smul (a n h : Vec) (c : ℝ) : receiverQ a n (c • h)=c • receiverQ a n h := by
  simp only [receiverQ,dot_smul_right,smul_add,smul_smul]
  module

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveK
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiff_spatialPartial {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => spatialPartial g x i) :=
  ((contDiff_infty_iff_fderiv.mp hg).2).clm_apply contDiff_const

lemma sphere_area : sphereMeasure.real univ = 4*Real.pi := by
  rw [sphereMeasure,Measure.toSphere_real_apply_univ]
  simp only [Vec,finrank_euclideanSpace,Measure.real,EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  norm_num
  ring

lemma contDiff_waveK {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (waveK g) :=
  contDiff_const.mul (contDiff_fst.mul (contDiff_sphereSum hg))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ParamPrimitive
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma contDiff_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e : H) : ContDiff ℝ ∞ (dirD F e) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


lemma contDiff_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : ContDiff ℝ ∞ F) (i : Fin 3) : ContDiff ℝ ∞ (fun x => F x i) :=
  (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF

lemma contDiff_curl {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (curl F) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> exact (contDiff_spatialPartial (contDiff_component hF _) _).sub
    (contDiff_spatialPartial (contDiff_component hF _) _)

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveGradient
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma contDiff_freeWave {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (freeWave g h) :=
  (contDiff_dirD (contDiff_waveK hg) (1,0)).add (contDiff_waveK hh)

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRadius
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma coneDirection_norm {x y : Vec} (h : x≠y) : ‖coneDirection x y‖=1 := by
  have hr : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  simp [coneDirection,coneRadius,norm_smul,hr.ne']



section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma contDiff_dot_pair {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : Vec × Vec => dot z.1 z.2) := by
  unfold dot
  fun_prop

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixMomentumForce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.continuous_prefixMomentumForce {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (z : Phase) :
    Continuous (prefixMomentumForce s F.flow T z) := by
  have hα : Continuous (prefixFlow F.flow T z) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have ht : Continuous (prefixClamp T) := continuous_const.max (continuous_const.min continuous_id)
  have hZ := ht.prodMk hα.fst
  have hE := hs.E_smooth.continuousOn.comp_continuous hZ (fun t=>⟨prefixClamp_mem hT t,mem_univ _⟩)
  have hB := hs.B_smooth.continuousOn.comp_continuous hZ (fun t=>⟨prefixClamp_mem hT t,mem_univ _⟩)
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp (((contDiff_velocity (k:=1)).continuous.comp hα.snd).prodMk hB))

end RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceWaveSpatialIbp
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_integral_bound_compact {H W : Type*}
    [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {P : Set H} {K : Set Vec} {F : H × Vec → W}
    (hP : IsCompact P) (hK : IsCompact K)
    (hF : ContinuousOn F (P ×ˢ univ)) (hz : ∀ p ∈ P, ∀ v ∉ K, F (p,v)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ p ∈ P, ‖∫ v : Vec, F (p,v)‖≤C := by
  obtain ⟨C,hC⟩ := ((hP.prod hK).image_of_continuousOn (hF.mono (by intro z hz; exact ⟨hz.1,mem_univ _⟩))).isBounded.exists_norm_le
  refine ⟨max C 0*volume.real K,mul_nonneg (le_max_right _ _) (measureReal_nonneg),?_⟩
  intro p hp
  have hc : Continuous (fun v : Vec => F (p,v)) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hp,mem_univ _⟩)
  have hi : Integrable (fun v : Vec => F (p,v)) :=
    hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz p hp))
  have hfi : (∫ v : Vec, F (p,v))=∫ v in K, F (p,v) := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (hz p hp)
  rw [hfi]
  apply le_trans (norm_integral_le_integral_norm _)
  calc
    (∫ v in K, ‖F (p,v)‖) ≤ ∫ v in K, max C 0 := by
      apply integral_mono_ae hi.norm.integrableOn
        (integrableOn_const (hK.measure_lt_top.ne))
      filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
      exact le_trans (hC _ ⟨(p,v),⟨hp,hv⟩,rfl⟩) (le_max_left _ _)
    _ = max C 0*volume.real K := by simp [mul_comm]

lemma coneRadius_add (x z : Vec) : coneRadius x (x+z)=‖z‖ := by
  unfold coneRadius
  rw [show x-(x+z) = -z by abel,norm_neg]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma normalisedElectricKernel_eq {r : ℝ} (hr : r≠0) (n u b : Vec) :
    normalisedElectricKernel r n u b=r^2 • physicalElectricKernel r n u b := by
  ext i
  simp only [normalisedElectricKernel,physicalElectricKernel,PiLp.add_apply,PiLp.smul_apply,
    PiLp.sub_apply,smul_eq_mul]
  field_simp

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ContinuousIntegralSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coneBoundary_radius {T a : ℝ} (hT : 0<T) (ha : a ∈ Icc 0 (T/2)) {n : Vec}
    (hn : n ∈ sphere (0:Vec) 1) (x : Vec) : coneRadius x (x+(T-a) • n)=T-a := by
  rw [coneRadius_add,norm_smul,Real.norm_of_nonneg (by linarith [ha.2]),
    show ‖n‖=1 by simpa only [mem_sphere,dist_zero_right] using hn,mul_one]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ElectricBoundaryField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma physical_force_kernel (r : ℝ) (n a v b : Vec) (hr : r≠0) (hn : ‖n‖=1) :
    (1-dot n (velocity v)) • receiverQ a n (physicalElectricKernel r n (velocity v) b) =
      forceTransportKernel r n a v+forceSourceKernel r n a v b := by
  have hd := (cone_denom_pos v n hn).ne'
  have hq := (q_pos v).ne'
  have h1 : (1-dot n (velocity v))*((1-dot (velocity v) (velocity v))/(r^2*(1-dot n (velocity v))^3)) =
      (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ := by
    rw [velocity_self]
    field_simp
    ring
  have h2 : (1-dot n (velocity v))*(r*(1-dot n (velocity v))^3)⁻¹ =
      (r*(1-dot n (velocity v))^2)⁻¹ := by
    field_simp
  simp only [physicalElectricKernel,receiverQ_add,receiverQ_smul,smul_add,smul_smul,h1,h2,
    forceTransportKernel,forceSourceKernel,sourceNumerator]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DatumElectricFluxKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma datum_velocity_support {f : Phase → ℝ} (hc : HasCompactSupport f) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ y v, v∉K → f (y,v)=0 := by
  refine ⟨Prod.snd '' tsupport f,hc.image continuous_snd,?_⟩
  intro y v hv
  by_contra h
  exact hv ⟨(y,v),subset_tsupport _ h,rfl⟩

lemma datum_integrand_continuousOn {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : Continuous f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ContinuousOn (fun p : (Vec × Vec) × Vec => f (p.1.1,p.2) • H (p.1.2,p.2))
      ((univ ×ˢ sphere (0:Vec) 1) ×ˢ univ) := by
  exact (hf.comp (continuous_fst.fst.prodMk continuous_snd)).continuousOn.smul
    (hH.comp (continuous_fst.snd.prodMk continuous_snd).continuousOn
      (fun _ h => ⟨h.1.2,mem_univ _⟩))

lemma uniform_datum_velocity_integral_bound {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : Continuous f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ y n : Vec, ‖n‖=1 → ‖∫ v : Vec, f (y,v) • H (n,v)‖≤C := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  let Kx : Set Vec := Prod.fst '' tsupport f
  have hKx : IsCompact Kx := hc.image continuous_fst
  have hF := datum_integrand_continuousOn hf hH
  have hP : IsCompact (Kx ×ˢ sphere (0:Vec) 1) := hKx.prod (isCompact_sphere (0:Vec) 1)
  obtain ⟨C,hC,hbound⟩ := uniform_integral_bound_compact hP hK
    (hF.mono (by intro p hp; exact ⟨⟨mem_univ _,hp.1.2⟩,hp.2⟩))
    (show ∀ p ∈ Kx ×ˢ sphere (0:Vec) 1, ∀ v ∉ K,
      f (p.1,v) • H (p.2,v)=0 from by intro p hp v hv; rw [hz p.1 v hv,zero_smul])
  refine ⟨C,hC,?_⟩
  intro y n hn
  by_cases hy : y∈Kx
  · exact hbound (y,n) ⟨hy,by simpa only [mem_sphere,dist_zero_right] using hn⟩
  · have he (v : Vec) : f (y,v)=0 := by
      by_contra h
      exact hy ⟨(y,v),subset_tsupport _ h,rfl⟩
    simpa only [he,zero_smul,integral_zero,norm_zero] using hC

lemma continuousOn_datumElectricFluxKernel (i : Fin 3) :
    ContinuousOn (datumElectricFluxKernel i) (sphere (0:Vec) 1 ×ˢ univ) := by
  have hu : Continuous (fun p : Vec × Vec => velocity p.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hd : Continuous (fun p : Vec × Vec => 1-dot p.1 (velocity p.2)) := continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
    (continuous_fst.prodMk hu))
  have hdi : ContinuousOn (fun p : Vec × Vec => (1-dot p.1 (velocity p.2))⁻¹)
      (sphere (0:Vec) 1 ×ˢ univ) := hd.continuousOn.inv₀ (by
    intro p hp
    exact (cone_denom_pos p.2 p.1 (by simpa only [mem_sphere,dist_zero_right] using hp.1)).ne')
  exact (hdi.mul (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp continuous_fst).sub
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hu)).continuousOn).smul hu.continuousOn

lemma continuousOn_datumMagneticFluxKernel (i : Fin 3) :
    ContinuousOn (datumMagneticFluxKernel i) (sphere (0:Vec) 1 ×ˢ univ) := by
  have hu : Continuous (fun p : Vec × Vec => velocity p.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hd : Continuous (fun p : Vec × Vec => 1-dot p.1 (velocity p.2)) := continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
    (continuous_fst.prodMk hu))
  have hdi : ContinuousOn (fun p : Vec × Vec => (1-dot p.1 (velocity p.2))⁻¹)
      (sphere (0:Vec) 1 ×ˢ univ) := hd.continuousOn.inv₀ (by
    intro p hp
    exact (cone_denom_pos p.2 p.1 (by simpa only [mem_sphere,dist_zero_right] using hp.1)).ne')
  have hc := (contDiff_cross (k:=1)).continuous.comp
    (continuous_fst.prodMk (continuous_fst.sub hu))
  exact (hdi.mul ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hc).continuousOn).smul hu.continuousOn

lemma datumElectricFlux_eq (d : Datum) (t : ℝ) (x y : Vec) (i : Fin 3) :
    retardedElectricFlux (datumBoundarySolution d) t x i y =
      (coneRadius x y)⁻¹ • ∫ v : Vec, d.f₀ (y,v) • datumElectricFluxKernel i (coneDirection x y,v) := by
  unfold retardedElectricFlux
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [retardedDensity,datumBoundarySolution,retardedG,eulerianG,
    PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,datumElectricFluxKernel,mul_inv_rev,smul_smul]
  congr 1
  ring

lemma datumMagneticFlux_eq (d : Datum) (t : ℝ) (x y : Vec) (i : Fin 3) :
    retardedMagneticFlux (datumBoundarySolution d) t x i y =
      (coneRadius x y)⁻¹ • ∫ v : Vec, d.f₀ (y,v) • datumMagneticFluxKernel i (coneDirection x y,v) := by
  unfold retardedMagneticFlux
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [retardedDensity,datumBoundarySolution,retardedH,retardedG,eulerianG,
    cross_smul_right,PiLp.smul_apply,smul_eq_mul,datumMagneticFluxKernel,mul_inv_rev,smul_smul]
  congr 1
  ring

lemma uniform_datumElectricFlux_bound {d : Datum} (hf : Continuous d.f₀)
    (hc : HasCompactSupport d.f₀) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (t : ℝ) (x y : Vec), x≠y →
      ‖retardedElectricFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y := by
  obtain ⟨C,hC,hbound⟩ := uniform_datum_velocity_integral_bound hf hc
    (continuousOn_datumElectricFluxKernel i)
  refine ⟨C,hC,?_⟩
  intro t x y hxy
  rw [datumElectricFlux_eq,norm_smul,coneRadius,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x-y)))]
  simpa only [div_eq_mul_inv,mul_comm C,coneRadius] using
    mul_le_mul_of_nonneg_left (hbound y (coneDirection x y) (coneDirection_norm hxy))
      (inv_nonneg.mpr (norm_nonneg _))

lemma uniform_datumMagneticFlux_bound {d : Datum} (hf : Continuous d.f₀)
    (hc : HasCompactSupport d.f₀) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (t : ℝ) (x y : Vec), x≠y →
      ‖retardedMagneticFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y := by
  obtain ⟨C,hC,hbound⟩ := uniform_datum_velocity_integral_bound hf hc
    (continuousOn_datumMagneticFluxKernel i)
  refine ⟨C,hC,?_⟩
  intro t x y hxy
  rw [datumMagneticFlux_eq,norm_smul,coneRadius,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x-y)))]
  simpa only [div_eq_mul_inv,mul_comm C,coneRadius] using
    mul_le_mul_of_nonneg_left (hbound y (coneDirection x y) (coneDirection_norm hxy))
      (inv_nonneg.mpr (norm_nonneg _))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_BranchIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma datum_moment_bounds {d : Datum} (hf : Continuous d.f₀) (hc : HasCompactSupport d.f₀) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, |rho d.f₀ x|≤C ∧ ‖current d.f₀ x‖≤C := by
  have hn : ‖basis 0‖=1 := by simp [basis,PiLp.norm_single]
  obtain ⟨C,hC,hb⟩ := uniform_datum_velocity_integral_bound (H:=fun _ : Vec × Vec => (1:ℝ))
    hf hc continuousOn_const
  obtain ⟨D,hD,hd⟩ := uniform_datum_velocity_integral_bound (H:=fun p : Vec × Vec => velocity p.2)
    hf hc ((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro x
  constructor
  · have hh := hb x (basis 0) hn
    simpa only [smul_eq_mul,mul_one,Real.norm_eq_abs,rho] using hh.trans (le_add_of_nonneg_right hD)
  · exact (hd x (basis 0) hn).trans (le_add_of_nonneg_left hC)

lemma norm_coordinate_le (v : Vec) (i : Fin 3) : |v i|≤‖v‖ := by
  exact (PiLp.norm_apply_le v i)

lemma norm_le_three_of_coordinate_bound {v : Vec} {C : ℝ} (hC : 0≤C)
    (h : ∀ i : Fin 3, |v i|≤C) : ‖v‖≤3*C := by
  have hsq (i : Fin 3) : (v i)^2≤C^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using h i)
  have hnorm := dot_self v
  simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hnorm
  change v 0*v 0+(v 1*v 1+v 2*v 2)=‖v‖^2 at hnorm
  nlinarith [hsq 0,hsq 1,hsq 2,norm_nonneg v]

lemma freeWave_bound_compact {g h : Vec → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (T R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x∈closedBall (0:Vec) R,
      |freeWave g h (t,x)|≤C := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc.prod (isCompact_closedBall (0:Vec) R)).image
    (contDiff_freeWave hg hh).continuous).isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht x hx
  exact (hC _ ⟨(t,x),⟨ht,hx⟩,rfl⟩).trans (le_max_left _ _)

lemma norm_initial_cone_flux {d : Datum} {C : ℝ} (i : Fin 3)
    (hb : ∀ t x y, x≠y → ‖retardedElectricFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    |t^2*dot n.1 (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))|≤C*t := by
  have hr : coneRadius x (x+t • n.1)=t := by
    simpa only [sub_zero] using coneBoundary_radius ht
      (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
  have hxy : x≠x+t • n.1 := by
    intro he
    have hh : coneRadius x (x+t • n.1)=0 := by rw [← he,coneRadius,sub_self,norm_zero]
    linarith
  have hnorm : ‖n.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using n.2
  have hf := hb t x (x+t • n.1) hxy
  rw [hr] at hf
  rw [abs_mul,abs_of_nonneg (sq_nonneg t)]
  have ha : |dot (n.1 : Vec) (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))| ≤
      ‖n.1‖*‖retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)‖ := by
    simpa only [dot_eq_inner] using
      abs_real_inner_le_norm (n.1 : Vec) (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))
  calc
    _ ≤ t^2*(‖n.1‖*‖retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)‖) :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg t)
    _ ≤ t^2*(C/t) := by rw [hnorm,one_mul]; gcongr
    _ = C*t := by field_simp

lemma norm_initial_magnetic_cone_flux {d : Datum} {C : ℝ} (i : Fin 3)
    (hb : ∀ t x y, x≠y → ‖retardedMagneticFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    |t^2*dot n.1 (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))|≤C*t := by
  have hr : coneRadius x (x+t • n.1)=t := by
    simpa only [sub_zero] using coneBoundary_radius ht
      (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
  have hxy : x≠x+t • n.1 := by
    intro he
    have hh : coneRadius x (x+t • n.1)=0 := by rw [← he,coneRadius,sub_self,norm_zero]
    linarith
  have hnorm : ‖n.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using n.2
  have hf := hb t x (x+t • n.1) hxy
  rw [hr] at hf
  rw [abs_mul,abs_of_nonneg (sq_nonneg t)]
  have ha : |dot (n.1 : Vec) (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))| ≤
      ‖n.1‖*‖retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)‖ := by
    simpa only [dot_eq_inner] using
      abs_real_inner_le_norm (n.1 : Vec) (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))
  calc
    _ ≤ t^2*(‖n.1‖*‖retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)‖) :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg t)
    _ ≤ t^2*(C/t) := by rw [hnorm,one_mul]; gcongr
    _ = C*t := by field_simp

lemma norm_sphere_integral_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Sphere → W} {C : ℝ} (hb : ∀ n, ‖g n‖≤C) :
    ‖∫ n, g n ∂sphereMeasure‖≤C*(4*Real.pi) := by
  simpa only [sphere_area] using norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)

lemma abs_sphere_integral_le {g : Sphere → ℝ} {C : ℝ} (hb : ∀ n, |g n|≤C) :
    |∫ n, g n ∂sphereMeasure|≤C*(4*Real.pi) := by
  simpa only [Real.norm_eq_abs] using norm_sphere_integral_le (g:=g) (C:=C) hb

lemma waveK_bound_of_bounded {g : Vec → ℝ} {C : ℝ} (hb : ∀ x, |g x|≤C)
    {t : ℝ} (ht : 0≤t) (x : Vec) : |waveK g (t,x)|≤t*C := by
  have hh := norm_sphere_integral_le (g:=fun n : Sphere => g (x+t • n.1))
    (fun n => hb (x+t • n.1))
  simp only [Real.norm_eq_abs] at hh
  dsimp only [waveK,sphereSum]
  rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹),abs_of_nonneg ht]
  calc
    _ ≤ (4*Real.pi)⁻¹*(t*(C*(4*Real.pi))) := by gcongr
    _ = t*C := by field_simp

lemma electricConeBoundary_datum_bound {d : Datum} (hd : Admissible d)
    (T R : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T, ∀ x∈closedBall (0:Vec) R,
      |electricConeBoundary (datumBoundarySolution d) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := uniform_datumElectricFlux_bound hd.1.continuous hd.2.1 i
  obtain ⟨D,hD,hmom⟩ := datum_moment_bounds hd.1.continuous hd.2.1
  obtain ⟨A,hA,hfree⟩ := freeWave_bound_compact (hproj.comp hd.2.2.2.1.1)
    (hproj.comp (contDiff_curl hd.2.2.2.2.1.1)) T R
  refine ⟨A+(C+2*D)*max T 0,by positivity,?_⟩
  intro t ht x hx
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_cone_flux i hflux ht.1 x n)
  have hrho : |∫ n : Sphere, t*n.1 i*rho d.f₀ (x+t • n.1) ∂sphereMeasure|≤
      (t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    have hn : |n.1 i|≤1 := by
      exact (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        (hmom (x+t • n.1)).1 (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = t*D := by ring
  have hj : |waveK (fun y => current d.f₀ y i) (t,x)|≤t*D :=
    waveK_bound_of_bounded (fun y => (norm_coordinate_le (current d.f₀ y) i).trans (hmom y).2) ht.1.le x
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t*n.1 i*rho d.f₀ (x+t • n.1) ∂sphereMeasure)|≤t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hrho hp
      _ = t*D := by field_simp
  have hf := hfree t ⟨ht.1.le,ht.2⟩ x hx
  simp only [electricConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)) hj)).trans (by
      have htT := ht.2.trans (le_max_left T 0)
      nlinarith)

lemma magneticConeBoundary_datum_bound {d : Datum} (hd : Admissible d)
    (T R : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T, ∀ x∈closedBall (0:Vec) R,
      |magneticConeBoundary (datumBoundarySolution d) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := uniform_datumMagneticFlux_bound hd.1.continuous hd.2.1 i
  obtain ⟨D,hD,hmom⟩ := datum_moment_bounds hd.1.continuous hd.2.1
  obtain ⟨A,hA,hfree⟩ := freeWave_bound_compact (hproj.comp hd.2.2.2.2.1.1)
    (hproj.comp (contDiff_curl hd.2.2.2.1.1)).neg T R
  refine ⟨A+(C+2*D)*max T 0,by positivity,?_⟩
  intro t ht x hx
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_magnetic_cone_flux i hflux ht.1 x n)
  have hem (n : Sphere) (j k : Fin 3) :
      |t*n.1 j*current d.f₀ (x+t • n.1) k|≤t*D := by
    have hn : |n.1 j|≤1 :=
      (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    have hj : |current d.f₀ (x+t • n.1) k|≤D :=
      (norm_coordinate_le _ k).trans (hmom _).2
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        hj (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = _ := by ring
  have hj : |∫ n : Sphere,
      t*n.1 (curlA i)*current d.f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current d.f₀ (x+t • n.1) (curlA i) ∂sphereMeasure|≤
      (2*t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    exact (abs_sub _ _).trans ((add_le_add (hem n _ _) (hem n _ _)).trans (by ring_nf; rfl))
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere,
      t*n.1 (curlA i)*current d.f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current d.f₀ (x+t • n.1) (curlA i) ∂sphereMeasure)|≤2*t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((2*t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hj hp
      _ = 2*t*D := by field_simp
  have hf := hfree t ⟨ht.1.le,ht.2⟩ x hx
  simp only [magneticConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)).trans (by
      have htT := ht.2.trans (le_max_left T 0)
      nlinarith)

lemma boundaryLorentzForce_datum_bound {d : Datum} (hd : Admissible d) (T R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T, ∀ x∈closedBall (0:Vec) R, ∀ a : Vec,
      ‖a‖≤1 → ‖boundaryLorentzForce (datumBoundarySolution d) t x a‖≤C := by
  classical
  choose C hC hb using electricConeBoundary_datum_bound hd T R
  choose D hD hd' using magneticConeBoundary_datum_bound hd T R
  let A := ∑ i : Fin 3, C i
  let B := ∑ i : Fin 3, D i
  have hA : 0≤A := Finset.sum_nonneg (fun i _ => hC i)
  have hB : 0≤B := Finset.sum_nonneg (fun i _ => hD i)
  refine ⟨3*A+3*B,by positivity,?_⟩
  intro t ht x hx a ha
  have he : ‖electricBoundaryField (datumBoundarySolution d) t x‖≤3*A := by
    apply norm_le_three_of_coordinate_bound hA
    intro i
    exact (hb i t ht x hx).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
  have hm : ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤3*B := by
    apply norm_le_three_of_coordinate_bound hB
    intro i
    exact (hd' i t ht x hx).trans (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i))
  exact (norm_add_le _ _).trans (add_le_add he ((norm_cross_le _ _).trans
    ((mul_le_mul ha hm (norm_nonneg _) zero_le_one).trans_eq (one_mul _))))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma measurableSet_trianglePhaseDomain (T : ℝ) : MeasurableSet (trianglePhaseDomain T) :=
  ((measurable_fst.fst measurableSet_Ioo).inter
    ((measurableSet_lt measurable_const measurable_fst.snd.fst).inter
      (measurableSet_lt measurable_fst.snd.fst measurable_fst.fst)))

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_IntegralBallPolarFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma normalisedSignedForce_flux {r : ℝ} (n a v b : Vec)
    (hr : r≠0) (hn : ‖n‖=1) (hD : 1-dot n a≠0) :
    (1-dot n a) • normalisedSignedForce r a (velocity v) n b=
      r^2 • (forceTransportKernel r n a v+forceSourceKernel r n a v b) := by
  rw [normalisedSignedForce,smul_smul]
  have hc : (1-dot n a)*((1-dot n (velocity v))/(1-dot n a))=1-dot n (velocity v) := by
    field_simp
  rw [hc,normalisedElectricKernel_eq hr,receiverQ_smul,smul_comm,
    ←physical_force_kernel r n a v b hr hn]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalDirectTransportDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma measurable_forceTransportFamily {α : Type*} [MeasurableSpace α]
    {r : α→ℝ} {n a v : α→Vec} (hr : Measurable r) (hn : Measurable n)
    (ha : Measurable a) (hv : Measurable v) :
    Measurable (fun x=>forceTransportKernel (r x) (n x) (a x) (v x)) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have hq := (contDiff_q (k:=0)).continuous.measurable.comp hv
  have hd : Measurable (fun x=>1-dot (n x) (velocity (v x))) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hu))
  have hD : Measurable (fun x=>1-dot (n x) (a x)) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk ha))
  unfold forceTransportKernel receiverQ
  exact (((hr.pow_const 2).mul (hq.pow_const 2)).mul (hd.pow_const 2)).inv.smul
    ((hD.smul (hn.sub hu)).add ((continuous_dot.measurable.comp (ha.prodMk (hn.sub hu))).smul hn))

lemma measurable_forceSourceFamily {α : Type*} [MeasurableSpace α]
    {r : α→ℝ} {n a v b : α→Vec} (hr : Measurable r) (hn : Measurable n)
    (ha : Measurable a) (hv : Measurable v) (hb : Measurable b) :
    Measurable (fun x=>forceSourceKernel (r x) (n x) (a x) (v x) (b x)) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have hd : Measurable (fun x=>1-dot (n x) (velocity (v x))) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hu))
  have hD : Measurable (fun x=>1-dot (n x) (a x)) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk ha))
  have hN : Measurable (fun x=>sourceNumerator (n x) (velocity (v x)) (b x)) :=
    ((continuous_dot.measurable.comp (hn.prodMk hb)).smul (hn.sub hu)).sub (hd.smul hb)
  unfold forceSourceKernel receiverQ
  exact ((hr.mul (hd.pow_const 2)).inv.smul
    ((hD.smul hN).add ((continuous_dot.measurable.comp (ha.prodMk hN)).smul hn)))

lemma measurable_lorentz_acceleration {α : Type*} [MeasurableSpace α]
    {v E B : α→Vec} (hv : Measurable v) (hE : Measurable E) (hB : Measurable B) :
    Measurable (fun x=>fderiv ℝ velocity (v x) (E x+cross (velocity (v x)) (B x))) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have hq := (contDiff_q (k:=0)).continuous.measurable.comp hv
  have hK := hE.add ((contDiff_cross (k:=0)).continuous.measurable.comp (hu.prodMk hB))
  simp_rw [fderiv_velocity_apply]
  exact hq.inv.smul (hK.sub ((continuous_dot.measurable.comp (hu.prodMk hK)).smul hu))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_DirectForce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma measurableSet_directTriangleDomain (T : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (directTriangleDomain T J) :=
  (measurableSet_trianglePhaseDomain T).inter (hJ.preimage measurable_fst.fst)

lemma measurable_directTriangleDensity {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X : ℝ→Vec} (hX : Measurable X)
    {J : Set ℝ} (hJ : MeasurableSet J) {K : TrianglePhase→Vec} (hK : Measurable K) :
    Measurable (directTriangleDensity s X T J K) := by
  have ht : Measurable (fun p : TrianglePhase=>p.1.1) := measurable_fst.fst
  have hσ : Measurable (fun p : TrianglePhase=>p.1.2.1) := measurable_fst.snd.fst
  have hn : Measurable (fun p : TrianglePhase=>p.1.2.2.1) :=
    measurable_subtype_coe.comp measurable_fst.snd.snd
  have hy := hσ.prodMk (((hX.comp ht).sub ((ht.sub hσ).smul hn)).prodMk measurable_snd)
  have hf := (hs.continuous_prefixParticle hT).measurable.comp hy
  exact (((ht.sub hσ).pow_const 2).ennreal_ofReal.mul
    (hf.smul hK).norm.ennreal_ofReal).indicator (measurableSet_directTriangleDomain T hJ)

lemma measurable_directTransportTriangleKernel {V : ℝ→Vec} (hV : Measurable V) :
    Measurable (directTransportTriangleKernel V) := by
  exact measurable_forceTransportFamily (measurable_fst.fst.sub measurable_fst.snd.fst)
    (measurable_subtype_coe.comp measurable_fst.snd.snd)
    ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst.fst)) measurable_snd

lemma measurable_directSourceTriangleKernel {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V) :
    Measurable (directSourceTriangleKernel s X V T) := by
  have ht : Measurable (fun p : TrianglePhase=>p.1.1) := measurable_fst.fst
  have hσ : Measurable (fun p : TrianglePhase=>p.1.2.1) := measurable_fst.snd.fst
  have hn : Measurable (fun p : TrianglePhase=>p.1.2.2.1) :=
    measurable_subtype_coe.comp measurable_fst.snd.snd
  have hy := hσ.prodMk ((hX.comp ht).sub ((ht.sub hσ).smul hn))
  exact measurable_forceSourceFamily (ht.sub hσ) hn
    ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp ht)) measurable_snd
    (measurable_lorentz_acceleration measurable_snd
      ((continuous_prefixField hs.E_smooth.continuousOn hT).measurable.comp hy)
      ((continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp hy))

lemma directTriangle_lintegral_polar {T : ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J) {g : TrianglePhase → ℝ≥0∞} (hg : Measurable g)
    (hsupp : ∀p,p∉directTriangleDomain T J → g p=0) :
    (∫⁻p,g p ∂trianglePhaseMeasure)=
      ∫⁻t in Ioo (0:ℝ) T∩J,∫⁻n : Sphere,∫⁻σ in Ioo (0:ℝ) t,∫⁻v : Vec,
        g ((t,σ,n),v) ∂volume ∂volume ∂sphereMeasure := by
  have hm : Measurable (fun z : ConeCoordinate=>∫⁻v : Vec,g (z,v)) := hg.lintegral_prod_right'
  have he : (∫⁻p,g p ∂trianglePhaseMeasure)=
      ∫⁻t : ℝ,∫⁻σ : ℝ,∫⁻n : Sphere,∫⁻v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure := by
    rw [trianglePhaseMeasure,lintegral_prod _ hg.aemeasurable,lintegral_prod _ hm.aemeasurable]
    apply lintegral_congr
    intro t
    exact lintegral_prod _ (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable
  rw [he,←lintegral_indicator (measurableSet_Ioo.inter hJ)]
  apply lintegral_congr
  intro t
  by_cases ht : t∈Ioo 0 T∩J
  · rw [indicator_of_mem ht]
    have hh : (∫⁻σ : ℝ,∫⁻n : Sphere,∫⁻v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure)=
        ∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,∫⁻v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure := by
      rw [←lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro σ
      by_cases hσ : σ∈Ioo 0 t
      · rw [indicator_of_mem hσ]
      · rw [indicator_of_notMem hσ]
        have hz (n : Sphere) (v : Vec) : g ((t,σ,n),v)=0 :=
          hsupp _ (fun hp=>hσ hp.1.2)
        simp only [hz,lintegral_zero]
    rw [hh]
    exact lintegral_lintegral_swap
      ((hm.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  · rw [indicator_of_notMem ht]
    have hz (σ : ℝ) (n : Sphere) (v : Vec) : g ((t,σ,n),v)=0 :=
      hsupp _ (fun hp=>ht ⟨hp.1.1,hp.2⟩)
    simp only [hz,lintegral_zero]

lemma directTriangleDensity_outside (s : Solution) (X : ℝ→Vec) (T : ℝ)
    (J : Set ℝ) (K : TrianglePhase→Vec) (p : TrianglePhase)
    (hp : p∉directTriangleDomain T J) : directTriangleDensity s X T J K p=0 :=
  indicator_of_notMem hp _

lemma normalised_direct_kernel_identity (s : Solution) (X V : ℝ→Vec) {T t σ : ℝ}
    (ht : t≤T) (hσ : σ∈Ioo 0 t) (n : Sphere) (v : Vec) :
    (1-dot n.1 (velocity (V t))) •
      (s.f (σ,(X t-(t-σ) • n.1,v)) •
        normalisedSignedForce (t-σ) (velocity (V t)) (velocity v) n.1
          (sourceAcceleration s (σ,(X t-(t-σ) • n.1,v))))=
      (t-σ)^2 • (prefixParticle s T (σ,(X t-(t-σ) • n.1,v)) •
        (directTransportTriangleKernel V ((t,σ,n),v)+
          directSourceTriangleKernel s X V T ((t,σ,n),v))) := by
  have hσT : σ∈Icc 0 T := ⟨hσ.1.le,hσ.2.le.trans ht⟩
  rw [smul_comm,normalisedSignedForce_flux n.1 (velocity (V t)) v _
    (sub_pos.mpr hσ.2).ne' (sphere_norm n) (cone_denom_pos (V t) n.1 (sphere_norm n)).ne',smul_comm]
  simp only [directTransportTriangleKernel,directSourceTriangleKernel,prefixParticle,prefixField,
    prefixClamp_eq hσT,sourceAcceleration]

lemma normalised_direct_density_bound (s : Solution) (X V : ℝ→Vec) {T t σ : ℝ}
    {J : Set ℝ} (ht : t∈Ioo 0 T∩J) (hσ : σ∈Ioo 0 t) (n : Sphere) (v : Vec) :
    ENNReal.ofReal ‖(1-dot n.1 (velocity (V t))) •
      (s.f (σ,(X t-(t-σ) • n.1,v)) •
        normalisedSignedForce (t-σ) (velocity (V t)) (velocity v) n.1
          (sourceAcceleration s (σ,(X t-(t-σ) • n.1,v))))‖≤
      directTriangleDensity s X T J (directTransportTriangleKernel V) ((t,σ,n),v)+
      directTriangleDensity s X T J (directSourceTriangleKernel s X V T) ((t,σ,n),v) := by
  rw [normalised_direct_kernel_identity s X V ht.1.2.le hσ n v]
  have hp : ((t,σ,n),v)∈directTriangleDomain T J := ⟨⟨ht.1,hσ⟩,ht.2⟩
  simp only [directTriangleDensity,indicator_of_mem hp]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (t-σ)),
    ENNReal.ofReal_mul (sq_nonneg _),smul_add,←mul_add,
    ←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (norm_add_le _ _))

lemma norm_integral_ENN_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (g : Ω → Vec) :
    ENNReal.ofReal ‖∫p,g p ∂μ‖ ≤ ∫⁻p,ENNReal.ofReal ‖g p‖ ∂μ := by
  simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm g

lemma SmoothClassicalPrefix.direct_force_fiber_bound {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (X V : ℝ→Vec) {J : Set ℝ} {t : ℝ}
    (ht : t∈Ioo 0 T∩J) :
    ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))-
      boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
        (∫⁻n : Sphere,∫⁻σ in Ioo (0:ℝ) t,∫⁻v : Vec,
          (directTriangleDensity s X T J (directTransportTriangleKernel V) ((t,σ,n),v)+
           directTriangleDensity s X T J (directSourceTriangleKernel s X V T) ((t,σ,n),v))
          ∂volume ∂volume ∂sphereMeasure) := by
  rw [hs.retarded_force_source_polar ht.1.1 ht.1.2 (X t) (velocity (V t))
    (norm_velocity_lt_one _),add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0<(4*Real.pi)⁻¹),ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹)]
  apply mul_le_mul' le_rfl
  apply (norm_integral_ENN_bound _).trans
  apply lintegral_mono
  intro n
  apply (norm_integral_ENN_bound _).trans
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with σ hσ
  rw [←integral_smul]
  apply (norm_integral_ENN_bound _).trans
  exact lintegral_mono (normalised_direct_density_bound s X V ht hσ n)

lemma restrict_inside_finite_prefix {T : ℝ} {J : Set ℝ} (hJT : J⊆Icc 0 T) :
    (volume : Measure ℝ).restrict J=volume.restrict (Ioo 0 T∩J) := by
  apply Measure.restrict_congr_set
  filter_upwards [Ioo_ae_eq_Icc (μ:=(volume : Measure ℝ)) (a:=0) (b:=T)] with t ht
  apply propext
  constructor
  · intro hj
    exact ⟨ht.mpr (hJT hj),hj⟩
  · exact fun h=>h.2

private lemma SmoothClassicalPrefix.directForceEnergyPrefix
    {datum : Datum} {solution : Solution} {horizon : ℝ}
    (hs : SmoothClassicalPrefix datum solution horizon) : EnergyPrefix solution horizon := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro time ht position momentum
    have hh := (hs.equations time ht.1.le ht.2).1 position momentum
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro time ht position
    have he := (hs.equations time ht.1.le ht.2).2.1 position
    have hb := (hs.equations time ht.1.le ht.2).2.2.1 position
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

lemma SmoothClassicalPrefix.direct_force_triangle_bound {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (X V : ℝ→Vec)
    (hX : Measurable X) (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJT : J⊆Icc 0 T) :
    (∫⁻t in J,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))-
      boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖)≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
        ((∫⁻p,directTriangleDensity s X T J (directTransportTriangleKernel V) p ∂trianglePhaseMeasure)+
         (∫⁻p,directTriangleDensity s X T J (directSourceTriangleKernel s X V T) p ∂trianglePhaseMeasure)) := by
  let g₁ := directTriangleDensity s X T J (directTransportTriangleKernel V)
  let g₂ := directTriangleDensity s X T J (directSourceTriangleKernel s X V T)
  have hm₁ : Measurable g₁ := measurable_directTriangleDensity hs.directForceEnergyPrefix hT hX hJ
    (measurable_directTransportTriangleKernel hV)
  have hm₂ : Measurable g₂ := measurable_directTriangleDensity hs.directForceEnergyPrefix hT hX hJ
    (measurable_directSourceTriangleKernel hs.directForceEnergyPrefix hT hX hV)
  have hsum : (∫⁻p,g₁ p+g₂ p ∂trianglePhaseMeasure)=
      (∫⁻p,g₁ p ∂trianglePhaseMeasure)+(∫⁻p,g₂ p ∂trianglePhaseMeasure) :=
    lintegral_add_left hm₁ _
  change _≤ENNReal.ofReal (4*Real.pi)⁻¹ *
    ((∫⁻p,g₁ p ∂trianglePhaseMeasure)+(∫⁻p,g₂ p ∂trianglePhaseMeasure))
  rw [←hsum,directTriangle_lintegral_polar (g:=fun p=>g₁ p+g₂ p) hJ (hm₁.add hm₂)
    (fun p hp=>by dsimp only [g₁,g₂]; rw [directTriangleDensity_outside s X T J _ p hp,
      directTriangleDensity_outside s X T J _ p hp]; exact add_zero 0)]
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,restrict_inside_finite_prefix hJT]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.inter hJ)] with t ht
  exact hs.direct_force_fiber_bound X V ht

lemma SmoothClassicalPrefix.direct_lorentz_triangle_bound {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (X V : ℝ→Vec)
    (hX : Measurable X) (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJT : J⊆Icc 0 T) (C : ℝ) (hC : 0≤C)
    (hdatum : ∀t∈Ioo 0 T∩J,‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤C) :
    (∫⁻t in J,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖)≤
      ENNReal.ofReal C*volume J + ENNReal.ofReal (4*Real.pi)⁻¹ *
        ((∫⁻p,directTriangleDensity s X T J (directTransportTriangleKernel V) p ∂trianglePhaseMeasure)+
         (∫⁻p,directTriangleDensity s X T J (directSourceTriangleKernel s X V T) p ∂trianglePhaseMeasure)) := by
  have hpt : ∀ᵐt∂volume.restrict J,
      ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖≤
        ENNReal.ofReal C+ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))-
          boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖ := by
    rw [restrict_inside_finite_prefix hJT]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.inter hJ)] with t ht
    rw [←ENNReal.ofReal_add hC (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _=‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))+
        (s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))-
          boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t)))‖ := by
          congr 1; abel
      _≤_ := (norm_add_le _ _).trans (add_le_add (hdatum t ht) le_rfl)
  apply (lintegral_mono_ae hpt).trans
  rw [lintegral_add_left measurable_const,lintegral_const,Measure.restrict_apply_univ]
  exact add_le_add le_rfl (hs.direct_force_triangle_bound hT X V hX hV hJ hJT)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma SmoothClassicalPrefix.energyPrefix {d : Datum} {s : Solution} {H : ℝ}
    (hs : SmoothClassicalPrefix d s H) : EnergyPrefix s H := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro t ht x v
    have hh := (hs.equations t ht.1.le ht.2).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.equations t ht.1.le ht.2).2.1 x
    have hb := (hs.equations t ht.1.le ht.2).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

end RVM

open Set MeasureTheory
open scoped ENNReal

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_DirectLorentzUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.supported_boundary_force_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀(T : ℝ),0≤T → T≤T₀ →
      ∀(E B : Field) (F : PhaseFlowOn E B T) (zX : Phase), zX∈tsupport d.f₀ →
      ∀t∈Ioc (0:ℝ) T,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
        (velocity (F.flow zX t).2)‖≤C := by
  obtain ⟨R,hR⟩ := hd.2.1.bddAbove_image
    (show ContinuousOn (fun z : Phase=>‖z.1‖) (tsupport d.f₀) from continuous_fst.norm.continuousOn)
  obtain ⟨C,hC,hb⟩ := boundaryLorentzForce_datum_bound hd (max 1 T₀) (R+max 1 T₀)
  refine ⟨C,hC,?_⟩
  intro T hT hTT E B F zX hz t ht
  have hx0 : ‖zX.1‖≤R := hR ⟨zX,hz,rfl⟩
  have hh := (F.position_lipschitz zX).dist_le_mul t ⟨ht.1.le,ht.2⟩ 0 ⟨le_rfl,hT⟩
  simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1.le] at hh
  apply hb t ⟨ht.1,ht.2.trans (hTT.trans (le_max_right _ _))⟩ (F.flow zX t).1 _ _ (norm_velocity_lt_one _).le
  rw [mem_closedBall,dist_zero_right]
  calc
    ‖(F.flow zX t).1‖=‖((F.flow zX t).1-zX.1)+zX.1‖ := by rw [sub_add_cancel]
    _≤‖(F.flow zX t).1-zX.1‖+‖zX.1‖ := norm_add_le _ _
    _≤t+R := add_le_add (by simpa only [dist_eq_norm] using hh) hx0
    _≤R+max 1 T₀ := by linarith only [ht.2,hTT,le_max_right (1:ℝ) T₀]

lemma Admissible.direct_lorentz_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) →
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀(zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)≤
      ENNReal.ofReal (C*Real.sqrt w*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cb,hCb,hdatum⟩ := hd.supported_boundary_force_uniform T₀
  obtain ⟨Ct,hCt,htrans⟩ := hd.direct_transport_uniform T₀
  obtain ⟨Cs,hCs,hsource⟩ := hd.direct_source_absolute_uniform T₀
  refine ⟨Cb+(4*Real.pi)⁻¹*(Ct+Cs),by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hphysical hband HZ
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hsw : 1≤Real.sqrt w := by simpa using Real.sqrt_le_sqrt hw
  have hIB : I≤B := by
    have hIs : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I]
    exact hIs.trans ((le_mul_of_one_le_left (Real.sqrt_nonneg I) hP).trans
      (show P*Real.sqrt I≤B from le_add_of_nonneg_right (by positivity)))
  have hJB : b-a≤Real.sqrt w*B := hJI.trans (hIB.trans (by nlinarith))
  have hcon := (F.continuous_prefixFlow hs.energyPrefix hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hX : Measurable X := hcon.fst.measurable
  have hV : Measurable V := hcon.snd.measurable
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hDb : ∀t∈Ioo 0 T∩Icc a b,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (X t) (velocity (V t))‖≤Cb := by
    intro t ht
    dsimp only [X,V,prefixFlow]
    rw [prefixClamp_eq (hJ ht.2)]
    exact hdatum T hT hTT s.E s.B F zX hzX t ⟨ht.1.1,ht.1.2.le⟩
  have hraw : (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)=
      ∫⁻t in Icc a b,ENNReal.ofReal ‖s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))‖ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [prefixMomentumForce,lorentzField,lorentzPhase,X,V,prefixFlow,prefixClamp_eq (hJ ht)]
  rw [hraw]
  apply (hs.direct_lorentz_triangle_bound hT X V hX hV measurableSet_Icc hJ Cb hCb hDb).trans
  have hD : ENNReal.ofReal Cb*volume (Icc a b)≤ENNReal.ofReal (Cb*Real.sqrt w*B) := by
    rw [Real.volume_Icc,←ENNReal.ofReal_mul hCb]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hJB hCb
  have ht := htrans M A P hM (zero_le_one.trans hA) hP hL s T F hs hT hTT zX a b I w
    hzX ha hb hI hI1 hJI (zero_lt_one.trans_le hw) hwP hphysical hband HZ
  have hs' := hsource M A P hM hA hP hL s T F hs hT hTT zX a b I w
    hzX ha hb hab hI hI1 hJI hw hwP hIP hphysical hband HZ
  have ht' := ht.trans (show ENNReal.ofReal (Ct*B)≤ENNReal.ofReal (Ct*Real.sqrt w*B) from
    ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsw hCt) hB
      simpa only [mul_one] using hh))
  apply (add_le_add hD (mul_le_mul' le_rfl (add_le_add ht' hs'))).trans_eq
  rw [←ENNReal.ofReal_add (by positivity : 0≤Ct*Real.sqrt w*B) (by positivity : 0≤Cs*Real.sqrt w*B),
    ←ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹),
    ←ENNReal.ofReal_add (by positivity : 0≤Cb*Real.sqrt w*B) (by positivity)]
  congr 1
  ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BulkTestWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma bounded_supported_test_mass {a b T : ℝ} {ψ : ℝ→ℝ}
    (hab : a≤b) (hψ : Continuous ψ) (hψ1 : ∀t,|ψ t|≤1)
    (hout : ∀t∉Icc a b,ψ t=0) : (∫t in Ioo (0:ℝ) T,|ψ t|)≤b-a := by
  have hs : tsupport ψ⊆Icc a b := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra hn
    exact ht (hout t hn)
  have hc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) hs
  have hi : Integrable ψ := hψ.integrable_of_hasCompactSupport hc
  have hone : Integrable ((Icc a b).indicator (fun _ : ℝ=>(1:ℝ))) :=
    (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  calc
    _≤∫t : ℝ,|ψ t| := setIntegral_le_integral hi.norm (ae_of_all _ (fun t=>abs_nonneg _))
    _≤∫t : ℝ,(Icc a b).indicator (fun _ : ℝ=>(1:ℝ)) t := by
      apply integral_mono hi.norm hone
      intro t
      by_cases ht : t∈Icc a b
      · rw [indicator_of_mem ht]; exact hψ1 t
      · simp [indicator_of_notMem ht,hout t ht]
    _=b-a := by rw [integral_indicator measurableSet_Icc, integral_const]; simp [hab]

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BulkReceiverResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.force_bulk_retarded_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cr,hCr,hresidual⟩ := hd.force_bulk_receiver_residual_uniform T₀ D hD
  obtain ⟨Ca,hCa,habsolute⟩ := hd.direct_lorentz_uniform T₀
  refine ⟨(4*Real.pi)⁻¹*(Cr+Cr*Ca),by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hresidual M A hM hA] with P hres
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  have hr := hres hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  have ha' := habsolute M A P hM hA hP hL s T F hs hT hTT zX a b I w
    hzX ha hb hab hI hI1 hJI hw hwP hIP hphysical hband HZ
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hc : w^(-1/2:ℝ)*Real.sqrt w=1 := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hw0]
    norm_num
  apply hr.trans
  apply (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl ha'))).trans_eq
  rw [←ENNReal.ofReal_mul (by positivity : 0≤Cr*w^(-1/2:ℝ)),
    ←ENNReal.ofReal_add (by positivity : 0≤Cr*B) (by positivity),
    ←ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹)]
  congr 1
  change (4*Real.pi)⁻¹*(Cr*B+Cr*w^(-1/2:ℝ)*(Ca*Real.sqrt w*B))=_
  calc
    _=(4*Real.pi)⁻¹*(Cr*B+Cr*Ca*(w^(-1/2:ℝ)*Real.sqrt w)*B) := by ring
    _=_ := by rw [hc]; ring

lemma Admissible.force_bulk_uniform_oai {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1)))‖ ≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cr,hCr,hretarded⟩ := hd.force_bulk_retarded_uniform T₀ D hD
  obtain ⟨Cb,hCb,hdatum⟩ := hd.supported_boundary_force_uniform T₀
  refine ⟨Cr+Cb,add_nonneg hCr hCb,?_⟩
  intro M A hM hA
  filter_upwards [hretarded M A hM hA] with P hret
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let K := fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))
  let G := fun t=>boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)
  have hB : 0≤B := by dsimp [B]; positivity
  have hIB : I≤B := by
    have hi : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I]
    exact hi.trans ((le_mul_of_one_le_left (Real.sqrt_nonneg I) hP).trans
      (show P*Real.sqrt I≤B from le_add_of_nonneg_right (by positivity)))
  have hiK : IntegrableOn (fun t=>ψ t • K t) (Ioo (0:ℝ) T) := by
    have hi := ((hψ.continuous.smul (F.continuous_prefixMomentumForce hs.energyPrefix hT zX)).continuousOn.integrableOn_Icc
      (μ:=volume) (a:=0) (b:=T)).mono_set Ioo_subset_Icc_self
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change ψ t • prefixMomentumForce s F.flow T zX t=ψ t • K t
    simp only [K,prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht),lorentzField,lorentzPhase]
  have hiR : IntegrableOn (fun t=>ψ t • (K t-G t)) (Ioo (0:ℝ) T) := by
    let W := fun t=>ψ t • ContinuousLinearMap.id ℝ Vec
    have hW : Continuous W := hψ.continuous.smul continuous_const
    simpa only [W,smul_apply,ContinuousLinearMap.id_apply] using
      hs.multiplier_retarded_force_integrable hT F zX hW.continuousOn
  have hiG : IntegrableOn (fun t=>ψ t • G t) (Ioo (0:ℝ) T) := by
    apply (hiK.sub hiR).congr
    exact ae_of_all _ (fun t=>by simp only [Pi.sub_apply,smul_sub,sub_sub_cancel])
  have hG : ‖∫t in Ioo (0:ℝ) T,ψ t • G t‖≤Cb*B := by
    apply le_trans (b:=Cb*(∫t in Ioo (0:ℝ) T,|ψ t|))
    · rw [←integral_const_mul]
      apply norm_integral_le_of_norm_le
        (((hψ.continuous.norm.const_mul Cb).continuousOn.integrableOn_Icc (a:=0) (b:=T)).mono_set Ioo_subset_Icc_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [norm_smul,Real.norm_eq_abs,mul_comm Cb]
      exact mul_le_mul_of_nonneg_left (hdatum T hT hTT s.E s.B F zX hzX t ⟨ht.1,ht.2.le⟩) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left
        ((bounded_supported_test_mass hab hψ.continuous hψ1 hout).trans (hJI.trans hIB)) hCb
  have he : (∫t in Ioo (0:ℝ) T,ψ t • K t)=
      (∫t in Ioo (0:ℝ) T,ψ t • (K t-G t))+(∫t in Ioo (0:ℝ) T,ψ t • G t) := by
    simp_rw [smul_sub]
    rw [integral_sub hiK hiG,sub_add_cancel]
  have hr := hret hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  change ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t • K t‖≤_
  rw [he]
  apply (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans
  rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  apply (add_le_add hr (ENNReal.ofReal_le_ofReal hG)).trans_eq
  rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCb hB)]
  congr 1
  change Cr*B+Cb*B=(Cr+Cb)*B
  ring

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.force_bulk_uniform_oai := @OAI.RVM.Admissible.force_bulk_uniform_oai
