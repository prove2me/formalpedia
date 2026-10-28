-- Prove2me | solution 1 for OAI.RVM.Admissible.direction_complete_count_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:54:22.148629+00:00
-- url     : https://prove2.me/submissions/e7353888-54a8-4eb3-88fe-869fca28084b

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direction_physical_family_log_bound
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_multiplier_retarded_force_integrable

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

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

lemma hasDerivAt_dot {f g : ℝ → Vec} {f' g' : Vec} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => dot (f t) (g t))
      (dot (f s) g' + dot f' (g s)) s := by
  simpa only [dot_eq_inner] using hf.inner ℝ hg

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_BallCutoff
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_NullConeFlux
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
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

lemma velocityProjection_norm (u b : Vec) (hu : ‖u‖ ≤ 1) :
    ‖velocityProjection u b‖ ≤ ‖b‖ := by
  have hsq : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have he : ‖velocityProjection u b‖^2 =
      ‖b‖^2 - 2*(dot u b)^2+(dot u b)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm b u]
    ring
  have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg (dot u b))
  nlinarith [norm_nonneg (velocityProjection u b), norm_nonneg b]

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

lemma transverseProjection_norm (w h : Vec) : ‖transverseProjection w h‖≤‖h‖ := by
  apply velocityProjection_norm
  by_cases hw : w=0
  · simp [hw]
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

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


lemma dot_zero_right_rvm (a : Vec) : dot a 0=0 := by simp [dot]

lemma hasDerivAt_norm_nonzero {Y : ℝ → Vec} {u : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h0 : Y s≠0) :
    HasDerivAt (fun t => ‖Y t‖) (dot (Y s) u / ‖Y s‖) s := by
  have hn := (hY.differentiableAt.norm ℝ h0).hasDerivAt
  have he := (hn.pow 2).unique hY.norm_sq
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,← dot_eq_inner] at he
  have hr : ‖Y s‖≠0 := norm_ne_zero_iff.mpr h0
  have he' : deriv (fun t => ‖Y t‖) s = dot (Y s) u / ‖Y s‖ := by
    apply (eq_div_iff hr).mpr
    linarith
  rwa [he'] at hn

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MomentumDirection
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
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma hasDerivAt_momentumDirection {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) :
    HasDerivAt (momentumDirection ∘ V)
      (‖V t‖⁻¹ • transverseProjection (V t) K) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hh := (hn.inv (norm_ne_zero_iff.mpr hv)).smul hV
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,transverseProjection,velocityProjection,dot_smul_left,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp
  ring

lemma hasDerivAt_angularMultiplier {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) (w : ℝ) (h : Vec) :
    HasDerivAt (fun r => angularMultiplier w (V r) h)
      ((-w/‖V t‖^2) •
        (dot (momentumDirection (V t)) K • transverseProjection (V t) h +
         dot (momentumDirection (V t)) h • transverseProjection (V t) K +
         dot (transverseProjection (V t) K) h • momentumDirection (V t))) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hξ := hasDerivAt_momentumDirection hV hv
  have hP := (hasDerivAt_const t h).sub
    ((hasDerivAt_dot hξ (hasDerivAt_const t h)).smul hξ)
  have hh := ((hasDerivAt_const t w).div hn (norm_ne_zero_iff.mpr hv)).smul hP
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.div_apply,Pi.sub_apply,Pi.smul_apply',momentumDirection,transverseProjection,velocityProjection,dot_smul_left,
      dot_sub_left,dot_zero_right_rvm,Function.comp_apply,zero_add,zero_sub,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,smul_eq_mul,
      zero_mul]
  field_simp
  ring

lemma transverseCLM_apply (v h : Vec) : transverseCLM v h=transverseProjection v h := by
  simp only [transverseCLM,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]
  rfl

lemma angularMultiplierCLM_apply (w : ℝ) (v h : Vec) :
    angularMultiplierCLM w v h=angularMultiplier w v h := by
  simp only [angularMultiplierCLM,smul_apply,transverseCLM_apply,angularMultiplier]

lemma contDiffAt_transverseCLM {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k transverseCLM v := by
  have hξ : ContDiffAt ℝ k momentumDirection v :=
    ((contDiffAt_id.norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id
  exact contDiffAt_const.sub (((InnerProductSpace.toDual ℝ Vec).contDiff.of_le hk).contDiffAt.comp v hξ |>.smulRight hξ)

lemma contDiffAt_angularMultiplierCLM (w : ℝ) {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k (angularMultiplierCLM w) v := by
  exact (contDiffAt_const.div (contDiffAt_id.norm ℝ hv) (norm_ne_zero_iff.mpr hv)).smul
    (contDiffAt_transverseCLM hv hk)

lemma angularDerivativeCLM_apply (w : ℝ) (v K h : Vec) :
    angularDerivativeCLM w v K h = (-w/‖v‖^2) •
      (dot (momentumDirection v) K • transverseProjection v h +
       dot (momentumDirection v) h • transverseProjection v K +
       dot (transverseProjection v K) h • momentumDirection v) := by
  simp only [angularDerivativeCLM,smul_apply,add_apply,
    transverseCLM_apply,ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]

lemma hasDerivAt_angularMultiplierCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t≠0) (w : ℝ) :
    HasDerivAt (fun r=>angularMultiplierCLM w (V r)) (angularDerivativeCLM w (V t) K) t := by
  have hd := ((contDiffAt_angularMultiplierCLM w hv (k:=1) (by simp)).differentiableAt one_ne_zero).comp t hV.differentiableAt
  have he : deriv (fun r=>angularMultiplierCLM w (V r)) t=angularDerivativeCLM w (V t) K := by
    apply ContinuousLinearMap.ext
    intro h
    have hh := hd.hasDerivAt.clm_apply (hasDerivAt_const t h)
    simp only [ContinuousLinearMap.map_zero,add_zero,Function.comp_apply,angularMultiplierCLM_apply] at hh
    exact hh.unique (by simpa only [angularDerivativeCLM_apply] using hasDerivAt_angularMultiplier hV hv w h)
  rw [←he]
  exact hd.hasDerivAt



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


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_AngularBump
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

lemma extendedAngularCLM_contDiff (w : ℝ) (hw : 0<w) :
    ContDiff ℝ ∞ (extendedAngularCLM w hw) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v=0
  · subst v
    apply (contDiffAt_const (c:=(0:Vec→L[ℝ]Vec))).congr_of_eventuallyEq
    have he := (angularZeroBump w hw).eventuallyEq_one_of_mem_ball
      (show (0:Vec)∈ball 0 (angularZeroBump w hw).rIn by simpa only [mem_ball,dist_self,angularZeroBump] using div_pos hw (by norm_num : (0:ℝ)<64))
    filter_upwards [he] with v hv
    change (1-angularZeroBump w hw v) • angularMultiplierCLM w v=0
    simp only [hv,Pi.one_apply,sub_self]
    exact zero_smul ℝ (angularMultiplierCLM w v)
  · exact ((contDiffAt_const.sub (angularZeroBump w hw).contDiff.contDiffAt).smul
      (contDiffAt_angularMultiplierCLM w hv le_rfl))

lemma extendedAngularCLM_eq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32≤‖v‖) :
    extendedAngularCLM w hw v=angularMultiplierCLM w v := by
  have hz := (angularZeroBump w hw).zero_of_le_dist (by simpa only [dist_zero_right,angularZeroBump] using hv)
  simp only [extendedAngularCLM,hz,sub_zero,one_smul]

lemma extendedAngularCLM_eventuallyEq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) :
    extendedAngularCLM w hw =ᶠ[𝓝 v] angularMultiplierCLM w := by
  have he : ∀ᶠ z : Vec in 𝓝 v,w/32<‖z‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds hv)
  filter_upwards [he] with z hz
  exact extendedAngularCLM_eq w hw hz.le

lemma hasDerivAt_extendedAngularCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (w : ℝ) (hw : 0<w) :
    HasDerivAt (fun r=>extendedAngularCLM w hw (V r))
      (fderiv ℝ (extendedAngularCLM w hw) (V t) K) t :=
  ((extendedAngularCLM_contDiff w hw).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hV

lemma extendedAngularCLM_fderiv (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) (K : Vec) :
    fderiv ℝ (extendedAngularCLM w hw) v K=angularDerivativeCLM w v K := by
  have hv0 : v≠0 := norm_pos_iff.mp ((div_pos hw (by norm_num : (0:ℝ)<32)).trans hv)
  have hcurve : HasDerivAt (fun r : ℝ=>v+r • K) K 0 := by
    convert (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const K) using 1 <;> first | rfl | simp only [one_smul,zero_add]
  have ht : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 v) := by
    have hc : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 (v+(0:ℝ) • K)) := hcurve.continuousAt
    simpa only [zero_smul,add_zero] using hc
  have he := (extendedAngularCLM_eventuallyEq w hw hv).comp_tendsto ht
  have ha := (hasDerivAt_angularMultiplierCLM hcurve (by simpa using hv0) w).congr_of_eventuallyEq he
  have hb := hasDerivAt_extendedAngularCLM hcurve w hw
  simpa only [zero_smul,add_zero] using hb.unique ha

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

lemma PhaseFlowOn.prefixMomentum_hasDerivAt {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) (ht : t∈Ioo 0 T) :
    HasDerivAt (fun r=>(prefixFlow F.flow T z r).2)
      (lorentzField E B (t,F.flow z t)).2 t := by
  have hd : HasDerivAt (fun r=>(F.flow z r).2) (lorentzField E B (t,F.flow z t)).2 t :=
    ((F.ode z t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).snd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  simp only [prefixFlow,prefixClamp_eq hr]

lemma PhaseFlowOn.prefixAngular_regular {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (hw : 0<w) (z : Phase) :
    Continuous (prefixAngularMultiplier s F.flow T w hw z) ∧
    Continuous (prefixAngularRate s F.flow T w hw z) ∧
    ∀t∈Ioo 0 T,HasDerivAt (prefixAngularMultiplier s F.flow T w hw z)
      (prefixAngularRate s F.flow T w hw z t) t := by
  have hV : Continuous (fun t=>(prefixFlow F.flow T z t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd
  have hd := extendedAngularCLM_contDiff w hw
  refine ⟨hd.continuous.comp hV,(hd.continuous_fderiv (by simp)).comp hV |>.clm_apply
    (F.continuous_prefixMomentumForce hs hT z),?_⟩
  intro t ht
  change HasDerivAt (fun r=>extendedAngularCLM w hw (prefixFlow F.flow T z r).2)
    (fderiv ℝ (extendedAngularCLM w hw) (prefixFlow F.flow T z t).2
      (prefixMomentumForce s F.flow T z t)) t
  have he : prefixMomentumForce s F.flow T z t=(lorentzField s.E s.B (t,F.flow z t)).2 := by
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht)]
  rw [he]
  exact hasDerivAt_extendedAngularCLM (F.prefixMomentum_hasDerivAt z ht) w hw

lemma prefixAngular_highband {s : Solution} {α : Phase→ℝ→Phase} {T t w : ℝ}
    (hw : 0<w) (z : Phase) (ht : t∈Icc 0 T) (hv : w/16≤‖(α z t).2‖) :
    prefixAngularMultiplier s α T w hw z t=angularMultiplierCLM w (α z t).2 ∧
    prefixAngularRate s α T w hw z t=angularDerivativeCLM w (α z t).2
      (lorentzField s.E s.B (t,α z t)).2 := by
  have hnorm : w/32<‖(α z t).2‖ := by linarith
  simp only [prefixAngularMultiplier,prefixAngularRate,prefixMomentumForce,prefixFlow,prefixClamp_eq ht]
  exact ⟨extendedAngularCLM_eq w hw hnorm.le,extendedAngularCLM_fderiv w hw hnorm _⟩

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ClippedRamp
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
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma clippedRamp_lipschitz (a ℓ : ℝ) : LipschitzWith ‖ℓ⁻¹‖₊ (clippedRamp a ℓ) := by
  have h : LipschitzWith ‖ℓ⁻¹‖₊ (fun t : ℝ=>(t-a)/ℓ) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [Real.dist_eq,coe_nnnorm,Real.norm_eq_abs]
    rw [←sub_div,sub_sub_sub_cancel_right,abs_div]
    simp only [div_eq_mul_inv,abs_inv]
    exact le_of_eq (mul_comm _ _)
  exact (h.const_max 0).const_min 1

lemma clippedRamp_of_le {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : t≤a) : clippedRamp a ℓ t=0 := by
  rw [clippedRamp,max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hℓ.le)]
  norm_num

lemma clippedRamp_of_ge {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : a+ℓ≤t) : clippedRamp a ℓ t=1 := by
  have h : 1≤(t-a)/ℓ := (le_div_iff₀ hℓ).mpr (by linarith)
  rw [clippedRamp,min_eq_left (le_trans h (le_max_right _ _))]

lemma clippedRamp_of_between {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : t∈Icc a (a+ℓ)) :
    clippedRamp a ℓ t=(t-a)/ℓ := by
  have h0 : 0≤(t-a)/ℓ := div_nonneg (sub_nonneg.mpr ht.1) hℓ.le
  have h1 : (t-a)/ℓ≤1 := (div_le_iff₀ hℓ).mpr (by linarith [ht.2])
  rw [clippedRamp,max_eq_right h0,min_eq_right h1]

lemma directionWeight_lipschitz (a b ℓ : ℝ) :
    LipschitzWith (‖ℓ⁻¹‖₊+‖ℓ⁻¹‖₊) (directionWeight a b ℓ) :=
  (clippedRamp_lipschitz a ℓ).sub (clippedRamp_lipschitz (b-ℓ) ℓ)

lemma directionWeight_left {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Icc a (a+ℓ)) : directionWeight a b ℓ t=(t-a)/ℓ := by
  rw [directionWeight,clippedRamp_of_between hℓ ht,clippedRamp_of_le hℓ (by linarith [ht.2]),sub_zero]

lemma directionWeight_right {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Icc (b-ℓ) b) : directionWeight a b ℓ t=(b-t)/ℓ := by
  rw [directionWeight,clippedRamp_of_ge hℓ (by linarith [ht.1]),
    clippedRamp_of_between hℓ (by simpa only [sub_add_cancel] using ht)]
  field_simp
  ring

lemma directionWeight_endpoints {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    directionWeight a b ℓ a=0 ∧ directionWeight a b ℓ b=0 := by
  constructor
  · rw [directionWeight_left hℓ hab ⟨le_rfl,by linarith⟩,sub_self,zero_div]
  · rw [directionWeight_right hℓ hab ⟨by linarith,le_rfl⟩,sub_self,zero_div]

lemma directionWeight_bounds {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    0≤directionWeight a b ℓ t ∧ directionWeight a b ℓ t≤1 := by
  have hmon : clippedRamp (b-ℓ) ℓ t ≤ clippedRamp a ℓ t := by
    apply min_le_min le_rfl
    apply max_le_max le_rfl
    exact div_le_div_of_nonneg_right (by linarith) hℓ.le
  have h0 (c : ℝ) : 0 ≤ clippedRamp c ℓ t := le_min (by norm_num) (le_max_left _ _)
  have h1 (c : ℝ) : clippedRamp c ℓ t≤1 := min_le_left _ _
  unfold directionWeight
  constructor
  · exact sub_nonneg.mpr hmon
  · linarith [h0 (b-ℓ),h1 a]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedMomentumForce
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
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff



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


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


lemma directionWeight_tsupport {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    tsupport (directionWeight a b ℓ)⊆Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have he : directionWeight a b ℓ t=0 := by
    rcases not_and_or.mp hn with ht|ht
    all_goals rw [not_le] at ht
    · rw [directionWeight,clippedRamp_of_le hℓ ht.le,clippedRamp_of_le hℓ (by linarith),sub_self]
    · rw [directionWeight,clippedRamp_of_ge hℓ (by linarith),clippedRamp_of_ge hℓ (by linarith),sub_self]
  exact ht he



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


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedReceiverWeightBoundFinite
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

lemma directionWeight_ne_zero_interior {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : directionWeight a b ℓ t≠0) : t∈Ioo a b := by
  have hc : t∈Icc a b := directionWeight_tsupport hℓ hab (subset_closure ht)
  refine ⟨lt_of_le_of_ne hc.1 ?_,lt_of_le_of_ne hc.2 ?_⟩
  · intro he
    subst t
    exact ht (directionWeight_endpoints hℓ hab).1
  · intro he
    subst t
    exact ht (directionWeight_endpoints hℓ hab).2

lemma directionWeight_sum_le_one {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) (t : ℝ) :
    ∑i∈S,directionWeight (a i) (b i) (ℓ i) t≤1 := by
  classical
  by_cases hz : ∀i∈S,directionWeight (a i) (b i) (ℓ i) t=0
  · simp only [Finset.sum_eq_zero hz,zero_le_one]
  · push Not at hz
    obtain ⟨i,hi,hit⟩ := hz
    rw [Finset.sum_eq_single i]
    · exact (directionWeight_bounds (hℓ i hi) (hlen i hi)).2
    · intro j hj hji
      by_contra hn
      exact Set.disjoint_left.mp (hdis hi hj (Ne.symm hji))
        (directionWeight_ne_zero_interior (hℓ i hi) (hlen i hi) hit)
        (directionWeight_ne_zero_interior (hℓ j hj) (hlen j hj) hn)
    · exact fun hn=>(hn hi).elim

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeClosedBinSourceIndices
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

lemma angularMultiplierCLM_norm_le {w : ℝ} (hw : 0<w) {v : Vec}
    (hv : w/64 ≤ ‖v‖) : ‖angularMultiplierCLM w v‖ ≤ 64 := by
  have hρ : 0<‖v‖ := (div_pos hw (by norm_num)).trans_le hv
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos hw hρ)]
  apply mul_le_mul _ (transverseProjection_norm v h) (norm_nonneg _) (by norm_num)
  apply (div_le_iff₀ hρ).mpr
  linarith only [hv]

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

lemma directionWeight_integrable {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ ≤ b-a) :
    Integrable (directionWeight a b ℓ) := by
  have hc : HasCompactSupport (directionWeight a b ℓ) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (directionWeight_tsupport hℓ hab)
  exact (directionWeight_lipschitz a b ℓ).continuous.integrable_of_hasCompactSupport hc

lemma directionWeight_family_mass {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i ≤ b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    {c d T : ℝ} (hcd : c ≤ d) (hcell : ∀i∈S,Icc (a i) (b i)⊆Icc c d) :
    (∑i∈S,∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) ≤ d-c := by
  have hi (i : ι) (hi : i∈S) : Integrable (directionWeight (a i) (b i) (ℓ i)) :=
    directionWeight_integrable (hℓ i hi) (hlen i hi)
  have hn (i : ι) (hi : i∈S) (t : ℝ) : 0 ≤ directionWeight (a i) (b i) (ℓ i) t :=
    (directionWeight_bounds (hℓ i hi) (hlen i hi)).1
  have hsumint : Integrable (fun t=>∑i∈S,directionWeight (a i) (b i) (ℓ i) t) :=
    integrable_finsetSum S hi
  calc
    _ = ∫t in Ioo (0:ℝ) T,∑i∈S,directionWeight (a i) (b i) (ℓ i) t := by
      rw [integral_finsetSum S (fun i hiS=>(hi i hiS).integrableOn)]
      apply Finset.sum_congr rfl
      intro i hiS
      simp_rw [abs_of_nonneg (hn i hiS _)]
    _ ≤ ∫t,∑i∈S,directionWeight (a i) (b i) (ℓ i) t :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (fun t=>Finset.sum_nonneg (fun i hiS=>hn i hiS t))) hsumint
    _ = ∫t in Icc c d,∑i∈S,directionWeight (a i) (b i) (ℓ i) t := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      apply Finset.sum_eq_zero
      intro i hiS
      exact image_eq_zero_of_notMem_tsupport
        (fun hit=>ht (hcell i hiS (directionWeight_tsupport (hℓ i hiS) (hlen i hiS) hit)))
    _ ≤ ∫_t in Icc c d,(1:ℝ) := by
      apply integral_mono_ae hsumint.integrableOn (integrableOn_const measure_Icc_lt_top.ne)
      exact ae_of_all _ (fun t=>directionWeight_sum_le_one S a b ℓ hℓ hlen hdis t)
    _ = d-c := by
      simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hcd),smul_eq_mul,mul_one]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


private lemma SmoothClassicalPrefix.directionCountsEnergyPrefix
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

lemma Admissible.supported_boundary_force_uniform_bound {d : Datum} (hd : Admissible d)
    (T₀ : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (T : ℝ), 0≤T → T≤T₀ → ∀ (E B : Field) (F : PhaseFlowOn E B T) (zX : Phase),
      zX∈tsupport d.f₀ → ∀t∈Ioc (0:ℝ) T,
      ‖boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
        (velocity (F.flow zX t).2)‖ ≤ C := by
  obtain ⟨R,hR⟩ := hd.2.1.bddAbove_image
    (show ContinuousOn (fun z : Phase=>‖z.1‖) (tsupport d.f₀) from continuous_fst.norm.continuousOn)
  obtain ⟨C,hC,hb⟩ := boundaryLorentzForce_datum_bound hd T₀ (R+T₀)
  refine ⟨C,hC,?_⟩
  intro T hT hTT E B F zX hz t ht
  have hx0 : ‖zX.1‖ ≤ R := hR ⟨zX,hz,rfl⟩
  have hh := (F.position_lipschitz zX).dist_le_mul t ⟨ht.1.le,ht.2⟩ 0 ⟨le_rfl,hT⟩
  simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1.le] at hh
  apply hb t ⟨ht.1,ht.2.trans hTT⟩ (F.flow zX t).1 _ _ (norm_velocity_lt_one _).le
  rw [mem_closedBall,dist_zero_right]
  calc
    ‖(F.flow zX t).1‖=‖((F.flow zX t).1-zX.1)+zX.1‖ := by rw [sub_add_cancel]
    _ ≤ ‖(F.flow zX t).1-zX.1‖+‖zX.1‖ := norm_add_le _ _
    _ ≤ t+R := add_le_add (by simpa only [dist_eq_norm] using hh) hx0
    _ ≤ R+T₀ := by linarith only [ht.2,hTT]

lemma Admissible.direction_family_datum_uniform_bound {d : Datum} (hd : Admissible d)
    (T₀ : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (T : ℝ), 0≤T → T≤T₀ → ∀ (E B : Field) (F : PhaseFlowOn E B T) (zX : Phase),
      zX∈tsupport d.f₀ → ∀(w c e : ℝ),0<w → c ≤ e →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i ≤ b i-a i) →
      (∀i∈S,Icc (a i) (b i)⊆Icc c e) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∀i∈S,∀t∈Icc (a i) (b i),w/16 ≤ ‖(F.flow zX t).2‖) →
      (∑i∈S,‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t •
        angularMultiplierCLM w (F.flow zX t).2
          (boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
            (velocity (F.flow zX t).2))‖) ≤ C*(e-c) := by
  obtain ⟨C,hC,hbound⟩ := hd.supported_boundary_force_uniform_bound T₀
  refine ⟨64*C,by positivity,?_⟩
  intro T hT hTT E B F zX hz w c e hw hce ι S a b ℓ hℓ hlen hcell hdis hband
  have hbnd (i : ι) (hi : i∈S) :
      ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t •
        angularMultiplierCLM w (F.flow zX t).2
          (boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1
            (velocity (F.flow zX t).2))‖ ≤
      64*C*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := by
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le ((directionWeight_integrable (hℓ i hi) (hlen i hi)).norm.const_mul _).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    by_cases hψ : directionWeight (a i) (b i) (ℓ i) t=0
    · simp only [hψ,zero_smul,norm_zero,mul_zero,le_refl]
    · have htc := (directionWeight_ne_zero_interior (hℓ i hi) (hlen i hi) hψ)
      have hG := angularMultiplierCLM_norm_le hw
        (show w/64 ≤ ‖(F.flow zX t).2‖ by linarith only [hw,hband i hi t (Ioo_subset_Icc_self htc)])
      have hB := hbound T hT hTT E B F zX hz t ⟨ht.1,ht.2.le⟩
      rw [norm_smul,Real.norm_eq_abs]
      calc
        _ ≤ |directionWeight (a i) (b i) (ℓ i) t| * (64*C) :=
          mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul hG hB (norm_nonneg _) (by norm_num))) (abs_nonneg _)
        _ = _ := by ring
  calc
    _ ≤ ∑i∈S,64*C*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := Finset.sum_le_sum hbnd
    _ = 64*C*(∑i∈S,∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (directionWeight_family_mass S a b ℓ hℓ hlen hdis hce hcell) (by positivity)



section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal


namespace WeightedDirectionPartition
variable {V K : ℝ → Vec} {a b w δ : ℝ}

lemma cell_subset (D : WeightedDirectionPartition V K a b w δ)
    {i : ℕ} (hi : i < D.count) : Icc (D.time i) (D.time (i+1)) ⊆ Icc a b :=
  Icc_subset_Icc (D.time_mem i (by omega)).1 (D.time_mem (i+1) (by omega)).2

lemma interiors_disjoint (D : WeightedDirectionPartition V K a b w δ) :
    (Finset.range (D.count-1) : Set ℕ).Pairwise
      (fun i j => Disjoint (Ioo (D.time i) (D.time (i+1)))
        (Ioo (D.time j) (D.time (j+1)))) := by
  intro i hi j hj hne
  have hi' : i < D.count-1 := Finset.mem_range.mp hi
  have hj' : j < D.count-1 := Finset.mem_range.mp hj
  apply Ioo_disjoint_Ioo.mpr
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (min_le_left _ _).trans ((D.strict.monotoneOn (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)).trans (le_max_right _ _))
  · exact (min_le_right _ _).trans ((D.strict.monotoneOn (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)).trans (le_max_left _ _))

lemma complete_force_lower (D : WeightedDirectionPartition V K a b w δ) :
    (D.count-1 : ℕ)*w*δ/2 ≤ ∑ i ∈ Finset.range (D.count-1),
      ‖∫ t in D.time i..D.time (i+1),
        directionWeight (D.time i) (D.time (i+1)) (D.ramp i) t •
          angularMultiplier w (V t) (K t)‖ := by
  calc
    _ = ∑ i ∈ Finset.range (D.count-1), w*δ/2 := by simp; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => D.signed_exit i (Finset.mem_range.mp hi))

end WeightedDirectionPartition

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma SmoothClassicalPrefix.direction_weighted_force_integrable {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) {a b ℓ : ℝ}
    (hℓ : 0<ℓ) (hlen : 2*ℓ≤b-a) (hcell : Icc a b⊆Icc 0 T)
    (hband : ∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) :
    IntegrableOn (fun t=>directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1)))) (Ioo (0:ℝ) T) ∧
    IntegrableOn (fun t=>directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2
      (boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))) (Ioo (0:ℝ) T) := by
  let W := fun t=>directionWeight a b ℓ t • prefixAngularMultiplier s F.flow T w hw zX t
  have hW : Continuous W := (directionWeight_lipschitz a b ℓ).continuous.smul
    (F.prefixAngular_regular hs.directionCountsEnergyPrefix hT hw zX).1
  have he (t : ℝ) (K : Vec) :
      W t K=directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2 K := by
    by_cases ht : t∈tsupport (directionWeight a b ℓ)
    · have hc := directionWeight_tsupport hℓ hlen ht
      simp only [W,smul_apply,(prefixAngular_highband hw zX (hcell hc) (hband t hc)).1]
    · simp only [W,smul_apply,image_eq_zero_of_notMem_tsupport ht,zero_smul]
  have hi : IntegrableOn (fun t=>W t (prefixMomentumForce s F.flow T zX t)) (Ioo (0:ℝ) T) :=
    ((hW.clm_apply (F.continuous_prefixMomentumForce hs.directionCountsEnergyPrefix hT zX)).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hiK : IntegrableOn (fun t=>directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1)))) (Ioo (0:ℝ) T) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [he,prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht),lorentzField,lorentzPhase]
  have hiD := hs.multiplier_retarded_force_integrable hT F zX hW.continuousOn
  have hiD' : IntegrableOn (fun t=>directionWeight a b ℓ t • angularMultiplierCLM w (F.flow zX t).2
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))) (Ioo (0:ℝ) T) := by
    simpa only [he] using hiD
  refine ⟨hiK,?_⟩
  apply (hiK.sub hiD').congr
  exact ae_of_all _ (fun t=>by simp only [Pi.sub_apply,map_sub,smul_sub,sub_sub_cancel])

lemma directionWeight_interval_eq_global {a b ℓ T : ℝ} (hℓ : 0<ℓ)
    (hlen : 2*ℓ≤b-a) (hcell : Icc a b⊆Icc 0 T) (H : ℝ→Vec) :
    (∫t in a..b,directionWeight a b ℓ t • H t)=
      ∫t in Ioo (0:ℝ) T,directionWeight a b ℓ t • H t := by
  have hab : a≤b := by linarith
  rw [intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
  · intro t ht
    exact ⟨(hcell ⟨le_rfl,hab⟩).1.trans_lt ht.1,ht.2.trans_le (hcell ⟨hab,le_rfl⟩).2⟩
  · intro t ht
    have hz : directionWeight a b ℓ t=0 := by
      by_contra hn
      exact ht.2 (directionWeight_ne_zero_interior hℓ hlen hn)
    rw [hz,zero_smul]

lemma SmoothClassicalPrefix.direction_force_family_triangle {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {ι : Type*} (D : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈D,0<ℓ i) (hlen : ∀i∈D,2*ℓ i≤b i-a i)
    (hcell : ∀i∈D,Icc (a i) (b i)⊆Icc 0 T)
    (hband : ∀i∈D,∀t∈Icc (a i) (b i),w/16≤‖(F.flow zX t).2‖) :
    let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
    let K := fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))
    let B := fun t=>boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)
    (∑i∈D,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t (K t)‖)≤
      (∑i∈D,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t (K t-B t)‖)+
      (∑i∈D,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t (B t)‖) := by
  classical
  dsimp only
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨hiK,hiB⟩ := hs.direction_weighted_force_integrable hT hw F zX (hℓ i hi) (hlen i hi) (hcell i hi) (hband i hi)
  simp only [map_sub,smul_sub]
  rw [integral_sub hiK hiB,←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_le_norm_sub_add _ _)

lemma Admissible.direction_complete_count_cost_bound_oai {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃ Ct Cr Cf Cl Cg Ci Ck Cw Cb : ℝ,
      0≤Ct ∧ 0≤Cr ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ci ∧ 0≤Ck ∧ 0≤Cw ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P δ : ℝ) (_ : 0<w),
      zX∈tsupport d.f₀ → IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
        (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b w δ,
      ENNReal.ofReal ((D.count-1:ℕ)*w*δ/2)≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
       (directionUnionBudget (∫x : Vec,totalEnergy s (0,x)) T w M A P Ct Cr Cf Cl Cg+
        ENNReal.ofReal (Ci*T*(b-a))+
        (D.count-1:ℕ)*ENNReal.ofReal (2*Cw*Real.sqrt (max 1 T)*(Real.log (2+P))^2)+
        (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
          ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w))+
      ENNReal.ofReal (Cb*(b-a)) := by
  classical
  obtain ⟨Ct,Cr,Cf,Cl,Cg,Ci,Ck,Cw,hCt,hCr,hCf,hCl,hCg,hCi,hCk,hCw,hfam⟩ :=
    hd₀.direction_physical_family_log_bound T₀
  obtain ⟨Cb,hCb,hdatum⟩ := hd₀.direction_family_datum_uniform_bound T₀
  refine ⟨Ct,Cr,Cf,Cl,Cg,Ci,Ck,Cw,Cb,hCt,hCr,hCf,hCl,hCg,hCi,hCk,hCw,hCb,?_⟩
  intro s T F hs hT hTT zX S a b w M A P δ hw hzX hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ D
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  let I := Finset.range (D.count-1)
  have hℓ i (hi : i∈I) := D.ramp_pos i (Finset.mem_range.mp hi)
  have hlen i (hi : i∈I) := D.ramp_separation i (Finset.mem_range.mp hi)
  have hcell i (hi : i∈I) : Icc (D.time i) (D.time (i+1))⊆Icc a b :=
    D.cell_subset (by have := Finset.mem_range.mp hi; omega)
  have hf := hfam s T F hs hT hTT zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw
    hsource hq hV HX HZ ℕ I D.time (fun i=>D.time (i+1)) D.ramp hℓ hlen hcell D.interiors_disjoint
  have hd := hdatum T hT hTT s.E s.B F zX hzX w a b hw hab ℕ I D.time (fun i=>D.time (i+1)) D.ramp
    hℓ hlen hcell D.interiors_disjoint (fun i hi t ht=>hV t (hcell i hi ht))
  have htri := hs.direction_force_family_triangle hT hw F zX I D.time (fun i=>D.time (i+1)) D.ramp
    hℓ hlen (fun i hi=>(hcell i hi).trans hJ) (fun i hi t ht=>hV t (hcell i hi ht))
  have hlo := ENNReal.ofReal_le_ofReal D.complete_force_lower
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>norm_nonneg _)] at hlo
  have he i (hi : i∈I) := directionWeight_interval_eq_global (hℓ i hi) (hlen i hi) ((hcell i hi).trans hJ)
    (fun t=>angularMultiplier w (F.flow zX t).2
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))))
  have hlo' : ENNReal.ofReal ((D.count-1:ℕ)*w*δ/2)≤
      ∑i∈I,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (D.time i) (D.time (i+1)) (D.ramp i) t •
        angularMultiplierCLM w (F.flow zX t).2
          (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1)))‖ := by
    apply hlo.trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi]
    simp only [angularMultiplierCLM_apply]
  have hd' := ENNReal.ofReal_le_ofReal hd
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>norm_nonneg _)] at hd'
  have hh := hlo'.trans (htri.trans (add_le_add hf hd'))
  simpa only [I,Finset.card_range] using hh



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direction_complete_count_cost_bound_oai := @OAI.RVM.Admissible.direction_complete_count_cost_bound_oai
