-- Prove2me | solution 1 for OAI.RVM.Admissible.direction_physical_family_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:55:17.898314+00:00
-- url     : https://prove2.me/submissions/a75b0090-f77b-4b93-8a09-14e686d0bec2

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direction_selected_bulk_log_bound
import Theorems.Thm_OAI_RVM_Admissible_direction_unselected_label_log_bound
import Theorems.Thm_OAI_RVM_Admissible_selected_moving_bound
import Theorems.Thm_OAI_RVM_Admissible_selected_receiver_weight_bound
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_actual_angular_family_bound
import Theorems.Thm_OAI_RVM_selectedInitialKernel_integrable_bound

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedPhaseDomain
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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

namespace EnergyPrefix
variable {s : Solution} {T : ℝ}

lemma particle_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ particleEnergy s (t,x) := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (q_pos v).le (hs.nonnegative t ht (x,v))

lemma total_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ totalEnergy s (t,x) := by
  dsimp [totalEnergy]
  have hp := particle_energy_nonneg hs ht x
  positivity

end EnergyPrefix

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

lemma directionWeight_middle {a b ℓ t : ℝ} (hℓ : 0<ℓ) (_hab : 2*ℓ≤b-a)
    (ht : t∈Icc (a+ℓ) (b-ℓ)) : directionWeight a b ℓ t=1 := by
  rw [directionWeight,clippedRamp_of_ge hℓ ht.1,clippedRamp_of_le hℓ ht.2,sub_zero]

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

lemma directionWeight_deriv_left {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo a (a+ℓ)) : deriv (directionWeight a b ℓ) t=ℓ⁻¹ := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun u=>(u-a)/ℓ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_left hℓ hab (Ioo_subset_Icc_self hu)
  have hd := (((hasDerivAt_id t).sub_const a).div_const ℓ).congr_of_eventuallyEq he
  simpa only [one_div] using hd.deriv

lemma directionWeight_deriv_middle {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo (a+ℓ) (b-ℓ)) : deriv (directionWeight a b ℓ) t=0 := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun _=>1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_middle hℓ hab (Ioo_subset_Icc_self hu)
  exact ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he).deriv

lemma directionWeight_deriv_right {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo (b-ℓ) b) : deriv (directionWeight a b ℓ) t= -ℓ⁻¹ := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun u=>(b-u)/ℓ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_right hℓ hab (Ioo_subset_Icc_self hu)
  have hd := (((hasDerivAt_id t).const_sub b).div_const ℓ).congr_of_eventuallyEq he
  simpa only [neg_div,one_div] using hd.deriv

lemma directionWeight_total_variation {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    (∫t in a..b,|deriv (directionWeight a b ℓ) t|)=2 := by
  have hab' : a≤b := by linarith
  have hL : a≤a+ℓ := by linarith
  have hC : a+ℓ≤b-ℓ := by linarith
  have hR : b-ℓ≤b := by linarith
  have hψ := (directionWeight_lipschitz a b ℓ).lipschitzOnWith (s:=uIcc a b) |>.absolutelyContinuousOnInterval
  have hi : IntervalIntegrable (fun t=>|deriv (directionWeight a b ℓ) t|) volume a b :=
    hψ.intervalIntegrable_deriv.norm
  have hiL := hi.mono_set (show uIcc a (a+ℓ)⊆uIcc a b by
    rw [uIcc_of_le hL,uIcc_of_le hab']; exact Icc_subset_Icc le_rfl (hC.trans hR))
  have hiC := hi.mono_set (show uIcc (a+ℓ) (b-ℓ)⊆uIcc a b by
    rw [uIcc_of_le hC,uIcc_of_le hab']; exact Icc_subset_Icc hL hR)
  have hiR := hi.mono_set (show uIcc (b-ℓ) b⊆uIcc a b by
    rw [uIcc_of_le hR,uIcc_of_le hab']; exact Icc_subset_Icc (hL.trans hC) le_rfl)
  have eL : (∫t in a..a+ℓ,|deriv (directionWeight a b ℓ) t|)=1 := by
    calc
      _ = ∫t in a..a+ℓ,ℓ⁻¹ := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        dsimp only
        rw [directionWeight_deriv_left hℓ hab (by simpa only [uIoo_of_le hL] using ht),
          abs_of_pos (inv_pos.mpr hℓ)]
      _ = 1 := by rw [intervalIntegral.integral_const]; simp [hℓ.ne']
  have eR : (∫t in b-ℓ..b,|deriv (directionWeight a b ℓ) t|)=1 := by
    calc
      _ = ∫t in b-ℓ..b,ℓ⁻¹ := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        dsimp only
        rw [directionWeight_deriv_right hℓ hab (by simpa only [uIoo_of_le hR] using ht),
          abs_neg,abs_of_pos (inv_pos.mpr hℓ)]
      _ = 1 := by rw [intervalIntegral.integral_const]; simp [hℓ.ne']
  have eC : (∫t in a+ℓ..b-ℓ,|deriv (directionWeight a b ℓ) t|)=0 := by
    rw [←intervalIntegral.integral_zero (a:=a+ℓ) (b:=b-ℓ)]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_middle hℓ hab (by simpa only [uIoo_of_le hC] using ht),abs_zero]
  rw [←intervalIntegral.integral_add_adjacent_intervals hiL (hiC.trans hiR),
    ←intervalIntegral.integral_add_adjacent_intervals hiC hiR,eL,eC,eR]
  norm_num

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


lemma selected_initial_support_congr (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (f : Phase→ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
    {G H : ℝ→Vec→L[ℝ]Vec} (hG : EqOn G H (tsupport ψ)) :
    selectedInitialKernel α zX T f Q ψ G=selectedInitialKernel α zX T f Q ψ H := by
  funext z
  by_cases hz : z∈initialPuncturedCone α zX T
  · simp only [selectedInitialKernel,indicator_of_mem hz]
    by_cases ht : branchTime α zX z T 0∈tsupport ψ
    · rw [hG ht]
    · simp only [image_eq_zero_of_notMem_tsupport ht,mul_zero,zero_mul,zero_smul]
  · simp only [selectedInitialKernel,indicator_of_notMem hz]

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

lemma directionWeight_deriv_outside {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∉Icc a b) : deriv (directionWeight a b ℓ) t=0 :=
  deriv_of_notMem_tsupport (fun h=>ht (directionWeight_tsupport hℓ hab h))

lemma directionWeight_lvariation {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    {J : Set ℝ} (hJ : Icc a b⊆J) :
    (∫⁻t in J,ENNReal.ofReal |deriv (directionWeight a b ℓ) t|)=2 := by
  have hs : Function.support (fun t=>ENNReal.ofReal |deriv (directionWeight a b ℓ) t|)⊆Icc a b := by
    intro t ht
    by_contra hn
    exact ht (by dsimp only; rw [directionWeight_deriv_outside hℓ hab hn,abs_zero,ENNReal.ofReal_zero])
  rw [setLIntegral_eq_of_support_subset (hs.trans hJ),←setLIntegral_eq_of_support_subset hs]
  have hi : IntervalIntegrable (fun t=>|deriv (directionWeight a b ℓ) t|) volume a b :=
    ((directionWeight_lipschitz a b ℓ).lipschitzOnWith (s:=uIcc a b)).absolutelyContinuousOnInterval.intervalIntegrable_deriv.norm
  rw [←ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (show a≤b by linarith)).mp hi)
    (ae_of_all _ (fun t=>abs_nonneg _)),integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (show a≤b by linarith),directionWeight_total_variation hℓ hab]
  norm_num

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

lemma directionWeight_sum_ofReal_le_one {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) (t : ℝ) :
    ∑i∈S,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t|≤1 := by
  have hn : ∀i∈S,0≤directionWeight (a i) (b i) (ℓ i) t :=
    fun i hi=>(directionWeight_bounds (hℓ i hi) (hlen i hi)).1
  simp_rw [Finset.sum_congr rfl (fun i hi=>congrArg ENNReal.ofReal (abs_of_nonneg (hn i hi)))]
  rw [←ENNReal.ofReal_sum_of_nonneg hn]
  exact (ENNReal.ofReal_le_ofReal (directionWeight_sum_le_one S a b ℓ hℓ hlen hdis t)).trans_eq (by norm_num)

lemma directionWeight_sum_kernel {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    {J : Set ℝ} {g : ℝ→ℝ≥0∞} (hg : AEMeasurable g (volume.restrict J)) :
    (∑i∈S,∫⁻t in J,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t| * g t)≤∫⁻t in J,g t := by
  have hm (i : ι) : AEMeasurable (fun t=>ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t| * g t) (volume.restrict J) := by
    apply AEMeasurable.mul
    · have hc : Continuous (fun t=>ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t|) :=
        ENNReal.continuous_ofReal.comp ((directionWeight_lipschitz (a i) (b i) (ℓ i)).continuous.abs)
      exact hc.measurable.aemeasurable
    · exact hg
  rw [←lintegral_finsetSum' S (fun i _=>hm i)]
  apply lintegral_mono
  intro t
  dsimp only
  rw [←Finset.sum_mul]
  exact (mul_le_mul' (directionWeight_sum_ofReal_le_one S a b ℓ hℓ hlen hdis t) le_rfl).trans_eq (one_mul _)

lemma PhaseFlowOn.aemeasurable_receiver_force {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (fun t=>ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖) (volume.restrict J) := by
  have hc : Continuous (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) :=
    ENNReal.continuous_ofReal.comp ((F.continuous_prefixMomentumForce hs hT zX).norm)
  apply hc.measurable.aemeasurable.congr
  filter_upwards [ae_restrict_mem hJ] with t ht
  simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (hJT ht)]

lemma Admissible.direction_family_moving_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
      (∀k∈Q,cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i≤b i-a i) → (∀i∈S,Icc (a i) (b i)⊆J) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∑i∈S,selectedAngularMovingCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))≤
      (∫⁻t in J,ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  obtain ⟨C,hC,hb⟩ := hd.selected_moving_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell hdis
  have hi (i : ι) (hi : i∈S) := hb s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv
    (directionWeight (a i) (b i) (ℓ i)) (directionWeight_lipschitz _ _ _).continuous.measurable
    (fun t ht=>image_eq_zero_of_notMem_tsupport (f:=directionWeight _ _ _)
      (fun hn=>ht (hcell i hi (directionWeight_tsupport (hℓ i hi) (hlen i hi) hn))))
  calc
    _ ≤ ∑i∈S,(∫⁻t in J,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t| *
        ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := Finset.sum_le_sum hi
    _ = (∑i∈S,∫⁻t in J,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t| *
        ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul' (directionWeight_sum_kernel S a b ℓ hℓ hlen hdis
      (F.aemeasurable_receiver_force hs hT zX hJ hJT)) le_rfl

lemma Admissible.direction_family_weight_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
      (∀k∈Q,cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i≤b i-a i) → (∀i∈S,Icc (a i) (b i)⊆J) →
      (∑i∈S,selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))≤
        (S.card:ℝ≥0∞)*ENNReal.ofReal (2*C*Real.sqrt (max 1 T)*(N:ℝ)^2) := by
  obtain ⟨C,hC,hb⟩ := hd.selected_receiver_weight_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell
  have hi (i : ι) (hi : i∈S) : selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))≤
      ENNReal.ofReal (2*C*Real.sqrt (max 1 T)*(N:ℝ)^2) := by
    have hk := hb s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv
      (deriv (directionWeight (a i) (b i) (ℓ i))) (measurable_deriv _)
      (fun t ht=>directionWeight_deriv_outside (hℓ i hi) (hlen i hi) (fun hn=>ht (hcell i hi hn)))
    rw [directionWeight_lvariation (hℓ i hi) (hlen i hi) (hcell i hi)] at hk
    apply hk.trans_eq
    rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hi

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CappedRepresentativePos
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma cappedRepresentative_pos (n : ℕ) : 0 < cappedRepresentative n := by
  dsimp [cappedRepresentative]
  positivity

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_IndexTwoPow
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

open Set

namespace RVM

lemma exists_dyadic_count_log {B : ℝ} (hB : 1 ≤ B) :
    ∃N : ℕ, B < (2:ℝ)^N ∧ (N:ℝ) ≤ 2+Real.log B/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ Real.log B/Real.log 2 := div_nonneg (Real.log_nonneg hB) h2.le
  let n := ⌈Real.log B/Real.log 2⌉₊
  refine ⟨n+1,?_,?_⟩
  · apply (Real.log_lt_log_iff (zero_lt_one.trans_le hB) (by positivity)).mp
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one]
    have hc : Real.log B/Real.log 2 < (n:ℝ)+1 := by
      have hh := Nat.le_ceil (Real.log B/Real.log 2)
      dsimp [n]
      linarith only [hh]
    exact (div_lt_iff₀ h2).mp hc
  · have hh : (n:ℝ) < Real.log B/Real.log 2+1 := Nat.ceil_lt_add_one h0
    push_cast
    linarith only [hh]

lemma exists_far_dyadic_count (T : ℝ) :
    ∃C : ℝ, 0 ≤ C ∧ ∀P : ℝ, 0 < P → 1 ≤ Real.log (2+P) →
      ∃N : ℕ, 2*P < (2:ℝ)^N ∧
        4096*P*Real.sqrt (max 1 T) < (2:ℝ)^N ∧
        (4096*P)^2*max 1 T < (2:ℝ)^N ∧
        (N:ℝ) ≤ C*Real.log (2+P) := by
  let H := max 1 T
  let D := 16777216*H
  let C := 2+Real.log D/Real.log 2+2/Real.log 2
  have hH1 : 1 ≤ H := le_max_left _ _
  have hH : 0 < H := zero_lt_one.trans_le hH1
  have hD1 : 1 ≤ D := by dsimp [D]; linarith only [hH1]
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro P hP hL
  let B := D*(2+P)^2
  have hB1 : 1 ≤ B := by
    have hs : 1 ≤ (2+P)^2 := by nlinarith only [hP,sq_nonneg P]
    simpa only [one_mul] using (mul_le_mul hD1 hs (by norm_num) hD.le : (1:ℝ)*1 ≤ D*(2+P)^2)
  obtain ⟨N,hN,hNc⟩ := exists_dyadic_count_log hB1
  refine ⟨N,?_,?_,?_,?_⟩
  · have hh : 2*P < D*(2+P)^2 := by
      have hd : (2:ℝ) ≤ D := by dsimp [D]; linarith only [hH1]
      have hx : 2*(2+P)^2 ≤ D*(2+P)^2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      nlinarith only [hx,hP,sq_nonneg P]
    exact hh.trans hN
  · have hsH : 1 ≤ Real.sqrt H := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hH1
    have hsqH : (Real.sqrt H)^2=H := Real.sq_sqrt hH.le
    have hterm : 4096*P*Real.sqrt H < D*(2+P)^2 := by
      have hx : 0 ≤ P*(Real.sqrt H)*(Real.sqrt H-1) := mul_nonneg (mul_nonneg hP.le (Real.sqrt_nonneg _)) (sub_nonneg.mpr hsH)
      have hy : 0 ≤ H*P^2 := mul_nonneg hH.le (sq_nonneg _)
      dsimp [D]
      nlinarith only [hx,hy,hsqH,hH1,hP,mul_pos hP hH]
    exact hterm.trans hN
  · have hterm : (4096*P)^2*H < D*(2+P)^2 := by
      have hh : P^2 < (2+P)^2 := by nlinarith only [hP]
      have hm := mul_lt_mul_of_pos_left hh (show 0 < 16777216*H by positivity)
      dsimp [D]
      nlinarith only [hm]
    exact hterm.trans hN
  · have hlog : Real.log B=Real.log D+2*Real.log (2+P) := by
      dsimp [B]
      rw [Real.log_mul (ne_of_gt hD) (ne_of_gt (sq_pos_of_pos (by linarith only [hP]))),Real.log_pow]
      norm_num
    rw [hlog] at hNc
    apply hNc.trans
    have hcoeff : 0 ≤ 2+Real.log D/Real.log 2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hL hcoeff
    dsimp [C]
    calc
      _ = (2+Real.log D/Real.log 2)+(2/Real.log 2)*Real.log (2+P) := by ring
      _ ≤ (2+Real.log D/Real.log 2)*Real.log (2+P)+(2/Real.log 2)*Real.log (2+P) := by linarith only [hh]
      _ = _ := by ring

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

lemma exists_source_dyadic_count : ∃C : ℝ,0≤C ∧ ∀P : ℝ,
    0<P → 1≤Real.log (2+P) → ∃N : ℕ,1024*P≤(2:ℝ)^N ∧ (N:ℝ)≤C*Real.log (2+P) := by
  obtain ⟨C,hC,hcount⟩ := exists_far_dyadic_count 0
  refine ⟨C,hC,?_⟩
  intro P hP hL
  obtain ⟨N,_hN0,hN1,_hN3,hNc⟩ := hcount P hP hL
  refine ⟨N,?_,hNc⟩
  norm_num at hN1
  linarith only [hN1,hP]

lemma Admissible.direction_family_moving_log_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w P : ℝ) (Q : Set (Fin 4→ℕ)),
      0<P → 1≤Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,q (F.flow z σ).2≤P) →
      (∀k∈Q,cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i≤b i-a i) → (∀i∈S,Icc (a i) (b i)⊆J) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∑i∈S,selectedAngularMovingCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))≤
      (∫⁻t in J,ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  obtain ⟨Cb,hCb,hb⟩ := hd.direction_family_moving_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨Cb*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX J w P Q hP hL hsource hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell hdis
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  have hsourceN : ∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N := by
    intro z hz σ hσ
    exact (mul_le_mul_of_nonneg_left (hsource z hz σ hσ) (by norm_num)).trans hN
  have hh := hb s T F hs hT h0 zX J w N Q hsourceN hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell hdis
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Cb*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2/w := by gcongr
    _ = _ := by ring

lemma Admissible.direction_family_weight_log_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w P : ℝ) (Q : Set (Fin 4→ℕ)),
      0<P → 1≤Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,q (F.flow z σ).2≤P) →
      (∀k∈Q,cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i≤b i-a i) → (∀i∈S,Icc (a i) (b i)⊆J) →
      (∑i∈S,selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))≤
        (S.card:ℝ≥0∞)*ENNReal.ofReal (2*C*Real.sqrt (max 1 T)*(Real.log (2+P))^2) := by
  obtain ⟨Cb,hCb,hb⟩ := hd.direction_family_weight_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨Cb*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX J w P Q hP hL hsource hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  have hsourceN : ∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N := by
    intro z hz σ hσ
    exact (mul_le_mul_of_nonneg_left (hsource z hz σ hσ) (by norm_num)).trans hN
  have hh := hb s T F hs hT h0 zX J w N Q hsourceN hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 2*Cb*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2 := by gcongr
    _ = _ := by ring

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

lemma extendedAngularCLM_norm_le (w : ℝ) (hw : 0<w) (v : Vec) :
    ‖extendedAngularCLM w hw v‖ ≤ 64 := by
  have hb : 0 ≤ angularZeroBump w hw v := (angularZeroBump w hw).nonneg
  have hb1 : angularZeroBump w hw v ≤ 1 := (angularZeroBump w hw).le_one
  by_cases hv : ‖v‖<w/64
  · have hvb : v∈closedBall (0:Vec) (angularZeroBump w hw).rIn := by
      simpa only [mem_closedBall,dist_zero_right,angularZeroBump] using hv.le
    rw [extendedAngularCLM,(angularZeroBump w hw).one_of_mem_closedBall hvb,sub_self,
      zero_smul ℝ (angularMultiplierCLM w v),norm_zero]
    norm_num
  · rw [extendedAngularCLM,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hb1)]
    calc
      _ ≤ ‖angularMultiplierCLM w v‖ := by
        nlinarith only [hb,hb1,norm_nonneg (angularMultiplierCLM w v)]
      _ ≤ 64 := angularMultiplierCLM_norm_le hw (le_of_not_gt hv)

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

lemma Admissible.direction_family_initial_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (w c e : ℝ),0<w → c ≤ e →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ) (Q : ι→Set (Fin 4→ℕ)),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i ≤ b i-a i) →
      (∀i∈S,Icc (a i) (b i)⊆Icc c e) →
      (∀i∈S,Icc (a i) (b i)⊆Icc 0 T) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∀i∈S,∀t∈Icc (a i) (b i),w/16 ≤ ‖(F.flow zX t).2‖) →
      (∑i∈S,‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) (Q i)
        (directionWeight (a i) (b i) (ℓ i)) (fun t=>angularMultiplierCLM w (F.flow zX t).2) z‖) ≤
      C*T*(e-c) := by
  obtain ⟨C,hC,hbound⟩ := selectedInitialKernel_integrable_bound hd.1.continuous hd.2.1 hd.2.2.1
  refine ⟨64*C,by positivity,?_⟩
  intro s T F hs hT h0 zX w c e hw hce ι S a b ℓ Q hℓ hlen hcell hcellT hdis hband
  let W := prefixAngularMultiplier s F.flow T w hw zX
  have hW : Continuous W := (F.prefixAngular_regular hs hT hw zX).1
  have hWM (t : ℝ) : ‖W t‖ ≤ 64 := extendedAngularCLM_norm_le w hw _
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext h0
  have hbnd (i : ι) (hi : i∈S) :
      ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) (Q i)
        (directionWeight (a i) (b i) (ℓ i)) (fun t=>angularMultiplierCLM w (F.flow zX t).2) z‖ ≤
      64*C*T*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := by
    have hG : EqOn W (fun t=>angularMultiplierCLM w (F.flow zX t).2)
        (tsupport (directionWeight (a i) (b i) (ℓ i))) := by
      intro t ht
      have htc := directionWeight_tsupport (hℓ i hi) (hlen i hi) ht
      exact (prefixAngular_highband hw zX (hcellT i hi htc) (hband i hi t htc)).1
    rw [←selected_initial_support_congr F.flow zX T (fun z=>s.f (0,z)) (Q i)
      (directionWeight (a i) (b i) (ℓ i)) hG,hdata]
    have hh := (hbound s.E s.B T F zX (Q i) (directionWeight (a i) (b i) (ℓ i)) W 64 hT
      (by norm_num) (directionWeight_lipschitz _ _ _).continuous.continuousOn hW.continuousOn
      (fun t _=>hWM t)).2
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  calc
    _ ≤ ∑i∈S,64*C*T*(∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := Finset.sum_le_sum hbnd
    _ = 64*C*T*(∑i∈S,∫t in Ioo (0:ℝ) T,|directionWeight (a i) (b i) (ℓ i) t|) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (directionWeight_family_mass S a b ℓ hℓ hlen hdis hce hcell) (by positivity)

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

lemma Admissible.direction_physical_family_log_bound_oai {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ct Cr Cf Cl Cg Ci Ck Cw : ℝ,
      0≤Ct ∧ 0≤Cr ∧ 0≤Cf ∧ 0≤Cl ∧ 0≤Cg ∧ 0≤Ci ∧ 0≤Ck ∧ 0≤Cw ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (_ : 0<w),
      IsCompact S → tsupport d.f₀⊆S →
      0≤a → b≤T → a≤b → b-a≤(w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀(ι : Type) (D : Finset ι) (c e ℓ : ι→ℝ),
      (∀i∈D,0<ℓ i) → (∀i∈D,2*ℓ i≤e i-c i) →
      (∀i∈D,Icc (c i) (e i)⊆Icc a b) →
      (D:Set ι).Pairwise (fun i j=>Disjoint (Ioo (c i) (e i)) (Ioo (c j) (e j))) →
      let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
      (∑i∈D,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (c i) (e i) (ℓ i) t • G t
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖)≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
       (directionUnionBudget (∫x : Vec,totalEnergy s (0,x)) T w M A P Ct Cr Cf Cl Cg+
        ENNReal.ofReal (Ci*T*(b-a))+
        (D.card:ℝ≥0∞)*ENNReal.ofReal (2*Cw*Real.sqrt (max 1 T)*(Real.log (2+P))^2)+
        (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
          ENNReal.ofReal (Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w)) := by
  classical
  obtain ⟨Ct,Cr,Cf,Cl,hCt,hCr,hCf,hCl,hun⟩ := hd₀.direction_unselected_label_log_bound T₀
  obtain ⟨Ce,Cf',Cl',Cg,Ck,hCe,hCf',hCl',hCg,hCk,hbulk⟩ := hd₀.direction_selected_bulk_log_bound T₀
  obtain ⟨Ci,hCi,hinit⟩ := hd₀.direction_family_initial_bound
  obtain ⟨Cm,hCm,hmove⟩ := hd₀.direction_family_moving_log_bound
  obtain ⟨Cw,hCw,hweight⟩ := hd₀.direction_family_weight_log_bound
  refine ⟨Ct,Cr+Ce,Cf+Cf',Cl+Cl',Cg,Ci,Ck+Cm,Cw,hCt,by positivity,by positivity,by positivity,hCg,hCi,by positivity,hCw,?_⟩
  intro s T F hs hT hTT zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ ι D c e ℓ hℓ hlen hcell hdis
  dsimp only
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
  have hS0' : tsupport (fun z=>s.f (0,z))⊆S := by rw [hdata]; exact hS0
  have hQ (k) (hk : k∈directionSelection T) :
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1 := by
    refine ⟨hk.1.trans ?_,hk.2⟩
    have hp := (cappedRepresentative_pos (k 2)).le
    linarith
  have hu := hun s T F hs.directionCountsEnergyPrefix hT hTT hs.initial_f zX S a b w M A P hw hS hS0' ha hb hab hJI
    hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ
  have hbu := hbulk s T F hs.directionCountsEnergyPrefix hT hTT hs.initial_f zX S a b w M A P hw hS hS0' ha hb hab hJI
    hM hA hP hL hw1 hwP hPw hsource hq hV HX HZ
  have hm := hmove s T F hs.directionCountsEnergyPrefix hT hs.initial_f zX (Icc a b) w P (directionSelection T)
    (zero_lt_one.trans_le hP) hL hsource hQ measurableSet_Icc hJ hw hq hV ι D c e ℓ hℓ hlen hcell hdis
  have hwc := hweight s T F hs.directionCountsEnergyPrefix hT hs.initial_f zX (Icc a b) w P (directionSelection T)
    (zero_lt_one.trans_le hP) hL hsource hQ measurableSet_Icc hJ hw hq hV ι D c e ℓ hℓ hlen hcell
  have hic := hinit s T F hs.directionCountsEnergyPrefix hT hs.initial_f zX w a b hw hab ι D c e ℓ (fun _=>directionSelection T)
    hℓ hlen hcell (fun i hi=>(hcell i hi).trans hJ) hdis (fun i hi t ht=>hV t (hcell i hi ht))
  have hi : (∑i∈D,ENNReal.ofReal ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z))
      (directionSelection T) (directionWeight (c i) (e i) (ℓ i)) (fun t=>angularMultiplierCLM w (F.flow zX t).2) z‖)≤
      ENNReal.ofReal (Ci*T*(b-a)) := by
    rw [←ENNReal.ofReal_sum_of_nonneg (fun i _=>norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hic
  have hforce : (∫⁻t in Icc a b,ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)=
      ∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖ := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (hJ ht)]
  rw [hforce] at hm
  let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
  let W := prefixAngularMultiplier s F.flow T w hw zX
  have heq (t : ℝ) (ht : t∈Icc a b) : W t=G t :=
    (prefixAngular_highband hw zX (hJ ht) (hV t ht)).1
  have huEq (p : ℝ×Phase) :
      {p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b}.indicator
        (fun p=>ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
          ((1-labelSelectedCutoff F.flow zX T (directionSelection T) p) • actualLabelSignedForce s F.flow zX T p)‖) p=
      ENNReal.ofReal ‖(Icc a b).indicator W (labelReceiverTime F.flow zX T p)
        ((1-labelSelectedCutoff F.flow zX T (directionSelection T) p) • actualLabelSignedForce s F.flow zX T p)‖ := by
    by_cases ht : labelReceiverTime F.flow zX T p∈Icc a b
    · simp only [indicator_of_mem ht,indicator_of_mem (show p∈{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b} from ht),heq _ ht]
    · simp only [indicator_of_notMem ht,indicator_of_notMem (show p∉{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b} from ht),zero_apply,norm_zero,ENNReal.ofReal_zero]
  have hbEq (p : ℝ×Phase) :
      {p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b}.indicator
        (selectedMultiplierBulkDensity s F.flow zX T (directionSelection T) G) p=
      selectedMultiplierBulkDensity s F.flow zX T (directionSelection T) ((Icc a b).indicator W) p := by
    by_cases ht : labelReceiverTime F.flow zX T p∈Icc a b
    · simp only [indicator_of_mem (show p∈{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b} from ht),selectedMultiplierBulkDensity,indicator_of_mem ht,heq _ ht]
    · simp only [indicator_of_notMem (show p∉{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈Icc a b} from ht),selectedMultiplierBulkDensity,indicator_of_notMem ht,zero_apply,norm_zero,ENNReal.ofReal_zero,add_zero]
  have hf := hs.actual_angular_family_bound hT hw F zX (directionSelection T) D c e ℓ hℓ hlen hdis
    (Icc a b) hJ hcell hV
  dsimp only at hf
  change _≤ENNReal.ofReal (4*Real.pi)⁻¹*(_+_+_+_+_) at hf
  rw [lintegral_congr huEq,lintegral_congr hbEq] at hf
  apply hf.trans
  apply mul_le_mul' le_rfl
  apply (add_le_add (add_le_add (add_le_add (add_le_add hu hi) hwc) hbu) hm).trans_eq
  have hE : 0≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.directionCountsEnergyPrefix.total_energy_nonneg ⟨le_rfl,hT⟩)
  dsimp only [directionUnionBudget]
  rw [show (Cr+Ce)*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5=
      Cr*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5+
      Ce*(1+(∫x : Vec,totalEnergy s (0,x)))*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5 by ring,
    show (Cf+Cf')*(∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5=
      Cf*(∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5+
      Cf'*(∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5 by ring,
    show (Cl+Cl')*(1+(∫x : Vec,totalEnergy s (0,x)))*(max 1 T)^2*(Real.log (2+P))^2=
      Cl*(1+(∫x : Vec,totalEnergy s (0,x)))*(max 1 T)^2*(Real.log (2+P))^2+
      Cl'*(1+(∫x : Vec,totalEnergy s (0,x)))*(max 1 T)^2*(Real.log (2+P))^2 by ring,
    show (Ck+Cm)*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w=
      Ck*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w+Cm*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w by ring]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_add (by positivity) (by positivity),mul_add]
  simp only [mul_add]
  ac_rfl



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direction_physical_family_log_bound_oai := @OAI.RVM.Admissible.direction_physical_family_log_bound_oai
