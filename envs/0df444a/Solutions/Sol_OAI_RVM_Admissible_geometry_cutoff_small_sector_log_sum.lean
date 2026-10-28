-- Prove2me | solution 1 for OAI.RVM.Admissible.geometry_cutoff_small_sector_log_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:03:57.489653+00:00
-- url     : https://prove2.me/submissions/65b0d219-f87e-4b1d-8a64-7846aaf61f80

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_central_density_small_sector_log_sum

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

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_add_right (a b c : Vec) : dot a (b + c) = dot a b + dot a c := by
  rw [dot_comm, dot_add_left, dot_comm b a, dot_comm c a]

lemma dot_sub_right (a b c : Vec) : dot a (b - c) = dot a b - dot a c := by
  rw [dot_comm, dot_sub_left, dot_comm b a, dot_comm c a]

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

lemma cone_angle_identity (v n : Vec) (hn : ‖n‖ = 1) :
    2 * (1 - dot n (velocity v)) = ‖n - velocity v‖ ^ 2 + (q v)⁻¹ ^ 2 := by
  rw [norm_sub_sq_real, ← dot_eq_inner, hn, ← dot_self (velocity v), velocity_self]
  ring

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RetardedSameTimeSeparation
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
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

lemma norm_sub_le_of_deficit {u a : Vec} {δ : ℝ} (hu : ‖u‖≤1) (ha : ‖a‖≤1)
    (hδ : 0≤δ) (hd : 1-dot u a≤δ^2/2) : ‖u-a‖≤δ := by
  have he : ‖u-a‖^2=‖u‖^2+‖a‖^2-2*dot u a := by rw [norm_sub_sq_real,dot_eq_inner]; ring
  have hu2 : ‖u‖^2≤1 := by nlinarith [norm_nonneg u]
  have ha2 : ‖a‖^2≤1 := by nlinarith [norm_nonneg a]
  nlinarith [norm_nonneg (u-a)]

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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma measurableSet_coneBinMomentumSet (B : ClosedConeBin) (n a : Vec) :
    MeasurableSet (coneBinMomentumSet B n a) := by
  exact ((measurableSet_Icc.preimage (contDiff_q (k:=0)).continuous.measurable).inter
    ((measurableSet_Icc.preimage (continuous_const.sub (continuous_dot.comp
      (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous))).measurable).inter
      (measurableSet_Icc.preimage (continuous_const.sub (continuous_dot.comp
      (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous))).measurable)))

lemma measurableSet_physicalBinBase {V : ℝ → Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (physicalBinBase V B J) := by
  have htime : MeasurableSet {z : ConeCoordinate | z.2.1 ∈ Icc 0 z.1} :=
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst)
  exact (hJ.preimage measurable_fst).inter (htime.inter
    ((measurableSet_Icc.preimage (measurable_fst.sub (measurable_fst.comp measurable_snd))).inter
      ((measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp
        (hV.comp measurable_fst))).inter
      (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp
        ((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).prodMk
          ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst)))))))))

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

lemma velocityProjection_add (u b c : Vec) :
    velocityProjection u (b+c) = velocityProjection u b + velocityProjection u c := by
  simp only [velocityProjection,dot_add_right,add_smul]
  module

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

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

lemma velocity_normal_distance_bound (v n : Vec) (hn : ‖n‖=1) :
    ‖velocity v-n‖ ≤ Real.sqrt (2*(1-dot n (velocity v))) := by
  have hi := cone_angle_identity v n hn
  rw [norm_sub_rev] at hi
  have hd := (cone_denom_pos v n hn).le
  have hh := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd)
  nlinarith [sq_nonneg ((q v)⁻¹), Real.sqrt_nonneg (2*(1-dot n (velocity v))),
    norm_nonneg (velocity v-n)]

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

lemma velocityProjection_smul (u h : Vec) (c : ℝ) :
    velocityProjection u (c • h)=c • velocityProjection u h := by
  simp only [velocityProjection,dot_smul_right,smul_sub,smul_smul]

lemma transverseProjection_velocity (w : Vec) : transverseProjection w (velocity w)=0 := by
  by_cases hw : w=0
  · simp [hw,transverseProjection,velocityProjection,velocity,dot]
  · have hn := norm_ne_zero_iff.mpr hw
    ext i
    simp only [transverseProjection,velocityProjection,velocity,dot_smul_left,dot_smul_right,
      dot_self,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul]
    field_simp
    ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BinHits
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal



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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal



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
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


lemma signedPrimitive_decomposition (a u n : Vec) (hD : 1-dot n a ≠ 0) :
    signedPrimitive a u n = (u-n)+
      ((1-dot n a-(1-dot a u))/(1-dot n a)) • n := by
  ext i
  simp only [signedPrimitive,PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp
  ring

lemma small_deficit_difference {a u n : Vec} {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hsmall : θ ≤ φ)
    (hd0 : 0 ≤ 1-dot n u) (hd : 1-dot n u ≤ 8*θ^2)
    (hun : ‖u-n‖ ≤ 4*θ) (han : ‖a-n‖ ≤ 4*φ) :
    |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ := by
  have he : (1-dot a u)-(1-dot n a)=(1-dot n u)+dot (a-n) (n-u) := by
    simp only [dot_sub_left,dot_sub_right,dot_self,hn,one_pow,dot_comm a n]
    ring
  rw [he]
  calc
    _ ≤ |1-dot n u|+|dot (a-n) (n-u)| := abs_add_le _ _
    _ ≤ 8*θ^2+‖a-n‖*‖n-u‖ := by
      gcongr
      · rwa [abs_of_nonneg hd0]
      · rw [dot_eq_inner]
        exact abs_real_inner_le_norm _ _
    _ ≤ 8*θ^2+(4*φ)*(4*θ) := by
      gcongr
      rwa [norm_sub_rev]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsmall hθ]

lemma transverseProjection_add (w h k : Vec) :
    transverseProjection w (h+k)=transverseProjection w h+transverseProjection w k :=
  velocityProjection_add _ _ _

lemma transverseProjection_smul (w h : Vec) (c : ℝ) :
    transverseProjection w (c • h)=c • transverseProjection w h := velocityProjection_smul _ _ _

lemma transverseProjection_normal_dist (w n : Vec) :
    ‖transverseProjection w n‖ ≤ ‖n-velocity w‖ := by
  have he : transverseProjection w n=transverseProjection w (n-velocity w) := by
    have hh := transverseProjection_add w (n-velocity w) (velocity w)
    rw [sub_add_cancel,transverseProjection_velocity,add_zero] at hh
    exact hh
  rw [he]
  exact transverseProjection_norm _ _

lemma small_primitive_transverse {w u n : Vec} {θ φ : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 < φ)
    (hD : φ^2/2 ≤ 1-dot n (velocity w))
    (hun : ‖u-n‖ ≤ 4*θ) (han : ‖velocity w-n‖ ≤ 4*φ)
    (he : |(1-dot (velocity w) u)-(1-dot n (velocity w))| ≤ 24*φ*θ) :
    ‖transverseProjection w (signedPrimitive (velocity w) u n)‖ ≤ 196*θ := by
  have hDpos : 0 < 1-dot n (velocity w) := lt_of_lt_of_le (by positivity) hD
  have hratio : |(1-dot n (velocity w)-(1-dot (velocity w) u))/(1-dot n (velocity w))| ≤ 48*θ/φ := by
    rw [abs_div,abs_of_pos hDpos,abs_sub_comm]
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 48*θ/φ)
    have hh : 48*θ/φ*(φ^2/2)=24*φ*θ := by field_simp; ring
    rw [hh] at hm
    exact he.trans hm
  have hpn : ‖transverseProjection w n‖ ≤ 4*φ :=
    (transverseProjection_normal_dist w n).trans (by rwa [norm_sub_rev])
  rw [signedPrimitive_decomposition _ _ _ hDpos.ne',transverseProjection_add,transverseProjection_smul]
  calc
    _ ≤ ‖transverseProjection w (u-n)‖+
        ‖((1-dot n (velocity w)-(1-dot (velocity w) u))/(1-dot n (velocity w))) • transverseProjection w n‖ := norm_add_le _ _
    _ ≤ 4*θ+(48*θ/φ)*(4*φ) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add ((transverseProjection_norm _ _).trans hun) (mul_le_mul hratio hpn (norm_nonneg _) (by positivity))
    _ = _ := by field_simp; ring


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal



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


open Set MeasureTheory
open scoped ENNReal


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DyadicCut
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

lemma contDiff_dyadicCut : ContDiff ℝ ∞ dyadicCut :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
lemma contDiff_dyadicBump : ContDiff ℝ ∞ dyadicBump :=
  contDiff_dyadicCut.sub (contDiff_dyadicCut.comp (contDiff_const.mul contDiff_id))
lemma contDiff_dyadicFactor (n : ℕ) : ContDiff ℝ ∞ (dyadicFactor n) :=
  contDiff_dyadicBump.comp (contDiff_const.mul contDiff_id)

lemma dyadicCut_one {x : ℝ} (hx : x≤1) : dyadicCut x=1 := by
  simp only [dyadicCut,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx),sub_zero]
lemma dyadicCut_zero {x : ℝ} (hx : 2≤x) : dyadicCut x=0 := by
  rw [dyadicCut,Real.smoothTransition.one_of_one_le (by linarith),sub_self]
lemma dyadicCut_antitone : Antitone dyadicCut := by
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (sub_le_sub_right hxy 1)) 1
lemma dyadicCut_nonneg (x : ℝ) : 0≤dyadicCut x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma dyadicCut_le_one (x : ℝ) : dyadicCut x≤1 := sub_le_self _ (Real.smoothTransition.nonneg _)
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_nonneg (x : ℝ) : 0≤dyadicBump x := by
  by_cases hx : x≤1/2
  · rw [dyadicBump_zero_left hx]
  · exact sub_nonneg.mpr (dyadicCut_antitone (by linarith : x≤2*x))
lemma dyadicBump_le_one (x : ℝ) : dyadicBump x≤1 :=
  (sub_le_self _ (dyadicCut_nonneg _)).trans (dyadicCut_le_one _)
lemma dyadicBump_support : tsupport dyadicBump ⊆ Icc (1/2) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    exact hx (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hx (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))
lemma dyadicFactor_nonneg (n : ℕ) (x : ℝ) : 0≤dyadicFactor n x := dyadicBump_nonneg _
lemma dyadicFactor_le_one (n : ℕ) (x : ℝ) : dyadicFactor n x≤1 := dyadicBump_le_one _

lemma dyadicFactor_zero_large {x : ℝ} {n : ℕ} (hn : 2≤(2:ℝ)^n*x) :
    dyadicFactor n x=0 := dyadicBump_zero_right hn

lemma hasDerivAt_dyadicFactor (n : ℕ) (x : ℝ) :
    HasDerivAt (dyadicFactor n) ((2:ℝ)^n*deriv dyadicBump ((2:ℝ)^n*x)) x := by
  have hh := ((contDiff_dyadicBump.differentiable (by simp)) _).hasDerivAt.comp x
    ((hasDerivAt_id x).const_mul ((2:ℝ)^n))
  change HasDerivAt (fun y => dyadicBump ((2:ℝ)^n*y)) _ x
  simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using hh

lemma dyadicFactor_log_derivative_bound : ∃ C : ℝ, 0≤C ∧
    ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C := by
  have hd : Continuous (deriv dyadicBump) := contDiff_dyadicBump.continuous_deriv (by simp)
  have hcon : Continuous (fun x : ℝ => x*deriv dyadicBump x) := continuous_id.mul hd
  obtain ⟨C,hC⟩ := (isCompact_Icc.image hcon).isBounded.exists_norm_le
  refine ⟨max 0 C,le_max_left _ _,fun n x => ?_⟩
  rw [(hasDerivAt_dyadicFactor n x).deriv]
  have he : x*((2:ℝ)^n*deriv dyadicBump ((2:ℝ)^n*x)) =
      ((2:ℝ)^n*x)*deriv dyadicBump ((2:ℝ)^n*x) := by ring
  rw [he]
  by_cases hx : (2:ℝ)^n*x ∈ Icc (1/2:ℝ) 2
  · exact (hC _ ⟨(2:ℝ)^n*x,hx,rfl⟩).trans (le_max_right _ _)
  · rw [deriv_of_notMem_tsupport (fun h => hx (dyadicBump_support h)),mul_zero,abs_zero]
    exact le_max_left _ _

lemma dyadicFactor_tsupport {n : ℕ} {x : ℝ} (hx : x ∈ tsupport (dyadicFactor n)) :
    DyadicBand n x := by
  have hcl : IsClosed {x : ℝ | DyadicBand n x} :=
    (isClosed_le continuous_const (continuous_const.mul continuous_id)).inter
      (isClosed_le (continuous_const.mul continuous_id) continuous_const)
  apply (closure_minimal (s:=(Function.support (dyadicFactor n))) ?_ hcl) hx
  intro y hy
  constructor
  · by_contra hn
    exact hy (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hy (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))

lemma dyadicBand_index_le {n m : ℕ} {x : ℝ} (hn : DyadicBand n x) (hm : DyadicBand m x) :
    m≤n+2 := by
  by_contra hmn
  have hnm : n+3 ≤ m := by omega
  have hx : 0≤x := by
    have hp : 0<(2:ℝ)^n := by positivity
    by_contra hh
    have he := mul_neg_of_pos_of_neg hp (lt_of_not_ge hh)
    linarith [hn.1]
  have he := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hnm) hx
  rw [pow_add] at he
  norm_num at he
  nlinarith [hn.1,hm.2]

lemma dyadicBand_card_le (S : Finset ℕ) {x : ℝ} (hS : ∀ n ∈ S, DyadicBand n x) :
    S.card≤5 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨n,hn⟩ := hs
    have hsub : S ⊆ Finset.Icc (n-2) (n+2) := by
      intro m hm
      have hlo := dyadicBand_index_le (hS m hm) (hS n hn)
      have hhi := dyadicBand_index_le (hS n hn) (hS m hm)
      exact Finset.mem_Icc.mpr ⟨by omega,hhi⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma dyadicMultiFactor_nonneg {ι : Type*} [Fintype ι] (n : ι→ℕ) (x : ι→ℝ) :
    0≤dyadicMultiFactor n x := Finset.prod_nonneg (fun _i _ => dyadicFactor_nonneg _ _)

lemma differentiableAt_dyadicMultiFactor_curve {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t) (n : ι→ℕ) :
    DifferentiableAt ℝ (fun r => dyadicMultiFactor n (fun i => g i r)) t := by
  classical
  exact DifferentiableAt.fun_finsetProd (fun i _ =>
    (contDiff_dyadicFactor (n i)).differentiable (by simp) (g i t) |>.comp t (hg i))

lemma dyadicMultiFactor_positive_bands {ι : Type*} [Fintype ι]
    {n : ι→ℕ} {x : ι→ℝ} (h : 0<dyadicMultiFactor n x) : ∀ i,DyadicBand (n i) (x i) := by
  classical
  intro i
  apply dyadicFactor_tsupport
  apply subset_tsupport
  intro he
  have hz : dyadicMultiFactor n x=0 := Finset.prod_eq_zero (Finset.mem_univ i) he
  linarith

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PhysicalCutoffCoordinates
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

namespace RVM

lemma physicalCutoffCoordinates_pos {T r : ℝ} {n v w : Vec}
    (hn : ‖n‖=1) (hr : 0 < r) : ∀ i,0<physicalCutoffCoordinates T r n v w i := by
  intro i
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · exact one_div_pos.mpr (q_pos v)
  · exact Real.sqrt_pos.mpr (div_pos (cone_denom_pos v n hn) (by norm_num))
  · exact Real.sqrt_pos.mpr (div_pos (cone_denom_pos w n hn) (by norm_num))
  · exact div_pos hr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

lemma angularCoordinate_log_deriv {d : ℝ→ℝ} {d' t : ℝ}
    (hd : HasDerivAt d d' t) (hp : 0<d t) :
    deriv (fun s => Real.sqrt (d s/2)) t / Real.sqrt (d t/2) = d'/(2*d t) := by
  have hhalf : 0<d t/2 := by positivity
  have hs := ((hd.div_const 2).sqrt hhalf.ne').deriv
  rw [hs]
  have hq := Real.sq_sqrt hhalf.le
  have hn := (Real.sqrt_pos.mpr hhalf).ne'
  field_simp
  rw [hq]
  ring

lemma dyadicMultiFactor_curve_locally_finite {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, ContinuousAt (g i) t) (hx : ∀ i,0<g i t) :
    ∃ N : ℕ, (∀ i,2≤(2:ℝ)^N*g i t) ∧
      ∀ᶠ r in 𝓝 t, ∀ n : ι→ℕ, n∉dyadicBox ι N → dyadicMultiFactor n (fun i => g i r)=0 := by
  classical
  have hp (i : ι) := pow_unbounded_of_one_lt (4/g i t) (by norm_num : (1:ℝ)<2)
  choose Ns hNs using hp
  let N := ∑ i,Ns i
  have hN (i : ι) : 4<(2:ℝ)^N*g i t := by
    have hNi : Ns i≤N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ((div_lt_iff₀ (hx i)).mp (hNs i)).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNi) (hx i).le)
  refine ⟨N,fun i => by linarith [hN i],?_⟩
  have he : ∀ᶠ r in 𝓝 t, ∀ i,g i t/2<g i r := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hg i).eventually (Ioi_mem_nhds (by linarith [hx i]))
  filter_upwards [he] with r hr n hn
  have hb : ∃ i,N≤n i := by
    by_contra hb
    push Not at hb
    apply hn
    simpa only [dyadicBox,Fintype.mem_piFinset,Finset.mem_range] using hb
  obtain ⟨i,hi⟩ := hb
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply dyadicFactor_zero_large
  have hpN : 0<(2:ℝ)^N := by positivity
  have hpni : (2:ℝ)^N≤(2:ℝ)^(n i) := pow_le_pow_right₀ (by norm_num) hi
  have hgr : 0≤g i r := le_of_lt ((by linarith [hx i] : 0<g i t/2).trans (hr i))
  have hh := mul_le_mul_of_nonneg_right hpni hgr
  have hh' := mul_lt_mul_of_pos_left (hr i) hpN
  linarith [hN i]

lemma selectedDyadicCutoff_curve_eventually {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, ContinuousAt (g i) t) (hx : ∀ i,0<g i t)
    (S : Set (ι→ℕ)) :
    ∃ N : ℕ, (∀ i,2≤(2:ℝ)^N*g i t) ∧
      (fun r => selectedDyadicCutoff S (fun i => g i r)) =ᶠ[𝓝 t]
        (fun r => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n (fun i => g i r)) := by
  classical
  obtain ⟨N,hN,he⟩ := dyadicMultiFactor_curve_locally_finite hg hx
  refine ⟨N,hN,?_⟩
  filter_upwards [he] with r hr
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using (Finset.sum_indicator_eq_sum_filter (dyadicBox ι N) (fun _ n => dyadicMultiFactor n (fun i => g i r)) (fun _ => S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hr n hn]
    · exact indicator_of_notMem hs _

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

lemma hasDerivAt_line_rvm (y u : Vec) :
    HasDerivAt (fun s : ℝ => y+s • u) u 0 := by
  have hh := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const u)
  change HasDerivAt (fun s : ℝ => y+s • u) (0+(1:ℝ) • u) 0 at hh
  simpa only [zero_add,one_smul] using hh



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_ContDiffDyadicMultiFactor
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

namespace RVM

lemma coneMotion_tangent {a u n : Vec} (hn : ‖n‖=1) (hD : 1-dot n a≠0) :
    dot n (coneMotion a u n)=0 := by
  simp only [coneMotion,dot_add_right,dot_sub_right,dot_smul_right,dot_self,hn,one_pow]
  field_simp
  ring

lemma geometric_cutoff_logarithmic_rates {v w n : Vec} {r : ℝ}
    (hn : ‖n‖=1) (hr : 0 < r)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity w)) :
    let d := 1-dot n (velocity v)
    let D := 1-dot n (velocity w)
    let N := r⁻¹ • coneMotion (velocity w) (velocity v) n
    |(d/D-1)/r| + |dot N (velocity v)/(2*d)| +
      |dot N (velocity w)/(2*D)| ≤ 5/r := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity w)
  let θ := Real.sqrt (d/2)
  let φ := Real.sqrt (D/2)
  let N := r⁻¹ • coneMotion (velocity w) (velocity v) n
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos w n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=D/2 := Real.sq_sqrt (by positivity)
  have hdθ : d=2*θ^2 := by linarith
  have hDφ : D=2*φ^2 := by linarith
  have hθφ : θ≤φ := Real.sqrt_le_sqrt (by dsimp [d,D]; linarith)
  have hun : ‖velocity v-n‖≤2*θ := by
    apply (velocity_normal_distance_bound v n hn).trans_eq
    change Real.sqrt (2*d)=2*θ
    have hh := Real.sq_sqrt (show 0≤2*d by positivity)
    nlinarith [Real.sqrt_nonneg (2*d)]
  have han : ‖velocity w-n‖≤2*φ := by
    apply (velocity_normal_distance_bound w n hn).trans_eq
    change Real.sqrt (2*D)=2*φ
    have hh := Real.sq_sqrt (show 0≤2*D by positivity)
    nlinarith [Real.sqrt_nonneg (2*D)]
  have hfac : (d/D)*(2*φ)≤2*θ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hD).mpr
    rw [hdθ,hDφ]
    nlinarith [mul_nonneg (show 0≤4*θ*φ by positivity) (sub_nonneg.mpr hθφ)]
  have hmotion : ‖coneMotion (velocity w) (velocity v) n‖≤4*θ := by
    have he : coneMotion (velocity w) (velocity v) n =
        (d/D) • (velocity w-n)-(velocity v-n) := by unfold coneMotion; dsimp [d,D]; module
    rw [he]
    calc
      _ ≤ ‖(d/D) • (velocity w-n)‖+‖velocity v-n‖ := norm_sub_le _ _
      _ ≤ (d/D)*(2*φ)+2*θ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hd hD)]
        exact add_le_add (mul_le_mul_of_nonneg_left han (div_nonneg hd.le hD.le)) hun
      _ ≤ _ := by linarith
  have hnorm : ‖N‖≤4*θ/r := by
    dsimp only [N]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left hmotion (inv_nonneg.mpr hr.le)).trans_eq (by ring)
  have htan : dot N n=0 := by
    dsimp only [N]
    rw [dot_smul_left,dot_comm _ n,coneMotion_tangent hn hD.ne',mul_zero]
  have hsDot : |dot N (velocity v)|≤(4*θ/r)*(2*θ) := by
    have he : dot N (velocity v)=dot N (velocity v-n) := by rw [dot_sub_right,htan,sub_zero]
    rw [he]
    exact (abs_dot_le _ _).trans (mul_le_mul hnorm hun (norm_nonneg _) (by positivity))
  have hrDot : |dot N (velocity w)|≤(4*θ/r)*(2*φ) := by
    have he : dot N (velocity w)=dot N (velocity w-n) := by rw [dot_sub_right,htan,sub_zero]
    rw [he]
    exact (abs_dot_le _ _).trans (mul_le_mul hnorm han (norm_nonneg _) (by positivity))
  have hsRate : |dot N (velocity v)/(2*d)|≤2/r := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*d)]
    apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
    apply hsDot.trans_eq
    rw [hdθ]
    ring
  have hrRate : |dot N (velocity w)/(2*D)|≤2/r := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*D)]
    apply (div_le_iff₀ (by positivity : 0<2*D)).mpr
    apply hrDot.trans
    rw [hDφ]
    have hh := mul_le_mul_of_nonneg_right hθφ (show 0≤8*φ/r by positivity)
    convert hh using 1 <;> ring
  have hrad : |(d/D-1)/r|≤1/r := by
    rw [abs_div,abs_of_pos hr]
    apply div_le_div_of_nonneg_right _ hr.le
    apply abs_le.mpr
    constructor
    · linarith [div_nonneg hd.le hD.le]
    · have hh : d/D≤1 := (div_le_one hD).mpr hsmall
      linarith
  change |(d/D-1)/r|+|dot N (velocity v)/(2*d)|+|dot N (velocity w)/(2*D)|≤5/r
  exact (add_le_add (add_le_add hrad hsRate) hrRate).trans_eq (by ring)

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


lemma dyadicFactor_curve_log_bound {C : ℝ}
    (hC : ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C)
    {g : ℝ → ℝ} {t : ℝ} (hg : DifferentiableAt ℝ g t) (hx : 0<g t) (n : ℕ) :
    |deriv (fun r => dyadicFactor n (g r)) t|≤C*|deriv g t/g t| := by
  change |deriv (dyadicFactor n ∘ g) t| ≤ _
  rw [deriv_comp t ((contDiff_dyadicFactor n).differentiable (by simp) (g t)) hg]
  calc
    _ = |(g t*deriv (dyadicFactor n) (g t))*(deriv g t/g t)| := by
      congr 1
      field_simp [hx.ne']
    _ = |g t*deriv (dyadicFactor n) (g t)| * |deriv g t/g t| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hC n (g t)) (abs_nonneg _)

lemma dyadicMultiFactor_curve_zero_derivative {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (n : ι→ℕ)
    (hz : dyadicMultiFactor n (fun i => g i t)=0) :
    deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t=0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun r => by
    dsimp only
    rw [hz]
    exact dyadicMultiFactor_nonneg _ _)

lemma dyadicMultiFactor_curve_log_bound {C : ℝ}
    (hC : ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C)
    {ι : Type*} [Fintype ι] {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i, DifferentiableAt ℝ (g i) t) (hx : ∀ i, 0<g i t) (n : ι→ℕ) :
    |deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t| ≤
      C * ∑ i, |deriv (g i) t/g i t| := by
  classical
  have hd (i : ι) : DifferentiableAt ℝ (fun r => dyadicFactor (n i) (g i r)) t :=
    ((contDiff_dyadicFactor (n i)).differentiable (by simp) (g i t)).comp t (hg i)
  unfold dyadicMultiFactor
  dsimp only
  rw [deriv_fun_finsetProd (u:=Finset.univ) (fun i _ => hd i)]
  simp only [smul_eq_mul]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp0 : 0≤∏ j∈Finset.univ.erase i,dyadicFactor (n j) (g j t) :=
    Finset.prod_nonneg (fun j _ => dyadicFactor_nonneg _ _)
  have hp1 : (∏ j∈Finset.univ.erase i,dyadicFactor (n j) (g j t))≤1 :=
    Finset.prod_le_one (fun j _ => dyadicFactor_nonneg _ _) (fun j _ => dyadicFactor_le_one _ _)
  rw [abs_mul,abs_of_nonneg hp0]
  exact (mul_le_of_le_one_left (abs_nonneg _) hp1).trans
    (dyadicFactor_curve_log_bound hC (hg i) (hx i) (n i))

lemma dyadicBand_multi_card_le {ι : Type*} [Fintype ι] (S : Finset (ι→ℕ)) {x : ι→ℝ}
    (hS : ∀ n∈S,∀ i,DyadicBand (n i) (x i)) : S.card≤5^Fintype.card ι := by
  classical
  let A : ι→Finset ℕ := fun i=>S.image (fun n=>n i)
  have hA : ∀ i,(A i).card≤5 := by
    intro i
    apply dyadicBand_card_le
    intro n hn
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
    exact hS m hm i
  calc
    S.card ≤ (Fintype.piFinset A).card := Finset.card_le_card (by
      intro n hn
      exact Fintype.mem_piFinset.mpr (fun i=>Finset.mem_image.mpr ⟨n,hn,rfl⟩))
    _ = ∏ i,(A i).card := Fintype.card_piFinset A
    _ ≤ ∏ _i : ι,5 := Finset.prod_le_prod' (fun i _=>hA i)
    _ = _ := by simp

lemma selectedDyadicCutoff_uniform_log_bound {C : ℝ}
    (hC0 : 0≤C) (hC : ∀ n : ℕ,∀ x : ℝ,|x*deriv (dyadicFactor n) x|≤C)
    {ι : Type*} [Fintype ι] {g : ι→ℝ→ℝ} {t : ℝ}
    (hg : ∀ i,DifferentiableAt ℝ (g i) t) (hp : ∀ i,0<g i t) (S : Set (ι→ℕ)) :
    |deriv (fun r=>selectedDyadicCutoff S (fun i=>g i r)) t| ≤
      (5:ℝ)^Fintype.card ι*C*∑ i,|deriv (g i) t/g i t| := by
  classical
  obtain ⟨N,_hN,he⟩ := selectedDyadicCutoff_curve_eventually (fun i=>(hg i).continuousAt) hp S
  rw [he.deriv_eq,deriv_fun_sum (fun n _=>differentiableAt_dyadicMultiFactor_curve hg n)]
  let A := (selectedDyadicBox N S).filter (fun n=>∀ i,DyadicBand (n i) (g i t))
  have hac : A.card≤5^Fintype.card ι := dyadicBand_multi_card_le A
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  have hz (n : ι→ℕ) (hnb : ¬∀ i,DyadicBand (n i) (g i t)) :
      deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t=0 := by
    apply dyadicMultiFactor_curve_zero_derivative
    by_contra h
    exact hnb (dyadicMultiFactor_positive_bands
      (lt_of_le_of_ne (dyadicMultiFactor_nonneg _ _) (Ne.symm h)))
  have heq : (∑ n∈selectedDyadicBox N S,deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t)=
      ∑ n∈A,deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hna
    exact hz n (by simpa only [A,Finset.mem_filter,hn,true_and] using hna)
  rw [heq]
  calc
    _ ≤ ∑ n∈A,|deriv (fun r=>dyadicMultiFactor n (fun i=>g i r)) t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n∈A,C*∑ i,|deriv (g i) t/g i t| :=
      Finset.sum_le_sum (fun n _=>dyadicMultiFactor_curve_log_bound hC hg hp n)
    _ = (A.card:ℝ)*(C*∑ i,|deriv (g i) t/g i t|) := by simp
    _ ≤ (5:ℝ)^Fintype.card ι*(C*∑ i,|deriv (g i) t/g i t|) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hac
    _ = _ := by ring

lemma transverseCLM_apply (v h : Vec) : transverseCLM v h=transverseProjection v h := by
  simp only [transverseCLM,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]
  rfl

lemma angularMultiplierCLM_apply (w : ℝ) (v h : Vec) :
    angularMultiplierCLM w v h=angularMultiplier w v h := by
  simp only [angularMultiplierCLM,smul_apply,transverseCLM_apply,angularMultiplier]



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CutoffState
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
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma selectedDyadicCutoff_eventually {ι : Type*} [Fintype ι]
    {x : ι→ℝ} (hx : ∀ i,0<x i) (S : Set (ι→ℕ)) :
    ∃ N : ℕ, selectedDyadicCutoff S =ᶠ[𝓝 x]
      (fun y => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n y) := by
  classical
  have hp (i : ι) := pow_unbounded_of_one_lt (4/x i) (by norm_num : (1:ℝ)<2)
  choose Ns hNs using hp
  let N := ∑ i,Ns i
  have hN (i : ι) : 4<(2:ℝ)^N*x i := by
    have hNi : Ns i≤N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ((div_lt_iff₀ (hx i)).mp (hNs i)).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNi) (hx i).le)
  have he : ∀ᶠ y in 𝓝 x, ∀ i,x i/2<y i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually (Ioi_mem_nhds (by linarith [hx i]))
  refine ⟨N,?_⟩
  filter_upwards [he] with y hy
  have hz : ∀ n : ι→ℕ,n∉dyadicBox ι N → dyadicMultiFactor n y=0 := by
    intro n hn
    have hb : ∃ i,N≤n i := by
      by_contra hb
      push Not at hb
      apply hn
      simpa only [dyadicBox,Fintype.mem_piFinset,Finset.mem_range] using hb
    obtain ⟨i,hi⟩ := hb
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply dyadicFactor_zero_large
    have hpN : 0<(2:ℝ)^N := by positivity
    have hpni : (2:ℝ)^N≤(2:ℝ)^(n i) := pow_le_pow_right₀ (by norm_num) hi
    have hyr : 0≤y i := le_of_lt ((by linarith [hx i] : 0<x i/2).trans (hy i))
    have hh := mul_le_mul_of_nonneg_right hpni hyr
    have hh' := mul_lt_mul_of_pos_left (hy i) hpN
    linarith [hN i]
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using
      (Finset.sum_indicator_eq_sum_filter (dyadicBox ι N)
        (fun _ n => dyadicMultiFactor n y) (fun _ => S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hz n hn]
    · exact indicator_of_notMem hs _

lemma contDiffAt_selectedDyadicCutoff {ι : Type*} [Fintype ι]
    {x : ι→ℝ} (hx : ∀ i,0<x i) (S : Set (ι→ℕ)) :
    ContDiffAt ℝ ∞ (selectedDyadicCutoff S) x := by
  classical
  obtain ⟨N,he⟩ := selectedDyadicCutoff_eventually hx S
  apply (ContDiffAt.sum (s:=selectedDyadicBox N S) (fun n _ => ?_)).congr_of_eventuallyEq he
  exact contDiffAt_prod (fun i _ => (contDiff_dyadicFactor (n i)).contDiffAt.comp x (contDiff_apply ℝ ℝ i).contDiffAt)

lemma contDiffAt_stateCutoff (T : ℝ) (Q : Set (Fin 4→ℕ)) {z : CutoffState}
    (hr : 0<z.1) (hn : ‖z.2.1‖=1) : ContDiffAt ℝ ∞ (stateCutoff T Q) z := by
  have hc : ContDiffAt ℝ ∞ (fun z : CutoffState =>
      physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) z := by
    apply contDiffAt_pi.mpr
    intro i
    have hv : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.1) z :=
      (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst
    have hw : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.2) z :=
      (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.snd
    have hd := (contDiffAt_const (c:=(1:ℝ))).sub
      ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hv))
    have hD := (contDiffAt_const (c:=(1:ℝ))).sub
      ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hw))
    fin_cases i <;> simp only [physicalCutoffCoordinates]
    · exact contDiffAt_const.div ((contDiff_q (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst) (q_pos _).ne'
    · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
    · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
    · exact contDiffAt_id.fst.div_const _
  exact (contDiffAt_selectedDyadicCutoff (physicalCutoffCoordinates_pos hn hr) Q).comp z hc

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


lemma projected_time_weight_small_kernel {w f r θ φ : ℝ} {v u n : Vec}
    (hf : 0≤f) (hr : 0 < r) (hθ : 0≤θ) (hφ : 0<φ)
    (hD : φ^2/2≤1-dot n (velocity v)) (hun : ‖u-n‖≤4*θ)
    (han : ‖velocity v-n‖≤4*φ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularMultiplierCLM w v (signedPrimitive (velocity v) u n)‖ ≤
      196*f*|w| *θ/(r*‖v‖) := by
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,norm_smul,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hf hr.le),
    abs_div,abs_norm]
  calc
    _ ≤ (f/r)*(|w|/‖v‖*(196*θ)) := by
      gcongr
      exact small_primitive_transverse hθ hφ hD hun han he
    _ = _ := by ring



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


lemma projected_primitive_highband_kernel {w f r θ φ : ℝ} {v u n : Vec}
    (hw : 0<w) (hv : w/16≤‖v‖) (hf : 0≤f) (hr : 0 < r)
    (hθ : 0≤θ) (hφ : 0<φ) (hD : φ^2/2≤1-dot n (velocity v))
    (hun : ‖u-n‖≤4*θ) (han : ‖velocity v-n‖≤4*φ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularMultiplierCLM w v (signedPrimitive (velocity v) u n)‖≤
      (3136*θ/r)*f := by
  have hvp : 0<‖v‖ := (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le hv
  have hratio : w/‖v‖≤16 := (div_le_iff₀ hvp).mpr (by linarith)
  calc
    _ ≤ 196*f*|w| *θ/(r*‖v‖) := projected_time_weight_small_kernel hf hr hθ hφ hD hun han he
    _ = (f/r)*((w/‖v‖)*(196*θ)) := by rw [abs_of_pos hw]; ring
    _ ≤ (f/r)*(16*(196*θ)) := by gcongr
    _ = _ := by ring


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_CutoffSourceTangent
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
open scoped ENNReal Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiffAt_physicalCutoffCoordinates {T : ℝ} {z : CutoffState}
    (_hr : 0<z.1) (hn : ‖z.2.1‖=1) :
    ContDiffAt ℝ ∞ (fun z : CutoffState =>
      physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) z := by
  apply contDiffAt_pi.mpr
  intro i
  have hv : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.1) z :=
    (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst
  have hw : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.2) z :=
    (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.snd
  have hd := (contDiffAt_const (c:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hv))
  have hD := (contDiffAt_const (c:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hw))
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · exact contDiffAt_const.div ((contDiff_q (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst) (q_pos _).ne'
  · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
  · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
  · exact contDiffAt_id.fst.div_const _

lemma stateCutoff_curve_log_bound {C T t : ℝ}
    (hC0 : 0≤C) (hC : ∀n : ℕ,∀x : ℝ,|x*deriv (dyadicFactor n) x|≤C)
    {z : ℝ→CutoffState} {h : CutoffState}
    (hz : HasDerivAt z h t) (hr : 0<(z t).1) (hn : ‖(z t).2.1‖=1)
    (Q : Set (Fin 4→ℕ)) :
    |fderiv ℝ (stateCutoff T Q) (z t) h| ≤
      625*C*∑i : Fin 4,|deriv (fun s=>physicalCutoffCoordinates T
        (z s).1 (z s).2.1 (z s).2.2.1 (z s).2.2.2 i) t /
        physicalCutoffCoordinates T (z t).1 (z t).2.1 (z t).2.2.1 (z t).2.2.2 i| := by
  have hd := ((contDiffAt_stateCutoff T Q hr hn).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hz
  rw [←hd.deriv]
  change |deriv (fun s=>selectedDyadicCutoff Q (physicalCutoffCoordinates T
    (z s).1 (z s).2.1 (z s).2.2.1 (z s).2.2.2)) t| ≤ _
  have hc := (contDiffAt_physicalCutoffCoordinates (T:=T) hr hn).differentiableAt (by simp)
  have hh := selectedDyadicCutoff_uniform_log_bound hC0 hC
    (fun i=>differentiableAt_pi.mp (hc.comp t hz.differentiableAt) i)
    (physicalCutoffCoordinates_pos (T:=T) hn hr) Q
  simpa only [stateCutoff,Function.comp_apply,Fintype.card_fin,show (5:ℝ)^4=625 by norm_num] using hh

lemma stateCutoff_geometry_bound {C T r : ℝ} {n v w : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hr : 0 < r) (hn : ‖n‖=1)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity w)) (Q : Set (Fin 4→ℕ)) :
    |fderiv ℝ (stateCutoff T Q) (r,n,v,w)
      (cutoffGeometryTangent r ((1-dot n (velocity v))/(1-dot n (velocity w)))
        (velocity w) (velocity v) n)| ≤ 625*C*(5/r) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity w)
  let M := r⁻¹ • coneMotion (velocity w) (velocity v) n
  let N : ℝ→Vec := fun s=>n+s • M
  let R : ℝ→ℝ := fun s=>r+s*(d/D-1)
  have hN : HasDerivAt N M 0 := hasDerivAt_line_rvm n M
  have hR : HasDerivAt R (d/D-1) 0 := by
    convert (hasDerivAt_const (0:ℝ) r).add ((hasDerivAt_id (0:ℝ)).mul_const (d/D-1)) using 1 <;>
      first | rfl | simp only [zero_add,one_mul]
  have hn0 : N 0=n := by simp [N]
  have hr0 : R 0=r := by simp [R]
  have hz : HasDerivAt (fun s : ℝ=>(R s,N s,v,w))
      (cutoffGeometryTangent r (d/D) (velocity w) (velocity v) n) 0 :=
    hR.prodMk (hN.prodMk ((hasDerivAt_const 0 v).prodMk (hasDerivAt_const 0 w)))
  have hb := stateCutoff_curve_log_bound (T:=T) hC0 hC hz (by rwa [hr0]) (by rwa [hn0]) Q
  simp only [hr0,hn0] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hd : HasDerivAt (fun s=>1-dot (N s) (velocity v)) (-dot M (velocity v)) 0 := by
    have hh := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_dot hN (hasDerivAt_const 0 (velocity v)))
    convert hh using 1 <;> first | rfl | simp only [dot_zero_right_rvm,zero_add,zero_sub]
  have hD : HasDerivAt (fun s=>1-dot (N s) (velocity w)) (-dot M (velocity w)) 0 := by
    have hh := (hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_dot hN (hasDerivAt_const 0 (velocity w)))
    convert hh using 1 <;> first | rfl | simp only [dot_zero_right_rvm,zero_add,zero_sub]
  have hed := angularCoordinate_log_deriv hd (by rw [hn0]; exact cone_denom_pos _ _ hn)
  have heD := angularCoordinate_log_deriv hD (by rw [hn0]; exact cone_denom_pos _ _ hn)
  have her : deriv (fun s=>R s/max 1 T) 0/(r/max 1 T)=(d/D-1)/r := by
    rw [(hR.div_const (max 1 T)).deriv]
    have hm : max 1 T≠0 := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'
    field_simp
  simp only [hn0] at hed heD
  simp only [Fin.sum_univ_succ,Fin.isValue,physicalCutoffCoordinates,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,
    deriv_const,zero_div,abs_zero,zero_add]
  rw [hed,heD,her]
  simp only [neg_div,abs_neg]
  have hh := geometric_cutoff_logarithmic_rates (v:=v) (w:=w) hn hr hsmall
  dsimp only at hh
  dsimp only [d,D,M]
  linarith

lemma projected_physical_small_primitive {v W n : Vec} {w : ℝ}
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) :
    ‖angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      3136*Real.sqrt ((1-dot n (velocity v))/2) := by
  let θ := Real.sqrt ((1-dot n (velocity v))/2)
  let φ := Real.sqrt ((1-dot n (velocity W))/2)
  have hd := cone_denom_pos v n hn
  have hD := cone_denom_pos W n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=(1-dot n (velocity v))/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=(1-dot n (velocity W))/2 := Real.sq_sqrt (by positivity)
  have hθφ : θ≤φ := Real.sqrt_le_sqrt (by linarith)
  have hun : ‖velocity v-n‖≤4*θ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le hn.le (by positivity)
    rw [dot_comm]
    nlinarith
  have han : ‖velocity W-n‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le hn.le (by positivity)
    rw [dot_comm]
    nlinarith
  have he := small_deficit_difference hn hθ.le hφ.le hθφ hd.le (by nlinarith) hun han
  simpa only [one_div_one,one_smul,div_one,mul_one] using
    projected_primitive_highband_kernel (w:=w) (f:=1) (r:=1) hw hW (by norm_num) (by norm_num)
      hθ.le hφ (by nlinarith) hun han he

lemma projected_physical_cutoff_cost {v W n : Vec} {w r f c L : ℝ}
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0 < r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (hL : |L| ≤ c) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*L) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      3136*(f/r)*(φ^2/θ)*c := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  let θ := Real.sqrt (d/2)
  let φ := Real.sqrt (D/2)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hθ : 0<θ := Real.sqrt_pos.mpr (by positivity)
  have hφ : 0<φ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ^2=d/2 := Real.sq_sqrt (by positivity)
  have hφsq : φ^2=D/2 := Real.sq_sqrt (by positivity)
  have hcb : 0 ≤ c := (abs_nonneg _).trans hL
  have hp := projected_physical_small_primitive hn hw hW hsmall
  change ‖(f*D/(r*d)*L) • _‖≤3136*(f/r)*(φ^2/θ)*c
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤f*D/(r*d))]
  calc
    _ ≤ (f*D/(r*d)*c)*(3136*θ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL (by positivity)) hp (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : d=2*θ^2 := by linarith
      have hE : D=2*φ^2 := by linarith
      rw [he,hE]
      field_simp

lemma projected_geometry_cutoff_cost {C T r f w : ℝ} {n v W : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0 < r) (hf : 0≤f)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    let θ := Real.sqrt ((1-dot n (velocity v))/2)
    let φ := Real.sqrt ((1-dot n (velocity W))/2)
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffGeometryTangent r ((1-dot n (velocity v))/(1-dot n (velocity W)))
          (velocity W) (velocity v) n)) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      9800000*C*f*φ^2/(r^2*θ) := by
  have hb := projected_physical_cutoff_cost hn hw hW hr hf hsmall
    (stateCutoff_geometry_bound (T:=T) (v:=v) (w:=W) hC0 hC hr hn hsmall Q)
  exact hb.trans_eq (by field_simp; ring)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_PhysicalGeometryCutoffDensity
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

namespace RVM

lemma projected_geometry_cutoff_bin_cost {A T r f w θ φ : ℝ} {n v W : Vec}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16 ≤ ‖W‖) (hr : 0 < r) (hf : 0 ≤ f)
    (hθ : 0<θ) (_hφ : 0 ≤ φ) (hd : θ^2/2 ≤ 1-dot n (velocity v))
    (hD : 1-dot n (velocity W) ≤ 8*φ^2)
    (hsmall : 1-dot n (velocity v) ≤ 1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffGeometryTangent r ((1-dot n (velocity v))/(1-dot n (velocity W)))
          (velocity W) (velocity v) n)) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      (78400000*A*φ^2/θ/r^2)*f := by
  let θa := Real.sqrt ((1-dot n (velocity v))/2)
  let φa := Real.sqrt ((1-dot n (velocity W))/2)
  have hθa : 0<θa := Real.sqrt_pos.mpr (div_pos (cone_denom_pos v n hn) (by norm_num))
  have hφa : 0 ≤ φa := Real.sqrt_nonneg _
  have hθl : θ/2 ≤ θa := by
    apply (Real.le_sqrt (by positivity) (div_nonneg (cone_denom_pos v n hn).le (by norm_num))).mpr
    nlinarith
  have hφl : φa^2 ≤ 4*φ^2 := by
    dsimp [φa]
    rw [Real.sq_sqrt (div_nonneg (cone_denom_pos W n hn).le (by norm_num))]
    linarith
  have hb := projected_geometry_cutoff_cost (T:=T) hA0 hA hn hw hW hr hf hsmall Q
  change _ ≤ 9800000*A*f*φa^2/(r^2*θa) at hb
  calc
    _ ≤ 9800000*A*f*φa^2/(r^2*θa) := hb
    _ ≤ 9800000*A*f*(4*φ^2)/(r^2*(θ/2)) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
    _ = _ := by field_simp; ring

lemma physicalGeometryCutoffDensity_bound {s : Solution} {X V : ℝ→Vec}
    {B : ClosedConeBin} {A T w θ φ : ℝ} {z : ConeCoordinate}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hw : 0<w) (hv : w/16 ≤ ‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hθ : 0<θ) (hφ : 0 ≤ φ) (hd : θ^2/2 ≤ B.dmin)
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1)) ≤ 8*φ^2)
    (hsmall : B.dmax ≤ 1-dot z.2.2.1 (velocity (V z.1)))
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))
    (Q : Set (Fin 4→ℕ)) :
    physicalGeometryCutoffDensity s X V B T w Q z ≤
      ENNReal.ofReal (78400000*A*φ^2/θ)*physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  have hp : ∀v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (V z.1)))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
        fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,V z.1)
          (cutoffGeometryTangent (z.1-z.2.1)
            ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (V z.1))))
            (velocity (V z.1)) (velocity v) z.2.2.1)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖ ≤
      ENNReal.ofReal (78400000*A*φ^2/θ/(z.1-z.2.1)^2)*
        ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
    intro v hvbin
    rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 78400000*A*φ^2/θ/(z.1-z.2.1)^2)]
    exact ENNReal.ofReal_le_ofReal (projected_geometry_cutoff_bin_cost hA0 hA (sphere_norm z.2.2)
      hw hv hr (hf v) hθ hφ (hd.trans hvbin.2.1.1) hDhi (hvbin.2.1.2.trans hsmall) Q)
  unfold physicalGeometryCutoffDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)* ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        ENNReal.ofReal (78400000*A*φ^2/θ/(z.1-z.2.1)^2)*
          ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :=
      mul_le_mul' le_rfl (setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _) hp)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,←ENNReal.ofReal_mul (sq_nonneg _)]
      have he : (z.1-z.2.1)^2*(78400000*A*φ^2/θ/(z.1-z.2.1)^2)=78400000*A*φ^2/θ := by field_simp [hr.ne']
      rw [he]
      rfl

lemma physicalGeometryCutoff_integral_bound {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {X V : ℝ→Vec} (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {A w θ φ : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hw : 0<w) (hθ : 0<θ) (hφ : 0 ≤ φ) (hsmall : B.dmax ≤ B.Dmin)
    (hr : 0<B.rmin) (hd : θ^2/2 ≤ B.dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hband : ∀t∈J,w/16 ≤ ‖V t‖) (Q : Set (Fin 4→ℕ)) :
    (∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s X V B T w Q z ∂physicalBinMeasure V B J) ≤
      ENNReal.ofReal (78400000*A*φ^2/θ)*∫⁻z : ConeCoordinate,
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J := by
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
  have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
  exact physicalGeometryCutoffDensity_bound hA0 hA hw (hband z.1 hz.1)
    (hr.trans_le hz.2.2.1.1) hθ hφ hd (hz.2.2.2.2.2.trans hDhi)
    (hsmall.trans hz.2.2.2.2.1) (fun v=>hs.nonnegative _ hzT _) Q

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

lemma representativeClosedBin_radius_pos (T w : ℝ) (k : Fin 4→ℕ) :
    0<(representativeClosedBin T w k).rmin := by
  have h : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  dsimp [representativeClosedBin,cappedRepresentative]
  positivity

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCutoffs
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

lemma Admissible.geometry_cutoff_small_sector_log_sum_oai {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 →
      0<M → 0≤A → 0<P → 1≤Real.log (2+P) → 0<w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
  classical
  obtain ⟨C,hC,hsum⟩ := hd₀.central_density_small_sector_log_sum
  obtain ⟨c,hc,hcut⟩ := dyadicFactor_log_derivative_bound
  refine ⟨c*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hPw hsource hband HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16}
  let f := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hband' : ∀t∈Icc a b,w/16≤‖V t‖ := by
    intro t ht
    simpa only [V,prefixFlow,prefixClamp_eq (hJ ht)] using hband t ht
  have hbnd (k : Fin 4→ℕ) (hk : k∈sector) :
      (∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))≤ENNReal.ofReal c*f k := by
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hsmall : (representativeClosedBin T w k).dmax≤(representativeClosedBin T w k).Dmin := by
      change 8*θ^2≤φ^2/2
      have hh : θ≤φ/16 := hk
      have hh2 := (sq_le_sq₀ hθ.le (by positivity : 0≤φ/16)).mpr hh
      nlinarith only [hh2]
    have hh := physicalGeometryCutoff_integral_bound (X:=X) hs hα.snd.measurable
      (representativeClosedBin T w k) measurableSet_Icc hJ hc hcut hw hθ hφ.le hsmall
      (representativeClosedBin_radius_pos T w k) le_rfl le_rfl hband' Q
    have he : 78400000*c*φ^2/θ=c*(78400000*φ^2/θ) := by ring
    rw [he,ENNReal.ofReal_mul hc,mul_assoc] at hh
    exact hh
  have hs1 : (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
      physicalGeometryCutoffDensity s X V (representativeClosedBin T w k) T w Q z
        ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ∑'k : Fin 4→ℕ,ENNReal.ofReal c*sector.indicator f k := by
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈sector
    · simpa only [indicator_of_mem hk] using hbnd k hk
    · simp only [indicator_of_notMem hk,mul_zero,le_refl]
  rw [ENNReal.tsum_mul_left] at hs1
  have hs2 := hsum s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab
    hM hA hP hL hw hwP hPw hsource HX HZ
  apply hs1.trans ((mul_le_mul' le_rfl hs2).trans_eq _)
  rw [←ENNReal.ofReal_mul hc]
  congr 1
  ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.geometry_cutoff_small_sector_log_sum_oai := @OAI.RVM.Admissible.geometry_cutoff_small_sector_log_sum_oai
