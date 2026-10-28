-- Prove2me | solution 1 for OAI.RVM.Admissible.direct_transport_sharp_all_radii
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:51:38.178827+00:00
-- url     : https://prove2.me/submissions/dd73e1bf-c755-4402-bb53-0d8d651ab7ca

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_central_density_baseline_radial_sum
import Theorems.Thm_OAI_RVM_Admissible_direct_transport_low_receiver_radii
import Theorems.Thm_OAI_RVM_Admissible_direct_transport_remaining_all_radii

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_RealJointEnergyBudget
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
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma relative_angle_identity (v w : Vec) :
    2*(1-dot (velocity w) (velocity v)) =
      ‖velocity v-velocity w‖^2+(q v)⁻¹^2+(q w)⁻¹^2 :=  by
  rw [norm_sub_sq_real,← dot_eq_inner,← dot_self (velocity v),
    ← dot_self (velocity w),velocity_self,velocity_self,dot_comm (velocity v)]
  ring

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

lemma receiverQ_normal (a n : Vec) : receiverQ a n n=n := by
  rw [receiverQ,dot_comm a n,← add_smul]
  simp

lemma cone_denom_le_two (v n : Vec) (hn : ‖n‖=1) : 1-dot n (velocity v)≤2 := by
  have h := abs_dot_le n (velocity v)
  rw [hn,one_mul] at h
  have h' := (neg_le_abs (dot n (velocity v))).trans h
  linarith [norm_velocity_lt_one v]

lemma receiverQ_tangent_bound (w n h : Vec) (hn : ‖n‖=1) (hh : dot n h=0) :
    ‖receiverQ (velocity w) n h‖≤2*Real.sqrt (2*(1-dot n (velocity w)))*‖h‖ := by
  let D := 1-dot n (velocity w)
  have hD : 0≤D := (cone_denom_pos w n hn).le
  have hD2 : D≤2 := cone_denom_le_two w n hn
  have hDs : D≤Real.sqrt (2*D) := by
    nlinarith [Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hD),Real.sqrt_nonneg (2*D)]
  have ha : |dot (velocity w) h|≤Real.sqrt (2*D)*‖h‖ := by
    rw [show dot (velocity w) h=dot (velocity w-n) h by rw [dot_sub_left,hh,sub_zero]]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (velocity_normal_distance_bound w n hn) (norm_nonneg h))
  calc
    _ ≤ ‖D • h‖+‖dot (velocity w) h • n‖ := norm_add_le _ _
    _ = D*‖h‖+|dot (velocity w) h| := by rw [norm_smul,norm_smul,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg hD,hn,mul_one]
    _ ≤ 2*Real.sqrt (2*D)*‖h‖ := by nlinarith [mul_le_mul_of_nonneg_right hDs (norm_nonneg h)]

lemma velocity_tangent_norm (v n : Vec) (hn : ‖n‖=1) :
    ‖(n-velocity v)-(1-dot n (velocity v)) • n‖≤Real.sqrt (2*(1-dot n (velocity v))) := by
  have he : (n-velocity v)-(1-dot n (velocity v)) • n =
      -(velocityProjection n (velocity v-n)) := by
    simp only [velocityProjection,dot_sub_right,dot_self,hn,one_pow]
    module
  rw [he,norm_neg]
  exact (velocityProjection_norm _ _ hn.le).trans (velocity_normal_distance_bound v n hn)

lemma receiverQ_transport_bound (w v n : Vec) (hn : ‖n‖=1) :
    ‖receiverQ (velocity w) n (n-velocity v)‖ ≤ (1-dot n (velocity v))+
      2*Real.sqrt (2*(1-dot n (velocity w)))*Real.sqrt (2*(1-dot n (velocity v))) := by
  let d := 1-dot n (velocity v)
  let h := (n-velocity v)-d • n
  have hh : dot n h=0 := by
    dsimp only [h,d]
    simp only [dot_sub_right,dot_smul_right,dot_self,hn,one_pow,mul_one]
    ring
  have he : n-velocity v=d • n+h := by dsimp [h]; module
  rw [he,receiverQ_add,receiverQ_smul,receiverQ_normal]
  calc
    _ ≤ ‖d • n‖+‖receiverQ (velocity w) n h‖ := norm_add_le _ _
    _ ≤ d+2*Real.sqrt (2*(1-dot n (velocity w)))*Real.sqrt (2*d) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (cone_denom_pos v n hn),hn,mul_one]
      exact add_le_add le_rfl ((receiverQ_tangent_bound w n h hn hh).trans
        (mul_le_mul_of_nonneg_left (velocity_tangent_norm v n hn) (by positivity)))

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

lemma forceTransportKernel_bound (r : ℝ) (n w v : Vec) (hn : ‖n‖=1) :
    ‖forceTransportKernel r n (velocity w) v‖ ≤
      (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ *
        ((1-dot n (velocity v))+2*Real.sqrt (2*(1-dot n (velocity w)))*
          Real.sqrt (2*(1-dot n (velocity v)))) := by
  unfold forceTransportKernel
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (receiverQ_transport_bound w v n hn) (by positivity)

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

lemma velocity_deficit_mem_unit2 (v w : Vec) :
    1-dot (velocity w) (velocity v)∈Icc (0:ℝ) 2 := by
  have hd := abs_real_inner_le_norm (velocity w) (velocity v)
  rw [←dot_eq_inner] at hd
  have hn : ‖velocity w‖*‖velocity v‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (norm_velocity_lt_one w).le).trans
      (norm_velocity_lt_one v).le
  have ha := (abs_le.mp (hd.trans hn))
  constructor <;> linarith

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedReceiverWeightBoundFinite
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

lemma source_angle_coordinate_lower (v n : Vec) (hn : ‖n‖=1) :
    1/2≤q v*Real.sqrt ((1-dot n (velocity v))/2) := by
  have hq := q_pos v
  have hv := norm_velocity_lt_one v
  have hdot := dot_le_norm n (velocity v)
  rw [hn,one_mul] at hdot
  have hs := velocity_self v
  rw [dot_self] at hs
  have hinv : (q v)^2*((q v)⁻¹)^2=1 := by field_simp
  have hd : ((q v)⁻¹)^2≤2*(1-dot n (velocity v)) := by
    nlinarith [sq_nonneg (1-‖velocity v‖)]
  have hdq := mul_le_mul_of_nonneg_left hd (sq_nonneg (q v))
  rw [hinv] at hdq
  have hroot := Real.sq_sqrt (div_nonneg (cone_denom_pos v n hn).le (by norm_num : (0:ℝ)≤2))
  have hp : 0≤q v*Real.sqrt ((1-dot n (velocity v))/2) := by positivity
  have hsq : 1≤4*(q v*Real.sqrt ((1-dot n (velocity v))/2))^2 := by
    nlinarith [sq_nonneg (q v)]
  nlinarith

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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionWeight
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

namespace RVM

lemma div_stabilityLength (P C₁ M A p w φ t : ℝ) :
    t/stabilityLength P C₁ M A p w φ =
      t*(stabilityRate P C₁ M A p w φ)^2 := by
  simp [stabilityLength, div_eq_mul_inv, inv_pow]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_NormalisedPartialCutoff
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

lemma product_le_min_scale {P p w : ℝ} (hp : 0≤p) (hw : 0≤w)
    (hpP : p≤P) (hwP : w≤P) : w*p≤P*min p w := by
  rcases le_total p w with h|h
  · rw [min_eq_left h]
    exact mul_le_mul_of_nonneg_right hwP hp
  · rw [min_eq_right h]
    calc w*p≤w*P := mul_le_mul_of_nonneg_left hpP hw
         _ = P*w := by ring

lemma sqrt_div_stabilityLength {P C M A p w φ I : ℝ}
    (hP : 0≤P) (hC : 0≤C) (hM : 0≤M) (hp : 0≤p) (hw : 0≤w)
    (hφ : 0≤φ) (hI : 0≤I) :
    Real.sqrt (I/stabilityLength P C M A p w φ)=
      Real.sqrt I*stabilityRate P C M A p w φ := by
  rw [div_stabilityLength,Real.sqrt_mul hI,Real.sqrt_sq]
  unfold stabilityRate
  positivity

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SqrtBaselineClippedLength
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

lemma sqrt_baseline_clipped_length {I lam : ℝ} (hI : 0 < I) (hlam : 0 < lam) :
    Real.sqrt (1+I/min I (lam/2))  ≤  2*(1+Real.sqrt (I/lam)) := by
  have hlen : 0 < min I (lam/2) := lt_min hI (by positivity)
  have hq : 0 ≤ I/lam := by positivity
  have hR : 0 ≤ Real.sqrt (I/lam) := Real.sqrt_nonneg _
  have hRsq := Real.sq_sqrt hq
  have hdiv : I/min I (lam/2)  ≤  1+2*(I/lam) := by
    rcases le_total I (lam/2) with h|h
    · rw [min_eq_left h,div_self hI.ne']
      linarith
    · rw [min_eq_right h]
      have he : I/(lam/2)=2*(I/lam) := by ring
      rw [he]
      linarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith

lemma stabilityLength_pos {P C M A p w φ : ℝ} (hP : 0 < P) (hC : 0 < C)
    (hM : 0 < M) (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) :
    0 < stabilityLength P C M A p w φ := by
  unfold stabilityLength stabilityRate
  have hm : 0 < min p w := lt_min hp hw
  have hr : 0  <  M/φ+Real.sqrt (A*Real.log (2+P)/φ) :=
    add_pos_of_pos_of_nonneg (div_pos hM hφ) (Real.sqrt_nonneg _)
  positivity

lemma stability_massScale_identity (P C M A p w φ : ℝ) :
    (C*(P/(min p w/128))*(M/φ+Real.sqrt (A*Real.log (2+P)/φ)))⁻¹^2 =
      stabilityLength P (128*C) M A p w φ := by
  unfold stabilityLength stabilityRate
  congr 2
  ring

lemma direction_baseline_R_bound128 {P C M A p w φ : ℝ}
    (hP : 0<P) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤128*P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      128*w*(1+C*(M+Real.sqrt (A*Real.log (2+P)))) := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : 0 < min p w := lt_min hp hw
  have hwP' : w≤128*P := hwP.trans (by linarith only [hP])
  have hwp := product_le_min_scale hp.le hw.le hpP hwP'
  have hmain : w^2*p/(P*min p w)≤128*w := by
    apply (div_le_iff₀ (mul_pos hP hm)).mpr
    nlinarith
  have hfirst : w*p*φ/P≤128*w := by
    apply (div_le_iff₀ hP).mpr
    have hh : p*φ≤128*P := (mul_le_of_le_one_right hp.le hφ1).trans hpP
    nlinarith
  have hroot : φ*Real.sqrt (A*Real.log (2+P)/φ)=
      Real.sqrt (A*Real.log (2+P)*φ) := by
    calc
      _ = Real.sqrt (φ^2)*Real.sqrt (A*Real.log (2+P)/φ) := by rw [Real.sqrt_sq hφ.le]
      _ = Real.sqrt (A*Real.log (2+P)*φ) := by
        rw [←Real.sqrt_mul (sq_nonneg φ)]
        congr 1
        field_simp
  have hsqrt : Real.sqrt (A*Real.log (2+P)*φ)≤Real.sqrt (A*Real.log (2+P)) :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right (mul_nonneg hA hL) hφ1)
  rw [Real.sqrt_sq (div_nonneg hw.le hP.le),
    sqrt_div_stabilityLength hP.le hC hM hp.le hw.le hφ.le (sq_nonneg _),
    Real.sqrt_sq (div_nonneg hw.le hP.le)]
  have he : (w/P)*(1+(w/P)*stabilityRate P C M A p w φ)*p*φ=
      w*p*φ/P+C*(w^2*p/(P*min p w))*(M+φ*Real.sqrt (A*Real.log (2+P)/φ)) := by
    unfold stabilityRate
    field_simp
  rw [he,hroot]
  calc
    _ ≤ 128*w+C*(128*w)*(M+Real.sqrt (A*Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma direction_baseline_R_log_bound128 {P C M A p w φ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤128*P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      128*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  apply (direction_baseline_R_bound128 hP hC hM hA hp hw hφ hφ1 hpP hwP).trans
  rw [Real.sqrt_mul hA]
  have hroot : 1≤Real.sqrt (Real.log (2+P)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have h0 : 0≤1+C*M := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg (show 0≤128*w by positivity) h0)]

lemma direction_clipped_baseline_R_log_bound128 {P C M A p w φ : ℝ}
    (hP : 0 < P) (hL : 1 ≤ Real.log (2+P)) (hC : 0 < C) (hM : 0 < M) (hA : 0 ≤ A)
    (hp : 0 < p) (hw : 0 < w) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hpP : p ≤ 128*P) (hwP : w ≤ P) :
    let I := (w/P)^2
    let lam := stabilityLength P C M A p w φ
    Real.sqrt I*Real.sqrt (1+I/min I (lam/2))*p*φ  ≤
      256*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  dsimp only
  have hI : 0 < (w/P)^2 := sq_pos_of_pos (div_pos hw hP)
  have hlam := stabilityLength_pos hP hC hM hp hw hφ (A:=A)
  have hroot := sqrt_baseline_clipped_length hI hlam
  have hbound := direction_baseline_R_log_bound128 hP hL hC.le hM.le hA hp hw hφ hφ1 hpP hwP
  calc
    _  ≤  Real.sqrt ((w/P)^2)*(2*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ)))*p*φ := by gcongr
    _ = 2*(Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ) := by ring
    _  ≤  2*(128*(1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by gcongr
    _ = _ := by ring

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

lemma direct_transport_bin_bound {r p θ φ : ℝ} (n W v : Vec)
    (hr : 0 < r) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) (hn : ‖n‖=1)
    (hq : p≤q v) (hdlo : θ^2/2≤1-dot n (velocity v))
    (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDhi : 1-dot n (velocity W)≤8*φ^2) :
    ‖forceTransportKernel r n (velocity W) v‖≤128*(θ+φ)/(r^2*p^2*θ^3) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hsθ : Real.sqrt (2*d)≤4*θ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hsφ : Real.sqrt (2*D)≤4*φ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hnum : d+2*Real.sqrt (2*D)*Real.sqrt (2*d)≤8*θ^2+32*φ*θ := by
    have hh := mul_le_mul hsφ hsθ (Real.sqrt_nonneg _) (by positivity : 0≤4*φ)
    dsimp only [d] at *
    nlinarith
  have hb := forceTransportKernel_bound r n W v hn
  change _ ≤ (r^2*(q v)^2*d^2)⁻¹*(d+2*Real.sqrt (2*D)*Real.sqrt (2*d)) at hb
  calc
    _ ≤ (r^2*(q v)^2*d^2)⁻¹*(d+2*Real.sqrt (2*D)*Real.sqrt (2*d)) := hb
    _ ≤ (r^2*p^2*(θ^2/2)^2)⁻¹*(8*θ^2+32*φ*θ) := by
      apply mul_le_mul _ hnum (by positivity) (by positivity)
      apply inv_anti₀ (by positivity)
      gcongr
    _ = (32*θ+128*φ)/(r^2*p^2*θ^3) := by field_simp; ring
    _ ≤ 128*(θ+φ)/(r^2*p^2*θ^3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith

lemma physicalDirectTransportDensity_bound {s : Solution} {X V : ℝ→Vec}
    {B : ClosedConeBin} {p θ φ : ℝ} {z : ConeCoordinate}
    (hr : 0<z.1-z.2.1) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ)
    (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin) (hdhi : B.dmax≤8*θ^2)
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalDirectTransportDensity s X V B z≤
      ENNReal.ofReal (128*(θ+φ)/(p^2*θ^3))*physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  unfold physicalDirectTransportDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)*
        ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
      intro v hv
      rw [←ENNReal.ofReal_mul (by positivity : 0≤128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3))]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hf v)]
      calc
        _ ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3)) :=
          mul_le_mul_of_nonneg_left
            (direct_transport_bin_bound _ _ _ hr hp hθ hφ (sphere_norm _)
              (hq.trans hv.1.1) (hdlo.trans hv.2.1.1) (hv.2.1.2.trans hdhi) hDhi) (hf v)
        _ = _ := mul_comm _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      field_simp

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

lemma cappedRepresentative_le_one (n : ℕ) : cappedRepresentative n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ClosedEulerianTimeBudget
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

lemma cone_relative_deficit_triangle (v w n : Vec) (hn : ‖n‖=1) :
    1-dot (velocity w) (velocity v)≤2*((1-dot n (velocity v))+(1-dot n (velocity w))) ∧
    1-dot n (velocity v)≤2*((1-dot (velocity w) (velocity v))+(1-dot n (velocity w))) ∧
    1-dot n (velocity w)≤2*((1-dot (velocity w) (velocity v))+(1-dot n (velocity v))) := by
  have hi := relative_angle_identity v w
  have hv := cone_angle_identity v n hn
  have hw := cone_angle_identity w n hn
  have hab : ‖velocity v-velocity w‖≤‖n-velocity v‖+‖n-velocity w‖ := by
    calc
      _ = ‖-(n-velocity v)+(n-velocity w)‖ := by congr 1; abel
      _ ≤ ‖-(n-velocity v)‖+‖n-velocity w‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hna : ‖n-velocity v‖≤‖velocity v-velocity w‖+‖n-velocity w‖ := by
    calc
      _ = ‖-(velocity v-velocity w)+(n-velocity w)‖ := by congr 1; abel
      _ ≤ ‖-(velocity v-velocity w)‖+‖n-velocity w‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hnb : ‖n-velocity w‖≤‖velocity v-velocity w‖+‖n-velocity v‖ := by
    calc
      _ = ‖(velocity v-velocity w)+(n-velocity v)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hsq {a b c : ℝ} (ha : 0≤a) (h : a≤b+c) : a^2≤2*(b^2+c^2) := by
    have hbc : 0≤b+c := ha.trans h
    have hh := mul_self_le_mul_self ha h
    nlinarith [sq_nonneg (b-c)]
  have hab2 := hsq (norm_nonneg _) hab
  have hna2 := hsq (norm_nonneg _) hna
  have hnb2 := hsq (norm_nonneg _) hnb
  refine ⟨?_,?_,?_⟩ <;>
    nlinarith [sq_nonneg ((q v)⁻¹),sq_nonneg ((q w)⁻¹)]

lemma cone_relative_bin_triangle {v w n : Vec} {θ φ σ : ℝ} (hn : ‖n‖=1)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDlo : φ^2/2≤1-dot n (velocity w)) (hDhi : 1-dot n (velocity w)≤8*φ^2)
    (helo : σ^2/2≤1-dot (velocity w) (velocity v))
    (hehi : 1-dot (velocity w) (velocity v)≤8*σ^2) :
    σ^2≤32*(θ^2+φ^2) ∧ θ^2≤32*(σ^2+φ^2) ∧ φ^2≤32*(σ^2+θ^2) := by
  obtain ⟨he,hd,hD⟩ := cone_relative_deficit_triangle v w n hn
  constructor
  · linarith
  constructor <;> linarith

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ProjectedSourceStableFarBound
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

lemma Admissible.central_density_stable_radial_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (np nθ nφ : ℕ)
        (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 0 < P → 1 ≤ Real.log (2+P) → 0 < w → w ≤ P →
      sourceRepresentative np ≤ 128*P →
      cappedRepresentative nθ ≤ cappedRepresentative nφ/16 →
      32 ≤ cappedRepresentative nφ*w →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>representativeClosedBin T w ![np,nθ,nφ,nr]
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,ENNReal.ofReal (78400000*(cappedRepresentative nφ)^2/cappedRepresentative nθ)*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (B nr) z.1 z.2.1 z.2.2
          ∂physicalBinMeasure V (B nr) (Icc a b))) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*
        Real.sqrt (Real.log (2+P))*cappedRepresentative nφ) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.central_density_baseline_radial_sum
  refine ⟨1536*C,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP
    hpP hsmall hwφ HX HZ
  dsimp only
  let p := sourceRepresentative np
  let φ := cappedRepresentative nφ
  let L := Real.log (2+P)
  let I := (w/P)^2
  let lam := stabilityLength P 16384 M A p w φ
  let len := min I (lam/2)
  let m := min p w/128
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0 < p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0 < φ := cappedRepresentative_pos _
  have hI : 0 < I := sq_pos_of_pos (div_pos hw hP)
  have hlam : 0 < lam := stabilityLength_pos hP (by norm_num) hM hp hw hφ
  have hlen : 0 < len := lt_min hI (by positivity)
  have hlenI : len ≤ I := min_le_left _ _
  have hlenlam : 2*len ≤ lam := by
    have hh : len ≤ lam/2 := min_le_right _ _
    linarith
  have hm : 0 < m := div_pos (lt_min hp hw) (by norm_num)
  have hmq : m ≤ p/128 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hmw : m ≤ w/8 := by
    have hh : min p w ≤ w := min_le_right _ _
    dsimp [m]
    linarith
  have hstable : 2*len ≤ (128*(P/m)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2 := by
    dsimp only [m,L]
    rw [stability_massScale_identity]
    convert hlenlam using 1; norm_num [lam]
  have hbnd := hbound s T F hs hT h0 zX S np nθ nφ a b I len w M A P L m 128
    hS hS0 ha hb hlen hlenI hab hM hA hP (by dsimp [L]; linarith) hm hw (by norm_num)
    hmq hmw hsmall hwφ hstable HX HZ
  have hR := direction_clipped_baseline_R_log_bound128 hP hL (show (0:ℝ) < 16384 by norm_num)
    hM hA hp hw hφ (cappedRepresentative_le_one _) hpP hwP
  have hR' : Real.sqrt I*Real.sqrt (1+I/len)*p*φ ≤
      256*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L := hR
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hgeom : 6*Real.sqrt I*Real.sqrt (1+I/len)*p*φ^2 ≤
      1536*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L*φ := by
    calc
      _ = 6*(Real.sqrt I*Real.sqrt (1+I/len)*p*φ)*φ := by ring
      _ ≤ 6*(256*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L)*φ := by gcongr
      _ = _ := by ring
  apply hbnd.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C*(1+E)*(1536*(1+16384*(M+Real.sqrt A))*w*Real.sqrt L*φ) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by dsimp [E,L,φ]; ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_GeneralDirectRadial
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

lemma relativeRepresentative_source_angle {T w : ℝ} {k : Fin 4→ℕ} {j : ℕ}
    {v n a : Vec} (hn : ‖n‖=1)
    (hv : v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n a) :
    1 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1) := by
  have he := source_angle_coordinate_lower v n hn
  have hθ := cappedRepresentative_pos (k 1)
  have hq := q_pos v
  have hhi : 1-dot n (velocity v)≤8*(cappedRepresentative (k 1))^2 := hv.2.1.2
  have hroot : Real.sqrt ((1-dot n (velocity v))/2)≤2*cappedRepresentative (k 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    linarith only [hhi]
  have hqθ : 1/2≤2*q v*cappedRepresentative (k 1) :=
    he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hroot hq.le])
  have hp : q v ≤ sourceRepresentative (k 0)/32 := hv.1.2
  nlinarith only [mul_le_mul_of_nonneg_right hp hθ.le,hqθ]

lemma cone_relative_bin_small {v w n : Vec} {θ φ σ : ℝ}
    (hn : ‖n‖=1) (hθ : 0≤θ) (hφ : 0≤φ) (hσ : 0≤σ) (hsep : 16*θ≤φ)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDlo : φ^2/2≤1-dot n (velocity w)) (hDhi : 1-dot n (velocity w)≤8*φ^2)
    (helo : σ^2/2≤1-dot (velocity w) (velocity v))
    (hehi : 1-dot (velocity w) (velocity v)≤8*σ^2) : φ/8≤σ ∧ σ≤8*φ := by
  obtain ⟨he,_,hD⟩ := cone_relative_bin_triangle hn hdlo hdhi hDlo hDhi helo hehi
  have hsq := mul_self_le_mul_self (show 0≤16*θ by positivity) hsep
  constructor <;> nlinarith

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relativeRepresentative_nonempty_geometry {T w : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} {k : Fin 4→ℕ} {j : ℕ} {z : ConeCoordinate} {v : Vec}
    (hz : z∈physicalBinBase V (relativeRepresentativeClosedBin T w k j) J)
    (hv : v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))) :
    1≤ sourceRepresentative (k 0)*cappedRepresentative (k 1) ∧
      (16*cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) →
        cappedRepresentative (k 2)≤8*cappedRepresentative j) := by
  refine ⟨relativeRepresentative_source_angle (sphere_norm z.2.2) hv,?_⟩
  intro hsep
  have h := cone_relative_bin_small (sphere_norm z.2.2)
    (cappedRepresentative_pos (k 1)).le (cappedRepresentative_pos (k 2)).le
    (cappedRepresentative_pos j).le hsep hv.2.1.1 hv.2.1.2
    hz.2.2.2.2.1 hz.2.2.2.2.2 hv.2.2.1 hv.2.2.2
  linarith only [h.1]

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

lemma physicalDirectTransport_integral_geometry_zero (s : Solution) {T w : ℝ}
    {X V : ℝ→Vec} (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    {k : Fin 4→ℕ} {j : ℕ}
    (hbad : ¬1≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)) :
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (relativeRepresentativeClosedBin T w k j) z
      ∂physicalBinMeasure V (relativeRepresentativeClosedBin T w k j) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  have hempty : coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hbad (relativeRepresentative_nonempty_geometry hz hv).1
  simp only [physicalDirectTransportDensity,hempty,Measure.restrict_empty,lintegral_zero_measure,mul_zero,Pi.zero_apply]

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedDirection
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

lemma relativeRepresentative_momentum_subset (T w : ℝ) (k : Fin 4→ℕ) (j : ℕ)
    (n W : Vec) : coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n (velocity W) ⊆
      coneBinMomentumSet (representativeClosedBin T w k) n (velocity W) := by
  intro v hv
  exact ⟨hv.1,hv.2.1,velocity_deficit_mem_unit2 v W⟩

lemma relativeRepresentative_density_le (s : Solution) (X V : ℝ→Vec) (T w : ℝ)
    (k : Fin 4→ℕ) (j : ℕ) (z : ConeCoordinate) :
    physicalBinDensity s X V (relativeRepresentativeClosedBin T w k j) z.1 z.2.1 z.2.2 ≤
      physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2 := by
  exact lintegral_mono' (Measure.restrict_mono
    (relativeRepresentative_momentum_subset T w k j z.2.2.1 (V z.1)) le_rfl) (fun _ => le_rfl)

lemma transport_small_central_coefficient {p θ φ : ℝ} (hp : 0<p) (hθ : 0<θ)
    (hφ : 0<φ) (hsmall : θ ≤ φ/16) (hpθ : 1 ≤ p*θ) :
    128*(θ+φ)/((p/128)^2*θ^3) ≤ φ⁻¹*(78400000*φ^2/θ) := by
  have hsq : 1 ≤ (p*θ)^2 := one_le_pow₀ hpθ
  apply (div_le_iff₀ (by positivity : 0<(p/128)^2*θ^3)).mpr
  have he : φ⁻¹*(78400000*φ^2/θ)*((p/128)^2*θ^3)=
      (78400000/16384:ℝ)*φ*(p*θ)^2 := by field_simp; ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hsq hφ.le
  nlinarith only [hsmall,hh,hφ]

lemma PhaseFlowOn.direct_transport_small_central {s : Solution} {T a b w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (k : Fin 4→ℕ) (j : ℕ) (ha : 0 ≤ a) (hb : b ≤ T)
    (hsmall : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16)
    (hpθ : 1  ≤  sourceRepresentative (k 0)*cappedRepresentative (k 1)) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    let B := relativeRepresentativeClosedBin T w k j
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z
      ∂physicalBinMeasure V B (Icc a b)) ≤
      ENNReal.ofReal (cappedRepresentative (k 2))⁻¹ *
        (ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
          (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
            z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))) := by
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := relativeRepresentativeClosedBin T w k j
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hα := (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk (continuous_const (y:=zX)))
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hm : physicalBinMeasure V B (Icc a b)=physicalBinMeasure V (representativeClosedBin T w k) (Icc a b) := rfl
  rw [←mul_assoc,←ENNReal.ofReal_mul (inv_nonneg.mpr hφ.le),
    ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←hm]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable B measurableSet_Icc)] with z hz
  have hrad : 0<z.1-z.2.1 := (representativeClosedBin_radius_pos T w k).trans_le hz.2.2.1.1
  have hn := physicalDirectTransportDensity_bound (s:=s) (X:=X) (V:=V) (B:=B) hrad
    (by positivity : 0<p/128) hθ hφ.le le_rfl le_rfl le_rfl hz.2.2.2.2.2
    (fun v=>hs.nonnegative _ ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩ _)
  apply hn.trans
  exact mul_le_mul'
    (ENNReal.ofReal_le_ofReal (transport_small_central_coefficient hp hθ hφ hsmall hpθ))
    (relativeRepresentative_density_le s X V T w k j z)

lemma Admissible.direct_transport_small_stable_radii {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 0<M → 0 ≤ A → 0<P → 1 ≤  Real.log (2+P) →
      0<w → w ≤ P → sourceRepresentative np ≤ 128*P →
      cappedRepresentative nθ ≤ cappedRepresentative nφ/16 → 32 ≤ cappedRepresentative nφ*w →
      1  ≤  sourceRepresentative np*cappedRepresentative nθ →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P))) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.central_density_stable_radial_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hpP hsmall hwφ hpθ HX HZ
  dsimp only
  have hφ : 0 < cappedRepresentative nφ := cappedRepresentative_pos _
  have h := hbound s T F hs hT h0 zX S np nθ nφ a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hpP hsmall hwφ HX HZ
  have hh (nr : ℕ) := F.direct_transport_small_central (w:=w) hs hT zX ![np,nθ,nφ,nr] j ha hb
    (by simpa using hsmall) (by simpa using hpθ)
  have hsum := ENNReal.tsum_le_tsum hh
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val] at hsum
  rw [ENNReal.tsum_mul_left] at hsum
  apply hsum.trans ((mul_le_mul' le_rfl h).trans ?_)
  rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hφ.le)]
  apply ENNReal.ofReal_le_ofReal
  have he : 0 ≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  field_simp
  exact le_rfl

lemma Admissible.direct_transport_sharp_all_radii_oai {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → b-a ≤ (w/P)^2 → 0<M → 0 ≤ A → 0<P → 1 ≤ Real.log (2+P) →
      0<w → w ≤ P → sourceRepresentative np ≤ 128*P →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*max 1 T*w*Real.sqrt (Real.log (2+P))) := by
  obtain ⟨C₁,hC₁,h₁⟩ := hd₀.direct_transport_remaining_all_radii
  obtain ⟨C₂,hC₂,h₂⟩ := hd₀.direct_transport_low_receiver_radii
  obtain ⟨C₃,hC₃,h₃⟩ := hd₀.direct_transport_small_stable_radii
  refine ⟨C₁+C₂+C₃,by positivity,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hpP HX HZ
  dsimp only
  have he : 0 ≤ ∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hMa : 1 ≤ 1+16384*(M+Real.sqrt A) := by linarith only [hM,Real.sqrt_nonneg A]
  have he1 : 1 ≤ 1+∫x : Vec,totalEnergy s (0,x) := by linarith only [he]
  have hL1 : 1 ≤ Real.sqrt (Real.log (2+P)) := Real.one_le_sqrt.mpr hL
  have hH : 1 ≤ max 1 T := le_max_left _ _
  have hI : 0<(w/P)^2 := sq_pos_of_pos (div_pos hw hP)
  have absorb (C : ℝ) (hC : 0 ≤ C) (hCc : C ≤ C₁+C₂+C₃) :
      C*max 1 T*w ≤ (C₁+C₂+C₃)*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*max 1 T*w*Real.sqrt (Real.log (2+P)) := by
    calc
      _ = C*1*1*max 1 T*w*1 := by ring
      _ ≤ _ := by gcongr
  by_cases hpθ : 1 ≤ sourceRepresentative np*cappedRepresentative nθ
  · by_cases hsmall : cappedRepresentative nθ ≤ cappedRepresentative nφ/16
    · by_cases hstable : 32 ≤ cappedRepresentative nφ*w
      · apply (h₃ s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hpP hsmall hstable hpθ HX HZ).trans
        apply ENNReal.ofReal_le_ofReal
        calc
          _ = C₃*(1+∫x : Vec,totalEnergy s (0,x))*(1+16384*(M+Real.sqrt A))*1*w*Real.sqrt (Real.log (2+P)) := by ring
          _ ≤ _ := by gcongr; linarith only [hC₁,hC₂]
      · apply (h₂ s T F hs hT h0 zX S np nθ nφ j a b ((w/P)^2) w P hS hS0 ha hb hab hI hw hP hwP le_rfl hpP hpθ (lt_of_not_ge hstable).le).trans
        exact ENNReal.ofReal_le_ofReal (absorb C₂ hC₂ (by linarith only [hC₁,hC₃]))
    · apply (h₁ s T F hs hT h0 zX S np nθ nφ j a b ((w/P)^2) w P hS hS0 ha hb hab hI hw hP hwP le_rfl hpP (by linarith only [hsmall])).trans
      exact ENNReal.ofReal_le_ofReal (absorb C₁ hC₁ (by linarith only [hC₂,hC₃]))
  · have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
      ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
    have hz (nr : ℕ) : (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s
        (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
        (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
          (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) (Icc a b))=0 := by
      exact physicalDirectTransport_integral_geometry_zero s hV measurableSet_Icc hpθ
    simp_rw [hz,tsum_zero]
    exact bot_le

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direct_transport_sharp_all_radii_oai := @OAI.RVM.Admissible.direct_transport_sharp_all_radii_oai
