-- Prove2me | solution 1 for OAI.RVM.Admissible.unselected_small_source_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:33:26.011279+00:00
-- url     : https://prove2.me/submissions/0e89f554-6ecb-4305-8842-1686fd429d88

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_magnetic_small_uniform
import Theorems.Thm_OAI_RVM_Admissible_representative_pure_occupation
import Theorems.Thm_OAI_RVM_Admissible_uniform_actual_bin_Cauchy
import Theorems.Thm_OAI_RVM_EnergyPrefix_goodFieldBudget_uniform

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

lemma dot_cross_self_left (a b : Vec) : dot a (cross a b) = 0 := by
  simp [dot, cross, Fin.sum_univ_succ]
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

lemma velocityProjection_dot_symm (u b n : Vec) :
    dot n (velocityProjection u b) = dot (velocityProjection u n) b := by
  simp only [velocityProjection,dot_sub_right,dot_sub_left,dot_smul_left,dot_smul_right]
  rw [dot_comm n u]
  ring

lemma norm_velocityProjection_normal (u n : Vec) (hu : ‖u‖ ≤ 1) (hn : ‖n‖=1) :
    ‖velocityProjection u n‖ ≤ Real.sqrt (2*(1-dot n u)) := by
  have hs : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hdot := dot_le_norm n u
  rw [hn,one_mul] at hdot
  have hd : 0 ≤ 2*(1-dot n u) := by linarith
  have he : ‖velocityProjection u n‖^2 =
      1-2*(dot n u)^2+(dot n u)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm u n,hn]
    ring
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg (dot n u))
  have hsq := Real.sq_sqrt hd
  nlinarith [Real.sqrt_nonneg (2*(1-dot n u)),sq_nonneg (1-dot n u)]

lemma cross_sub_left (a b c : Vec) : cross (a-b) c = cross a c-cross b c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_normal_decomposition (u n B : Vec) :
    dot n n • cross u B = dot n u • cross n B +
      dot n (cross u B) • n + dot n B • cross u n := by
  ext i
  fin_cases i <;> simp [cross,dot,Fin.sum_univ_succ] <;> ring

lemma magnetic_projection_identity (u n B : Vec) (hn : ‖n‖=1) :
    velocityProjection u (cross (u-n) B) =
      -(1-dot n u) • cross n B - dot n (cross (u-n) B) • (u-n) +
        dot n B • cross u n := by
  have hn' : dot n n=1 := by rw [dot_self,hn]; norm_num
  have hd := cross_normal_decomposition u n B
  rw [hn',one_smul] at hd
  have hc : dot u (cross (u-n) B) = dot n (cross (u-n) B) := by
    have hh := dot_cross_self_left (u-n) B
    rw [dot_sub_left] at hh
    linarith
  unfold velocityProjection
  rw [hc,cross_sub_left]
  have he : dot n (cross u B-cross n B) = dot n (cross u B) := by
    rw [dot_sub_right,dot_cross_self_left,sub_zero]
  rw [he]
  ext i
  have hi := congrArg (fun w : Vec => w i) hd
  simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hi ⊢
  linear_combination hi

lemma magnetic_projection_normal_identity (u n B : Vec) :
    dot n (velocityProjection u (cross (u-n) B)) =
      (1-dot n u)*dot n (cross (u-n) B) := by
  have hc : dot u (cross (u-n) B) = dot n (cross (u-n) B) := by
    have hh := dot_cross_self_left (u-n) B
    rw [dot_sub_left] at hh
    linarith
  simp only [velocityProjection,dot_sub_right,dot_smul_right,hc]
  ring

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

lemma magnetic_projection_bound (v n B : Vec) (hn : ‖n‖=1) :
    ‖velocityProjection (velocity v) (cross (velocity v-n) B)‖ ≤
      3*(1-dot n (velocity v))*‖B‖+|dot n B| := by
  let u := velocity v
  let d := 1-dot n u
  let θ := Real.sqrt (2*d)
  have hd : 0 ≤ d := (cone_denom_pos v n hn).le
  have ht : 0 ≤ θ := Real.sqrt_nonneg _
  have ht2 : θ^2=2*d := Real.sq_sqrt (by positivity)
  have hk : ‖u-n‖ ≤ θ := velocity_normal_distance_bound v n hn
  have hb : ‖cross n B‖ ≤ ‖B‖ := by simpa only [hn,one_mul] using norm_cross_le n B
  have hcn : ‖cross u n‖ ≤ 1 := by
    have hh := norm_cross_le u n
    rw [hn,mul_one] at hh
    exact hh.trans (norm_velocity_lt_one v).le
  have hc : |dot n (cross (u-n) B)| ≤ θ*‖B‖ := by
    have hh := abs_dot_le n (cross (u-n) B)
    rw [hn,one_mul] at hh
    exact hh.trans ((norm_cross_le (u-n) B).trans
      (mul_le_mul_of_nonneg_right hk (norm_nonneg B)))
  have hmul := mul_le_mul hc hk (norm_nonneg _) (mul_nonneg ht (norm_nonneg B))
  have hmul' : |dot n (cross (u-n) B)| *‖u-n‖ ≤ 2*d*‖B‖ := by
    calc
      _ ≤ θ*‖B‖*θ := hmul
      _ = θ^2*‖B‖ := by ring
      _ = 2*d*‖B‖ := by rw [ht2]
  have htri := norm_add_le (-(1-dot n u) • cross n B -
      dot n (cross (u-n) B) • (u-n)) (dot n B • cross u n)
  rw [magnetic_projection_identity _ _ _ hn]
  have hsub := norm_sub_le (-(1-dot n u) • cross n B)
    (dot n (cross (u-n) B) • (u-n))
  simp only [norm_smul,Real.norm_eq_abs,abs_neg] at htri hsub
  rw [abs_of_nonneg hd] at hsub
  have hh₁ := mul_le_mul_of_nonneg_left hb hd
  have hh₂ := mul_le_mul_of_nonneg_left hcn (abs_nonneg (dot n B))
  dsimp only [u,d] at *
  linarith

lemma lorentz_source_acceleration_bound (v E B n : Vec) (hn : ‖n‖=1) :
    ‖fderiv ℝ velocity v (E+cross (velocity v) B)‖ ≤
      (q v)⁻¹*(goodField E B n+3*(1-dot n (velocity v))*‖B‖) := by
  rw [fderiv_velocity_apply,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (q_pos v))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (q_pos v).le)
  have he : E+cross (velocity v) B =
      (E+cross n B)+cross (velocity v-n) B := by
    rw [cross_sub_left]
    module
  change ‖velocityProjection (velocity v) (E+cross (velocity v) B)‖ ≤ _
  rw [he,velocityProjection_add]
  have ht := norm_add_le (velocityProjection (velocity v) (E+cross n B))
      (velocityProjection (velocity v) (cross (velocity v-n) B))
  have hg := velocityProjection_norm (velocity v) (E+cross n B) (norm_velocity_lt_one v).le
  have hb := magnetic_projection_bound v n B hn
  dsimp only [goodField]
  linarith

lemma lorentz_source_normal_acceleration_bound (v E B n : Vec) (hn : ‖n‖=1) :
    |dot n (fderiv ℝ velocity v (E+cross (velocity v) B))| ≤
      (q v)⁻¹*Real.sqrt (2*(1-dot n (velocity v)))*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  let u := velocity v
  let d := 1-dot n u
  let θ := Real.sqrt (2*d)
  have hd : 0 ≤ d := (cone_denom_pos v n hn).le
  have ht : 0 ≤ θ := Real.sqrt_nonneg _
  have he : E+cross u B = (E+cross n B)+cross (u-n) B := by
    rw [cross_sub_left]
    module
  have hg : |dot n (velocityProjection u (E+cross n B))| ≤ θ*‖E+cross n B‖ := by
    rw [velocityProjection_dot_symm]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_velocityProjection_normal u n (norm_velocity_lt_one v).le hn) (norm_nonneg _))
  have hb : |dot n (velocityProjection u (cross (u-n) B))| ≤ d*θ*‖B‖ := by
    rw [magnetic_projection_normal_identity,abs_mul,abs_of_nonneg hd]
    have hc : |dot n (cross (u-n) B)| ≤ θ*‖B‖ := by
      have hh := abs_dot_le n (cross (u-n) B)
      rw [hn,one_mul] at hh
      exact hh.trans ((norm_cross_le _ _).trans (mul_le_mul_of_nonneg_right
        (velocity_normal_distance_bound v n hn) (norm_nonneg _)))
    nlinarith [mul_le_mul_of_nonneg_left hc hd]
  have hsum : |dot n (velocityProjection u (E+cross u B))| ≤
      θ*(goodField E B n+d*‖B‖) := by
    rw [he,velocityProjection_add,dot_add_right]
    have hh := abs_add_le (dot n (velocityProjection u (E+cross n B)))
      (dot n (velocityProjection u (cross (u-n) B)))
    dsimp only [goodField]
    nlinarith [mul_nonneg ht (abs_nonneg (dot n B))]
  rw [fderiv_velocity_apply,dot_smul_right,abs_mul,
    abs_of_pos (inv_pos.mpr (q_pos v))]
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (q_pos v).le)
  convert! h using 1; ring

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

lemma dyadicWindow_one_sqrt {D : ℝ} (j : ℕ)
    (hlo : ((2:ℝ)^j)⁻¹^2/2≤D) (hhi : D≤8*((2:ℝ)^j)⁻¹^2) :
    DyadicWindow 1 j (Real.sqrt (D/2)) := by
  have hp : 0<(2:ℝ)^j := by positivity
  have hi : 0<((2:ℝ)^j)⁻¹ := inv_pos.mpr hp
  have hD0 : 0≤D := (by positivity : 0≤((2:ℝ)^j)⁻¹^2/2).trans hlo
  have hD : 0≤D/2 := by positivity
  have hsq := Real.sq_sqrt hD
  have hlo' : ((2:ℝ)^j)⁻¹/2≤Real.sqrt (D/2) := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  have hhi' : Real.sqrt (D/2)≤2*((2:ℝ)^j)⁻¹ := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo' hp.le
    simpa only [pow_one,← mul_div_assoc,mul_inv_cancel₀ hp.ne'] using hh
  · have hh := mul_le_mul_of_nonneg_left hhi' hp.le
    simpa only [pow_one,mul_left_comm,mul_inv_cancel₀ hp.ne',mul_one] using hh

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

lemma measurable_coneBinDensity {g : Particle} (hg : Measurable g)
    {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin) :
    Measurable (fun z : ConeCoordinate => ∫⁻ v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal (g (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))) := by
  let H : Set (ConeCoordinate × Vec) :=
    {p | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))}
  have hn : Measurable (fun p : ConeCoordinate × Vec => p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate × Vec => velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate × Vec => velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp (measurable_fst.comp measurable_fst))
  have hH : MeasurableSet H := by
    exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
      ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
        (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))
  have hf : Measurable (fun p : ConeCoordinate × Vec =>
      ENNReal.ofReal (g (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) := by
    exact (hg.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (((hX.comp (measurable_fst.comp measurable_fst)).sub
        (((measurable_fst.comp measurable_fst).sub (measurable_fst.comp (measurable_snd.comp measurable_fst))).smul hn)).prodMk
        measurable_snd))).ennreal_ofReal
  have hm : Measurable (fun z : ConeCoordinate =>
      ∫⁻ v : Vec, H.indicator (fun p => ENNReal.ofReal (g (p.1.2.1,
        (X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) (z,v)) :=
    (hf.indicator hH).lintegral_prod_right'
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  rw [← lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
  apply lintegral_congr
  intro v
  rfl

lemma physicalBinDensity_aemeasurable {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    (hT : 0 ≤ T) {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (fun z : ConeCoordinate => physicalBinDensity s X V B z.1 z.2.1 z.2.2)
      (physicalBinMeasure V B J) := by
  have hm := (measurable_coneBinDensity (hs.continuous_prefixParticle hT).measurable hX hV B).aemeasurable
    (μ := physicalBinMeasure V B J)
  apply hm.congr
  apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B hJ)
  intro z hz
  unfold physicalBinDensity
  apply lintegral_congr
  intro v
  rw [prefixParticle,prefixClamp_eq (show z.2.1∈Icc 0 T from ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩)]

lemma EnergyPrefix.measurable_prefixConeGood {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) {X : ℝ → Vec} (hX : Measurable X) :
    Measurable (prefixConeGood s T X) := by
  have hn : Measurable (fun z : ConeCoordinate => z.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hy : Measurable (fun z : ConeCoordinate =>
      (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) :=
    (measurable_fst.comp measurable_snd).prodMk
      ((hX.comp measurable_fst).sub ((measurable_fst.sub (measurable_fst.comp measurable_snd)).smul hn))
  have hE := (continuous_prefixField hs.E_smooth.continuousOn hT).measurable.comp hy
  have hB := (continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp hy
  exact (hE.add ((contDiff_cross (k:=0)).continuous.measurable.comp (hn.prodMk hB))).norm.add
    (continuous_dot.measurable.comp (hn.prodMk hB)).abs

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

lemma sourceNumerator_tangent (n u b : Vec) (hn : ‖n‖=1) :
    dot n (sourceNumerator n u b)=0 := by
  simp only [sourceNumerator,dot_sub_right,dot_smul_right,dot_self,hn,one_pow]
  ring

lemma sourceNumerator_bound (v E B n : Vec) (hn : ‖n‖=1) :
    ‖sourceNumerator n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B))‖ ≤
      5*(1-dot n (velocity v))*(q v)⁻¹*(goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  let d := 1-dot n (velocity v)
  let b := fderiv ℝ velocity v (E+cross (velocity v) B)
  have hd : 0≤d := (cone_denom_pos v n hn).le
  have hq : 0≤(q v)⁻¹ := (inv_pos.mpr (q_pos v)).le
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb := lorentz_source_acceleration_bound v E B n hn
  have hnb := lorentz_source_normal_acceleration_bound v E B n hn
  have hnu : ‖n-velocity v‖≤Real.sqrt (2*d) := by
    rw [norm_sub_rev]
    exact velocity_normal_distance_bound v n hn
  have hprod : |dot n b| *‖n-velocity v‖ ≤
      (q v)⁻¹*(2*d)*(goodField E B n+d*‖B‖) := by
    calc
      _ ≤ ((q v)⁻¹*Real.sqrt (2*d)*(goodField E B n+d*‖B‖))*Real.sqrt (2*d) :=
        mul_le_mul hnb hnu (norm_nonneg _) (by positivity)
      _ = (q v)⁻¹*(Real.sqrt (2*d))^2*(goodField E B n+d*‖B‖) := by ring
      _ = _ := by rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hd)]
  have hdb := mul_le_mul_of_nonneg_left hb hd
  calc
    _ ≤ |dot n b| *‖n-velocity v‖+d*‖b‖ := by
      exact (norm_sub_le _ _).trans (by rw [norm_smul,norm_smul,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg hd])
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hd hq) hG]

lemma receiverQ_source_bound (w v E B n : Vec) (hn : ‖n‖=1) :
    ‖receiverQ (velocity w) n
        (sourceNumerator n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B)))‖ ≤
      10*Real.sqrt (2*(1-dot n (velocity w)))*(1-dot n (velocity v))*(q v)⁻¹*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  exact (receiverQ_tangent_bound _ _ _ hn (sourceNumerator_tangent _ _ _ hn)).trans
    (by convert mul_le_mul_of_nonneg_left (sourceNumerator_bound v E B n hn)
          (show 0≤2*Real.sqrt (2*(1-dot n (velocity w))) by positivity) using 1; ring)

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

lemma forceSourceKernel_bound (r : ℝ) (n w v E B : Vec) (hr : 0 < r) (hn : ‖n‖=1) :
    ‖forceSourceKernel r n (velocity w) v (fderiv ℝ velocity v (E+cross (velocity v) B))‖ ≤
      (10*Real.sqrt (2*(1-dot n (velocity w))))/(r*q v*(1-dot n (velocity v)))*
        (goodField E B n+(1-dot n (velocity v))*‖B‖) := by
  have hd := cone_denom_pos v n hn
  have hq := q_pos v
  unfold forceSourceKernel
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (receiverQ_source_bound w v E B n hn) (by positivity)).trans_eq
  field_simp

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

lemma finset_subset_dyadicBox {ι : Type*} [Fintype ι] (S : Finset (ι→ℕ)) :
    ∃M : ℕ,S⊆dyadicBox ι M := by
  classical
  obtain ⟨M,hM⟩ := (S.biUnion (fun k=>Finset.univ.image k)).exists_nat_subset_range
  refine ⟨M,?_⟩
  intro k hk
  simp only [dyadicBox,Fintype.mem_piFinset]
  intro i
  apply hM
  exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

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

lemma pureOccupationEnvelope_nonneg
    {P C₀ C₁ M A p w φ h I : ℝ} (hp : 0 ≤ p) (hφ : 0 ≤ φ)
    (hh : 0 ≤ h) (hI : 0 ≤ I) :
    0 ≤ pureOccupationEnvelope P C₀ C₁ M A p w φ h I := by
  classical
  unfold pureOccupationEnvelope
  dsimp only
  split_ifs <;> positivity

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

lemma direct_source_bin_bound {r p θ φ : ℝ} (n W v E B : Vec)
    (hr : 0 < r) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) (hn : ‖n‖=1)
    (hq : p≤q v) (hdlo : θ^2/2≤1-dot n (velocity v))
    (hDhi : 1-dot n (velocity W)≤8*φ^2) :
    ‖forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤
      (80*φ/(r*p))*(goodField E B n/θ^2+‖B‖) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsφ : Real.sqrt (2*D)≤4*φ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hc : 10*Real.sqrt (2*D)/(r*q v)≤40*φ/(r*p) := by
    calc
      _ ≤ 10*(4*φ)/(r*p) := by gcongr
      _ = _ := by ring
  have hg : goodField E B n/d≤2*(goodField E B n/θ^2) := by
    calc
      goodField E B n/d≤goodField E B n/(θ^2/2) := by gcongr
      _ = _ := by ring
  have hb := forceSourceKernel_bound r n W v E B hr hn
  change _ ≤ (10*Real.sqrt (2*D))/(r*q v*d)*(goodField E B n+d*‖B‖) at hb
  calc
    _ ≤ (10*Real.sqrt (2*D))/(r*q v*d)*(goodField E B n+d*‖B‖) := hb
    _ = (10*Real.sqrt (2*D)/(r*q v))*(goodField E B n/d+‖B‖) := by field_simp
    _ ≤ (40*φ/(r*p))*(2*(goodField E B n/θ^2+‖B‖)) := by
      apply mul_le_mul hc _ (by positivity) (by positivity)
      linarith [norm_nonneg B]
    _ = _ := by ring

lemma physicalDirectSourceDensity_bound {s : Solution} {X V : ℝ→Vec}
    {C : ClosedConeBin} {p θ φ : ℝ} {z : ConeCoordinate}
    (hr : 0<z.1-z.2.1) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ)
    (hq : p≤C.qmin) (hd : θ^2/2≤C.dmin)
    (hD : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalDirectSourceDensity s X V C z ≤
      ENNReal.ofReal ((80*φ/p)*(z.1-z.2.1)*
        (goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
          (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1/θ^2+
          ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖))*
        physicalBinDensity s X V C z.1 z.2.1 z.2.2 := by
  let G := goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
    (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1
  let b := ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖
  have hG : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb : 0≤b := norm_nonneg _
  unfold physicalDirectSourceDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2) *
        ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal ((80*φ/((z.1-z.2.1)*p))*(G/θ^2+b))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
      intro v hv
      rw [←ENNReal.ofReal_mul (by positivity : 0≤(80*φ/((z.1-z.2.1)*p))*(G/θ^2+b))]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_smul,Real.norm_of_nonneg (hf v)]
      calc
        _ ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            ((80*φ/((z.1-z.2.1)*p))*(G/θ^2+b)) :=
          mul_le_mul_of_nonneg_left
            (direct_source_bin_bound _ _ _ _ _ hr hp hθ hφ (sphere_norm _)
              (hq.trans hv.1.1) (hd.trans hv.2.1.1) hD) (hf v)
        _ = _ := mul_comm _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      field_simp [hr.ne']
      rfl

lemma physicalDirectSource_integral_bound {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {p θ φ : ℝ} (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hr : 0<B.rmin) (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin)
    (hDhi : B.Dmax≤8*φ^2)
    :
    (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B J)≤
      ENNReal.ofReal (80*φ/(p*θ^2))*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
      ENNReal.ofReal (80/p)*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*ENNReal.ofReal (prefixConeMagnetic s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) := by
  have hN := physicalBinDensity_aemeasurable hs hT hX hV B hJ hJT
  have hG := hs.measurable_prefixConeGood hT hX
  have hR : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal (z.1-z.2.1)) :=
    (measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal
  have hb : (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,
        ENNReal.ofReal (80*φ/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)+
        ENNReal.ofReal (80/p)*(ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
          ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)
          ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hrz : 0<z.1-z.2.1 := hr.trans_le hz.2.2.1.1
    have hb := physicalDirectSourceDensity_bound (X:=X)
      hrz hp hθ hφ.le hq hdlo (hz.2.2.2.2.2.trans hDhi)
      (fun v=>hs.nonnegative _ hzT _)
    apply hb.trans_eq
    let G := prefixConeGood s T X z
    let b := prefixConeMagnetic s T X z
    have hG0 : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
    have hb0 : 0≤b := norm_nonneg _
    have heG : goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
        (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1=G := by
      simp [G,prefixConeGood,prefixField,prefixClamp_eq hzT]
    have heb : ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖=b := by
      simp [b,prefixConeMagnetic,coneFoot,prefixField,prefixClamp_eq hzT]
    rw [heG,heb]
    have he : (80*φ/p)*(z.1-z.2.1)*(G/θ^2+b)=
        (80*φ/(p*θ^2))*((z.1-z.2.1)*G)+
          (80/p)*((z.1-z.2.1)*φ*b) := by ring
    rw [he,ENNReal.ofReal_add (by positivity) (by positivity),add_mul]
    simp only [ENNReal.ofReal_mul (by positivity : 0≤80*φ/(p*θ^2)),
      ENNReal.ofReal_mul (by positivity : 0≤80/p),
      ENNReal.ofReal_mul (mul_nonneg hrz.le hφ.le),ENNReal.ofReal_mul hrz.le]
    dsimp only [G,b]
    ac_rfl
  refine hb.trans_eq ?_
  have hMG : AEMeasurable (fun z : ConeCoordinate=>
      ENNReal.ofReal (80*φ/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2))
      (physicalBinMeasure V B J) := by
    simpa only [Pi.mul_apply] using (((hR.mul hG.ennreal_ofReal).aemeasurable.mul hN).const_mul
      (ENNReal.ofReal (80*φ/(p*θ^2))))
  rw [lintegral_add_left' hMG,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

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

lemma ennreal_half_ofReal {x : ℝ} (hx : 0≤x) :
    (ENNReal.ofReal x)^(1/2:ℝ)=ENNReal.ofReal (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow,ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_QuadIndexEquiv
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

lemma tsum_quad_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'np,∑'nt,∑'nf,∑'nr,f ![np,nt,nf,nr] := by
  have h := quadIndexEquiv.symm.tsum_eq f
  rw [←h]
  simp only [ENNReal.tsum_prod']
  rfl

end RVM

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

lemma sqrt_near_product {a b I E r φ D : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hI : 0≤I) (hE : 0≤E) (hr : 0 ≤ r) (hφ : 0≤φ) (hD : 0≤D) :
    Real.sqrt (a*E)*Real.sqrt (D^2*(b*I*r*φ^2))=
      D*φ*Real.sqrt (a*I)*Real.sqrt (b*E)*Real.sqrt r := by
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hD]
  calc
    _ = D*Real.sqrt ((a*E)*(b*I*r*φ^2)) := by
      rw [Real.sqrt_mul (mul_nonneg ha hE)]
      ring
    _ = D*Real.sqrt ((a*I)*(b*E)*r*φ^2) := by congr 2; ring
    _ = _ := by
      rw [Real.sqrt_mul (by positivity : 0≤(a*I)*(b*E)*r),
        Real.sqrt_sq hφ,Real.sqrt_mul (by positivity : 0≤(a*I)*(b*E)),
        Real.sqrt_mul (mul_nonneg ha hI)]
      ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

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


open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma Admissible.datumEnergyNumber_nonneg {d : Datum} (hd : Admissible d) :
    0≤datumEnergyNumber d := by
  apply integral_nonneg
  intro x
  apply add_nonneg (by positivity)
  exact integral_nonneg (fun v=>mul_nonneg (q_pos v).le (hd.2.2.1 _))

lemma SmoothClassicalPrefix.initial_energy_eq {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) :
    (∫x : Vec,totalEnergy s (0,x))=datumEnergyNumber d := by
  unfold totalEnergy particleEnergy datumEnergyNumber
  simp only [hs.initial_E,hs.initial_B,hs.initial_f]

end RVM

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionCounts
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

lemma Admissible.representative_good_Cauchy {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → ∀(zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let H := max 1 T
      let B := representativeClosedBin T w k
      let O := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
          (max 0 (a-B.rmax)) (min T (b-B.rmin)))
      let E := datumEnergyNumber d
      let D := ENNReal.ofReal (128*C*p^3*θ^2)
      representativeGoodCost s F zX w k a b ≤
        ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (min (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))
            (D*(O/ENNReal.ofReal ((H*h)^2*φ^2/8))))^(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := hd.uniform_actual_bin_Cauchy
  refine ⟨C,hC,?_⟩
  intro s T F hs hT zX k a b I w ha hb hI hab
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hmeasure : volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)≤
      ENNReal.ofReal (768*I*r*φ^2) := by
    calc
      _ ≤ ENNReal.ofReal I*ENNReal.ofReal (2*r)*ENNReal.ofReal (384*φ^2) := by
        apply mul_le_mul' (mul_le_mul' _ _) le_rfl
        · rw [Real.volume_Icc]
          exact ENNReal.ofReal_le_ofReal hab
        · apply ENNReal.ofReal_le_ofReal
          rw [hBmax,hBmin]
          linarith only [hr]
      _ = _ := by rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)≤
      ENNReal.ofReal (20*I*datumEnergyNumber d) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.energyPrefix.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hab)
    rw [hs.initial_energy_eq] at hh
    calc
      _ ≤ ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*datumEnergyNumber d)) := mul_le_mul' le_rfl hh
      _ = _ := by
        norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat]
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hbnd := hbound s T F hs.energyPrefix hT hs.initial_f zX B (tsupport d.f₀)
    a b I p θ φ 1 1 (k 2) hd.2.1 hS0 hJ hI hp hθ.le hφ.le (by norm_num)
    (by change 0 < r/2; positivity) (by change 0<φ^2/2; positivity)
    (by change p/32≤p; linarith) le_rfl le_rfl (by norm_num [B,representativeClosedBin]) hangle
  dsimp only at hbnd
  have hθ1 : θ≤1 := cappedRepresentative_le_one (k 1)
  simp only [min_eq_left hθ1] at hbnd
  have hden : B.rmin^2*B.Dmin=r^2*φ^2/8 := by change (r/2)^2*(φ^2/2)=_; ring
  rw [hden] at hbnd
  unfold representativeGoodCost
  dsimp only
  apply mul_le_mul' le_rfl
  apply hbnd.trans
  apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  exact min_le_min (mul_le_mul' le_rfl hmeasure) le_rfl

lemma direct_good_near_scalar {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*
      Real.sqrt ((128*C*p^3*θ^2)^2*(768*I*(H*h)*φ^2)))=
    (128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2) := by
  rw [sqrt_near_product (by positivity : 0≤20*I) (by norm_num : (0:ℝ)≤768)
    hI hE (mul_nonneg hH hh) hφ (by positivity)]
  rw [show (20:ℝ)*I*I=20*(I:ℝ)^2 from by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤20),Real.sqrt_sq hI,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤768),Real.sqrt_mul hH]
  have he : Real.sqrt (20:ℝ)*Real.sqrt 768=Real.sqrt 15360 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤20)]
    norm_num
  calc
    _ = (128*C*(Real.sqrt 20*Real.sqrt 768)*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2) := by
      field_simp
    _ = _ := by rw [he]

lemma direct_good_far_sqrt {C K E p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 0<H) (hh : 0<h) (hφ : 0<φ) :
    Real.sqrt ((128*C*p^3*θ^2)*(K*O*E/((H*h)^2*φ^2/8)))=
      Real.sqrt (1024*C*K*E)*p*θ*Real.sqrt (p*O)/(H*h*φ) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  simp only [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤1024*C*K*E),
    Real.sq_sqrt (mul_nonneg hp.le hO)]
  field_simp
  ring

lemma direct_good_far_scalar {C K E I p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 1≤H) (hh : 0<h) (hφ : 0<φ) :
    (φ/(p*θ^2))*(Real.sqrt (20*I*E)*
      Real.sqrt ((128*C*p^3*θ^2)*(K*O*E/((H*h)^2*φ^2/8))))≤
      (Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h)) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  rw [direct_good_far_sqrt hC hK hE hp hθ hO hH0 hh hφ]
  have hsq : Real.sqrt (20*I*E)*Real.sqrt (1024*C*K*E)=
      Real.sqrt (20480*C*K)*E*Real.sqrt I := by
    rw [←Real.sqrt_mul (by positivity : 0≤20*I*E)]
    rw [show (20*I*E)*(1024*C*K*E)=((20480*C*K)*E^2)*I by ring,
      Real.sqrt_mul (by positivity : 0≤(20480*C*K)*E^2),
      Real.sqrt_mul (by positivity : 0≤20480*C*K),Real.sqrt_sq hE]
  calc
    _ = ((Real.sqrt (20*I*E)*Real.sqrt (1024*C*K*E))*Real.sqrt (p*O)/(θ*h))/H := by
      field_simp
    _ = ((Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h)))/H := by
      rw [hsq]
      ring
    _ ≤ _ := div_le_self (by positivity) hH

lemma direct_good_near_ennreal {C I E H h φ p θ : ℝ}
    (hC : 0≤C) (hI : 0≤I) (hE : 0≤E) (hH : 0≤H) (hh : 0≤h) (hφ : 0≤φ)
    (hp : 0<p) (hθ : 0<θ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))^2*ENNReal.ofReal (768*I*(H*h)*φ^2))^(1/2:ℝ))=
    ENNReal.ofReal ((128*C*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*(I*Real.sqrt h*p^2*φ^2)) := by
  rw [←ENNReal.ofReal_pow (by positivity : 0≤128*C*p^3*θ^2),
    ←ENNReal.ofReal_mul (sq_nonneg _),ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity),
    direct_good_near_scalar hC hI hE hH hh hφ hp hθ]

lemma direct_good_far_ennreal {C K E I p θ O H h φ : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hE : 0≤E) (hI : 0≤I) (hp : 0<p) (hθ : 0<θ)
    (hO : 0≤O) (hH : 1≤H) (hh : 0<h) (hφ : 0<φ) :
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      ((ENNReal.ofReal (128*C*p^3*θ^2))*(ENNReal.ofReal (K*O)*ENNReal.ofReal E/
        ENNReal.ofReal ((H*h)^2*φ^2/8)))^(1/2:ℝ))≤
    ENNReal.ofReal ((Real.sqrt (20480*C*K)*E)*(Real.sqrt I*Real.sqrt (p*O)/(θ*h))) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  rw [←ENNReal.ofReal_mul (by positivity : 0≤K*O),
    ←ENNReal.ofReal_div_of_pos (by positivity : 0<(H*h)^2*φ^2/8),
    ←ENNReal.ofReal_mul (by positivity : 0≤128*C*p^3*θ^2),
    ennreal_half_ofReal (by positivity),ennreal_half_ofReal (by positivity),
    ←ENNReal.ofReal_mul (Real.sqrt_nonneg _),←ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (direct_good_far_scalar hC hK hE hI hp hθ hO hH hh hφ)

lemma selectionDecay_pos : 0 < selectionDecay := Real.rpow_pos_of_pos (by norm_num) _
lemma selectionDecay_lt_one : selectionDecay<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma selectionDecay_pow (n : ℕ) :
    selectionDecay^n=((2:ℝ)^n)^(-1/100000:ℝ) := by
  rw [selectionDecay,←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma cappedRepresentative_selection_pow (n : ℕ) :
    (cappedRepresentative n)^(1/100000:ℝ)=selectionDecay^n := by
  rw [selectionDecay_pow]
  dsimp [cappedRepresentative]
  rw [inv_pow,Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity)]
  congr 1
  norm_num

lemma sourceRepresentative_two_pow (n : ℕ) : sourceRepresentative n=(2:ℝ)^(n+6) := by
  simp only [sourceRepresentative,pow_add]
  ring

lemma selection_angle_index {np nt : ℕ}
    (h : 1/sourceRepresentative np ≤ cappedRepresentative nt) : nt≤np+6 := by
  rw [sourceRepresentative_two_pow] at h
  have he : (2:ℝ)^nt≤2^(np+6) := by
    have hp : 0<(2:ℝ)^nt := by positivity
    have hq : 0<(2:ℝ)^(np+6) := by positivity
    dsimp [cappedRepresentative] at h
    rw [inv_pow,one_div] at h
    exact (inv_le_inv₀ hq hp).mp h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp he

lemma selectionWeight_gap_bound {P : ℝ} {N : ℕ} {k : Fin 4→ℕ}
    (hP : sourceRepresentative N≤P) (h0 : k 0≤N) (h1 : k 1≤k 0+6) :
    selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤
      selectionDecay^(N-k 0)*selectionDecay^(k 0+6-k 1)*selectionDecay^(k 2)*selectionDecay^(k 3) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hN := sourceRepresentative_two_pow N
  have hle : k 1≤N+6 := by omega
  have hid : sourceRepresentative N*cappedRepresentative (k 1)=(2:ℝ)^(N+6-k 1) := by
    rw [hN]
    dsimp [cappedRepresentative]
    rw [inv_pow, pow_sub₀ (2:ℝ) (by norm_num) hle]
  have hdec : (P*cappedRepresentative (k 1))^(-1/100000:ℝ)≤ selectionDecay^(N+6-k 1) := by
    rw [selectionDecay_pow,←hid]
    exact Real.rpow_le_rpow_of_nonpos (by rw [hN]; positivity)
      (mul_le_mul_of_nonneg_right hP hθ.le) (by norm_num)
  have he : N+6-k 1=(N-k 0)+(k 0+6-k 1) := by omega
  unfold selectionWeight
  rw [cappedRepresentative_selection_pow,cappedRepresentative_selection_pow]
  rw [he,pow_add] at hdec
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdec
    (pow_nonneg selectionDecay_pos.le _)) (pow_nonneg selectionDecay_pos.le _)

lemma sum_selectionDecay (N : ℕ) :
    ∑n∈Finset.range N,selectionDecay^n≤(1-selectionDecay)⁻¹ := by
  have hr : |selectionDecay|<1 := by rw [abs_of_pos selectionDecay_pos]; exact selectionDecay_lt_one
  exact ((summable_geometric_of_abs_lt_one hr).sum_le_tsum (Finset.range N)
    (fun _ _=>pow_nonneg selectionDecay_pos.le _)).trans_eq (tsum_geometric_of_abs_lt_one hr)

lemma sum_selectionDecay_box (N : ℕ) :
    ∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  classical
  have heq : (instDecidableEqFin 4 : DecidableEq (Fin 4))=
      (fun a b=>Classical.propDecidable (a=b)) := Subsingleton.elim _ _
  have hh := Finset.sum_prod_piFinset (Finset.range N) (fun (_i : Fin 4) (n : ℕ)=>selectionDecay^n)
  rw [heq] at hh
  have hsum : (∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i))=
      (∑n∈Finset.range N,selectionDecay^n)^4 := by
    simpa [dyadicBox,Fin.prod_univ_four,pow_succ] using hh
  rw [hsum]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))
    (sum_selectionDecay N) 4

lemma sum_selectionDecay_finset (S : Finset (Fin 4→ℕ)) :
    ∑k∈S,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  obtain ⟨N,hN⟩ := finset_subset_dyadicBox S
  exact (Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _=>Finset.prod_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))).trans
    (sum_selectionDecay_box N)

lemma sum_selectionWeight (S : Finset (Fin 4→ℕ)) {P : ℝ}
    (hP : ∀k∈S,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈S,1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1)) :
    ∑k∈S,selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤((1-selectionDecay)⁻¹)^4 := by
  classical
  by_cases hS : S.Nonempty
  · let N := S.sup (fun k=>k 0)
    have hN (k) (hk : k∈S) : k 0≤N := Finset.le_sup (f:=fun k : Fin 4→ℕ=>k 0) hk
    have hNP : sourceRepresentative N≤P := by
      obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup S hS (fun k=>k 0)
      change sourceRepresentative (S.sup (fun k : Fin 4→ℕ=>k 0))≤P
      rw [he]
      exact hP k hk
    let g : (Fin 4→ℕ)→(Fin 4→ℕ) := fun k=>![N-k 0,k 0+6-k 1,k 2,k 3]
    have hg : Set.InjOn g ↑S := by
      intro k hk l hl hkl
      have hk1 := selection_angle_index (hθ k hk)
      have hl1 := selection_angle_index (hθ l hl)
      have h00 := congrFun hkl 0
      have h11 := congrFun hkl 1
      have h22 := congrFun hkl 2
      have h33 := congrFun hkl 3
      change N-k 0=N-l 0 at h00
      change k 0+6-k 1=l 0+6-l 1 at h11
      change k 2=l 2 at h22
      change k 3=l 3 at h33
      have hk0 := hN k hk
      have hl0 := hN l hl
      have h0e : k 0=l 0 := by omega
      have h1e : k 1=l 1 := by omega
      apply funext
      intro i
      fin_cases i
      · exact h0e
      · exact h1e
      · exact h22
      · exact h33
    calc
      _≤∑k∈S,∏i,selectionDecay^(g k i) := Finset.sum_le_sum (fun k hk=>by
        simpa [g,Fin.prod_univ_four] using selectionWeight_gap_bound hNP (hN k hk) (selection_angle_index (hθ k hk)))
      _=∑k∈S.image g,∏i,selectionDecay^(k i) := (Finset.sum_image (f:=fun k : Fin 4→ℕ=>∏i,selectionDecay^(k i)) (fun k hk l hl he=>hg hk hl he)).symm
      _≤_ := sum_selectionDecay_finset _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    positivity

lemma Admissible.representative_good_envelope {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      representativeGoodCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*Real.sqrt h*p^2*φ^2)
          (Real.sqrt I*Real.sqrt (p*pureOccupationEnvelope P 512 16384 M A p w φ h I)/(θ*h))) := by
  obtain ⟨Cg,hCg,hcauchy⟩ := hd.representative_good_Cauchy
  let E := datumEnergyNumber d
  let H₀ := max 1 T₀
  let K := 1000000000*H₀^2
  let Cn := 128*Cg*Real.sqrt 15360*Real.sqrt E*Real.sqrt H₀
  let Cf := Real.sqrt (20480*Cg*K)*E
  let C := max Cn Cf
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hK : 0≤K := by dsimp [K]; positivity
  have hCn : 0≤Cn := by dsimp [Cn]; positivity
  have hCf : 0≤Cf := by dsimp [Cf]; positivity
  have hC : 0≤C := hCn.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hd.representative_pure_occupation T₀ M A hM hA] with P hoccup
  intro s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let O := coneOccupation F.flow zX T s.f
    (closedBinEulerian F.flow zX T B (tsupport d.f₀) a b
      (max 0 (a-B.rmax)) (min T (b-B.rmin)))
  let U := pureOccupationEnvelope P 512 16384 M A p w φ h I
  let D := ENNReal.ofReal (128*Cg*p^3*θ^2)
  let N := I*Real.sqrt h*p^2*φ^2
  let R := Real.sqrt I*Real.sqrt (p*U)/(θ*h)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hH0 : 0≤H := zero_le_one.trans hH
  have hHH : H≤H₀ := max_le_max le_rfl hTT
  have hU : 0≤U := pureOccupationEnvelope_nonneg hp.le hφ.le hh.le hI.le
  have hN : 0≤N := by dsimp [N]; positivity
  have hR : 0≤R := by dsimp [R]; positivity
  have hc := hcauchy s T F hs hT zX k a b I w ha hb hI hJI
  change representativeGoodCost s F zX w k a b≤
    ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
      (min (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))
        (D*(O/ENNReal.ofReal ((H*h)^2*φ^2/8))))^(1/2:ℝ)) at hc
  have ho : O≤ENNReal.ofReal (K*U)*ENNReal.ofReal E :=
    hoccup s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hsmall hsource HZ
  rw [mul_min_of_nonneg _ _ hC,ENNReal.ofReal_min]
  apply le_min
  · apply hc.trans
    calc
      _ ≤ ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (D^2*ENNReal.ofReal (768*I*(H*h)*φ^2))^(1/2:ℝ)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (min_le_left _ _) (by norm_num)))
      _ = ENNReal.ofReal ((128*Cg*Real.sqrt 15360*Real.sqrt E*Real.sqrt H)*N) :=
        direct_good_near_ennreal hCg hI.le hE hH0 hh.le hφ.le hp hθ
      _ ≤ ENNReal.ofReal (C*N) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hN
        apply le_trans _ (le_max_left _ _)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHH) (by positivity)
  · apply hc.trans
    calc
      _ ≤ ENNReal.ofReal (φ/(p*θ^2))*((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (D*(ENNReal.ofReal (K*U)*ENNReal.ofReal E/ENNReal.ofReal ((H*h)^2*φ^2/8)))^(1/2:ℝ)) := by
        apply mul_le_mul' le_rfl
        apply mul_le_mul' le_rfl
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        exact (min_le_right _ _).trans (mul_le_mul' le_rfl (ENNReal.div_le_div_right ho _))
      _ ≤ ENNReal.ofReal (Cf*R) := direct_good_far_ennreal hCg hK hE hI.le hp hθ hU hH hh hφ
      _ ≤ ENNReal.ofReal (C*R) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)

lemma selectionWeight_nonneg {P θ φ h : ℝ} (hP : 0≤P) (hθ : 0≤θ) (hφ : 0≤φ) (hh : 0≤h) :
    0 ≤ selectionWeight P θ φ h := by unfold selectionWeight; positivity

lemma selection_weighted_tsum {P c : ℝ} (hP0 : 0≤P) (hc : 0 ≤ c)
    (Q : Set (Fin 4→ℕ)) (hP : ∀k∈Q,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈Q,1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1))
    (f : (Fin 4→ℕ)→ℝ≥0∞)
    (hf : ∀k∈Q,f k≤ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) :
    (∑'k,Q.indicator f k)≤ENNReal.ofReal (c*((1-selectionDecay)⁻¹)^4) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun k=>k∈Q)
  have hU (k) (hk : k∈U) : k∈Q := (Finset.mem_filter.mp hk).2
  have hsum : (∑k∈S,Q.indicator f k)=∑k∈U,f k := by simp [U,Finset.sum_filter,indicator_apply]
  rw [hsum]
  calc
    _ ≤ ∑k∈U,ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3))) := Finset.sum_le_sum (fun k hk=>hf k (hU k hk))
    _ = ENNReal.ofReal (c*(∑k∈U,selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun k _=>mul_nonneg hc
        (selectionWeight_nonneg hP0 (cappedRepresentative_pos _).le
          (cappedRepresentative_pos _).le (cappedRepresentative_pos _).le)),Finset.mul_sum]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (sum_selectionWeight U (fun k hk=>hP k (hU k hk)) (fun k hk=>hθ k (hU k hk))) hc)

lemma Admissible.unselected_good_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeGoodCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*P*Real.sqrt I) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_good_envelope T₀
  refine ⟨C*((1-selectionDecay)⁻¹)^4,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hbound M A hM hA,eventually_ge_atTop (1:ℝ)] with P hbnd hP
  intro s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hsource HZ
  dsimp only
  let Q := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
  have hh := selection_weighted_tsum (zero_le_one.trans hP) (by positivity : 0≤C*P*Real.sqrt I)
    Q (fun _ hk=>hk.1.1) (fun _ hk=>hk.1.2.1)
    (fun k=>representativeGoodCost s F zX w k a b) (fun k hk=>by
      have he := hbnd s T F hs hT hTT zX k a b I w hzX ha hb hab hI hJI hw hk.1.2.2 hsource HZ
      have hnot := le_of_not_gt hk.2
      exact he.trans (ENNReal.ofReal_le_ofReal (by
        have hmul := mul_le_mul_of_nonneg_left hnot hC
        simpa only [mul_assoc] using hmul)))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_ReceiverWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma tsum_quad_pair_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'n : ℕ×ℕ,∑'nt : ℕ,∑'nr : ℕ,f ![n.1,nt,n.2,nr] := by
  rw [tsum_quad_index,ENNReal.tsum_prod']
  apply tsum_congr
  intro np
  exact ENNReal.tsum_comm

lemma tsum_centralIndexSector (P : ℝ) (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,(centralIndexSector P).indicator f k)=
      ∑'n : ℕ×ℕ,({n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}).indicator
        (fun n=>∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt ≤ cappedRepresentative n.2/16
          then f ![n.1,nt,n.2,nr] else 0) n := by
  classical
  rw [tsum_quad_pair_index]
  apply tsum_congr
  intro n
  by_cases hn : sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1 ≤ cappedRepresentative n.2
  · have hn' : n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} := hn
    rw [indicator_of_mem hn']
    apply tsum_congr
    intro nt
    apply tsum_congr
    intro nr
    have hi : (![n.1,nt,n.2,nr]∈centralIndexSector P) ↔
        cappedRepresentative nt ≤ cappedRepresentative n.2/16 := by
      change (sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2 ∧
        cappedRepresentative nt ≤ cappedRepresentative n.2/16) ↔_
      simp only [hn.1,hn.2,true_and]
    simp only [indicator_apply,hi]
  · have hn' : n∉{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} := hn
    rw [indicator_of_notMem hn']
    apply ENNReal.tsum_eq_zero.mpr
    intro nt
    apply ENNReal.tsum_eq_zero.mpr
    intro nr
    apply indicator_of_notMem
    change ¬(sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1 ≤ cappedRepresentative n.2 ∧
      cappedRepresentative nt ≤ cappedRepresentative n.2/16)
    exact fun h=>hn ⟨h.1,h.2.1⟩

lemma representativeSmallSector_subset_centralIndexSector (P : ℝ) :
    representativeSmallSector P⊆centralIndexSector P := by
  intro k hk
  refine ⟨hk.1,hk.2.1.trans (hk.2.2.trans ?_),hk.2.2⟩
  have hφ := (cappedRepresentative_pos (k 2)).le
  linarith



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_UnselectedCover
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

lemma PhaseFlowOn.direct_source_representative_cost {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (k : Fin 4→ℕ) {a b : ℝ} (ha : 0≤a) (hb : b≤T) :
    (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal 10240*(representativeGoodCost s F zX w k a b+
        representativeMagneticCost s F zX w k a b) := by
  have hc := (F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hp : 0 < sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
  have ht := cappedRepresentative_pos (k 1)
  have hf := cappedRepresentative_pos (k 2)
  have hh := physicalDirectSource_integral_bound hs hT hc.fst.measurable hc.snd.measurable
    (representativeClosedBin T w k) measurableSet_Icc (Icc_subset_Icc ha hb)
    (show 0 < sourceRepresentative (k 0)/128 by positivity) ht hf
    (representativeClosedBin_radius_pos T w k) le_rfl le_rfl le_rfl
  apply hh.trans_eq
  unfold representativeGoodCost representativeMagneticCost
  dsimp only
  rw [mul_add,←mul_assoc,←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240),
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240)]
  congr 1
  · congr 1
    congr 1
    ring
  · rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    have he : 10240*(cappedRepresentative (k 2)/sourceRepresentative (k 0))=
        (80/(sourceRepresentative (k 0)/128))*cappedRepresentative (k 2) := by ring
    rw [he,ENNReal.ofReal_mul (by positivity : 0≤80/(sourceRepresentative (k 0)/128))]
    dsimp only [Function.comp_apply,id_eq]
    ac_rfl

lemma Admissible.unselected_small_source_uniform_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let R := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,R.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectSourceDensity s X V (representativeClosedBin T w k) z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cg,hCg,hgood⟩ := hd.unselected_good_uniform T₀
  obtain ⟨Cm,hCm,hmag⟩ := hd.magnetic_small_uniform T₀
  refine ⟨10240*(Cg+Cm),by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hgood M A (zero_lt_one.trans_le hM) hA] with P hg
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource HZ
  dsimp only
  let R := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
  let G := fun k=>representativeGoodCost s F zX w k a b
  let H := fun k=>representativeMagneticCost s F zX w k a b
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hPB : P*Real.sqrt I≤B := le_add_of_nonneg_right (by positivity)
  have hsum : (∑'k : Fin 4→ℕ,R.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal 10240*((∑'k,R.indicator G k)+(∑'k,R.indicator H k)) := by
    rw [←ENNReal.tsum_add,←ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈R
    · simp only [indicator_of_mem hk]
      exact F.direct_source_representative_cost hs.energyPrefix hT zX k ha hb
    · simp only [indicator_of_notMem hk,zero_add,mul_zero,le_refl]
  have hg' : (∑'k,R.indicator G k)≤ENNReal.ofReal (Cg*B) := by
    apply (hg s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI
      (zero_lt_one.trans_le hw) hsource HZ).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hPB hCg
  have hm : (∑'k,R.indicator H k)≤ENNReal.ofReal (Cm*B) := by
    calc
      _≤∑'k,(centralIndexSector P).indicator H k := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases hk : k∈R
        · rw [indicator_of_mem hk,indicator_of_mem (representativeSmallSector_subset_centralIndexSector P hk.1)]
        · rw [indicator_of_notMem hk]; exact bot_le
      _≤_ := by
        rw [tsum_centralIndexSector]
        exact hmag M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  apply hsum.trans
  apply (mul_le_mul' le_rfl (add_le_add hg' hm)).trans_eq
  rw [←ENNReal.ofReal_add (mul_nonneg hCg hB) (mul_nonneg hCm hB),
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240)]
  congr 1
  ring

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.unselected_small_source_uniform_oai := @OAI.RVM.Admissible.unselected_small_source_uniform_oai
