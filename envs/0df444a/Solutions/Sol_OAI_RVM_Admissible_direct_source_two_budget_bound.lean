-- Prove2me | solution 1 for OAI.RVM.Admissible.direct_source_two_budget_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:48:25.278502+00:00
-- url     : https://prove2.me/submissions/daaa67ca-c2a3-4e1e-93d9-f5cd3659d9ae

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_uniform_actual_bin_Cauchy
import Theorems.Thm_OAI_RVM_Admissible_uniform_actual_magnetic_Cauchy

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

lemma Admissible.direct_source_two_budget_bound_oai {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb : ℝ, 0≤Cg ∧ 0≤Cb ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (B : ClosedConeBin) (S : Set Phase)
      (a b I p P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z=>s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<p → 0<P → 0<θ → 0<φ → 0≤σ → 0<B.rmin → 0<B.Dmin →
      p≤B.qmin → B.qmax≤P → θ^2/2≤B.dmin → B.dmax≤8*θ^2 →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.emax≤8*σ^2 →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
          ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*P^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*P^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/(p*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*M))^(1/2:ℝ))+
        ENNReal.ofReal (80/p)*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*M))^(1/2:ℝ)) := by
  obtain ⟨Cg,hCg,hgood⟩ := hd₀.uniform_actual_bin_Cauchy
  obtain ⟨Cb,hCb,hmag⟩ := hd₀.uniform_actual_magnetic_Cauchy
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX B S a b I p P θ φ σ k j hS hS0 hJ hI hp hP hθ hφ hσ
    hR hD hqlo hqhi hdlo hdhi hDlo hDhi he hangle
  dsimp only
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hb := physicalDirectSource_integral_bound hs hT hα.fst.measurable hα.snd.measurable B
    measurableSet_Icc hJ hp hθ hφ hR hqlo hdlo hDhi
  exact hb.trans (add_le_add
    (mul_le_mul' le_rfl (hgood s T F hs hT h0 zX B S a b I P θ φ σ k j hS hS0 hJ
      hI hP hθ.le hφ.le hσ hR hD hqhi hdhi hDhi he hangle))
    (mul_le_mul' le_rfl (hmag s T F hs hT h0 zX B S a b I P θ φ σ k j hS hS0 hJ
      hI hP hθ.le hφ.le hσ hR hD hDlo hqhi hdhi hDhi he hangle)))

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

theorem solution : type_of% @OAI.RVM.Admissible.direct_source_two_budget_bound_oai := @OAI.RVM.Admissible.direct_source_two_budget_bound_oai
