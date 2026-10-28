-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:54:32.036318+00:00
-- url     : https://prove2.me/submissions/c80f34fd-7e35-4fe7-8e1b-ecf95be1c306

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
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

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_WithinFlow
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
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open scoped Topology NNReal ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

open Set MeasureTheory Filter
open scoped Topology ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


lemma PhaseFlowOn.continuousOn_time {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (z : Phase) : ContinuousOn (F.flow z) (Icc 0 T) :=
  fun t ht => (F.ode z t ht).continuousWithinAt

open Set MeasureTheory Filter
open scoped Topology ContDiff


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
lemma dyadicFactor_nonneg (n : ℕ) (x : ℝ) : 0≤dyadicFactor n x := dyadicBump_nonneg _

lemma dyadicFactor_eq (n : ℕ) (x : ℝ) :
    dyadicFactor n x=dyadicCut ((2:ℝ)^n*x)-dyadicCut ((2:ℝ)^(n+1)*x) := by
  simp only [dyadicFactor,dyadicBump,pow_succ]
  congr 2
  ring
lemma sum_dyadicFactor (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range N, dyadicFactor n x=dyadicCut x-dyadicCut ((2:ℝ)^N*x) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,dyadicFactor_eq]; ring

lemma dyadicFactor_zero_large {x : ℝ} {n : ℕ} (hn : 2≤(2:ℝ)^n*x) :
    dyadicFactor n x=0 := dyadicBump_zero_right hn

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

lemma hasDerivAt_dyadicCut_zero_left {x : ℝ} (hx : x≤1) : HasDerivAt dyadicCut 0 x := by
  have hm : IsLocalMax dyadicCut x := Filter.Eventually.of_forall (fun y => by
    rw [dyadicCut_one hx]
    exact dyadicCut_le_one y)
  rw [← hm.deriv_eq_zero]
  exact (contDiff_dyadicCut.differentiable (by simp) x).hasDerivAt

lemma hasDerivAt_dyadicCut_zero_right {x : ℝ} (hx : 2≤x) : HasDerivAt dyadicCut 0 x := by
  have hm : IsLocalMin dyadicCut x := Filter.Eventually.of_forall (fun y => by
    rw [dyadicCut_zero hx]
    exact dyadicCut_nonneg y)
  rw [← hm.deriv_eq_zero]
  exact (contDiff_dyadicCut.differentiable (by simp) x).hasDerivAt

lemma hasDerivAt_sum_dyadicFactor_zero {x : ℝ} (N : ℕ) (hx : x≤1)
    (hN : 2≤(2:ℝ)^N*x) :
    HasDerivAt (fun y => ∑ n∈Finset.range N, dyadicFactor n y) 0 x := by
  have h := (hasDerivAt_dyadicCut_zero_left hx).sub
    ((hasDerivAt_dyadicCut_zero_right hN).comp x ((hasDerivAt_id x).const_mul ((2:ℝ)^N)))
  convert h using 1 <;> first | rfl | (simp [sum_dyadicFactor] <;> rfl)

lemma dyadicMultiFactor_nonneg {ι : Type*} [Fintype ι] (n : ι→ℕ) (x : ι→ℝ) :
    0≤dyadicMultiFactor n x := Finset.prod_nonneg (fun _i _ => dyadicFactor_nonneg _ _)

lemma sum_dyadicMultiFactor {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x =
      ∏ i, (dyadicCut (x i)-dyadicCut ((2:ℝ)^N*x i)) := by
  classical
  unfold dyadicBox dyadicMultiFactor
  convert Finset.sum_prod_piFinset (Finset.range N) (fun i n => dyadicFactor n (x i)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [sum_dyadicFactor]

lemma differentiableAt_dyadicMultiFactor_curve {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t) (n : ι→ℕ) :
    DifferentiableAt ℝ (fun r => dyadicMultiFactor n (fun i => g i r)) t := by
  classical
  exact DifferentiableAt.fun_finsetProd (fun i _ =>
    (contDiff_dyadicFactor (n i)).differentiable (by simp) (g i t) |>.comp t (hg i))

lemma hasDerivAt_sum_dyadicMultiFactor_zero {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t)
    (N : ℕ) (hx : ∀ i, g i t≤1) (hN : ∀ i, 2≤(2:ℝ)^N*g i t) :
    HasDerivAt (fun r => ∑ n∈dyadicBox ι N, dyadicMultiFactor n (fun i => g i r)) 0 t := by
  classical
  have hd (i : ι) : HasDerivAt (fun r => ∑ n∈Finset.range N,dyadicFactor n (g i r)) 0 t := by
    simpa only [Function.comp_def,zero_mul] using
      (hasDerivAt_sum_dyadicFactor_zero N (hx i) (hN i)).comp t (hg i).hasDerivAt
  have H := HasDerivAt.fun_finsetProd (u:=Finset.univ) (fun i _ => hd i)
  simpa only [smul_zero,Finset.sum_const_zero,sum_dyadicFactor,← sum_dyadicMultiFactor] using H

lemma selected_dyadic_derivative_cancel {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t)
    (N : ℕ) (hx : ∀ i, g i t≤1) (hN : ∀ i, 2≤(2:ℝ)^N*g i t)
    (S : Finset (ι→ℕ)) (hS : S⊆dyadicBox ι N) :
    deriv (fun r => ∑ n∈S,dyadicMultiFactor n (fun i => g i r)) t =
      -(∑ n∈dyadicBox ι N \ S,deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t) := by
  classical
  have hd := differentiableAt_dyadicMultiFactor_curve hg
  rw [deriv_fun_sum (fun n _ => hd n)]
  have hall := (hasDerivAt_sum_dyadicMultiFactor_zero hg N hx hN).deriv
  rw [deriv_fun_sum (fun n _ => hd n)] at hall
  have he := Finset.sum_sdiff (f:=fun n => deriv (fun r => dyadicMultiFactor n (fun i => g i r)) t) hS
  rw [hall] at he
  linarith

lemma selected_dyadic_derivative_boundary {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, DifferentiableAt ℝ (g i) t)
    (N : ℕ) (hx : ∀ i, g i t≤1) (hN : ∀ i, 2≤(2:ℝ)^N*g i t)
    (S : Finset (ι→ℕ)) (hS : S⊆dyadicBox ι N)
    (hne : deriv (fun r => ∑ n∈S,dyadicMultiFactor n (fun i => g i r)) t ≠ 0) :
    (∃ n∈S, 0<dyadicMultiFactor n (fun i => g i t)) ∧
    (∃ n∈dyadicBox ι N \ S, 0<dyadicMultiFactor n (fun i => g i t)) := by
  classical
  have pos_of_ne (U : Finset (ι→ℕ))
      (hu : deriv (fun r => ∑ n∈U,dyadicMultiFactor n (fun i => g i r)) t≠0) :
      ∃ n∈U,0<dyadicMultiFactor n (fun i => g i t) := by
    by_contra hh
    push Not at hh
    have he : ∑ n∈U,dyadicMultiFactor n (fun i => g i t)=0 :=
      Finset.sum_eq_zero (fun n hn => le_antisymm (hh n hn) (dyadicMultiFactor_nonneg _ _))
    apply hu
    apply IsLocalMin.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun r => by
      dsimp only
      rw [he]
      exact Finset.sum_nonneg (fun n _ => dyadicMultiFactor_nonneg _ _))
  refine ⟨pos_of_ne S hne,pos_of_ne (dyadicBox ι N \ S) ?_⟩
  intro he
  apply hne
  rw [selected_dyadic_derivative_cancel hg N hx hN S hS,
    ← deriv_fun_sum (fun n _ => differentiableAt_dyadicMultiFactor_curve hg n),he,neg_zero]

lemma dyadicMultiFactor_positive_bands {ι : Type*} [Fintype ι]
    {n : ι→ℕ} {x : ι→ℝ} (h : 0<dyadicMultiFactor n x) : ∀ i,DyadicBand (n i) (x i) := by
  classical
  intro i
  apply dyadicFactor_tsupport
  apply subset_tsupport
  intro he
  have hz : dyadicMultiFactor n x=0 := Finset.prod_eq_zero (Finset.mem_univ i) he
  linarith

lemma dyadicMultiFactor_positive_index_comparison {ι : Type*} [Fintype ι]
    {n m : ι→ℕ} {x : ι→ℝ} (hn : 0<dyadicMultiFactor n x)
    (hm : 0<dyadicMultiFactor m x) : ∀ i, m i ≤ n i + 2 ∧ n i ≤ m i + 2 := by
  intro i
  exact ⟨dyadicBand_index_le (dyadicMultiFactor_positive_bands hn i)
    (dyadicMultiFactor_positive_bands hm i),dyadicBand_index_le
      (dyadicMultiFactor_positive_bands hm i) (dyadicMultiFactor_positive_bands hn i)⟩

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

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

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

lemma real_deficit_le_two {n : Vec} (hn : ‖n‖=1) (v : Vec) : 1-dot n (velocity v) ≤ 2 := by
  have h := (abs_dot_le n (velocity v)).trans (by simpa only [hn,one_mul] using (norm_velocity_lt_one v).le)
  linarith [neg_abs_le (dot n (velocity v))]

lemma physicalCutoffCoordinates_le_one {T r : ℝ} {n v w : Vec}
    (hn : ‖n‖=1) (hr : r ≤ max 1 T) : ∀ i,physicalCutoffCoordinates T r n v w i≤1 := by
  intro i
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · apply (div_le_one (q_pos v)).mpr
    have hs := q_sq v
    nlinarith [q_pos v,sq_nonneg ‖v‖]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [real_deficit_le_two hn v]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [real_deficit_le_two hn w]
  · exact (div_le_one (lt_of_lt_of_le (by norm_num) (le_max_left _ _))).mpr hr

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

lemma selectedDyadicCutoff_local_box {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} {N : ℕ}
    (he : ∀ᶠ r in 𝓝 t,∀ n : ι→ℕ,n∉dyadicBox ι N → dyadicMultiFactor n (fun i=>g i r)=0)
    (S : Set (ι→ℕ)) :
    (fun r => selectedDyadicCutoff S (fun i => g i r)) =ᶠ[𝓝 t]
      (fun r => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n (fun i=>g i r)) := by
  classical
  filter_upwards [he] with r hr
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using (Finset.sum_indicator_eq_sum_filter
      (dyadicBox ι N) (fun _ n => dyadicMultiFactor n (fun i=>g i r)) (fun _=>S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hr n hn]
    · exact indicator_of_notMem hs _

lemma selectedDyadicCutoff_derivative_boundary {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ}
    (hg : ∀ i,DifferentiableAt ℝ (g i) t) (hp : ∀ i,0<g i t)
    (h1 : ∀ i,g i t≤1) (S : Set (ι→ℕ))
    (hne : deriv (fun r=>selectedDyadicCutoff S (fun i=>g i r)) t≠0) :
    ∃ n∈S,∃ m∉S,0<dyadicMultiFactor n (fun i=>g i t) ∧
      0<dyadicMultiFactor m (fun i=>g i t) ∧ ∀ i,m i ≤ n i+2 ∧ n i ≤ m i+2 := by
  classical
  obtain ⟨N,hN,he⟩ := dyadicMultiFactor_curve_locally_finite (fun i=>(hg i).continuousAt) hp
  rw [(selectedDyadicCutoff_local_box he S).deriv_eq] at hne
  obtain ⟨⟨n,hn,hnpos⟩,⟨m,hm,hmpos⟩⟩ := selected_dyadic_derivative_boundary hg N h1 hN
    (selectedDyadicBox N S) (Finset.filter_subset _ _) hne
  have hnS : n∈S := (Finset.mem_filter.mp hn).2
  have hmS : m∉S := by
    intro hmS
    exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hm).1,hmS⟩)
  exact ⟨n,hnS,m,hmS,hnpos,hmpos,dyadicMultiFactor_positive_index_comparison hnpos hmpos⟩

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ClosedBranchDomain
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

lemma continuousOn_normalisedPrimitive {Q : Type*} [TopologicalSpace Q]
    {r : Q→ℝ} {a u n : Q→Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S) (hu : ContinuousOn u S)
    (hn : ContinuousOn n S) (hd : ∀p∈S,1-dot (n p) (u p)≠0)
    (hD : ∀p∈S,1-dot (n p) (a p)≠0) :
    ContinuousOn (fun p=>normalisedPrimitive (r p) (a p) (u p) (n p)) S := by
  have hdot {f g : Q→Vec} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun p=>dot (f p) (g p)) S := by
    simpa only [dot_eq_inner] using hf.inner hg
  exact (hr.div (continuousOn_const.sub (hdot hn hu)) hd).smul
    (hu.sub (((continuousOn_const.sub (hdot ha hu)).div
      (continuousOn_const.sub (hdot hn ha)) hD).smul hn))

lemma PhaseFlowOn.normalised_primitive_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) :
    ContinuousOn (fun p : ConeKernelState=>normalisedPrimitive (p.1.1-p.1.2)
      (velocity (F.flow zX p.1.1).2) (velocity p.2.2.2) p.2.1) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  refine continuousOn_normalisedPrimitive (continuous_fst.fst.sub continuous_fst.snd).continuousOn
    ha hu.continuousOn continuous_snd.fst.continuousOn ?_ ?_
  · intro p hp
    exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  · intro p hp
    exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

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


lemma dyadicBand_capped_range {n : ℕ} {x : ℝ} (h : DyadicBand n x) :
    cappedRepresentative n/2≤x ∧ x≤2*cappedRepresentative n := by
  have hp : 0<(2:ℝ)^n := by positivity
  have he : cappedRepresentative n = ((2:ℝ)^n)⁻¹ := by simp [cappedRepresentative,inv_pow]
  rw [he]
  constructor
  · rw [inv_eq_one_div,div_div]
    exact (div_le_iff₀ (mul_pos hp (by norm_num))).mpr (by nlinarith [h.1])
  · rw [inv_eq_one_div,mul_one_div]
    exact (le_div_iff₀ hp).mpr (by nlinarith [h.2])

lemma dyadicBand_source_range {n : ℕ} {v : Vec} (h : DyadicBand n (1/q v)) :
    sourceRepresentative n/128≤q v ∧ q v≤ sourceRepresentative n/32 := by
  have hlo := h.1
  have hhi := h.2
  rw [mul_one_div] at hlo hhi
  have ha := (le_div_iff₀ (q_pos v)).mp hlo
  have hb := (div_le_iff₀ (q_pos v)).mp hhi
  dsimp [sourceRepresentative]
  constructor <;> linarith

lemma dyadicBand_angular_range {n : ℕ} {d : ℝ} (hd : 0≤d)
    (h : DyadicBand n (Real.sqrt (d/2))) :
    (cappedRepresentative n)^2/2≤d ∧ d≤8*(cappedRepresentative n)^2 := by
  have hh := dyadicBand_capped_range h
  have hp : 0 < cappedRepresentative n := by dsimp [cappedRepresentative]; positivity
  have hs := Real.sq_sqrt (by positivity : 0≤d/2)
  have hn := Real.sqrt_nonneg (d/2)
  have hlo := mul_self_le_mul_self (by positivity : 0 ≤ cappedRepresentative n/2) hh.1
  have hhi := mul_self_le_mul_self hn hh.2
  constructor <;> nlinarith

lemma dyadicBand_radius_range {n : ℕ} {T r : ℝ}
    (h : DyadicBand n (r/max 1 T)) :
    max 1 T*cappedRepresentative n/2 ≤ r ∧ r≤2*max 1 T*cappedRepresentative n := by
  have hm : 0 < max (1:ℝ) T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hh := dyadicBand_capped_range h
  have ha := (le_div_iff₀ hm).mp hh.1
  have hb := (div_le_iff₀ hm).mp hh.2
  constructor <;> nlinarith



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

lemma hasDerivAt_cutoffRay (z h : CutoffState) :
    HasDerivAt (fun s : ℝ => z+s • h) h 0 := by
  have hh := (hasDerivAt_const (0:ℝ) z).add ((hasDerivAt_id (0:ℝ)).smul_const h)
  change HasDerivAt (fun s : ℝ=>z+s • h) (0+(1:ℝ) • h) 0 at hh
  simpa only [zero_add,one_smul] using hh

lemma stateCutoff_ray_deriv {T : ℝ} {z : CutoffState} (Q : Set (Fin 4→ℕ))
    (hr : 0<z.1) (hn : ‖z.2.1‖=1) (h : CutoffState) :
    deriv (fun s : ℝ=>stateCutoff T Q (z+s • h)) 0 =
      fderiv ℝ (stateCutoff T Q) z h := by
  have hd := ((contDiffAt_stateCutoff T Q hr hn).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (stateCutoff T Q) (fderiv ℝ (stateCutoff T Q) z) (z+(0:ℝ) • h) := by
    simpa only [zero_smul,add_zero] using hd
  exact (hd'.comp_hasDerivAt 0 (hasDerivAt_cutoffRay z h)).deriv

lemma stateCutoff_partial_boundary {T : ℝ} {z : CutoffState} (Q : Set (Fin 4→ℕ))
    (hr : 0<z.1) (hT : z.1≤ max 1 T) (hn : ‖z.2.1‖=1) (h : CutoffState)
    (hne : fderiv ℝ (stateCutoff T Q) z h≠0) :
    ∃j∈Q,∃k∉Q,
      0<dyadicMultiFactor j (physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
      0<dyadicMultiFactor k (physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
      ∀i,k i≤j i+2 ∧ j i≤k i+2 := by
  let g : Fin 4→ℝ→ℝ := fun i s=>
    physicalCutoffCoordinates T (z+s • h).1 (z+s • h).2.1 (z+s • h).2.2.1 (z+s • h).2.2.2 i
  have hg : ∀i,DifferentiableAt ℝ (g i) 0 := by
    intro i
    have hc := (contDiffAt_physicalCutoffCoordinates (T:=T) hr hn).differentiableAt (by simp)
    have hc' : DifferentiableAt ℝ (fun z : CutoffState=>
        physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) (z+(0:ℝ) • h) := by
      simpa only [zero_smul,add_zero] using hc
    exact differentiableAt_pi.mp (hc'.comp (f:=fun s : ℝ=>z+s • h) 0 (hasDerivAt_cutoffRay z h).differentiableAt) i
  have hp : ∀i,0<g i 0 := by simpa only [g,zero_smul,add_zero] using physicalCutoffCoordinates_pos (T:=T) hn hr
  have h1 : ∀i,g i 0≤1 := by simpa only [g,zero_smul,add_zero] using physicalCutoffCoordinates_le_one hn hT
  have hd : deriv (fun s=>selectedDyadicCutoff Q (fun i=>g i s)) 0≠0 := by
    change deriv (fun s=>stateCutoff T Q (z+s • h)) 0≠0
    rwa [stateCutoff_ray_deriv Q hr hn h]
  simpa only [g,zero_smul,add_zero] using selectedDyadicCutoff_derivative_boundary hg hp h1 Q hd

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

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

lemma velocity_deficit_mem_unit2 (v w : Vec) :
    1-dot (velocity w) (velocity v)∈Icc (0:ℝ) 2 := by
  have hd := abs_real_inner_le_norm (velocity w) (velocity v)
  rw [←dot_eq_inner] at hd
  have hn : ‖velocity w‖*‖velocity v‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (norm_velocity_lt_one w).le).trans
      (norm_velocity_lt_one v).le
  have ha := (abs_le.mp (hd.trans hn))
  constructor <;> linarith

lemma physicalCutoff_positive_closedBin {T w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t) (hband : q (V t)∈Icc (w/8) (8*w))
    {k : Fin 4→ℕ} {n : Sphere} {v : Vec}
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))) :
    (t,σ,n)∈physicalBinBase V (representativeClosedBin T w k) J ∧
      v∈coneBinMomentumSet (representativeClosedBin T w k) n.1 (velocity (V t)) := by
  have hh := dyadicMultiFactor_positive_bands hk
  have hq := dyadicBand_source_range (show DyadicBand (k 0) (1/q v) from hh 0)
  have hd := dyadicBand_angular_range (cone_denom_pos v n.1 (sphere_norm n)).le
    (show DyadicBand (k 1) (Real.sqrt ((1-dot n.1 (velocity v))/2)) from hh 1)
  have hD := dyadicBand_angular_range (cone_denom_pos (V t) n.1 (sphere_norm n)).le
    (show DyadicBand (k 2) (Real.sqrt ((1-dot n.1 (velocity (V t)))/2)) from hh 2)
  have hr := dyadicBand_radius_range
    (show DyadicBand (k 3) ((t-σ)/max 1 T) from hh 3)
  exact ⟨⟨ht,hσ,hr,hband,hD⟩,⟨hq,hd,velocity_deficit_mem_unit2 v (V t)⟩⟩

lemma measurableSet_trianglePhaseDomain (T : ℝ) : MeasurableSet (trianglePhaseDomain T) :=
  ((measurable_fst.fst measurableSet_Ioo).inter
    ((measurableSet_lt measurable_const measurable_fst.snd.fst).inter
      (measurableSet_lt measurable_fst.snd.fst measurable_fst.fst)))

lemma PhaseFlowOn.triangleKernelState_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (triangleKernelState F.flow zX) (trianglePhaseDomain T) := by
  have hX : ContinuousOn (fun p : TrianglePhase=>F.flow zX p.1.1) (trianglePhaseDomain T) :=
    (F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>Ioo_subset_Icc_self hp.1)
  exact (continuous_fst.fst.prodMk continuous_fst.snd.fst).continuousOn.prodMk
    (continuous_fst.snd.snd.subtype_val.continuousOn.prodMk
      ((hX.fst.sub ((continuous_fst.fst.sub continuous_fst.snd.fst).continuousOn.smul
        continuous_fst.snd.snd.subtype_val.continuousOn)).prodMk continuous_snd.continuousOn))

lemma triangleKernelState_mem (α : Phase→ℝ→Phase) (zX : Phase) {T : ℝ} {p : TrianglePhase}
    (hp : p∈trianglePhaseDomain T) : triangleKernelState α zX p∈coneKernelDomain T := by
  exact ⟨⟨Ioo_subset_Icc_self hp.1,⟨hp.2.1.le,hp.2.2.le.trans hp.1.2.le⟩⟩,
    ⟨p.1.2.2.2,mem_univ _⟩⟩

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

lemma source_energy_index_lt {n N : ℕ} {v : Vec}
    (h : DyadicBand n (1/q v)) (hP : 1024*q v≤(2:ℝ)^N) : n<N := by
  by_contra hc
  have hn : N≤n := Nat.le_of_not_gt hc
  have hpow : (2:ℝ)^N≤(2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
  have hr := (dyadicBand_source_range h).1
  dsimp [sourceRepresentative] at hr
  nlinarith [q_pos v]

lemma source_angle_index_lt {n N : ℕ} {v nu : Vec} (hnu : ‖nu‖=1)
    (h : DyadicBand n (Real.sqrt ((1-dot nu (velocity v))/2)))
    (hP : 1024*q v≤(2:ℝ)^N) : n<N := by
  by_contra hc
  have hn : N≤n := Nat.le_of_not_gt hc
  have hpow : (2:ℝ)^N≤(2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
  have hm := mul_le_mul_of_nonneg_right (hP.trans hpow)
    (Real.sqrt_nonneg ((1-dot nu (velocity v))/2))
  have hl := source_angle_coordinate_lower v nu hnu
  nlinarith [h.2]

lemma physicalCutoff_positive_source_indices {T r : ℝ} {v w n : Vec} {k : Fin 4→ℕ} {N : ℕ}
    (hn : ‖n‖=1) (hP : 1024*q v≤(2:ℝ)^N)
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v w)) :
    k 0<N ∧ k 1<N := by
  have hb := dyadicMultiFactor_positive_bands hk
  exact ⟨source_energy_index_lt (hb 0) hP,source_angle_index_lt hn (hb 1) hP⟩

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeKernelInterior
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

lemma PhaseFlowOn.coneCutoffState_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (coneCutoffState F.flow zX) (coneKernelInterior T) := by
  exact (continuous_fst.fst.sub continuous_fst.snd).continuousOn.prodMk
    (continuous_snd.fst.continuousOn.prodMk (continuous_snd.snd.snd.continuousOn.prodMk
      (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1.1)).snd)))

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

lemma PhaseFlowOn.normalisedPartialCutoff_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {H : ConeKernelState→CutoffState} (hH : ContinuousOn H (coneKernelInterior T)) :
    ContinuousOn (normalisedPartialCutoff F.flow zX T Q H) (coneKernelInterior T) := by
  have hz := F.coneCutoffState_continuousOn zX
  have hder : ContinuousOn (fun p=>fderiv ℝ (stateCutoff T Q) (coneCutoffState F.flow zX p))
      (coneKernelInterior T) := by
    intro p hp
    exact ((contDiffAt_stateCutoff T Q (z:=coneCutoffState F.flow zX p)
      (sub_pos.mpr hp.2) (by simpa only [coneCutoffState,mem_sphere,dist_zero_right] using hp.1.2.1)).continuousAt_fderiv
        (by simp)).comp_continuousWithinAt (hz p hp)
  exact (hder.clm_apply hH).smul ((F.normalised_primitive_continuousOn zX).mono inter_subset_left)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_PhysicalBinPhaseSet
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

lemma measurableSet_coneMomentumFiber {V : ℝ→Vec} (hV : Measurable V) (B : ClosedConeBin) :
    MeasurableSet {p : ConeCoordinate×Vec | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))} := by
  have hn : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate×Vec=>velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate×Vec=>velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst.fst)
  exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
    ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
      (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))

lemma measurableSet_physicalBinPhaseSet {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (physicalBinPhaseSet V B J) :=
  ((measurableSet_physicalBinBase hV B hJ).preimage measurable_fst).inter
    (measurableSet_coneMomentumFiber hV B)

lemma physicalBinPhase_integral {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J)
    {g : TrianglePhase→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻p in physicalBinPhaseSet V B J,g p ∂trianglePhaseMeasure)=
      ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        g (z,v) ∂volume ∂physicalBinMeasure V B J := by
  classical
  rw [←lintegral_indicator (measurableSet_physicalBinPhaseSet hV B hJ)]
  rw [trianglePhaseMeasure,lintegral_prod _ (hg.indicator (measurableSet_physicalBinPhaseSet hV B hJ)).aemeasurable]
  rw [physicalBinMeasure,←lintegral_indicator (measurableSet_physicalBinBase hV B hJ)]
  apply lintegral_congr
  intro z
  by_cases hz : z∈physicalBinBase V B J
  · rw [indicator_of_mem hz,←lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
    apply lintegral_congr
    intro v
    by_cases hv : v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1))
    · rw [indicator_of_mem (show (z,v)∈physicalBinPhaseSet V B J from ⟨hz,hv⟩),indicator_of_mem hv]
    · rw [indicator_of_notMem (show (z,v)∉physicalBinPhaseSet V B J from fun h=>hv h.2),indicator_of_notMem hv]
  · rw [indicator_of_notMem hz]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun v=>indicator_of_notMem (show (z,v)∉physicalBinPhaseSet V B J from fun h=>hz h.1) _)

lemma stateCutoff_derivative_physical_cover {T w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (htT : t≤T) (hσ : σ∈Ico 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) {n : Sphere} {v : Vec} {N : ℕ}
    (hP : 1024*q v≤(2:ℝ)^N) (Q : Set (Fin 4→ℕ)) (H : CutoffState)
    (hd : fderiv ℝ (stateCutoff T Q) (t-σ,n.1,v,V t) H≠0) :
    ∃k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N},
      ((t,σ,n),v)∈physicalBinPhaseSet V (representativeClosedBin T w k) J := by
  have hr : 0<t-σ := sub_pos.mpr hσ.2
  have hrT : t-σ ≤ max 1 T := by linarith [hσ.1,le_max_right (1:ℝ) T]
  obtain ⟨j,hj,k,hk,hjp,hkp,_⟩ := stateCutoff_partial_boundary (z:=(t-σ,n.1,v,V t)) Q hr hrT (sphere_norm n) H hd
  have hnear := dyadicMultiFactor_positive_index_comparison hjp hkp
  have hjb : j∈dyadicSelectionBoundary Q :=
    ⟨⟨j,hj,fun i=>⟨Nat.le_add_right (j i) 2,Nat.le_add_right (j i) 2⟩⟩,⟨k,hk,fun i=>hnear i⟩⟩
  exact ⟨j,⟨hjb,physicalCutoff_positive_source_indices (sphere_norm n) hP hjp⟩,
    physicalCutoff_positive_closedBin ht ⟨hσ.1,hσ.2.le⟩ hband hjp⟩

lemma physicalBinPhase_cover_lintegral {V : ℝ→Vec} (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (T w : ℝ) (R : Set (Fin 4→ℕ))
    {g : TrianglePhase→ℝ≥0∞} (hg : Measurable g)
    (hcover : ∀p,g p≠0→∃k∈R,p∈physicalBinPhaseSet V (representativeClosedBin T w k) J) :
    (∫⁻p,g p ∂trianglePhaseMeasure)≤
      ∑'k : Fin 4→ℕ,R.indicator (fun k=>
        ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k)
          z.2.2.1 (velocity (V z.1)),g (z,v) ∂volume
          ∂physicalBinMeasure V (representativeClosedBin T w k) J) k := by
  classical
  let f : (Fin 4→ℕ)→TrianglePhase→ℝ≥0∞ := fun k=>
    if k∈R then (physicalBinPhaseSet V (representativeClosedBin T w k) J).indicator g else 0
  have hm (k : Fin 4→ℕ) : Measurable (f k) := by
    dsimp only [f]
    split_ifs
    · exact hg.indicator (measurableSet_physicalBinPhaseSet hV _ hJ)
    · exact measurable_const
  calc
    _ ≤ ∫⁻p,∑'k : Fin 4→ℕ,f k p ∂trianglePhaseMeasure := by
      apply lintegral_mono
      intro p
      by_cases hp : g p=0
      · rw [hp]; exact bot_le
      · obtain ⟨k,hk,hpk⟩ := hcover p hp
        calc
          _ = f k p := by simp only [f,ite_eq_left hk,indicator_of_mem hpk]
          _ ≤ _ := ENNReal.le_tsum (f := fun index => f index p) k
    _ = ∑'k : Fin 4→ℕ,∫⁻p,f k p ∂trianglePhaseMeasure := lintegral_tsum (fun k=>(hm k).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro k
      by_cases hk : k∈R
      · simp only [f,ite_eq_left hk,indicator_of_mem hk]
        rw [lintegral_indicator (measurableSet_physicalBinPhaseSet hV _ hJ),physicalBinPhase_integral hV _ hJ hg]
      · simp only [f,ite_eq_right hk,Pi.zero_apply,lintegral_zero,indicator_of_notMem hk]

lemma PhaseFlowOn.triangleConeKernel_measurable_interior {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T)) :
    Measurable (triangleConeKernel s F.flow zX T A) := by
  classical
  have hS := F.triangleKernelState_continuousOn zX
  have hSA := hA.comp hS (fun _ hp=>⟨triangleKernelState_mem _ _ hp,hp.2.2⟩)
  have hSf := hs.f_smooth.continuousOn.comp (hS.fst.snd.prodMk hS.snd.snd)
    (fun _ hp=>⟨(triangleKernelState_mem F.flow zX hp).1.2,mem_univ _⟩)
  have hV : ContinuousOn (fun p : TrianglePhase=>(F.flow zX p.1.1).2) (trianglePhaseDomain T) :=
    ((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn
      (fun _ hp=>Ioo_subset_Icc_self hp.1)).snd
  have hD : ContinuousOn (fun p : TrianglePhase=>1-dot p.1.2.2.1 (velocity (F.flow zX p.1.1).2))
      (trianglePhaseDomain T) := by
    simp only [dot_eq_inner]
    exact continuousOn_const.sub (continuous_fst.snd.snd.subtype_val.continuousOn.inner
      ((contDiff_velocity (k:=1)).continuous.comp_continuousOn hV))
  exact (hD.smul (hSf.smul hSA)).measurable_piecewise continuousOn_const
    (measurableSet_trianglePhaseDomain T)

lemma partialCutoffTriangle_of_mem {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    {Q : Set (Fin 4→ℕ)} {H : ConeKernelState→CutoffState} {W : ℝ→Vec→L[ℝ]Vec}
    {J : Set ℝ} {p : TrianglePhase} (ht : p.1.1∈J) :
    partialCutoffTriangle s α zX T Q H W J p =
      W p.1.1 (triangleConeKernel s α zX T (normalisedPartialCutoff α zX T Q H) p) :=
  indicator_of_mem (show p∈{p : TrianglePhase | p.1.1∈J} from ht) _

lemma partialCutoffTriangle_of_notMem {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    {Q : Set (Fin 4→ℕ)} {H : ConeKernelState→CutoffState} {W : ℝ→Vec→L[ℝ]Vec}
    {J : Set ℝ} {p : TrianglePhase} (ht : p.1.1∉J) :
    partialCutoffTriangle s α zX T Q H W J p = 0 :=
  indicator_of_notMem (show p∉{p : TrianglePhase | p.1.1∈J} from ht) _

lemma PhaseFlowOn.partialCutoffTriangle_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable (partialCutoffTriangle s F.flow zX T Q H W J) := by
  apply Measurable.indicator _ (hJ.preimage measurable_fst.fst)
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp
    ((hW.comp measurable_fst.fst).prodMk (F.triangleConeKernel_measurable_interior hs zX
      (F.normalisedPartialCutoff_continuousOn zX Q hH)))

lemma PhaseFlowOn.partialCutoffTriangle_support {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (H : ConeKernelState→CutoffState) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N)
    {p : TrianglePhase} (hp : partialCutoffTriangle s F.flow zX T Q H W J p≠0) :
    ∃k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N},
      p∈physicalBinPhaseSet (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J := by
  classical
  have ht : p.1.1∈J := by
    by_contra hc
    exact hp (partialCutoffTriangle_of_notMem hc)
  have hc : p∈trianglePhaseDomain T := by
    by_contra hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_notMem hh,map_zero]
  have hf : s.f ((triangleKernelState F.flow zX p).1.2,(triangleKernelState F.flow zX p).2.2)≠0 := by
    intro hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_mem hc,hh,
      zero_smul,smul_zero,map_zero]
  have hd : fderiv ℝ (stateCutoff T Q) (coneCutoffState F.flow zX (triangleKernelState F.flow zX p))
      (H (triangleKernelState F.flow zX p))≠0 := by
    intro hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_mem hc,
      normalisedPartialCutoff,hh,zero_smul,smul_zero,map_zero]
  have he : (prefixFlow F.flow T zX p.1.1).2=(F.flow zX p.1.1).2 := by
    simp only [prefixFlow,prefixClamp_eq (hJT ht)]
  have hdp : fderiv ℝ (stateCutoff T Q)
      (p.1.1-p.1.2.1,p.1.2.2.1,p.2,(prefixFlow F.flow T zX p.1.1).2)
      (H (triangleKernelState F.flow zX p))≠0 := by
    rw [he]
    exact hd
  exact stateCutoff_derivative_physical_cover ht (hJT ht).2 ⟨hc.2.1.le,hc.2.2⟩
    (by rw [he]; exact hband _ ht)
    (hP _ ⟨hc.2.1.le,hc.2.2.le.trans hc.1.2.le⟩ _ hf) Q _ hdp

lemma PhaseFlowOn.partialCutoffTriangle_boundary_sum_oai {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) :
    (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J p‖ ∂trianglePhaseMeasure)≤
      ∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator (fun k=>
        ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k)
          z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
          ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J (z,v)‖ ∂volume
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  apply physicalBinPhase_cover_lintegral hV hJ T w _
    (F.partialCutoffTriangle_measurable hs zX Q hH hW hJ).norm.ennreal_ofReal
  intro p hp
  apply F.partialCutoffTriangle_support zX Q H W hJT hband N hP
  intro hh
  exact hp (by rw [hh,norm_zero,ENNReal.ofReal_zero])

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum_oai := @OAI.RVM.PhaseFlowOn.partialCutoffTriangle_boundary_sum_oai
