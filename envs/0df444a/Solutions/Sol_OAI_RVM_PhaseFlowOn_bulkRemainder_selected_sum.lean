-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:45:00.866021+00:00
-- url     : https://prove2.me/submissions/9ff09c76-db6b-4303-8b36-ee3b5a3f33bf

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

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

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

lemma sum_dyadicMultiFactor {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x =
      ∏ i, (dyadicCut (x i)-dyadicCut ((2:ℝ)^N*x i)) := by
  classical
  unfold dyadicBox dyadicMultiFactor
  convert Finset.sum_prod_piFinset (Finset.range N) (fun i n => dyadicFactor n (x i)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [sum_dyadicFactor]

lemma sum_dyadicMultiFactor_eq_one {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ)
    (hx : ∀ i, x i≤1) (hN : ∀ i, 2≤(2:ℝ)^N*x i) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x=1 := by
  rw [sum_dyadicMultiFactor]
  simp only [dyadicCut_one (hx _),dyadicCut_zero (hN _),sub_zero,Finset.prod_const_one]

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
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.acceleration_continuousOn_closed {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContinuousOn (phaseAcceleration s.E s.B F.flow z) (Icc 0 T) := by
  have hf := F.continuousOn_time z
  have hp : ContinuousOn (fun t => (t,(F.flow z t).1)) (Icc 0 T) := continuousOn_id.prodMk hf.fst
  have hE : ContinuousOn (fun t => s.E (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.E_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hB : ContinuousOn (fun t => s.B (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.B_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hu : ContinuousOn (fun t => velocity (F.flow z t).2) (Icc 0 T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  have hK : ContinuousOn (fun t => s.E (t,(F.flow z t).1)+
      cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) (Icc 0 T) :=
    hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))
  exact (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp_continuousOn hf.snd).clm_apply hK

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
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma normalisedRemainder_eq {r : ℝ} (a u n b : Vec) (hr : r≠0) :
    normalisedRemainder r a u n b=r^2 • signedRemainder r a u n b := by
  simp only [normalisedRemainder,signedRemainder,smul_add,smul_smul]
  congr 2 <;> field_simp

lemma continuousOn_normalisedRemainder {Q : Type*} [TopologicalSpace Q]
    {r : Q→ℝ} {a u n b : Q→Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S) (hu : ContinuousOn u S)
    (hn : ContinuousOn n S) (hb : ContinuousOn b S)
    (hD : ∀p∈S,1-dot (n p) (a p)≠0) :
    ContinuousOn (fun p=>normalisedRemainder (r p) (a p) (u p) (n p) (b p)) S := by
  have hdot {f g : Q→Vec} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun p=>dot (f p) (g p)) S := by
    simpa only [dot_eq_inner] using hf.inner hg
  have hden : ContinuousOn (fun p=>1-dot (n p) (a p)) S :=
    continuousOn_const.sub (hdot hn ha)
  have hp : ContinuousOn (fun p=>signedPrimitive (a p) (u p) (n p)) S :=
    hu.sub (((continuousOn_const.sub (hdot ha hu)).div hden hD).smul hn)
  exact (((continuousOn_const.sub (hdot ha hu)).div (hden.pow 2)
    (fun p hp=>pow_ne_zero _ (hD p hp))).smul
      ((((continuousOn_const.sub (hdot ha ha)).div hden hD).smul hn).sub ha)).add
    (((hr.mul (hdot hb hp)).div (hden.pow 2) (fun p hp=>pow_ne_zero _ (hD p hp))).smul hn)

lemma PhaseFlowOn.normalised_remainder_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (fun p : ConeKernelState=>normalisedRemainder (p.1.1-p.1.2)
      (velocity (F.flow zX p.1.1).2) (velocity p.2.2.2) p.2.1
      (phaseAcceleration s.E s.B F.flow zX p.1.1)) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  have hb : ContinuousOn (fun p : ConeKernelState=>phaseAcceleration s.E s.B F.flow zX p.1.1)
      (coneKernelDomain T) := (F.acceleration_continuousOn_closed hs zX).comp
        continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)
  refine continuousOn_normalisedRemainder (continuous_fst.fst.sub continuous_fst.snd).continuousOn
    ha hu.continuousOn continuous_snd.fst.continuousOn hb ?_
  intro p hp
  exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

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

lemma small_primitive_acceleration_pairing {a u n b : Vec} {θ φ K : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 < φ) (hK : 0 ≤ K)
    (hD : φ^2/2 ≤ 1-dot n a) (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ)
    (hb : ‖b‖ ≤ K) (hbn : |dot b n| ≤ 20*φ*K) :
    |dot b (signedPrimitive a u n)| ≤ 964*θ*K := by
  have hDpos : 0 < 1-dot n a := lt_of_lt_of_le (by positivity) hD
  have hratio : |(1-dot n a-(1-dot a u))/(1-dot n a)| ≤ 48*θ/φ := by
    rw [abs_div,abs_of_pos hDpos,abs_sub_comm]
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 48*θ/φ)
    have hh : 48*θ/φ*(φ^2/2)=24*φ*θ := by field_simp; ring
    rw [hh] at hm
    exact he.trans hm
  rw [signedPrimitive_decomposition _ _ _ hDpos.ne',dot_add_right,dot_smul_right]
  calc
    _ ≤ |dot b (u-n)|+|(1-dot n a-(1-dot a u))/(1-dot n a)*dot b n| := abs_add_le _ _
    _ ≤ ‖b‖*‖u-n‖+|(1-dot n a-(1-dot a u))/(1-dot n a)| *|dot b n| := by
      rw [abs_mul]
      apply add_le_add _ le_rfl
      rw [dot_eq_inner]
      exact abs_real_inner_le_norm _ _
    _ ≤ K*(4*θ)+(48*θ/φ)*(20*φ*K) := by gcongr
    _ = _ := by field_simp; ring

lemma receiver_acceleration_bounds (w K n : Vec) {φ : ℝ}
    (hn : ‖n‖=1) (hφ : 0 ≤ φ) (hD : 1-dot n (velocity w) ≤ 8*φ^2) :
    ‖fderiv ℝ velocity w K‖ ≤ ‖K‖/q w ∧
    |dot (fderiv ℝ velocity w K) n| ≤ 4*φ*(‖K‖/q w) := by
  have hp : ‖velocityProjection (velocity w) n‖ ≤ 4*φ := by
    apply (norm_velocityProjection_normal _ _ (norm_velocity_lt_one w).le hn).trans
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have he : fderiv ℝ velocity w K=(q w)⁻¹ • velocityProjection (velocity w) K := by
    rw [fderiv_velocity_apply]
    rfl
  constructor
  · rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (q_pos w))]
    have hh := mul_le_mul_of_nonneg_left
      (velocityProjection_norm (velocity w) K (norm_velocity_lt_one w).le)
      (inv_pos.mpr (q_pos w)).le
    simpa only [div_eq_mul_inv,mul_comm] using hh
  · rw [he,dot_smul_left,abs_mul,abs_of_pos (inv_pos.mpr (q_pos w)),
      dot_comm (velocityProjection _ _) n,velocityProjection_dot_symm]
    calc
      _ ≤ (q w)⁻¹*(‖velocityProjection (velocity w) n‖*‖K‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (q_pos w)).le
        rw [dot_eq_inner]
        exact abs_real_inner_le_norm _ _
      _ ≤ (q w)⁻¹*((4*φ)*‖K‖) := by
        gcongr
        exact (inv_pos.mpr (q_pos w)).le
      _ = _ := by ring

lemma receiver_small_primitive_pairing (w K u n : Vec) {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 < φ)
    (hD : φ^2/2 ≤ 1-dot n (velocity w))
    (hDu : 1-dot n (velocity w) ≤ 8*φ^2)
    (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot (velocity w) u)-(1-dot n (velocity w))| ≤ 24*φ*θ) :
    |dot (fderiv ℝ velocity w K) (signedPrimitive (velocity w) u n)| ≤
      964*θ*(‖K‖/q w) := by
  have hb := receiver_acceleration_bounds w K n hn hφ.le hDu
  have hK : 0 ≤ ‖K‖/q w := div_nonneg (norm_nonneg _) (q_pos w).le
  apply small_primitive_acceleration_pairing hθ hφ hK hD hun he hb.1
  exact hb.2.trans (mul_le_mul_of_nonneg_right (by nlinarith) hK)

lemma receiver_bulk_vector_bound {w n : Vec} (hn : ‖n‖=1) :
    ‖((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • n-velocity w‖ ≤ 3 := by
  have hD : 0 < 1-dot n (velocity w) := cone_denom_pos w n hn
  have hnon : 0 ≤ 1-dot (velocity w) (velocity w) := by
    rw [dot_self]
    nlinarith [norm_velocity_lt_one w,norm_nonneg (velocity w)]
  have hfrac : |(1-dot (velocity w) (velocity w))/(1-dot n (velocity w))| ≤ 2 := by
    rw [abs_of_nonneg (div_nonneg hnon hD.le)]
    apply (div_le_iff₀ hD).mpr
    have hh := sq_nonneg ‖n-velocity w‖
    rw [norm_sub_sq_real,← dot_eq_inner,hn,one_pow] at hh
    rw [dot_self]
    linarith
  calc
    _ ≤ ‖((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • n‖+
        ‖velocity w‖ := norm_sub_le _ _
    _ ≤ 2+1 := by
      rw [norm_smul,Real.norm_eq_abs,hn,mul_one]
      exact add_le_add hfrac (norm_velocity_lt_one w).le
    _ = _ := by norm_num

lemma small_energy_ratio {a u n : Vec} {θ φ : ℝ}
    (_hθ : 0 ≤ θ) (hφ : 0 < φ) (hsmall : θ ≤ φ)
    (hD : φ^2/2 ≤ 1-dot n a)
    (he : |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ) :
    |(1-dot a u)/(1-dot n a)| ≤ 49 := by
  have hDp : 0<1-dot n a := lt_of_lt_of_le (by positivity) hD
  rw [abs_div,abs_of_pos hDp]
  apply (div_le_iff₀ hDp).mpr
  have hab : |1-dot a u| ≤ |(1-dot a u)-(1-dot n a)|+|1-dot n a| :=
    calc
      _ = |((1-dot a u)-(1-dot n a))+(1-dot n a)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  rw [abs_of_pos hDp] at hab
  have hm := mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤24*φ)
  nlinarith

lemma signedRemainder_physical_decomposition {r f : ℝ} {a u n b : Vec}
    (hr : r≠0) (hD : 1-dot n a≠0) :
    (f*(1-dot n a)) • signedRemainder r a u n b =
      (f/r^2*((1-dot a u)/(1-dot n a))) •
        (((1-dot a a)/(1-dot n a)) • n-a) +
      (f/r*(dot b (signedPrimitive a u n)/(1-dot n a))) • n := by
  ext i
  simp only [signedRemainder,PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma signedRemainder_small_norm {r f θ φ : ℝ} (w K u n : Vec)
    (hr : 0 < r) (hf : 0≤f) (hn : ‖n‖=1) (hθ : 0≤θ) (hφ : 0<φ)
    (hsmall : θ≤φ) (hD : φ^2/2≤1-dot n (velocity w))
    (hDu : 1-dot n (velocity w)≤8*φ^2) (hun : ‖u-n‖≤4*θ)
    (he : |(1-dot (velocity w) u)-(1-dot n (velocity w))|≤24*φ*θ) :
    ‖(f*(1-dot n (velocity w))) •
      signedRemainder r (velocity w) u n (fderiv ℝ velocity w K)‖ ≤
      147*f/r^2+1928*f*θ*(‖K‖/q w)/(r*φ^2) := by
  have hDp : 0<1-dot n (velocity w) := cone_denom_pos w n hn
  have hpair := receiver_small_primitive_pairing w K u n hn hθ hφ hD hDu hun he
  have hratio := small_energy_ratio hθ hφ hsmall hD he
  have hK : 0≤‖K‖/q w := div_nonneg (norm_nonneg _) (q_pos w).le
  have hpairD : |dot (fderiv ℝ velocity w K) (signedPrimitive (velocity w) u n)/
      (1-dot n (velocity w))| ≤ 1928*θ*(‖K‖/q w)/φ^2 := by
    rw [abs_div,abs_of_pos hDp]
    apply (div_le_iff₀ hDp).mpr
    have hm := mul_le_mul_of_nonneg_left hD
      (by positivity : 0≤1928*θ*(‖K‖/q w)/φ^2)
    have heq : 1928*θ*(‖K‖/q w)/φ^2*(φ^2/2)=964*θ*(‖K‖/q w) := by field_simp; ring
    rw [heq] at hm
    exact hpair.trans hm
  rw [signedRemainder_physical_decomposition hr.ne' hDp.ne']
  calc
    _ ≤ ‖(f/r^2*((1-dot (velocity w) u)/(1-dot n (velocity w)))) •
        (((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • n-velocity w)‖+
      ‖(f/r*(dot (fderiv ℝ velocity w K) (signedPrimitive (velocity w) u n)/(1-dot n (velocity w)))) • n‖ :=
      norm_add_le _ _
    _ ≤ (f/r^2*49)*3+(f/r*(1928*θ*(‖K‖/q w)/φ^2))*1 := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg hf (sq_nonneg r)),
        abs_of_nonneg (div_nonneg hf hr.le)]
      exact add_le_add (mul_le_mul
        (mul_le_mul_of_nonneg_left hratio (by positivity)) (receiver_bulk_vector_bound hn)
        (norm_nonneg _) (by positivity))
        (by rw [hn,mul_one,mul_one]; exact mul_le_mul_of_nonneg_left hpairD (by positivity))
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


lemma selectedDyadicCutoff_mem_unit {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hp : ∀ i,0<x i) (h1 : ∀ i,x i≤1) (S : Set (ι→ℕ)) :
    selectedDyadicCutoff S x∈Icc (0:ℝ) 1 := by
  classical
  obtain ⟨N,hN,he⟩ := selectedDyadicCutoff_curve_eventually
    (t:=0) (g:=fun i (_r : ℝ)=>x i) (fun _=>continuousAt_const) hp S
  have hh := he.eq_of_nhds
  change selectedDyadicCutoff S x = ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n x at hh
  rw [hh]
  refine ⟨Finset.sum_nonneg (fun n _=>dyadicMultiFactor_nonneg n x),?_⟩
  calc
    _ ≤ ∑ n∈dyadicBox ι N,dyadicMultiFactor n x := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun n _ _=>dyadicMultiFactor_nonneg n x)
    _ = 1 := sum_dyadicMultiFactor_eq_one N x h1 hN

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

lemma sourceRepresentative_mem_range {n : ℕ} {v : Vec} {P : ℝ}
    (h : DyadicBand n (1/q v)) (hP : 1024*q v≤P) :
    sourceRepresentative n∈Icc (64:ℝ) P := by
  have hh := dyadicBand_source_range h
  have hp : (1:ℝ)≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
  constructor
  · dsimp [sourceRepresentative]; linarith
  · nlinarith [q_pos v]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SelectedConeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma selectedDyadicCutoff_active {ι : Type*} [Fintype ι] {Q : Set (ι→ℕ)} {x : ι→ℝ}
    (h : selectedDyadicCutoff Q x≠0) : ∃k∈Q,0<dyadicMultiFactor k x := by
  classical
  by_contra hh
  push Not at hh
  apply h
  suffices hz : ∀k, Q.indicator (fun k=>dyadicMultiFactor k x) k=0 by
    simp only [selectedDyadicCutoff,hz,tsum_zero]
  intro k
  by_cases hk : k∈Q
  · rw [Set.indicator_of_mem hk]
    exact le_antisymm (hh k hk) (dyadicMultiFactor_nonneg _ _)
  · exact Set.indicator_of_notMem hk _

lemma PhaseFlowOn.selectedConeKernel_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T)) :
    ContinuousOn (selectedConeKernel F.flow zX T Q A) (coneKernelInterior T) := by
  have hcut : ContinuousOn (fun p=>stateCutoff T Q (coneCutoffState F.flow zX p))
      (coneKernelInterior T) := by
    intro p hp
    exact ((contDiffAt_stateCutoff T Q (sub_pos.mpr hp.2)
      (by simpa only [coneCutoffState,mem_sphere,dist_zero_right] using hp.1.2.1)).continuousAt).comp_continuousWithinAt
        (F.coneCutoffState_continuousOn zX p hp)
  exact hcut.smul hA

lemma PhaseFlowOn.selectedConeTriangle_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable (selectedConeTriangle s F.flow zX T Q A W J) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp
    (((hW.indicator hJ).comp measurable_fst.fst).prodMk
      (F.triangleConeKernel_measurable_interior hs zX (F.selectedConeKernel_continuousOn zX Q hA)))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_SelectedRemainderPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma selectedConeTriangle_norm_le {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec) (J : Set ℝ)
    (p : TrianglePhase) :
    ‖selectedConeTriangle s α zX T Q A W J p‖≤
      ‖J.indicator W p.1.1 (triangleConeKernel s α zX T A p)‖ := by
  classical
  by_cases hp : p∈trianglePhaseDomain T
  · have hr : 0<p.1.1-p.1.2.1 := sub_pos.mpr hp.2.2
    have hrT : p.1.1-p.1.2.1≤ max 1 T := by
      linarith only [hp.1.2,hp.2.1,le_max_right (1:ℝ) T]
    have hu := selectedDyadicCutoff_mem_unit
      (physicalCutoffCoordinates_pos (T:=T) (v:=p.2) (w:=(α zX p.1.1).2) (sphere_norm p.1.2.2) hr)
      (physicalCutoffCoordinates_le_one (T:=T) (sphere_norm p.1.2.2) hrT) Q
    have he : selectedConeTriangle s α zX T Q A W J p=
        stateCutoff T Q (p.1.1-p.1.2.1,p.1.2.2.1,p.2,(α zX p.1.1).2) •
          J.indicator W p.1.1 (triangleConeKernel s α zX T A p) := by
      simp only [selectedConeTriangle,triangleConeKernel,Set.indicator_of_mem hp,
        selectedConeKernel,coneCutoffState,triangleKernelState,map_smul]
      module
    rw [he,norm_smul,Real.norm_eq_abs]
    change |selectedDyadicCutoff Q _| * _ ≤ _
    rw [abs_of_nonneg hu.1]
    exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)).trans_eq (one_mul _)
  · simp only [selectedConeTriangle,triangleConeKernel,Set.indicator_of_notMem hp,map_zero]
    exact le_rfl

end RVM

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


lemma PhaseFlowOn.bulkRemainder_density {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (hw : 0<w)
    (Q : Set (Fin 4→ℕ)) {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16)
    {z : ConeCoordinate} (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J) :
    (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (remainderConeKernel s F.flow zX) W J (z,v)‖)≤
      ENNReal.ofReal 147*physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2+
      ENNReal.ofReal (15424*(cappedRepresentative (k 1)/(w*(cappedRepresentative (k 2))^2)))*
        (ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX z.1‖*ENNReal.ofReal (z.1-z.2.1)*
          physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
  let c := 15424*(cappedRepresentative (k 1)/(w*(cappedRepresentative (k 2))^2))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcoeff : 0≤147+c*‖prefixMomentumForce s F.flow T zX z.1‖*(z.1-z.2.1) := by positivity
  have hb : (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (remainderConeKernel s F.flow zX) W J (z,v)‖)≤
      ENNReal.ofReal (147+c*‖prefixMomentumForce s F.flow T zX z.1‖*(z.1-z.2.1))*
        physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2 := by
    unfold physicalBinDensity
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
    intro v hv
    rw [←ENNReal.ofReal_mul hcoeff]
    apply ENNReal.ofReal_le_ofReal
    have hcost {radius density theta phi speed : ℝ} {normal momentum receiver force : Vec}
        (hnormal : ‖normal‖=1) (hradius : 0 < radius) (hdensity : 0≤density)
        (htheta : 0<theta) (hphi : 0<phi) (hspeed : 0 < speed)
        (hsector : theta≤phi/16)
        (hdeficit : 1-dot normal (velocity momentum)∈Icc (theta^2/2) (8*theta^2))
        (hreceiver : 1-dot normal (velocity receiver)∈Icc (phi^2/2) (8*phi^2))
        (hquantum : speed/8≤q receiver) :
        ‖(density*(1-dot normal (velocity receiver))) •
          normalisedRemainder radius (velocity receiver) (velocity momentum) normal
            (fderiv ℝ velocity receiver force)‖≤
          147*density+15424*(theta/(speed*phi^2))*‖force‖*radius*density := by
      have hsector' : theta≤phi := by linarith
      have hnormalBound {input : Vec} {angle : ℝ} (hangle : 0≤angle)
          (hbound : 1-dot normal (velocity input)≤8*angle^2) :
          ‖velocity input-normal‖≤4*angle := by
        apply norm_sub_le_of_deficit (norm_velocity_lt_one input).le hnormal.le (by positivity)
        rw [dot_comm]
        nlinarith
      have hmomentum := hnormalBound htheta.le hdeficit.2
      have hreceiverNorm := hnormalBound hphi.le hreceiver.2
      have hdifference := small_deficit_difference hnormal htheta.le hphi.le hsector'
        (cone_denom_pos momentum normal hnormal).le hdeficit.2 hmomentum hreceiverNorm
      have hremainder := signedRemainder_small_norm receiver force (velocity momentum) normal
        hradius hdensity hnormal htheta.le hphi hsector' hreceiver.1 hreceiver.2
        hmomentum hdifference
      have hforce : ‖force‖/q receiver≤8*‖force‖/speed := by
        calc
          _≤‖force‖/(speed/8) := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hquantum
          _=_ := by ring
      rw [normalisedRemainder_eq _ _ _ _ hradius.ne',
        smul_comm (density*(1-dot normal (velocity receiver))),
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg radius)]
      calc
        _ ≤ radius^2*(147*density/radius^2+1928*density*theta*(‖force‖/q receiver)/(radius*phi^2)) :=
          mul_le_mul_of_nonneg_left hremainder (sq_nonneg radius)
        _ ≤ radius^2*(147*density/radius^2+1928*density*theta*(8*‖force‖/speed)/(radius*phi^2)) := by
          gcongr
        _=_ := by field_simp; ring
    have htime := hJT hz.1
    have hsourceTime : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans htime.2⟩
    have hdensity := hs.nonnegative _ hsourceTime
      ((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)
    by_cases hphase : (z,v)∈trianglePhaseDomain T
    · have hflow : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
        simp only [prefixFlow,prefixClamp_eq htime]
      have hforce : prefixMomentumForce s F.flow T zX z.1=
          (lorentzField s.E s.B (z.1,F.flow zX z.1)).2 := by
        simp only [prefixMomentumForce,hflow,prefixClamp_eq htime]
      have hdeficit : 1-dot z.2.2.1 (velocity (F.flow zX z.1).2)∈
          Icc ((cappedRepresentative (k 2))^2/2) (8*(cappedRepresentative (k 2))^2) := by
        simpa only [hflow,representativeClosedBin] using hz.2.2.2.2
      have hquantum : w/8≤q (F.flow zX z.1).2 := by
        simpa only [hflow,representativeClosedBin] using hz.2.2.2.1.1
      dsimp only
      rw [hflow] at hv ⊢
      rw [hforce]
      apply (selectedConeTriangle_norm_le Q (remainderConeKernel s F.flow zX) W J (z,v)).trans
      rw [indicator_of_mem hz.1]
      apply ((W z.1).le_opNorm _).trans
      apply (mul_le_mul_of_nonneg_right (hW _ hz.1) (norm_nonneg _)).trans
      rw [one_mul,triangleConeKernel,indicator_of_mem hphase,smul_smul,mul_comm]
      have hbound := hcost (force := (lorentzField s.E s.B (z.1,F.flow zX z.1)).2)
        (sphere_norm z.2.2) (sub_pos.mpr hphase.2.2)
        (by simpa only [hflow] using hdensity) hθ hφ hw hsmall hv.2.1 hdeficit hquantum
      simp only [triangleKernelState,remainderConeKernel,phaseAcceleration,lorentzField,lorentzPhase] at hbound ⊢
      convert hbound using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [c]
      ring
    · simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem hphase,map_zero,norm_zero]
      positivity
  apply hb.trans_eq
  rw [ENNReal.ofReal_add (by norm_num) (by positivity),add_mul,
    ENNReal.ofReal_mul (mul_nonneg hc (norm_nonneg _)),ENNReal.ofReal_mul hc]
  simp only [c,mul_assoc]

lemma PhaseFlowOn.bulkRemainder_bin_integral {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
    (Q : Set (Fin 4→ℕ)) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈Icc a b,‖W t‖≤1)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q
        (remainderConeKernel s F.flow zX) W (Icc a b) (z,v)‖
      ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal 147*representativeCentralCost s F zX w k a b+
      ENNReal.ofReal 15424*representativeReceiverCost s F zX w k a b
        (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hX : Measurable (fun t=>(prefixFlow F.flow T zX t).1) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).fst.measurable
  have hN := physicalBinDensity_aemeasurable hs hT hX hV (representativeClosedBin T w k)
    measurableSet_Icc (Icc_subset_Icc ha hb)
  have hcost := fun z hz=>F.bulkRemainder_density hs zX hw Q (Icc_subset_Icc ha hb) W hW k hsmall (z:=z) hz
  have hbnd := setLIntegral_mono' (μ:=volume.prod (volume.prod sphereMeasure)) (measurableSet_physicalBinBase hV (representativeClosedBin T w k) measurableSet_Icc) hcost
  apply hbnd.trans_eq
  unfold physicalBinMeasure at hN
  rw [lintegral_add_left' (hN.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold representativeCentralCost representativeReceiverCost
  dsimp only
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤15424),mul_assoc]
  rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SpatialEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma physicalCutoff_positive_source_floor {T r : ℝ} {v W n : Vec} {k : Fin 4→ℕ}
    (hn : ‖n‖=1)
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v W)) :
    1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1) := by
  have hb := dyadicMultiFactor_positive_bands hk
  have hq := (dyadicBand_source_range (hb 0)).2
  have hθ := (dyadicBand_capped_range (hb 1)).2
  have hl := source_angle_coordinate_lower v n hn
  change Real.sqrt ((1-dot n (velocity v))/2)≤2*cappedRepresentative (k 1) at hθ
  have hp : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hθ0 := cappedRepresentative_pos (k 1)
  have hm := mul_le_mul hq hθ (Real.sqrt_nonneg _) (by positivity : 0≤ sourceRepresentative (k 0)/32)
  apply (div_le_iff₀ hp).mpr
  nlinarith

lemma bulkSelection_positive_smallSector {T P M A w I r : ℝ} {v W n : Vec} {k : Fin 4→ℕ}
    (hn : ‖n‖=1) (hP : 1024*q v≤P) (hsel : k∈bulkSelection P M A w I)
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v W)) :
    k∈representativeSmallSector P := by
  refine ⟨(sourceRepresentative_mem_range (dyadicMultiFactor_positive_bands hk 0) hP).2,
    physicalCutoff_positive_source_floor hn hk,?_⟩
  have hθ := hsel.1
  have hφ := cappedRepresentative_pos (k 2)
  linarith


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma PhaseFlowOn.bulkRemainder_selected_sum_oai {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
    {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1) :
    (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
      (remainderConeKernel s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal 147*(∑'k : Fin 4→ℕ,(centralIndexSector P).indicator
        (fun k=>representativeCentralCost s F zX w k a b) k)+
      ENNReal.ofReal 15424*(∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
        (fun k=>representativeReceiverCost s F zX w k a b (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) k) := by
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  have hV : Measurable (fun time=>(prefixFlow F.flow T zX time).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hcover : ∀point,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T
      (bulkSelection P M A w I) (remainderConeKernel s F.flow zX) W (Icc a b) point‖≠0→
      ∃index∈Q,point∈physicalBinPhaseSet (fun time=>(prefixFlow F.flow T zX time).2)
        (representativeClosedBin T w index) (Icc a b) := by
    intro point hnonzero
    have htriangle : selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
        (remainderConeKernel s F.flow zX) W (Icc a b) point≠0 := by
      intro hzero
      exact hnonzero (by rw [hzero,norm_zero,ENNReal.ofReal_zero])
    have htime : point.1.1∈Icc a b := by
      by_contra houtside
      exact htriangle (by simp only [selectedConeTriangle,indicator_of_notMem houtside,zero_apply])
    have hdomain : point∈trianglePhaseDomain T := by
      by_contra houtside
      exact htriangle (by simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem houtside,map_zero])
    have hdensity : s.f ((triangleKernelState F.flow zX point).1.2,
        (triangleKernelState F.flow zX point).2.2)≠0 := by
      intro hzero
      apply htriangle
      simp only [selectedConeTriangle,triangleConeKernel,indicator_of_mem hdomain,hzero,
        zero_smul,smul_zero,map_zero]
    have hcutoff : stateCutoff T (bulkSelection P M A w I)
        (coneCutoffState F.flow zX (triangleKernelState F.flow zX point))≠0 := by
      intro hzero
      apply htriangle
      simp only [selectedConeTriangle,triangleConeKernel,indicator_of_mem hdomain,selectedConeKernel,
        hzero,zero_smul,smul_zero,map_zero]
    have hprefix : (prefixFlow F.flow T zX point.1.1).2=(F.flow zX point.1.1).2 := by
      simp only [prefixFlow,prefixClamp_eq (Icc_subset_Icc ha hb htime)]
    change stateCutoff T (bulkSelection P M A w I)
      (point.1.1-point.1.2.1,point.1.2.2.1,point.2,(F.flow zX point.1.1).2)≠0 at hcutoff
    rw [←hprefix] at hcutoff
    obtain ⟨index,hindex,hpositive⟩ := selectedDyadicCutoff_active hcutoff
    have hmomentum : 1024*q point.2≤P := hP point.1.2.1
      ⟨hdomain.2.1.le,hdomain.2.2.le.trans hdomain.1.2.le⟩
      ((triangleKernelState F.flow zX point).2.2) hdensity
    refine ⟨index,⟨bulkSelection_positive_smallSector (sphere_norm point.1.2.2)
      hmomentum hindex hpositive,hindex.2⟩,?_⟩
    exact physicalCutoff_positive_closedBin htime ⟨hdomain.2.1.le,hdomain.2.2.le⟩
      (by rw [hprefix]; exact hband _ htime) hpositive
  apply (physicalBinPhase_cover_lintegral hV measurableSet_Icc T w Q
    (F.selectedConeTriangle_measurable hs zX (bulkSelection P M A w I)
      ((F.normalised_remainder_continuousOn hs zX).mono inter_subset_left)
      hW measurableSet_Icc).norm.ennreal_ofReal hcover).trans
  rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left,←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈Q
  · rw [indicator_of_mem hk,indicator_of_mem hk,
      indicator_of_mem (representativeSmallSector_subset_centralIndexSector P hk.1)]
    exact F.bulkRemainder_bin_integral hs hT zX hw _ ha hb W hW1 k hk.1.2.2
  · rw [indicator_of_notMem hk]
    exact bot_le



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum_oai := @OAI.RVM.PhaseFlowOn.bulkRemainder_selected_sum_oai
