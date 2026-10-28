-- Prove2me | solution 1 for OAI.RVM.Admissible.exists_stable_direction_partition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:02:35.65187+00:00
-- url     : https://prove2.me/submissions/25bf12d4-0914-49cf-8430-f9a6598e60a5

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_exists_bounded_direction_partition

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_IncrementBootstrap
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

lemma norm_fderiv_q_le (v : Vec) : ‖fderiv ℝ q v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  rw [fderiv_q_apply,Real.norm_eq_abs,one_mul]
  calc
    _ ≤ ‖velocity v‖ * ‖h‖ := by simpa only [dot_eq_inner] using abs_real_inner_le_norm (velocity v) h
    _ ≤ ‖h‖ := mul_le_of_le_one_left (norm_nonneg h) (norm_velocity_lt_one v).le

lemma q_lipschitz (v w : Vec) : |q w-q v| ≤ ‖w-v‖ := by
  have h := (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => contDiff_q.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) x)
    (fun x _ => norm_fderiv_q_le x) (mem_univ v) (mem_univ w)
  simpa only [Real.norm_eq_abs,one_mul] using h

lemma norm_relativistic_projection_le (u h : Vec) (hu : ‖u‖ ≤ 1) :
    ‖h-dot u h • u‖ ≤ ‖h‖ := by
  have hsq : ‖h-dot u h • u‖^2 = ‖h‖^2-2*(dot u h)^2+(dot u h)^2*‖u‖^2 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← dot_eq_inner,
      dot_smul_right,dot_comm h u]
    ring
  have hu2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hh := mul_le_mul_of_nonneg_left hu2 (sq_nonneg (dot u h))
  nlinarith [norm_nonneg (h-dot u h • u),norm_nonneg h,sq_nonneg (dot u h)]

lemma norm_fderiv_velocity_le (v : Vec) : ‖fderiv ℝ velocity v‖ ≤ (q v)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (q_pos v).le)
  intro h
  rw [fderiv_velocity_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (q_pos v))]
  exact mul_le_mul_of_nonneg_left
    (norm_relativistic_projection_le _ _ (norm_velocity_lt_one v).le)
    (inv_nonneg.mpr (q_pos v).le)

lemma velocity_local_lipschitz (v w : Vec) (hvw : ‖w-v‖ ≤ q v/2) :
    ‖velocity w-velocity v‖ ≤ (2/q v)*‖w-v‖ := by
  apply (convex_closedBall v (q v/2)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) x)
    (fun x hx => ?_) (mem_closedBall_self (div_nonneg (q_pos v).le (by norm_num)))
    (by simpa only [mem_closedBall,dist_eq_norm] using hvw)
  have hb : q v/2 ≤ q x := by
    have h := q_lipschitz x v
    rw [norm_sub_rev] at h
    have hx' : ‖x-v‖ ≤ q v/2 := hx
    have hh := (le_abs_self (q v-q x)).trans h
    linarith
  calc
    _ ≤ (q x)⁻¹ := norm_fderiv_velocity_le x
    _ ≤ (q v/2)⁻¹ := inv_anti₀ (half_pos (q_pos v)) hb
    _ = 2/q v := by field_simp

lemma continuous_barrier {f : ℝ → ℝ} {a b R C : ℝ} (_hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < R) (hCR : C < R)
    (hstop : ∀ t ∈ Icc a b, (∀ u ∈ Icc a t, f u ≤ R) → f t ≤ C) :
    ∀ t ∈ Icc a b, f t ≤ C := by
  have hlt : ∀ t ∈ Icc a b, f t < R := by
    intro t ht
    by_contra ht'
    have hRt : R ≤ f t := le_of_not_gt ht'
    obtain ⟨x,hx,hfx⟩ := intermediate_value_Icc ht.1 (hf.mono (Icc_subset_Icc_right ht.2)) ⟨ha.le,hRt⟩
    let S : Set ℝ := Icc a b ∩ f ⁻¹' {R}
    have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
    obtain ⟨m,hm,hmin⟩ := hS.exists_isMinOn ⟨x,⟨⟨hx.1,hx.2.trans ht.2⟩,hfx⟩⟩ continuousOn_id
    have hall : ∀ u ∈ Icc a m, f u ≤ R := by
      intro u hu
      by_contra hu'
      have hRu : R < f u := lt_of_not_ge hu'
      obtain ⟨y,hy,hey⟩ := intermediate_value_Icc hu.1
        (hf.mono (Icc_subset_Icc_right (hu.2.trans hm.1.2))) ⟨ha.le,hRu.le⟩
      have hyS : y ∈ S := ⟨⟨hy.1,hy.2.trans (hu.2.trans hm.1.2)⟩,hey⟩
      have hmu : m ≤ u := (hmin hyS).trans hy.2
      have he : u=m := le_antisymm hu.2 hmu
      have hfm : f m=R := hm.2
      rw [he,hfm] at hRu
      exact (lt_irrefl _ hRu)
    have hb := hstop m hm.1 hall
    have hfm : f m=R := hm.2
    rw [hfm] at hb
    exact (not_le_of_gt hCR) hb
  intro t ht
  exact hstop t ht (fun u hu => (hlt u ⟨hu.1,hu.2.trans ht.2⟩).le)

lemma momentum_stopping {V : ℝ → Vec} {a b ε : ℝ} (hab : a ≤ b)
    (hV : ContinuousOn V (Icc a b)) (hε : ε < q (V a)/2)
    (hb : ∀ t ∈ Icc a b, (∀ u ∈ Icc a t,
      q (V a)/2 ≤ q (V u) ∧ q (V u) ≤ 2*q (V a)) → ‖V t-V a‖ ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V a‖ ≤ ε ∧
      q (V a)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V a) := by
  have hband (u : ℝ) (hu : ‖V u-V a‖ ≤ q (V a)/2) :
      q (V a)/2 ≤ q (V u) ∧ q (V u) ≤ 2*q (V a) := by
    have h := (q_lipschitz (V a) (V u)).trans hu
    rw [abs_le] at h
    constructor <;> linarith [q_pos (V a)]
  have hbound := continuous_barrier hab ((hV.sub continuousOn_const).norm)
    (by simpa only [Pi.sub_apply,sub_self,norm_zero] using (half_pos (q_pos (V a)))) hε
    (fun t ht hu => hb t ht (fun u hu' => hband u (hu u hu')))
  intro t ht
  exact ⟨hbound t ht,hband t ((hbound t ht).trans hε.le)⟩

lemma one_le_q (v : Vec) : 1 ≤ q v := by
  have := q_sq v
  have := q_pos v
  nlinarith [sq_nonneg ‖v‖]

lemma IncrementBootstrap.stopped_forward {V : ℝ → Vec} {T M A P L a b ε : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hV : ContinuousOn V (Icc a b)) (hM : 0 ≤ M) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hε : ε < q (V a)/2)
    (hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V a) ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V a‖ ≤ ε ∧
      q (V a)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V a) := by
  obtain ⟨n,hnlo,hnhi⟩ := exists_nat_pow_near (one_le_q (V a)) (by norm_num : (1 : ℝ)<2)
  have hn : 0 < (2 : ℝ)^n := by positivity
  have hq : q (V a) ≤ 2*(2 : ℝ)^n := by
    rw [pow_succ] at hnhi
    nlinarith
  apply momentum_stopping hab hV hε
  intro t ht htband
  have hta := ht.1
  have htb := ht.2
  have hqa := q_pos (V a)
  have hband : ∀ u ∈ Icc a t, (2 : ℝ)^n/8 ≤ q (V u) ∧ q (V u) ≤ 8*(2 : ℝ)^n := by
    intro u hu
    have hu' := htband u hu
    constructor <;> nlinarith
  have Ht := H n a t ha ht.1 (ht.2.trans hb) hband
  have hrat : 1/(2 : ℝ)^n ≤ 2/q (V a) := by
    apply (div_le_div_iff₀ hn (q_pos (V a))).mpr
    nlinarith
  have hfirst : M*P*Real.sqrt (t-a) ≤ M*P*Real.sqrt (b-a) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (mul_nonneg hM hP)
  have hsecond : A*(t-a)*(P^2*L/(2 : ℝ)^n) ≤ 2*A*(b-a)*P^2*L/q (V a) := by
    calc
      _ = (A*(t-a)*P^2*L)*(1/(2 : ℝ)^n) := by ring
      _ ≤ (A*(t-a)*P^2*L)*(2/q (V a)) :=
        mul_le_mul_of_nonneg_left hrat (by positivity)
      _ ≤ (A*(b-a)*P^2*L)*(2/q (V a)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA) (sq_nonneg P)) hL
      _ = _ := by ring
  exact (Ht.trans (add_le_add hfirst hsecond)).trans hstep

lemma IncrementBootstrap.velocity_stopped_forward {V : ℝ → Vec} {T M A P L a b ε : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hV : ContinuousOn V (Icc a b)) (hM : 0 ≤ M) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hε : ε < q (V a)/2)
    (hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V a) ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V a‖ ≤ ε ∧
      ‖velocity (V t)-velocity (V a)‖ ≤ 2*ε/q (V a) ∧
      q (V a)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V a) := by
  intro t ht
  have hqa := q_pos (V a)
  have hs := H.stopped_forward ha hab hb hV hM hA hP hL hε hstep t ht
  refine ⟨hs.1,?_,hs.2⟩
  calc
    _ ≤ (2/q (V a))*‖V t-V a‖ := velocity_local_lipschitz _ _ (hs.1.trans hε.le)
    _ ≤ (2/q (V a))*ε := mul_le_mul_of_nonneg_left hs.1 (by positivity)
    _ = _ := by ring
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalElectricKernel
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
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma IncrementBootstrap.reflect {V : ℝ → Vec} {T M A P L : ℝ}
    (H : IncrementBootstrap V T M A P L) :
    IncrementBootstrap (fun t => V (T-t)) T M A P L := by
  intro n a b ha hab hb hband
  have h := H n (T-b) (T-a) (by linarith) (by linarith) (by linarith)
    (by
      intro t ht
      have hh := hband (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
      simpa only [sub_sub_cancel] using hh)
  have he : T-(T-a)=a := by ring
  have he' : T-(T-b)=b := by ring
  have hd : (T-a)-(T-b)=b-a := by ring
  simpa only [he,he',hd,norm_sub_rev] using h

lemma IncrementBootstrap.velocity_stopped_backward {V : ℝ → Vec} {T M A P L a b ε : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hV : ContinuousOn V (Icc a b)) (hM : 0 ≤ M) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hε : ε < q (V b)/2)
    (hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V b) ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V b‖ ≤ ε ∧
      ‖velocity (V t)-velocity (V b)‖ ≤ 2*ε/q (V b) ∧
      q (V b)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V b) := by
  have he : T-(T-b)=b := by ring
  have hd : (T-a)-(T-b)=b-a := by ring
  have hcont : ContinuousOn (fun t => V (T-t)) (Icc (T-b) (T-a)) :=
    hV.comp (continuous_const.sub continuous_id).continuousOn
      (fun t ht => ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  have hh := H.reflect.velocity_stopped_forward (a:=T-b) (b:=T-a)
    (by linarith) (by linarith) (by linarith) hcont hM hA hP hL
    (by simpa only [he] using hε) (by simpa only [he,hd] using hstep)
  intro t ht
  have hht := hh (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have het : T-(T-t)=t := by ring
  simpa only [he,het] using hht

lemma stopping_modulus_mono {M A P L q l l' : ℝ}
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L) (hq : 0≤q) (hll : l≤l') :
    M*P*Real.sqrt l+2*A*l*P^2*L/q ≤
      M*P*Real.sqrt l'+2*A*l'*P^2*L/q := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hll) (mul_nonneg hM hP)
  · apply div_le_div_of_nonneg_right _ hq
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hll (by positivity))
        (sq_nonneg P)) hL

lemma IncrementBootstrap.velocity_stopped_about {V : ℝ → Vec} {T M A P L a b r ε : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0 ≤ a) (hb : b ≤ T)
    (hr : r ∈ Icc a b) (hV : ContinuousOn V (Icc a b))
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hε : ε < q (V r)/2)
    (hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V r) ≤ ε) :
    ∀ t ∈ Icc a b, ‖V t-V r‖ ≤ ε ∧
      ‖velocity (V t)-velocity (V r)‖ ≤ 2*ε/q (V r) ∧
      q (V r)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V r) := by
  intro t ht
  by_cases htr : r≤t
  · apply H.velocity_stopped_forward (ha.trans hr.1) hr.2 hb
      (hV.mono (Icc_subset_Icc hr.1 le_rfl)) hM hA hP hL hε
      ((stopping_modulus_mono hM hA hP hL (q_pos (V r)).le (by linarith [hr.1])).trans hstep)
      t ⟨htr,ht.2⟩
  · apply H.velocity_stopped_backward ha hr.1 (hr.2.trans hb)
      (hV.mono (Icc_subset_Icc le_rfl hr.2)) hM hA hP hL hε
      ((stopping_modulus_mono hM hA hP hL (q_pos (V r)).le (by linarith [hr.2])).trans hstep)
      t ⟨ht.1,le_of_not_ge htr⟩

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

lemma stopping_modulus_on_stability_scale {M A P L massScale ang C ℓ Q : ℝ}
    (hM : 0  <  M) (hA : 0  ≤  A) (hP : 0  <  P) (hL : 0  ≤  L)
    (hm : 0  <  massScale) (hom : 0  <  ang) (hC : 0  <  C) (hℓ : 0  ≤  ℓ) (hQ : 0  <  Q)
    (hlen : ℓ  ≤  (C*(P/massScale)*(M/ang+Real.sqrt (A*L/ang)))⁻¹^2) :
    M*P*Real.sqrt ℓ+2*A*ℓ*P^2*L/Q  ≤
      massScale*ang/C+2*massScale^2*ang/(C^2*Q) :=  by
  let R :=  C*(P/massScale)*(M/ang+Real.sqrt (A*L/ang))
  have hR : 0  <  R :=  mul_pos (mul_pos hC (div_pos hP hm))
    (add_pos_of_pos_of_nonneg (div_pos hM hom) (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt ℓ ≤ R⁻¹ :=  by
    calc
      _  ≤  Real.sqrt (R⁻¹^2) :=  Real.sqrt_le_sqrt hlen
      _  =  _ :=  Real.sqrt_sq (inv_nonneg.mpr hR.le)
  have hfirst : M*P*R⁻¹ ≤ massScale*ang/C :=  by
    rw [← div_eq_mul_inv,div_le_div_iff₀ hR hC]
    have he : massScale*ang*R = M*P*C+massScale*ang*(C*(P/massScale))*Real.sqrt (A*L/ang) :=  by
      dsimp [R]
      field_simp
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  have hs0 : 0  ≤  A*L/ang :=  by positivity
  have hs : C*(P/massScale)*Real.sqrt (A*L/ang) ≤ R :=  by
    dsimp [R]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (div_nonneg hM.le hom.le)) (by positivity)
  have hs2 := (sq_le_sq₀ (by positivity : 0 ≤ C*(P/massScale)*Real.sqrt (A*L/ang)) hR.le).mpr hs
  rw [mul_pow,Real.sq_sqrt hs0] at hs2
  have hlen' : ℓ*R^2 ≤ 1 :=  by
    change ℓ ≤ R⁻¹^2 at hlen
    have hh :=  mul_le_mul_of_nonneg_right hlen (sq_nonneg R)
    simpa only [← mul_pow,inv_mul_cancel₀ hR.ne',one_pow] using hh
  have hproduct : ℓ*(C*(P/massScale))^2*(A*L/ang) ≤ 1 :=  by
    calc
      _  =  ℓ*((C*(P/massScale))^2*(A*L/ang)) :=  by ring
      _  ≤  ℓ*R^2 :=  mul_le_mul_of_nonneg_left hs2 hℓ
      _  ≤  1 :=  hlen'
  have hbase : A*ℓ*P^2*L ≤ massScale^2*ang/C^2 :=  by
    rw [le_div_iff₀ (sq_pos_of_pos hC)]
    have hh :=  mul_le_mul_of_nonneg_right hproduct (by positivity : 0  ≤  massScale^2*ang)
    have he : (ℓ*(C*(P/massScale))^2*(A*L/ang))*(massScale^2*ang) = (A*ℓ*P^2*L)*C^2 :=  by
      field_simp
    simpa only [he,one_mul] using hh
  apply add_le_add ((mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hM.le hP.le)).trans hfirst)
  have hh :=  mul_le_mul_of_nonneg_left hbase (show 0  ≤  2/Q by positivity)
  convert hh using 1  <;>  ring

lemma IncrementBootstrap.velocity_stability_scale {V : ℝ → Vec}
    {T M A P L a b r massScale ang C : ℝ}
    (H : IncrementBootstrap V T M A P L) (ha : 0  ≤  a) (hb : b ≤ T)
    (hr : r∈Icc a b) (hV : ContinuousOn V (Icc a b))
    (hM : 0  <  M) (hA : 0  ≤  A) (hP : 0  <  P) (hL : 0  ≤  L)
    (hm : 0  <  massScale) (hom : 0  <  ang) (hom1 : ang ≤ 1) (hC : 128 ≤ C)
    (hmq : massScale ≤ q (V r))
    (hlen : b-a ≤ (C*(P/massScale)*(M/ang+Real.sqrt (A*L/ang)))⁻¹^2) :
    ∀ t∈Icc a b, ‖V t-V r‖ ≤ massScale*ang/64 ∧
      ‖velocity (V t)-velocity (V r)‖ ≤ ang/32 ∧
      q (V r)/2 ≤ q (V t) ∧ q (V t) ≤ 2*q (V r) :=  by
  have hC0 : 0  <  C :=  by linarith
  have hε : massScale*ang/64 < q (V r)/2 :=  by
    have hh :=  mul_le_mul_of_nonneg_left hom1 hm.le
    nlinarith [q_pos (V r)]
  have hst :=  stopping_modulus_on_stability_scale hM hA hP hL hm hom hC0
    (sub_nonneg.mpr (hr.1.trans hr.2)) (q_pos (V r)) hlen
  have he₁ : massScale*ang/C ≤ massScale*ang/128 :=  div_le_div_of_nonneg_left (by positivity) (by norm_num) hC
  have he₂ : 2*massScale^2*ang/(C^2*q (V r)) ≤ massScale*ang/128 :=  by
    rw [div_le_div_iff₀ (mul_pos (sq_pos_of_pos hC0) (q_pos _)) (by norm_num : (0:ℝ) < 128)]
    have hC2 : (256:ℝ) ≤ C^2 :=  by nlinarith
    have hh :=  mul_le_mul_of_nonneg_left hmq (sq_nonneg C)
    have hh' : 256*massScale ≤ C^2*q (V r) :=
      (mul_le_mul_of_nonneg_right hC2 hm.le).trans hh
    have hfinal :=  mul_le_mul_of_nonneg_left hh' (by positivity : 0  ≤  massScale*ang)
    nlinarith
  have hstep : M*P*Real.sqrt (b-a)+2*A*(b-a)*P^2*L/q (V r) ≤ massScale*ang/64 :=  by
    linarith
  intro t ht
  obtain ⟨hg,hu,hq⟩ :=  H.velocity_stopped_about ha hb hr hV hM.le hA hP.le hL hε hstep t ht
  refine ⟨hg,hu.trans ?_,hq⟩
  rw [div_le_iff₀ (q_pos _)]
  have hh :=  mul_le_mul_of_nonneg_right hmq (show 0  ≤  ang/32 by positivity)
  nlinarith

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

lemma norm_momentum_of_high_band {v : Vec} {w : ℝ} (hw : 16≤w) (hq : w/8≤q v) :
    w/16≤‖v‖ := by
  have hqn := q_pos v
  have hn := norm_nonneg v
  have hqs := q_sq v
  nlinarith [sq_nonneg (q v-w/8),sq_nonneg (‖v‖-w/16)]

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


open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma eventually_direction_absorption (C : ℝ) :
    ∀ᶠ P : ℝ in atTop, 1≤P ∧ 1≤Real.log (2+P) ∧
      ∀ w δ : ℝ, P^(3/5:ℝ)≤w → w^(-3/5:ℝ)≤δ →
        1≤w ∧ 16≤w ∧ P≤w^2 ∧ Real.log (2+P)≤Real.sqrt w ∧
          4*C*(Real.log (2+P))^2≤w*δ := by
  have ht (k : ℕ) (ε : ℝ) (hε : 0<ε) (D : ℝ) :
      ∀ᶠ P : ℝ in atTop, D*(Real.log (2+P))^k≤P^ε := by
    have ho := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hε).const_mul_left (D*2^k)
    filter_upwards [ho.bound (by norm_num : (0:ℝ)<1),eventually_ge_atTop (2:ℝ)] with P hp hP
    have hp0 : 0<P := by linarith
    have hlog : 0≤Real.log P := Real.log_nonneg (by linarith)
    have hlog2nonneg : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
    have hlog2 : Real.log (2+P)≤2*Real.log P := by
      calc
        _≤Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
        _=_ := by rw [Real.log_pow]; norm_num
    have hbo : |D*2^k| * (Real.log P)^k≤P^ε := by
      simpa only [Real.norm_eq_abs,Real.rpow_natCast,abs_mul,abs_of_nonneg (pow_nonneg hlog _),
        one_mul,abs_of_pos (Real.rpow_pos_of_pos hp0 _)] using hp
    calc
      D*(Real.log (2+P))^k≤|D| * (Real.log (2+P))^k := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _≤|D| * (2*Real.log P)^k := by gcongr
      _=|D*2^k| * (Real.log P)^k := by rw [mul_pow,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤2^k)]; ring
      _≤_ := hbo
  filter_upwards [ht 1 (3/10) (by norm_num) 1,ht 2 (6/25) (by norm_num) (4*C),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/5)).eventually_ge_atTop 16,
    (Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop tendsto_id)).eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℝ)] with P hroot hcharge h16 hL hP
  refine ⟨hP,hL,?_⟩
  intro w δ hw hδ
  have hp0 := zero_lt_one.trans_le hP
  have hw16 := h16.trans hw
  have hw1 : 1≤w := by linarith
  have hw0 := zero_lt_one.trans_le hw1
  have hsq : P≤w^2 := by
    calc
      P = P^(1:ℝ) := (Real.rpow_one P).symm
      _≤P^(6/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _=(P^(3/5:ℝ))^2 := by rw [←Real.rpow_natCast,←Real.rpow_mul hp0.le]; norm_num
      _≤w^2 := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hw _
  have hs : Real.log (2+P)≤Real.sqrt w := by
    simp only [pow_one,one_mul] at hroot
    apply hroot.trans
    rw [Real.sqrt_eq_rpow]
    calc
      P^(3/10:ℝ) = (P^(3/5:ℝ))^(1/2:ℝ) := by rw [←Real.rpow_mul hp0.le]; norm_num
      _≤w^(1/2:ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hp0.le _) hw (by norm_num)
  refine ⟨hw1,hw16,hsq,hs,?_⟩
  calc
    4*C*(Real.log (2+P))^2≤P^(6/25:ℝ) := hcharge
    _=(P^(3/5:ℝ))^(2/5:ℝ) := by rw [←Real.rpow_mul hp0.le]; norm_num
    _≤w^(2/5:ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hp0.le _) hw (by norm_num)
    _=w^(1+(-3/5:ℝ)) := by norm_num
    _=w*w^(-3/5:ℝ) := by rw [Real.rpow_add hw0,Real.rpow_one]
    _≤w*δ := mul_le_mul_of_nonneg_left hδ hw0.le



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_PartitionOccupation
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

lemma PhaseFlowOn.momentum_le_on_initial_tsupport {d : Datum} {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (hP : ∀ z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    {z : Phase} (hz : z∈tsupport d.f₀) {r : ℝ} (hr : r∈Icc 0 T) :
    q (F.flow z r).2≤P := by
  have hc : Continuous (fun z=>q (prefixFlow F.flow T z r).2) :=
    (contDiff_q (k:=1)).continuous.comp
      (((F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_const.prodMk continuous_id)).snd)
  have hsub : Function.support d.f₀⊆{z | q (prefixFlow F.flow T z r).2≤P} := by
    intro z hz
    simpa only [mem_ofPred_eq,prefixFlow,prefixClamp_eq hr] using hP z (by simpa only [hs.initial_f,Function.mem_support] using hz) r hr
  have hh := closure_minimal hsub (isClosed_le hc continuous_const) hz
  simpa only [mem_ofPred_eq,prefixFlow,prefixClamp_eq hr] using hh

lemma momentum_ne_zero_of_band {v : Vec} {w : ℝ} (hw : 16≤w) (hq : w/8≤q v) : v≠0 := by
  intro he
  have hh := norm_momentum_of_high_band hw hq
  rw [he,norm_zero] at hh
  linarith

lemma Admissible.exists_stable_direction_partition_oai {d : Datum} (hd : Admissible d)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (z : Phase) (a b r m δ : ℝ),
      z∈tsupport d.f₀ → 0≤a → b≤T → r∈Icc a b → 0 < m → m≤q (F.flow z r).2 →
      b-a≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
      b-a≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ∃ k : ℕ, ∃ D : WeightedDirectionPartition (fun t=>(F.flow z t).2)
        (fun t=>s.E (t,(F.flow z t).1)+cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) a b ((2:ℝ)^k) δ,
        (D.count:ℝ)≤C*(Real.log (2+P))^6/δ ∧ 16≤(2:ℝ)^k ∧
        (∀t∈Icc a b,m/2≤q (F.flow z t).2 ∧ (F.flow z t).2≠0) := by
  obtain ⟨C,hC,hcount⟩ := hd.exists_bounded_direction_partition T₀ M A hM hA
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_direction_absorption 0] with P hcount hlarge
  intro s T F hs hT hTT z a b r m δ hz ha hb hr hm hmq hlen hlen' hhigh hδ hδ1 hsource HZ
  have hp : 0<P := zero_lt_one.trans_le hlarge.1
  have hL : 0≤Real.log (2+P) := zero_le_one.trans hlarge.2.1
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hstable := (HZ z hz).velocity_stability_scale ha hb hr
    ((F.continuousOn_time z).snd.mono hJ) hM hA.le hp hL hm
    (by norm_num : (0:ℝ)<1) le_rfl (by norm_num : (128:ℝ)≤128) hmq
    (by simpa only [div_one] using hlen)
  obtain ⟨k,hkq,hqk⟩ := exists_nat_pow_near (one_le_q (F.flow z r).2) (by norm_num : (1:ℝ)<2)
  have href : q (F.flow z r).2≤2*(2:ℝ)^k := by rw [pow_succ] at hqk; nlinarith
  have hmk : m/2≤(2:ℝ)^k := by linarith
  have hkP : (2:ℝ)^k≤P := hkq.trans (F.momentum_le_on_initial_tsupport hs hT hsource hz (hJ hr))
  have hkδ : ((2:ℝ)^k)^(-3/5:ℝ)≤δ :=
    (Real.rpow_le_rpow_of_nonpos (half_pos hm) hmk (by norm_num)).trans hδ
  have hband : ∀t∈Icc a b,q (F.flow z t).2∈Icc ((2:ℝ)^k/8) (8*(2:ℝ)^k) := by
    intro t ht
    have hh := (hstable t ht).2.2
    constructor <;> nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) k]
  have hm16 := (hlarge.2.2 ((2:ℝ)^k) δ (hhigh.trans hmk) hkδ).2.1
  obtain ⟨D,hD⟩ := hcount s T F hs hT hTT z a b δ k hz ha hb (hr.1.trans hr.2)
    (hlen'.trans (by gcongr)) (hhigh.trans hmk) hkP hkδ hδ1 hsource hband HZ
  refine ⟨k,D,hD,hm16,?_⟩
  intro t ht
  exact ⟨by linarith [(hstable t ht).2.2.1],momentum_ne_zero_of_band hm16 (hband t ht).1⟩

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.exists_stable_direction_partition_oai := @OAI.RVM.Admissible.exists_stable_direction_partition_oai
