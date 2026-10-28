-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:56:11.024483+00:00
-- url     : https://prove2.me/submissions/27884768-6b8d-469b-8a04-7e66aec1344a

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_PhaseFlowOn_label_occupation_cell_bound

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

lemma dot_sub_right (a b c : Vec) : dot a (b - c) = dot a b - dot a c := by
  rw [dot_comm, dot_sub_left, dot_comm b a, dot_comm c a]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

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

lemma hit_duration_bound {F : Set ℝ} {g : ℝ → ℝ} {c R : ℝ}
    (hc : 0 < c)
    (hgrowth : ∀ x ∈ F, ∀ y ∈ F, x ≤ y → c*(y-x) ≤ g y-g x)
    (hrange : ∀ x ∈ F, |g x| ≤ R) :
    volume F ≤ ENNReal.ofReal (2*R/c) := by
  apply (Real.volume_le_diam F).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro x hx y hy
  have hxg := abs_le.mp (hrange x hx)
  have hyg := abs_le.mp (hrange y hy)
  rcases le_total x y with hxy | hyx
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hxy)]
    have h := hgrowth x hx y hy hxy
    apply (le_div_iff₀ hc).2
    nlinarith
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hyx)]
    have h := hgrowth y hy x hx hyx
    apply (le_div_iff₀ hc).2
    nlinarith

lemma projected_hit_duration {X Y : ℝ → Vec} {a u : ℝ → Vec}
    {D F : Set ℝ} {e : Vec} {c R : ℝ}
    (hD : Convex ℝ D) (hFD : F ⊆ D) (hc : 0 < c)
    (hXc : ContinuousOn X D) (hYc : ContinuousOn Y D)
    (hX : ∀ s ∈ interior D, HasDerivAt X (a s) s)
    (hY : ∀ s ∈ interior D, HasDerivAt Y (u s) s)
    (hvel : ∀ s ∈ interior D, c ≤ dot e (u s-a s))
    (hsep : ∀ s ∈ F, |dot e (Y s-X s)| ≤ R) :
    volume F ≤ ENNReal.ofReal (2*R/c) := by
  apply hit_duration_bound hc _ hsep
  have hd : ∀ s ∈ interior D, HasDerivAt (fun t => dot e (Y t-X t))
      (dot e (u s-a s)) s := by
    intro s hs
    simpa [dot] using hasDerivAt_dot (hasDerivAt_const s e) ((hY s hs).sub (hX s hs))
  have hcont : ContinuousOn (fun t => dot e (Y t-X t)) D := by
    simp only [dot_eq_inner]
    exact continuousOn_const.inner (hYc.sub hXc)
  intro x hx y hy hxy
  apply hD.mul_sub_le_image_sub_of_le_deriv hcont
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(hd s hs).deriv]; exact hvel s hs) x (hFD hx) y (hFD hy) hxy

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

lemma inClosedConeBin_iff {α : Phase → ℝ → Phase} {zX z : Phase} {B : ClosedConeBin}
    {t r : ℝ} (hR : 0<t-r) :
    InClosedConeBin α zX B t r z ↔
      t-r=‖(α zX t).1-(α z r).1‖ ∧ t-r∈Icc B.rmin B.rmax ∧
      q (α z r).2∈Icc B.qmin B.qmax ∧ q (α zX t).2∈Icc B.wmin B.wmax ∧
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) (velocity (α z r).2)∈Icc B.dmin B.dmax ∧
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) (velocity (α zX t).2)∈Icc B.Dmin B.Dmax ∧
      1-dot (velocity (α zX t).2) (velocity (α z r).2)∈Icc B.emin B.emax := by
  have he (v : Vec) :
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) v=
        ((t-r)-dot ((α zX t).1-(α z r).1) v)/(t-r) := by
    rw [dot_smul_left]
    field_simp
  simp only [InClosedConeBin,he,mem_Icc]
  rw [le_div_iff₀ hR,div_le_iff₀ hR,le_div_iff₀ hR,div_le_iff₀ hR]
  simp only [mul_comm]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ObservationCone
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

namespace RVM

lemma stable_positive_projection {v w : Vec} {c : ℝ} (hc : 0 < c)
    (hv : c≤‖v‖) (hw : ‖w-v‖ ≤ c/2) :
    c/2 ≤ dot (‖v‖⁻¹ • v) w := by
  have hv0 : 0<‖v‖ := hc.trans_le hv
  have he : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hv0),inv_mul_cancel₀ hv0.ne']
  have hdot : dot (‖v‖⁻¹ • v) v=‖v‖ := by
    rw [dot_smul_left,dot_self]
    field_simp
  have hh := dot_le_norm (‖v‖⁻¹ • v) (v-w)
  rw [he,one_mul,norm_sub_rev,dot_sub_right,hdot] at hh
  linarith

lemma stable_cell_duration {X Y a u : ℝ → Vec} {C H : Set ℝ} {v : Vec} {c R : ℝ}
    (hC : Convex ℝ C) (hHC : H ⊆ C) (hc : 0 < c) (hv : c≤‖v‖)
    (hXc : ContinuousOn X C) (hYc : ContinuousOn Y C)
    (hX : ∀ r ∈ interior C, HasDerivAt X (a r) r)
    (hY : ∀ r ∈ interior C, HasDerivAt Y (u r) r)
    (hvel : ∀ r ∈ interior C, ‖u r-a r-v‖ ≤ c/2)
    (hsep : ∀ r ∈ H, ‖Y r-X r‖≤R) :
    volume H ≤ ENNReal.ofReal (4*R/c) := by
  have he : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hc.trans_le hv)),
      inv_mul_cancel₀ (hc.trans_le hv).ne']
  have hh := projected_hit_duration (e:=‖v‖⁻¹ • v) hC hHC (half_pos hc)
    hXc hYc hX hY (fun r hr => stable_positive_projection hc hv (hvel r hr))
    (fun r hr => by
      rw [dot_eq_inner]
      exact (abs_real_inner_le_norm (‖v‖⁻¹ • v) (Y r-X r)).trans (by
        simpa only [he,one_mul] using hsep r hr))
  have hid : 2*R/(c/2)=4*R/c := by ring
  simpa only [hid] using hh

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

lemma retarded_same_time_separation {X a : ℝ → Vec} {s t C : ℝ} {y n : Vec}
    (hst : s≤t)
    (hX : ∀ r ∈ Icc s t, HasDerivWithinAt X (a r) (Icc s t) r)
    (hvel : ∀ r ∈ Icc s t, ‖a r-n‖≤C)
    (hgeom : X t-y=(t-s) • n) : ‖y-X s‖≤C*(t-s) := by
  have hd (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivWithinAt (fun r => X r-r • n) (a r-n) (Icc s t) r := by
    have hn : HasDerivWithinAt (fun r : ℝ => r • n) n (Icc s t) r := by
      convert ((hasDerivAt_id r).smul_const n).hasDerivWithinAt using 1 <;> try rfl
      exact (one_smul ℝ n).symm
    exact (hX r hr).sub hn
  have hh := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hvel (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst)
  have hid : X t-t • n-(X s-s • n)=y-X s := by
    have he : X t=y+(t-s) • n := by rw [← hgeom]; abel
    rw [he,sub_smul]
    module
  simpa only [hid,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using hh

lemma velocity_ref_triangle {v a A n : Vec} {η φ : ℝ}
    (hv : ‖v-A‖≤η) (ha : ‖a-A‖≤η) (han : ‖a-n‖≤φ) :
    ‖v-n‖≤φ+2*η := by
  have he : v-n=(v-A)-(a-A)+(a-n) := by abel
  rw [he]
  have hh := (norm_add_le ((v-A)-(a-A)) (a-n)).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add hv ha)) han)
  linarith

lemma relative_ref_triangle {u a U A : Vec} {η : ℝ}
    (hu : ‖u-U‖≤η) (ha : ‖a-A‖≤η) : ‖u-a-(U-A)‖≤2*η := by
  have he : u-a-(U-A)=(u-U)-(a-A) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

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

lemma actual_relative_separation {v w : Vec} {ang : ℝ}
    (_hom : 0  ≤  ang) (hv : (q v)⁻¹ ≤ ang/4) (hw : (q w)⁻¹ ≤ ang/4)
    (he : ang^2/2 ≤ 1-dot (velocity w) (velocity v)) :
    ang/2 ≤ ‖velocity v-velocity w‖ :=  by
  have hid :=  relative_angle_identity v w
  have hv0 : 0  ≤  (q v)⁻¹ :=  inv_nonneg.mpr (q_pos v).le
  have hw0 : 0  ≤  (q w)⁻¹ :=  inv_nonneg.mpr (q_pos w).le
  have hv2 :=  mul_self_le_mul_self hv0 hv
  have hw2 :=  mul_self_le_mul_self hw0 hw
  nlinarith [norm_nonneg (velocity v-velocity w)]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RelativeClosedBinHitGeometry
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

lemma relative_closed_bin_hit_geometry {α : Phase → ℝ → Phase} {zX z : Phase}
    {B : ClosedConeBin} {t r φ σ : ℝ} (hbin : InClosedConeBin α zX B t r z)
    (hr : 0 < B.rmin) (hφ : 0 < φ) (hσ : 0 < σ)
    (hDhi : B.Dmax ≤ 8*φ^2) (helo : σ^2/2 ≤ B.emin) (hehi : B.emax ≤ 8*σ^2)
    (hq : 4 ≤ σ*B.qmin) (hw : 4 ≤ σ*B.wmin) :
    ∃ n : Vec, ‖n‖=1 ∧ (α zX t).1-(α z r).1=(t-r) • n ∧
      ‖velocity (α zX t).2-n‖ ≤ 4*φ ∧
      σ/2 ≤ ‖velocity (α z r).2-velocity (α zX t).2‖ ∧
      ‖velocity (α z r).2-velocity (α zX t).2‖ ≤ 4*σ := by
  have hR : 0 < t-r := hr.trans_le hbin.2.1.1
  have hb := (inClosedConeBin_iff hR).mp hbin
  let n : Vec := (t-r)⁻¹ • ((α zX t).1-(α z r).1)
  have hn : ‖n‖=1 := by
    dsimp only [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),← hb.1,
      inv_mul_cancel₀ hR.ne']
  have hgeom : (α zX t).1-(α z r).1=(t-r) • n := by
    dsimp only [n]
    rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
  have hhi : 1-dot n (velocity (α zX t).2) ≤ 8*φ^2 :=
    hb.2.2.2.2.2.1.2.trans hDhi
  have hinv (z' : Phase) (qlo : ℝ) (hlo : qlo ≤ q z'.2)
      (hsmall : 4 ≤ σ*qlo) : (q z'.2)⁻¹ ≤ σ/4 := by
    rw [inv_le_iff_one_le_mul₀ (q_pos _)]
    have hh := mul_le_mul_of_nonneg_left hlo hσ.le
    nlinarith
  have hsource := hinv (α z r) B.qmin hb.2.2.1.1 hq
  have hreceiver := hinv (α zX t) B.wmin hb.2.2.2.1.1 hw
  have hlower := actual_relative_separation hσ.le hsource hreceiver
    (helo.trans hb.2.2.2.2.2.2.1)
  have hupper : ‖velocity (α z r).2-velocity (α zX t).2‖ ≤ 4*σ := by
    have hid := relative_angle_identity (α z r).2 (α zX t).2
    have hh := hb.2.2.2.2.2.2.2.trans hehi
    nlinarith [sq_nonneg ((q (α z r).2)⁻¹),sq_nonneg ((q (α zX t).2)⁻¹),
      norm_nonneg (velocity (α z r).2-velocity (α zX t).2)]
  have hrec : ‖velocity (α zX t).2-n‖ ≤ 4*φ := by
    rw [norm_sub_rev]
    have hid := cone_angle_identity (α zX t).2 n hn
    nlinarith [sq_nonneg ((q (α zX t).2)⁻¹),norm_nonneg (n-velocity (α zX t).2)]
  exact ⟨n,hn,hgeom,hrec,hlower,hupper⟩

lemma PhaseFlowOn.relative_closed_bin_cell_data {s : Solution}
    {T M A P L lo hi a b c d massScale φ σ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (helo : σ^2/2 ≤ B.emin) (hehi : B.emax ≤ 8*σ^2)
    (hq : 4 ≤ σ*B.qmin) (hw : 4 ≤ σ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ∀ z, (closedBinHits F.flow zX B S a b c d z).Nonempty →
      volume (closedBinHits F.flow zX B S a b c d z) ≤ ENNReal.ofReal (40*B.rmax*(1+φ/σ)) ∧
      ∀ t∈Icc c d, p/256 ≤ q (F.flow z t).2 ∧ q (F.flow z t).2 ≤ p/16 ∧
        σ/4 ≤ ‖velocity (F.flow z t).2-velocity (F.flow zX t).2‖ ∧
        ‖velocity (F.flow z t).2-velocity (F.flow zX t).2‖ ≤ 5*σ := by
  let U := Icc lo hi
  have hUT : U ⊆ Icc 0 T := Icc_subset_Icc hlo0 hhiT
  have hCT : Icc c d ⊆ Icc 0 T := hC.trans hUT
  have hstable (z : Phase) (H : IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
      (r : ℝ) (hr : r∈U) (hqm : massScale ≤ q (F.flow z r).2) :=
    H.velocity_stability_scale hlo0 hhiT hr ((F.continuousOn_time z).snd.mono hUT)
      hM hA hP hL hm hσ hσ1 hconst hqm hlen
  intro z hz
  obtain ⟨r₀,hzS,hr₀,t₀,ht₀,hbin₀⟩ := hz
  have hsource := hstable z (HZ z hzS) r₀ (hC hr₀) (hmq.trans hbin₀.2.2.1.1)
  have hreceiver := hstable zX HX t₀ (hJ ht₀) (hmw.trans hbin₀.2.2.2.1.1)
  obtain ⟨n₀,_,_,_,hsep₀,hupper₀⟩ := relative_closed_bin_hit_geometry hbin₀ hr hφ hσ hDhi helo hehi hq hw
  have href (t : ℝ) (ht : t∈U) :
      ‖velocity (F.flow z t).2-velocity (F.flow zX t).2-
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)‖ ≤ σ/16 := by
    have hh := relative_ref_triangle (hsource t ht).2.1 (hreceiver t ht).2.1
    linarith
  constructor
  · have hsep (r : ℝ) (hrH : r∈closedBinHits F.flow zX B S a b c d z) :
        ‖(F.flow z r).1-(F.flow zX r).1‖ ≤ 5*B.rmax*(φ+σ) := by
      obtain ⟨_,hrC,t,htJ,hbin⟩ := hrH
      obtain ⟨n,_,hgeom,hangle,_,_⟩ := relative_closed_bin_hit_geometry hbin hr hφ hσ hDhi helo hehi hq hw
      have hrt : r ≤ t := by linarith [hbin.2.1.1]
      have hsub : Icc r t ⊆ U := Icc_subset_Icc (hC hrC).1 (hJ htJ).2
      have hh := retarded_same_time_separation hrt
        (fun u hu => ((F.ode zX u (hUT (hsub hu))).mono (hsub.trans hUT)).fst)
        (fun u hu => velocity_ref_triangle (hreceiver u (hsub hu)).2.1
          (hreceiver t (hJ htJ)).2.1 hangle) hgeom
      have hrad : 0 ≤ B.rmax := (sub_nonneg.mpr hrt).trans hbin.2.1.2
      calc
        _ ≤ (4*φ+2*(σ/32))*(t-r) := hh
        _ ≤ (5*(φ+σ))*B.rmax := mul_le_mul (by linarith) hbin.2.1.2
          (sub_nonneg.mpr hrt) (by positivity)
        _ = _ := by ring
    have hh := stable_cell_duration (convex_Icc c d)
      (show closedBinHits F.flow zX B S a b c d z ⊆ Icc c d from fun _ h => h.2.1)
      (half_pos hσ) hsep₀ ((F.continuousOn_time zX).fst.mono hCT)
      ((F.continuousOn_time z).fst.mono hCT)
      (fun r hr => ((F.ode zX r (hCT (interior_subset hr))).mono hCT).hasDerivAt
        (mem_interior_iff_mem_nhds.mp hr) |>.fst)
      (fun r hr => ((F.ode z r (hCT (interior_subset hr))).mono hCT).hasDerivAt
        (mem_interior_iff_mem_nhds.mp hr) |>.fst)
      (fun r hr => (href r (hC (interior_subset hr))).trans (by linarith)) hsep
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    field_simp; ring
  · intro t ht
    have hq := (hsource t (hC ht)).2.2
    have hqlo := hqmin.trans hbin₀.2.2.1.1
    have hqhi := hbin₀.2.2.1.2.trans hqmax
    refine ⟨by linarith,by linarith,?_,?_⟩
    · have hn := norm_sub_norm_le
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)
        (velocity (F.flow z t).2-velocity (F.flow zX t).2)
      have hh : ‖(velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)-
          (velocity (F.flow z t).2-velocity (F.flow zX t).2)‖ ≤ σ/16 := by
        rw [norm_sub_rev]
        exact href t (hC ht)
      linarith
    · have hn := norm_sub_norm_le
        (velocity (F.flow z t).2-velocity (F.flow zX t).2)
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)
      linarith [href t (hC ht)]

lemma PhaseFlowOn.relative_closed_bin_cell_crude_oai {s : Solution}
    {T M A P L lo hi a b c d massScale φ σ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (t₀ : ℝ) (ht₀ : t₀∈Icc c d) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (helo : σ^2/2 ≤ B.emin) (hehi : B.emax ≤ 8*σ^2)
    (hq : 4 ≤ σ*B.qmin) (hw : 4 ≤ σ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ENNReal.ofReal (40*B.rmax*(1+φ/σ)) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  have hdata := F.relative_closed_bin_cell_data zX B hlo0 hhiT hJ hC hM hA hP hL
    hm hφ hσ hσ1 hconst hlen hqmin hqmax hmq hmw hr hDhi helo hehi hq hw HX HZ
  apply F.label_occupation_cell_bound hs ((hC.trans (Icc_subset_Icc hlo0 hhiT)) ht₀)
  · intro z
    by_cases hz : (closedBinHits F.flow zX B S a b c d z).Nonempty
    · exact (hdata z hz).1
    · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]
  · exact fun z hz => ((hdata z hz).2 t₀ ht₀).1

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude_oai := @OAI.RVM.PhaseFlowOn.relative_closed_bin_cell_crude_oai
