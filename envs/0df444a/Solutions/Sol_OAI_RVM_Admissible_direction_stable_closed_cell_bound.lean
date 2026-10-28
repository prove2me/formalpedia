-- Prove2me | solution 1 for OAI.RVM.Admissible.direction_stable_closed_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:00:19.33463+00:00
-- url     : https://prove2.me/submissions/3a4379a1-fbdb-421d-b826-51f0f8bc8447

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_exists_stable_direction_partition
import Theorems.Thm_OAI_RVM_PhaseFlowOn_label_occupation_cell_bound

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
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

lemma actual_small_sector_velocity {v w n : Vec} {φ : ℝ}
    (hn : ‖n‖ = 1) (hφ : 0  ≤  φ) (hw : (q w)⁻¹ ≤ φ/4)
    (hsource : ‖n-velocity v‖ ≤ φ/4)
    (hlo : φ^2/2 ≤ 1-dot n (velocity w))
    (hhi : 1-dot n (velocity w) ≤ 8*φ^2) :
    φ/2 ≤ ‖velocity v-velocity w‖ ∧ ‖velocity v-velocity w‖ ≤ 5*φ :=  by
  have hid :=  cone_angle_identity w n hn
  have hi0 : 0  ≤  (q w)⁻¹ :=  inv_nonneg.mpr (q_pos w).le
  have hi2 :=  mul_self_le_mul_self hi0 hw
  have hna0 :=  norm_nonneg (n-velocity w)
  have hnalow : 3*φ/4 ≤ ‖n-velocity w‖ :=  by nlinarith
  have hnahi : ‖n-velocity w‖ ≤ 4*φ :=  by nlinarith [sq_nonneg ((q w)⁻¹)]
  have hlo' : ‖n-velocity w‖ ≤ ‖n-velocity v‖+‖velocity v-velocity w‖ :=  by
    calc
      _  =  ‖(n-velocity v)+(velocity v-velocity w)‖ :=  by congr 1; abel
      _  ≤  _ :=  norm_add_le _ _
  have hhi' : ‖velocity v-velocity w‖ ≤ ‖n-velocity v‖+‖n-velocity w‖ :=  by
    calc
      _  =  ‖(velocity v-n)+(n-velocity w)‖ :=  by congr 1; abel
      _  ≤  ‖velocity v-n‖+‖n-velocity w‖ :=  norm_add_le _ _
      _  =  _ :=  by rw [norm_sub_rev (velocity v) n]
  exact ⟨by linarith,by linarith⟩

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


lemma small_closed_bin_hit_geometry {α : Phase → ℝ → Phase} {zX z : Phase}
    {B : ClosedConeBin} {t r φ : ℝ} (hbin : InClosedConeBin α zX B t r z)
    (hr : 0 < B.rmin) (hφ : 0 < φ)
    (hd : B.dmax ≤ φ^2/32) (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hw : 4 ≤ φ*B.wmin) :
    ∃ n : Vec, ‖n‖=1 ∧ (α zX t).1-(α z r).1=(t-r) • n ∧
      ‖velocity (α zX t).2-n‖ ≤ 4*φ ∧
      φ/2 ≤ ‖velocity (α z r).2-velocity (α zX t).2‖ ∧
      ‖velocity (α z r).2-velocity (α zX t).2‖ ≤ 5*φ := by
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
  have hsrc : ‖n-velocity (α z r).2‖ ≤ φ/4 := by
    have hid := cone_angle_identity (α z r).2 n hn
    have hbound := hb.2.2.2.2.1.2.trans hd
    nlinarith [sq_nonneg ((q (α z r).2)⁻¹),norm_nonneg (n-velocity (α z r).2)]
  have hlo : φ^2/2 ≤ 1-dot n (velocity (α zX t).2) :=
    hDlo.trans hb.2.2.2.2.2.1.1
  have hhi : 1-dot n (velocity (α zX t).2) ≤ 8*φ^2 :=
    hb.2.2.2.2.2.1.2.trans hDhi
  have hinv : (q (α zX t).2)⁻¹ ≤ φ/4 := by
    rw [inv_le_iff_one_le_mul₀ (q_pos _)]
    have hh := mul_le_mul_of_nonneg_left hb.2.2.2.1.1 hφ.le
    nlinarith
  have hrec : ‖velocity (α zX t).2-n‖ ≤ 4*φ := by
    rw [norm_sub_rev]
    have hid := cone_angle_identity (α zX t).2 n hn
    nlinarith [sq_nonneg ((q (α zX t).2)⁻¹),norm_nonneg (n-velocity (α zX t).2)]
  exact ⟨n,hn,hgeom,hrec,actual_small_sector_velocity hn hφ.le hinv hsrc hlo hhi⟩



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


lemma momentumDirection_norm {v : Vec} (hv : v ≠ 0) : ‖momentumDirection v‖=1 := by
  simp [momentumDirection,norm_smul,norm_ne_zero_iff.mpr hv]



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



section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal


namespace WeightedDirectionPartition
variable {V K : ℝ → Vec} {a b w δ : ℝ}

lemma cell_subset (D : WeightedDirectionPartition V K a b w δ)
    {i : ℕ} (hi : i < D.count) : Icc (D.time i) (D.time (i+1)) ⊆ Icc a b :=
  Icc_subset_Icc (D.time_mem i (by omega)).1 (D.time_mem (i+1) (by omega)).2

end WeightedDirectionPartition

end

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

namespace RVM

lemma directionOverlap_card_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ)
    (hleft : ∀ i j, i ≠ j → Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀ i j, i ≠ j → Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j))) :
    Fintype.card (DirectionOverlap l r l' r') ≤ Fintype.card ι + Fintype.card κ := by
  classical
  let charge : DirectionOverlap l r l' r' → ι ⊕ κ := fun z =>
    if l z.1.1 ≤ l' z.1.2 then Sum.inr z.1.2 else Sum.inl z.1.1
  have hc : Function.Injective charge := by
    intro a b hab
    have ha := a.2
    have hb := b.2
    dsimp [charge] at hab
    split_ifs at hab with h₁ h₂ h₂
    · have hj : a.1.2 = b.1.2 := Sum.inr.inj hab
      have hi : a.1.1 = b.1.1 := by
        by_contra hn
        have hd := Set.disjoint_left.mp (hleft _ _ hn)
        apply hd (a := l' a.1.2)
        · exact ⟨h₁, (le_max_right _ _).trans_lt (lt_of_lt_of_le ha (min_le_left _ _))⟩
        · rw [hj]
          exact ⟨h₂, (le_max_right _ _).trans_lt (lt_of_lt_of_le hb (min_le_left _ _))⟩
      exact Subtype.ext (Prod.ext hi hj)
    · have hi : a.1.1 = b.1.1 := Sum.inl.inj hab
      have hj : a.1.2 = b.1.2 := by
        by_contra hn
        have hd := Set.disjoint_left.mp (hright _ _ hn)
        apply hd (a := l a.1.1)
        · exact ⟨(lt_of_not_ge h₁).le,
            (le_max_left _ _).trans_lt (lt_of_lt_of_le ha (min_le_right _ _))⟩
        · rw [hi]
          exact ⟨(lt_of_not_ge h₂).le,
            (le_max_left _ _).trans_lt (lt_of_lt_of_le hb (min_le_right _ _))⟩
      exact Subtype.ext (Prod.ext hi hj)
  simpa only [Fintype.card_sum] using Fintype.card_le_of_injective charge hc

lemma retarded_boundary_hit_duration {H : Set ℝ} (arrival : ℝ → ℝ)
    (B : Finset ℝ) {L : ℝ}
    (hdelay : ∀ s ∈ H, arrival s - s ≤ L) :
    volume {s ∈ H | ∃ b ∈ B, s ≤ b ∧ b ≤ arrival s} ≤
      (B.card : ℝ≥0∞) * ENNReal.ofReal L := by
  classical
  have hcov : {s ∈ H | ∃ b ∈ B, s ≤ b ∧ b ≤ arrival s} ⊆
      ⋃ b ∈ B, Icc (b-L) b := by
    intro s hs
    obtain ⟨b, hb, hsb, hba⟩ := hs.2
    exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hb, by
      have := hdelay s hs.1
      constructor <;> linarith⟩⟩
  calc
    _ ≤ volume (⋃ b ∈ B, Icc (b-L) b) := measure_mono hcov
    _ ≤ ∑ b ∈ B, volume (Icc (b-L) b) := measure_biUnion_finset_le B _
    _ = (B.card : ℝ≥0∞) * ENNReal.ofReal L := by
      simp only [Real.volume_Icc,sub_sub_cancel]
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

namespace RVM

lemma velocity_direction_deficit {v : Vec} (hv : v ≠ 0) :
    ‖velocity v - momentumDirection v‖ ≤ (q v)⁻¹^2 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hq := q_pos v
  have hnq := norm_lt_q v
  have hsq := q_sq v
  have he : velocity v = (‖v‖ / q v) • momentumDirection v := by
    rw [velocity,momentumDirection,smul_smul]
    congr 1
    field_simp
  rw [he]
  conv_lhs => arg 1; rhs; rw [← one_smul ℝ (momentumDirection v)]
  rw [← sub_smul,norm_smul,
    momentumDirection_norm hv,mul_one,Real.norm_eq_abs,abs_of_nonpos]
  · have hr : 0 < q v * (q v + ‖v‖) := mul_pos hq (by positivity)
    have hid : 1 - ‖v‖/q v = (q v * (q v + ‖v‖))⁻¹ := by
      field_simp
      nlinarith
    rw [neg_sub,hid]
    rw [inv_pow]
    exact (inv_le_inv₀ hr (sq_pos_of_pos hq)).mpr (by nlinarith)
  · exact sub_nonpos.mpr ((div_le_one hq).mpr hnq.le)

lemma velocity_change_of_direction {v w : Vec} {δ ε : ℝ}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hdir : ‖momentumDirection v - momentumDirection w‖ ≤ δ)
    (hvq : (q v)⁻¹^2 ≤ ε) (hwq : (q w)⁻¹^2 ≤ ε) :
    ‖velocity v - velocity w‖ ≤ δ + 2*ε := by
  calc
    _ = ‖(velocity v-momentumDirection v) +
      (momentumDirection v-momentumDirection w) + (momentumDirection w-velocity w)‖ := by
        congr 1; abel
    _ ≤ ‖velocity v-momentumDirection v‖ + ‖momentumDirection v-momentumDirection w‖ +
      ‖momentumDirection w-velocity w‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε + δ + ε := by
      gcongr
      · exact (velocity_direction_deficit hv).trans hvq
      · rw [norm_sub_rev]; exact (velocity_direction_deficit hw).trans hwq
    _ = _ := by ring

lemma refined_direction_hit_duration_of_hits {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ)
    (hleft : ∀ i j, i ≠ j → Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀ i j, i ≠ j → Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j)))
    {X Y a u : ℝ → Vec} {D H : Set ℝ} {c R : ℝ}
    (hc : 0 < c)
    (hD : ∀ i, Ico (l i) (r i) ⊆ D)
    (hcover : ∀ t ∈ H, (∃ i, t ∈ Ico (l i) (r i)) ∧
      (∃ j, t ∈ Ico (l' j) (r' j)))
    (hXc : ContinuousOn X D) (hYc : ContinuousOn Y D)
    (hX : ∀ t ∈ interior D, HasDerivAt X (a t) t)
    (hY : ∀ t ∈ interior D, HasDerivAt Y (u t) t)
    (hstable : ∀ z : DirectionOverlap l r l' r',
      (H ∩ Ico (max (l z.1.1) (l' z.1.2)) (min (r z.1.1) (r' z.1.2))).Nonempty →
      ∃ v : Vec, c ≤ ‖v‖ ∧ ∀ t ∈ Ioo (max (l z.1.1) (l' z.1.2))
        (min (r z.1.1) (r' z.1.2)), ‖u t-a t-v‖ ≤ c/2)
    (hsep : ∀ t ∈ H, ‖Y t - X t‖ ≤ R) :
    volume H ≤ (Fintype.card ι + Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal (4*R/c) := by
  classical
  let C : DirectionOverlap l r l' r' → Set ℝ :=
    fun z => Ico (max (l z.1.1) (l' z.1.2)) (min (r z.1.1) (r' z.1.2))
  have hcov : H ⊆ ⋃ z, H ∩ C z := by
    intro t ht
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hcover t ht
    have he : max (l i) (l' j) ≤ t := max_le hi.1 hj.1
    have hf : t < min (r i) (r' j) := lt_min hi.2 hj.2
    exact mem_iUnion.mpr ⟨⟨(i,j),he.trans_lt hf⟩,ht,he,hf⟩
  have hCD (z : DirectionOverlap l r l' r') : C z ⊆ D := fun _ ht =>
    hD z.1.1 ⟨(le_max_left _ _).trans ht.1,ht.2.trans_le (min_le_left _ _)⟩
  have hcell (z : DirectionOverlap l r l' r') : volume (H ∩ C z) ≤ ENNReal.ofReal (4*R/c) := by
    by_cases hh : (H ∩ C z).Nonempty
    · obtain ⟨v,hv,hvel⟩ := hstable z hh
      apply stable_cell_duration (convex_Ico _ _) inter_subset_right hc hv
        (hXc.mono (hCD z)) (hYc.mono (hCD z))
      · intro t ht
        exact hX t (interior_mono (hCD z) ht)
      · intro t ht
        exact hY t (interior_mono (hCD z) ht)
      · intro t ht
        apply hvel t
        simpa only [C,interior_Ico] using ht
      · intro t ht
        exact hsep t ht.1
    · rw [not_nonempty_iff_eq_empty.mp hh,measure_empty]
      exact bot_le
  calc
    volume H ≤ volume (⋃ z, H ∩ C z) := measure_mono hcov
    _ ≤ ∑ z, volume (H ∩ C z) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _z : DirectionOverlap l r l' r', ENNReal.ofReal (4*R/c) :=
      Finset.sum_le_sum (fun z _ => hcell z)
    _ = (Fintype.card (DirectionOverlap l r l' r') : ℝ≥0∞) * ENNReal.ofReal (4*R/c) := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast directionOverlap_card_le l r l' r' hleft hright

lemma relative_velocity_direction_cell {V W : ℝ → Vec} {t s₀ t₀ : ℝ} {c δ ε : ℝ}
    (hVt : V t ≠ 0) (hVs : V s₀ ≠ 0) (hWt : W t ≠ 0) (hWs : W s₀ ≠ 0)
    (hWt₀ : W t₀ ≠ 0)
    (hVdir : ‖momentumDirection (V t)-momentumDirection (V s₀)‖ ≤ δ)
    (hWdir : ‖momentumDirection (W t)-momentumDirection (W s₀)‖ ≤ δ)
    (hWcross : ‖momentumDirection (W s₀)-momentumDirection (W t₀)‖ ≤ δ)
    (hVqt : (q (V t))⁻¹^2 ≤ ε) (hVqs : (q (V s₀))⁻¹^2 ≤ ε)
    (hWqt : (q (W t))⁻¹^2 ≤ ε) (hWqs : (q (W s₀))⁻¹^2 ≤ ε)
    (hWqt₀ : (q (W t₀))⁻¹^2 ≤ ε)
    (hhit : 2*c ≤ ‖velocity (V s₀)-velocity (W t₀)‖)
    (hsmall : δ+2*ε ≤ c/4) :
    c ≤ ‖velocity (V s₀)-velocity (W s₀)‖ ∧
      ‖velocity (V t)-velocity (W t)-(velocity (V s₀)-velocity (W s₀))‖ ≤ c/2 := by
  have hcross := velocity_change_of_direction hWs hWt₀ hWcross hWqs hWqt₀
  constructor
  · have hn := norm_sub_le (velocity (V s₀)-velocity (W s₀))
      (velocity (W t₀)-velocity (W s₀))
    have he : velocity (V s₀)-velocity (W s₀)-(velocity (W t₀)-velocity (W s₀)) =
        velocity (V s₀)-velocity (W t₀) := by abel
    rw [he,norm_sub_rev (velocity (W t₀))] at hn
    have hnn := norm_nonneg (velocity (W s₀)-velocity (W t₀))
    linarith
  · have hvs := velocity_change_of_direction hVt hVs hVdir hVqt hVqs
    have hws := velocity_change_of_direction hWt hWs hWdir hWqt hWqs
    have he : velocity (V t)-velocity (W t)-(velocity (V s₀)-velocity (W s₀)) =
      (velocity (V t)-velocity (V s₀))-(velocity (W t)-velocity (W s₀)) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)

lemma direction_good_hit_separation {X : ℝ → Vec} {Y n : Vec} {V : ℝ → Vec}
    {s t δ ε b : ℝ} (hst : s ≤ t)
    (hX : ∀ r ∈ Icc s t, HasDerivWithinAt X (velocity (V r)) (Icc s t) r)
    (hnz : ∀ r ∈ Icc s t, V r ≠ 0)
    (hq : ∀ r ∈ Icc s t, (q (V r))⁻¹^2 ≤ ε)
    (hdir : ∀ r ∈ Icc s t, ‖momentumDirection (V r)-momentumDirection (V t)‖ ≤ δ)
    (hcone : X t-Y=(t-s) • n) (hbin : ‖velocity (V t)-n‖ ≤ b) :
    ‖Y-X s‖ ≤ (δ+2*ε+b)*(t-s) := by
  have ht : t ∈ Icc s t := right_mem_Icc.mpr hst
  have hd (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivWithinAt (fun v => X v-v • n) (velocity (V r)-n) (Icc s t) r := by
    have hh := (hX r hr).sub ((hasDerivWithinAt_id r _).smul_const n)
    change HasDerivWithinAt (fun v => X v-v • n) (velocity (V r)-1 • n) (Icc s t) r at hh
    simpa only [one_smul] using hh
  have hb (r : ℝ) (hr : r ∈ Icc s t) : ‖velocity (V r)-n‖ ≤ δ+2*ε+b := by
    have hc := velocity_change_of_direction (hnz r hr) (hnz t ht) (hdir r hr) (hq r hr) (hq t ht)
    calc
      _ = ‖(velocity (V r)-velocity (V t))+(velocity (V t)-n)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hc hbin)
  have hh := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (left_mem_Icc.mpr hst) ht
  have he : X t-t • n-(X s-s • n)=Y-X s := by
    calc
      _ = (X t-Y-(t-s) • n)+(Y-X s) := by rw [sub_smul]; abel
      _ = _ := by rw [hcone,sub_self,zero_add]
  rw [he,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] at hh
  exact hh

lemma PhaseFlowOn.direction_closed_bin_hit_separation {s : Solution} {T φ δ ε t τ l r : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase) (B : ClosedConeBin)
    (hcellT : Ico l r ⊆ Icc 0 T) (ht : t ∈ Ico l r) (hτ : τ ∈ Ico l r)
    (hnz : ∀ u ∈ Ico l r, (F.flow zX u).2 ≠ 0)
    (hq : ∀ u ∈ Ico l r, (q (F.flow zX u).2)⁻¹^2 ≤ ε)
    (hdir : ∀ a ∈ Ico l r, ∀ b ∈ Ico l r,
      ‖momentumDirection (F.flow zX a).2-momentumDirection (F.flow zX b).2‖ ≤ δ)
    (hbin : InClosedConeBin F.flow zX B τ t zY)
    (hr : 0 < B.rmin) (hφ : 0 < φ)
    (hd : B.dmax ≤ φ^2/32) (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hw : 4 ≤ φ*B.wmin) (hsmall : δ+2*ε ≤ φ/16) :
    ‖(F.flow zY t).1-(F.flow zX t).1‖ ≤ 5*B.rmax*φ := by
  obtain ⟨n,_,hcone,hbound,_,_⟩ := small_closed_bin_hit_geometry hbin hr hφ hd hDlo hDhi hw
  have hdelay := hbin.2.1
  have hta : t ≤ τ := by linarith [hdelay.1]
  have hinside : Icc t τ ⊆ Ico l r := fun u hu => ⟨ht.1.trans hu.1,hu.2.trans_lt hτ.2⟩
  have hST := hinside.trans hcellT
  have hder (u : ℝ) (hu : u ∈ Icc t τ) : HasDerivWithinAt
      (fun v => (F.flow zX v).1) (velocity (F.flow zX u).2) (Icc t τ) u := by
    have hh : HasDerivWithinAt (fun v => (F.flow zX v).1)
        (velocity (F.flow zX u).2) (Icc 0 T) u := (F.ode zX u (hST hu)).fst
    exact hh.mono hST
  have hh := direction_good_hit_separation hta hder
    (fun u hu => hnz u (hinside hu)) (fun u hu => hq u (hinside hu))
    (fun u hu => hdir u (hinside hu) τ hτ) hcone hbound
  calc
    _ ≤ (δ+2*ε+4*φ)*(τ-t) := hh
    _ ≤ (5*φ)*(τ-t) := mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hta)
    _ ≤ (5*φ)*B.rmax := mul_le_mul_of_nonneg_left hdelay.2 (by positivity)
    _ = _ := by ring

lemma PhaseFlowOn.direction_good_hit_duration {s : Solution} {T φ δ ε : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase) (B : ClosedConeBin)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ)
    (hleft : ∀ i j, i ≠ j → Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀ i j, i ≠ j → Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j)))
    (hsrcT : ∀ i, Ico (l i) (r i) ⊆ Icc 0 T)
    (hrecT : ∀ j, Ico (l' j) (r' j) ⊆ Icc 0 T)
    (hsrcnz : ∀ i t, t ∈ Ico (l i) (r i) → (F.flow zY t).2 ≠ 0)
    (hrecnz : ∀ j t, t ∈ Ico (l' j) (r' j) → (F.flow zX t).2 ≠ 0)
    (hsrcq : ∀ i t, t ∈ Ico (l i) (r i) → (q (F.flow zY t).2)⁻¹^2 ≤ ε)
    (hrecq : ∀ j t, t ∈ Ico (l' j) (r' j) → (q (F.flow zX t).2)⁻¹^2 ≤ ε)
    (hsrcdir : ∀ i, ∀ a ∈ Ico (l i) (r i), ∀ b ∈ Ico (l i) (r i),
      ‖momentumDirection (F.flow zY a).2-momentumDirection (F.flow zY b).2‖ ≤ δ)
    (hrecdir : ∀ j, ∀ a ∈ Ico (l' j) (r' j), ∀ b ∈ Ico (l' j) (r' j),
      ‖momentumDirection (F.flow zX a).2-momentumDirection (F.flow zX b).2‖ ≤ δ)
    {H : Set ℝ} (arrival : ℝ → ℝ)
    (hcover : ∀ t ∈ H, ∃ i, t ∈ Ico (l i) (r i))
    (hgood : ∀ t ∈ H, ∃ j, t ∈ Ico (l' j) (r' j) ∧ arrival t ∈ Ico (l' j) (r' j))
    (hbin : ∀ t ∈ H, InClosedConeBin F.flow zX B (arrival t) t zY)
    (hr : 0 < B.rmin) (hφ : 0 < φ)
    (hd : B.dmax ≤ φ^2/32) (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hw : 4 ≤ φ*B.wmin) (hsmall : δ+2*ε ≤ φ/16) :
    volume H ≤ (Fintype.card ι + Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal (80*B.rmax) := by
  have hcov : ∀ t ∈ H, (∃ i, t ∈ Ico (l i) (r i)) ∧
      (∃ j, t ∈ Ico (l' j) (r' j)) := by
    intro t ht
    obtain ⟨j,hj,_⟩ := hgood t ht
    exact ⟨hcover t ht,j,hj⟩
  have hsep (t : ℝ) (ht : t ∈ H) : ‖(F.flow zY t).1-(F.flow zX t).1‖ ≤ 5*B.rmax*φ := by
    obtain ⟨j,hj,hja⟩ := hgood t ht
    exact F.direction_closed_bin_hit_separation zX zY B (hrecT j) hj hja
      (hrecnz j) (hrecq j) (hrecdir j) (hbin t ht) hr hφ hd hDlo hDhi hw hsmall
  have hstab (z : DirectionOverlap l r l' r')
      (hh : (H ∩ Ico (max (l z.1.1) (l' z.1.2)) (min (r z.1.1) (r' z.1.2))).Nonempty) :
      ∃ v : Vec, φ/4 ≤ ‖v‖ ∧ ∀ t ∈ Ioo (max (l z.1.1) (l' z.1.2))
        (min (r z.1.1) (r' z.1.2)),
        ‖velocity (F.flow zY t).2-velocity (F.flow zX t).2-v‖ ≤ (φ/4)/2 := by
    obtain ⟨u,hu,huc⟩ := hh
    have hui : u ∈ Ico (l z.1.1) (r z.1.1) :=
      ⟨(le_max_left _ _).trans huc.1,huc.2.trans_le (min_le_left _ _)⟩
    have huj : u ∈ Ico (l' z.1.2) (r' z.1.2) :=
      ⟨(le_max_right _ _).trans huc.1,huc.2.trans_le (min_le_right _ _)⟩
    obtain ⟨j,hj,hja⟩ := hgood u hu
    have hjz : j=z.1.2 := by
      by_contra hne
      exact Set.disjoint_left.mp (hright j z.1.2 hne) hj huj
    subst j
    obtain ⟨_,_,_,_,hlo,_⟩ := small_closed_bin_hit_geometry (hbin u hu) hr hφ hd hDlo hDhi hw
    have hsmall' : δ+2*ε ≤ (φ/4)/4 := by linarith
    have hh (t : ℝ) (hti : t ∈ Ico (l z.1.1) (r z.1.1))
        (htj : t ∈ Ico (l' z.1.2) (r' z.1.2)) :=
      relative_velocity_direction_cell (V:=fun t => (F.flow zY t).2)
        (W:=fun t => (F.flow zX t).2) (t:=t) (s₀:=u) (t₀:=arrival u)
        (c:=φ/4) (δ:=δ) (ε:=ε)
        (hsrcnz _ t hti) (hsrcnz _ u hui) (hrecnz _ t htj) (hrecnz _ u huj) (hrecnz _ _ hja)
        (hsrcdir _ t hti u hui) (hrecdir _ t htj u huj) (hrecdir _ u huj _ hja)
        (hsrcq _ t hti) (hsrcq _ u hui) (hrecq _ t htj) (hrecq _ u huj) (hrecq _ _ hja)
        (show 2*(φ/4) ≤ ‖velocity (F.flow zY u).2-velocity (F.flow zX (arrival u)).2‖ by linarith)
        hsmall'
    refine ⟨velocity (F.flow zY u).2-velocity (F.flow zX u).2,(hh u hui huj).1,?_⟩
    intro t ht
    exact (hh t ⟨(le_max_left _ _).trans ht.1.le,ht.2.trans_le (min_le_left _ _)⟩
      ⟨(le_max_right _ _).trans ht.1.le,ht.2.trans_le (min_le_right _ _)⟩).2
  have hbound := refined_direction_hit_duration_of_hits l r l' r' hleft hright
    (X:=fun t => (F.flow zX t).1) (Y:=fun t => (F.flow zY t).1)
    (a:=fun t => velocity (F.flow zX t).2) (u:=fun t => velocity (F.flow zY t).2)
    (D:=Icc 0 T) (H:=H) (R:=5*B.rmax*φ)
    (by positivity : 0 < φ/4) hsrcT hcov
    ((F.continuousOn_time zX).fst) ((F.continuousOn_time zY).fst)
    (fun t ht => ((F.ode zX t (interior_subset ht)).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)).fst)
    (fun t ht => ((F.ode zY t (interior_subset ht)).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)).fst)
    hstab hsep
  have he : 4*(5*B.rmax*φ)/(φ/4)=80*B.rmax := by field_simp [hφ.ne']; ring
  simpa only [he] using hbound

lemma receiver_cells_good_or_bad {κ : Type*} [Fintype κ]
    (l r : κ→ℝ) {s t : ℝ} (hst : s≤t) (hc : ∃j,s∈Ico (l j) (r j)) :
    (∃j,s∈Ico (l j) (r j) ∧ t∈Ico (l j) (r j)) ∨
      ∃b∈Finset.univ.image r,s≤b ∧ b≤t := by
  classical
  obtain ⟨j,hj⟩ := hc
  by_cases ht : t < r j
  · exact Or.inl ⟨j,hj,⟨hj.1.trans hst,ht⟩⟩
  · exact Or.inr ⟨r j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,hj.2.le,le_of_not_gt ht⟩

lemma PhaseFlowOn.direction_total_hit_duration {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase) (B : ClosedConeBin)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι→ℝ) (l' r' : κ→ℝ)
    (hleft : ∀i j,i≠j→Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀i j,i≠j→Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j)))
    {δ ε φ : ℝ}
    (hsrcT : ∀i,Ico (l i) (r i)⊆Icc 0 T)
    (hrecT : ∀j,Ico (l' j) (r' j)⊆Icc 0 T)
    (hsrcnz : ∀i t,t∈Ico (l i) (r i)→(F.flow zY t).2≠0)
    (hrecnz : ∀j t,t∈Ico (l' j) (r' j)→(F.flow zX t).2≠0)
    (hsrcq : ∀i t,t∈Ico (l i) (r i)→(q (F.flow zY t).2)⁻¹^2≤ε)
    (hrecq : ∀j t,t∈Ico (l' j) (r' j)→(q (F.flow zX t).2)⁻¹^2≤ε)
    (hsrcdir : ∀i,∀a∈Ico (l i) (r i),∀b∈Ico (l i) (r i),
      ‖momentumDirection (F.flow zY a).2-momentumDirection (F.flow zY b).2‖≤δ)
    (hrecdir : ∀j,∀a∈Ico (l' j) (r' j),∀b∈Ico (l' j) (r' j),
      ‖momentumDirection (F.flow zX a).2-momentumDirection (F.flow zX b).2‖≤δ)
    {H : Set ℝ} (arrival : ℝ→ℝ)
    (hsrc : ∀t∈H,∃i,t∈Ico (l i) (r i))
    (hrec : ∀t∈H,∃j,t∈Ico (l' j) (r' j))
    (hbin : ∀t∈H,InClosedConeBin F.flow zX B (arrival t) t zY)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hφ : 0<φ)
    (hd : B.dmax≤φ^2/32) (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2)
    (hw : 4≤φ*B.wmin) (hsmall : δ+2*ε≤φ/16) :
    volume H≤(Fintype.card ι+Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal (81*B.rmax) := by
  classical
  let ends := Finset.univ.image r'
  let Bad := {t∈H | ∃b∈ends,t≤b ∧ b≤arrival t}
  let Good := H\Bad
  have hgood : ∀t∈Good,∃j,t∈Ico (l' j) (r' j) ∧ arrival t∈Ico (l' j) (r' j) := by
    intro t ht
    have hh := (hbin t ht.1).2.1.1
    rcases receiver_cells_good_or_bad l' r' (s:=t) (t:=arrival t)
      (by linarith) (hrec t ht.1) with hg|hb
    · exact hg
    · exact False.elim (ht.2 ⟨ht.1,hb⟩)
  have hg := F.direction_good_hit_duration zX zY B l r l' r' hleft hright
    hsrcT hrecT hsrcnz hrecnz hsrcq hrecq hsrcdir hrecdir arrival
    (fun t ht=>hsrc t ht.1) hgood (fun t ht=>hbin t ht.1)
    hr hφ hd hDlo hDhi hw hsmall
  have hb : volume Bad≤(Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal B.rmax := by
    have he : ends.card≤Fintype.card κ := (Finset.card_image_le).trans (by simp)
    have h := retarded_boundary_hit_duration (H:=H) arrival ends
      (fun t ht=>(hbin t ht).2.1.2)
    apply h.trans
    gcongr
  have hc : H⊆Good∪Bad := by
    intro t ht
    by_cases htb : t∈Bad
    · exact Or.inr htb
    · exact Or.inl ⟨ht,htb⟩
  calc
    volume H≤volume Good+volume Bad := (measure_mono hc).trans (measure_union_le _ _)
    _ ≤ (Fintype.card ι+Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal (80*B.rmax)+
      (Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal B.rmax := add_le_add hg hb
    _ ≤ (Fintype.card ι+Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal (80*B.rmax)+
      (Fintype.card ι+Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal B.rmax := by gcongr; exact le_add_left le_rfl
    _ = _ := by
      rw [←mul_add,←ENNReal.ofReal_add (by positivity) hrmax]
      congr 2
      ring

end RVM

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

namespace WeightedDirectionPartition
variable {V K : ℝ→Vec} {a b w δ : ℝ}

lemma halfopen_disjoint (D : WeightedDirectionPartition V K a b w δ)
    (i j : Fin D.count) (hne : i≠j) :
    Disjoint (Ico (D.time i) (D.time (i+1))) (Ico (D.time j) (D.time (j+1))) := by
  apply Ico_disjoint_Ico.mpr
  have hn : (i:ℕ)≠j := fun h=>hne (Fin.ext h)
  rcases lt_or_gt_of_ne hn with hij|hji
  · exact (min_le_left _ _).trans ((D.strict.monotoneOn (a := (i:ℕ)+1) (b := (j:ℕ)) (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)).trans (le_max_right _ _))
  · exact (min_le_right _ _).trans ((D.strict.monotoneOn (a := (j:ℕ)+1) (b := (i:ℕ)) (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)).trans (le_max_left _ _))

lemma halfopen_cover (D : WeightedDirectionPartition V K a b w δ) {t : ℝ}
    (ht : t∈Ico a b) : ∃i : Fin D.count,t∈Ico (D.time i) (D.time (i+1)) := by
  have ht' : t∈Ico (D.time 0) (D.time D.count) := by rwa [D.initial,D.terminal]
  obtain ⟨i,hi,hit⟩ := mem_iUnion₂.mp (Ico_subset_biUnion_Ico D.count D.time ht')
  exact ⟨⟨i,Finset.mem_range.mp hi⟩,hit⟩

lemma cell_direction_oscillation (D : WeightedDirectionPartition V K a b w δ)
    (i : Fin D.count) {s t : ℝ}
    (hs : s∈Icc (D.time i) (D.time (i+1))) (ht : t∈Icc (D.time i) (D.time (i+1))) :
    ‖momentumDirection (V t)-momentumDirection (V s)‖≤2*δ := by
  calc
    _≤‖momentumDirection (V t)-momentumDirection (V (D.time i))‖+
        ‖momentumDirection (V (D.time i))-momentumDirection (V s)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤δ+δ := add_le_add (D.direction_control i i.isLt t ht)
      (by rw [norm_sub_rev]; exact D.direction_control i i.isLt s hs)
    _=_ := by ring

end WeightedDirectionPartition

lemma inv_q_sq_le_of_lower {v : Vec} {m : ℝ} (hm : 0 < m) (h : m ≤ q v) :
    (q v)⁻¹ ^ 2 ≤ m⁻¹ ^ 2 := by
  gcongr
  exact inv_nonneg.mpr (q_pos v).le

lemma PhaseFlowOn.direction_partition_closed_duration {s : Solution} {T c d e w p δ ε φ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase) (B : ClosedConeBin)
    (DY : WeightedDirectionPartition (fun t=>(F.flow zY t).2)
      (fun t=>s.E (t,(F.flow zY t).1)+cross (velocity (F.flow zY t).2) (s.B (t,(F.flow zY t).1))) c d p δ)
    (DX : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
      (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) c e w δ)
    (hc : 0 ≤ c) (hdT : d≤T) (heT : e≤T) (hde : d≤e)
    (hsnz : ∀t∈Icc c d,(F.flow zY t).2≠0)
    (hrnz : ∀t∈Icc c e,(F.flow zX t).2≠0)
    (hsq : ∀t∈Icc c d,(q (F.flow zY t).2)⁻¹^2≤ε)
    (hrq : ∀t∈Icc c e,(q (F.flow zX t).2)⁻¹^2≤ε)
    {H : Set ℝ} (hH : H⊆Icc c d)
    (hbin : ∀r∈H,∃t,InClosedConeBin F.flow zX B t r zY)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hφ : 0<φ)
    (hd : B.dmax≤φ^2/32) (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2)
    (hw : 4≤φ*B.wmin) (hsmall : 2*δ+2*ε≤φ/16) :
    volume H≤ENNReal.ofReal (((DY.count:ℝ)+DX.count)*(81*B.rmax)) := by
  classical
  choose arrival harr using hbin
  let ar : ℝ→ℝ := fun r=>if h:r∈H then arrival r h else 0
  have hsubY (i : Fin DY.count) : Ico (DY.time i) (DY.time (i+1))⊆Icc c d :=
    Ico_subset_Icc_self.trans (DY.cell_subset i.isLt)
  have hsubX (i : Fin DX.count) : Ico (DX.time i) (DX.time (i+1))⊆Icc c e :=
    Ico_subset_Icc_self.trans (DX.cell_subset i.isLt)
  have hb := F.direction_total_hit_duration zX zY B
    (fun i : Fin DY.count=>DY.time i) (fun i=>DY.time (i+1))
    (fun i : Fin DX.count=>DX.time i) (fun i=>DX.time (i+1))
    DY.halfopen_disjoint DX.halfopen_disjoint
    (fun i=>(hsubY i).trans (Icc_subset_Icc hc hdT))
    (fun i=>(hsubX i).trans (Icc_subset_Icc hc heT))
    (fun i t ht=>hsnz t (hsubY i ht)) (fun i t ht=>hrnz t (hsubX i ht))
    (fun i t ht=>hsq t (hsubY i ht)) (fun i t ht=>hrq t (hsubX i ht))
    (fun i a ha b hb=>DY.cell_direction_oscillation i (Ico_subset_Icc_self hb) (Ico_subset_Icc_self ha))
    (fun i a ha b hb=>DX.cell_direction_oscillation i (Ico_subset_Icc_self hb) (Ico_subset_Icc_self ha))
    (H:=H\{d}) ar
    (fun r hr=>DY.halfopen_cover ⟨(hH hr.1).1,lt_of_le_of_ne (hH hr.1).2 (by simpa using hr.2)⟩)
    (fun r hr=>DX.halfopen_cover ⟨(hH hr.1).1,(lt_of_le_of_ne (hH hr.1).2 (by simpa using hr.2)).trans_le hde⟩)
    (fun r hr=>by simpa only [ar,dite_eq_left hr.1] using harr r hr.1)
    hr hrmax hφ hd hDlo hDhi hw hsmall
  rw [measure_sdiff_null (measure_singleton d)] at hb
  simpa only [Fintype.card_fin,ENNReal.ofReal_mul (by positivity : 0≤(DY.count:ℝ)+DX.count),
    ENNReal.ofReal_add (by positivity : 0≤(DY.count:ℝ)) (by positivity : 0≤(DX.count:ℝ)),
    ENNReal.ofReal_natCast] using hb

lemma Admissible.direction_stable_closed_cell_bound_oai {d₀ : Datum} (hd₀ : Admissible d₀)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d₀ s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (B : ClosedConeBin) (a b c d e m δ φ : ℝ),
      zX∈tsupport d₀.f₀ → 0 ≤ c → c≤d → d≤e → e≤T → Icc a b⊆Icc c e →
      0 < m → m≤B.qmin → m≤B.wmin →
      e-c≤(128*(P/m)*(M+Real.sqrt (A*Real.log (2+P))))⁻¹^2 →
      e-c≤((m/2)/P)^2 → P^(3/5:ℝ)≤ m/2 → (m/2)^(-3/5:ℝ)≤δ → δ≤1 →
      0<B.rmin → 0≤B.rmax → 0<φ →
      B.dmax≤φ^2/32 → φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → 4≤φ*B.wmin →
      2*δ+2*((m/2)⁻¹)^2≤φ/16 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d₀.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ENNReal.ofReal (B.qmin/2)*labelOccupation (fun z=>s.f (0,z))
        (closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d)≤
      ENNReal.ofReal (C*B.rmax*(Real.log (2+P))^6/δ)*ENNReal.ofReal (datumEnergyNumber d₀) := by
  obtain ⟨C,hC,hpart⟩ := hd₀.exists_stable_direction_partition T₀ M A hM hA
  refine ⟨162*C,by positivity,?_⟩
  filter_upwards [hpart,eventually_direction_absorption 0] with P hpart hlarge
  intro s T F hs hT hTT zX B a b c d e m δ φ hzX hc hcd hde he hJ hm hmq hmw hstable hlen hhigh hδ hδ1
    hr hrmax hφ hd hDlo hDhi hw hsmall hsource HZ
  have hp : 0<P := zero_lt_one.trans_le hlarge.1
  have hL : 0≤Real.log (2+P) := zero_le_one.trans hlarge.2.1
  have hδ0 : 0<δ := (Real.rpow_pos_of_pos (half_pos hm) (-3/5)).trans_le hδ
  have hCtime : Icc c d⊆Icc 0 T := Icc_subset_Icc hc (hde.trans he)
  have hdata : ∀ z,(closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d z).Nonempty →
      volume (closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d z)≤
          ENNReal.ofReal (162*C*B.rmax*(Real.log (2+P))^6/δ) ∧
        B.qmin/2≤q (F.flow z c).2 := by
    intro z hz
    obtain ⟨r,hzS,hrC,t,htJ,hbin⟩ := hz
    have hqm : m≤q (F.flow z r).2 := hmq.trans hbin.2.2.1.1
    have hwm : m≤q (F.flow zX t).2 := hmw.trans hbin.2.2.2.1.1
    obtain ⟨kY,DY,hDY,hkY,hqY⟩ := hpart s T F hs hT hTT z c d r m δ hzS hc (hde.trans he) hrC hm hqm
      ((by linarith : d-c≤e-c).trans hstable) ((by linarith : d-c≤e-c).trans hlen)
      hhigh hδ hδ1 hsource HZ
    obtain ⟨kX,DX,hDX,hkX,hqX⟩ := hpart s T F hs hT hTT zX c e t m δ hzX hc he (hJ htJ) hm hwm
      hstable hlen hhigh hδ hδ1 hsource HZ
    constructor
    · have hbound := F.direction_partition_closed_duration zX z B DY DX hc (hde.trans he) he hde
        (fun r hr=>(hqY r hr).2) (fun r hr=>(hqX r hr).2)
        (fun r hr=>inv_q_sq_le_of_lower (half_pos hm) (hqY r hr).1)
        (fun r hr=>inv_q_sq_le_of_lower (half_pos hm) (hqX r hr).1)
        (H:=closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d z)
        (fun _ hh=>hh.2.1) (fun r hh=>by obtain ⟨_,_,t,_,ht⟩:=hh; exact ⟨t,ht⟩)
        hr hrmax hφ hd hDlo hDhi hw hsmall
      refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
      calc
        _≤(C*(Real.log (2+P))^6/δ+C*(Real.log (2+P))^6/δ)*(81*B.rmax) :=
          mul_le_mul_of_nonneg_right (add_le_add hDY hDX) (by positivity)
        _=_ := by ring
    · have hh := (HZ z hzS).velocity_stability_scale hc (hde.trans he) hrC
        ((F.continuousOn_time z).snd.mono hCtime) hM hA.le hp hL hm
        (by norm_num : (0:ℝ)<1) le_rfl (by norm_num : (128:ℝ)≤128) hqm
        (by simpa only [div_one] using ((by linarith : d-c≤e-c).trans hstable)) c (left_mem_Icc.mpr hcd)
      linarith [hh.2.2.1,hbin.2.2.1.1]
  rw [←hs.initial_energy_eq]
  apply F.label_occupation_cell_bound hs.energyPrefix (hCtime (left_mem_Icc.mpr hcd))
  · intro z
    by_cases hz : (closedBinHits F.flow zX B (tsupport d₀.f₀) a b c d z).Nonempty
    · exact (hdata z hz).1
    · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]
  · exact fun z hz=>(hdata z hz).2

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direction_stable_closed_cell_bound_oai := @OAI.RVM.Admissible.direction_stable_closed_cell_bound_oai
