-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:59:30.684591+00:00
-- url     : https://prove2.me/submissions/783d7e22-d633-415c-823d-53977d756bd4

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

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma full_directional_derivative {f : Particle} {t : ℝ} {x v u K : Vec}
    (hf : DifferentiableAt ℝ f (t,x,v)) :
    fderiv ℝ f (t,x,v) (1,u,K) =
      deriv (fun t' => f (t',x,v)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,v)) x i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,x,v')) v i) := by
  let L := fderiv ℝ f (t,x,v)
  have hT := hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (x,v)))
  have hιX : HasFDerivAt (fun y : Vec => (t,y,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) x := by
    exact (hasFDerivAt_const t x).prodMk
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const v x))
  have hιV : HasFDerivAt (fun y : Vec => (t,x,y))
      ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
    exact (hasFDerivAt_const t v).prodMk
      ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))
  have hX := hf.hasFDerivAt.comp x hιX
  have hV := hf.hasFDerivAt.comp v hιV
  have ht : deriv (fun t' => f (t',x,v)) t = L (1,0,0) := by
    convert hT.deriv using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hx : fderiv ℝ (fun y => f (t,y,v)) x u = L (0,u,0) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F u) hX.fderiv
    convert h using 1 <;> rfl
  have hv : fderiv ℝ (fun v' => f (t,x,v')) v K = L (0,0,K) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F K) hV.fderiv
    convert h using 1 <;> rfl
  change L (1,u,K) = deriv (fun t' => f (t',x,v)) t +
    (∑ i : Fin 3, u i * fderiv ℝ (fun y => f (t,y,v)) x (basis i)) +
    (∑ i : Fin 3, K i * fderiv ℝ (fun v' => f (t,x,v')) v (basis i))
  rw [← clm_sum_basis, ← clm_sum_basis, ht, hx, hv]
  rw [← map_add, ← map_add]
  congr 1
  ext <;> simp

lemma hasDerivAt_particle_along_curve {f : Particle} {X V : ℝ → Vec}
    {t : ℝ} {u K : Vec} (hf : DifferentiableAt ℝ f (t,X t,V t))
    (hX : HasDerivAt X u t) (hV : HasDerivAt V K t) :
    HasDerivAt (fun s => f (s,X s,V s))
      (deriv (fun s => f (s,X t,V t)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,V t)) (X t) i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,X t,v')) (V t) i)) t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hX.prodMk hV))
  rw [full_directional_derivative hf] at h
  exact h

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedPhaseDomain
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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.transport {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) (z : Phase) :
    f (t,F.flow z t) = f (0,z) := by
  rcases ht.1.eq_or_lt with h | h
  · simp only [← h,F.initial]
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hc : ContinuousOn (fun s => f (s,F.flow z s)) (Icc 0 t) :=
    hf.continuousOn.comp (continuousOn_id.prodMk ((F.continuousOn_time z).mono hsub))
      (fun _ hs => ⟨hsub hs,mem_univ _⟩)
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => f (r,F.flow z r)) (0 : ℝ) s := by
    intro s hs
    have hsT : s ∈ Ioo 0 T := ⟨hs.1,hs.2.trans_le ht.2⟩
    have hdiff : DifferentiableAt ℝ f (s,F.flow z s) :=
      ((hf (s,F.flow z s) ⟨Ioo_subset_Icc_self hsT,mem_univ _⟩).contDiffAt
        (prod_mem_nhds (Icc_mem_nhds hsT.1 hsT.2) univ_mem)).differentiableAt (by simp)
    have hode := (F.ode z s (Ioo_subset_Icc_self hsT)).hasDerivAt (Icc_mem_nhds hsT.1 hsT.2)
    have hh := hasDerivAt_particle_along_curve (X := fun r => (F.flow z r).1)
      (V := fun r => (F.flow z r).2) hdiff hode.fst hode.snd
    simpa only [lorentzField,lorentzPhase,heq s hsT] using hh
  obtain ⟨r,_,he⟩ := exists_hasDerivAt_eq_slope (fun s => f (s,F.flow z s)) (fun _ => 0) h hc hd
  have hnum : f (t,F.flow z t)-f (0,F.flow z 0)=0 :=
    (div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr (ne_of_gt h))
  simpa only [F.initial] using sub_eq_zero.mp hnum

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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_PhaseHits
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.lintegral_comp {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (g : Phase → ENNReal) :
    ∫⁻ z, g (F.flow z t) = ∫⁻ z, g z := by
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (s := univ) MeasurableSet.univ
    (fun z _ => (F.label z t ht).hasFDerivWithinAt) (F.bijective t ht).1.injOn g
  simpa only [Set.image_univ,(F.bijective t ht).2.range_eq,setLIntegral_univ,
    F.det_one _ _ ht,abs_one,ENNReal.ofReal_one,one_mul] using hh.symm

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_PhaseAcceleration
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
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

namespace RVM

lemma jointEnergyBudget_eq {s : Solution} {α : Phase → ℝ → Phase} {zX : Phase} {T : ℝ}
    (k : ℕ) {a b I : ℝ} (hJ : Icc a b⊆Icc (0:ℝ) T) (n : ℕ × ℕ) :
    jointEnergyBudget s α zX T k a b I n =
      (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc a b, ∫⁻ z : Phase,
        (sameTimeBudgetSet α zX T k n).indicator (fun p => ENNReal.ofReal (q p.2.2*s.f p)) (t,z)+
        (arrivalBudgetSet α zX T k n).indicator (fun p => ENNReal.ofReal (q p.2.2*s.f p)) (t,z) := by
  unfold jointEnergyBudget
  congr 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  apply lintegral_congr
  intro z
  have he : prefixPhaseEnergy s T (t,z)=ENNReal.ofReal (q z.2*s.f (t,z)) :=
    by simp only [prefixPhaseEnergy,indicator_of_mem (show (t,z)∈Icc 0 T ×ˢ (univ : Set Phase) from ⟨hJ ht,mem_univ _⟩)]
  by_cases h₁ : (t,z)∈sameTimeBudgetSet α zX T k n <;>
    by_cases h₂ : (t,z)∈arrivalBudgetSet α zX T k n <;> simp [h₁,h₂,he]

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

namespace RVM

lemma labelOccupation_le_duration_mass {f₀ : Phase → ℝ} {H : Phase → Set ℝ}
    {Z : Set Phase} (hZ : MeasurableSet Z) {D : ℝ}
    (hD : ∀ z, volume (H z)≤ENNReal.ofReal D)
    (hz : ∀ z, (H z).Nonempty → z∈Z) :
    labelOccupation f₀ H ≤ ENNReal.ofReal D * ∫⁻ z in Z, ENNReal.ofReal (f₀ z) := by
  rw [← lintegral_indicator hZ,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro z
  dsimp only
  by_cases he : (H z).Nonempty
  · rw [indicator_of_mem (hz z he)]
    calc
      _ ≤ ENNReal.ofReal (f₀ z)*ENNReal.ofReal D := by gcongr; exact hD z
      _ = _ := mul_comm _ _
  · simp only [not_nonempty_iff_eq_empty.mp he,measure_empty,mul_zero,zero_le]

lemma PhaseFlowOn.restricted_label_mass_bound {s : Solution} {T t p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (ht : t∈Icc 0 T)
    {Z : Set Phase} (hZ : MeasurableSet Z) {G : Set (ℝ × Phase)}
    (hmom : ∀ z∈Z, p≤q (F.flow z t).2)
    (hG : ∀ z∈Z, (t,F.flow z t)∈G) :
    ENNReal.ofReal p * (∫⁻ z in Z, ENNReal.ofReal (s.f (0,z))) ≤
      ∫⁻ z : Phase, G.indicator (fun p => ENNReal.ofReal (q p.2.2 * s.f p)) (t,z) := by
  rw [← lintegral_indicator hZ,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← F.lintegral_comp ht (fun z => G.indicator (fun p => ENNReal.ofReal (q p.2.2 * s.f p)) (t,z))]
  apply lintegral_mono
  intro z
  dsimp only
  by_cases hz : z∈Z
  · rw [indicator_of_mem hz,indicator_of_mem (hG z hz),F.transport hs.f_smooth hs.vlasov ht,
      ENNReal.ofReal_mul (q_pos _).le]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hmom z hz)) le_rfl
  · rw [indicator_of_notMem hz,mul_zero]
    exact zero_le

end RVM

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

lemma compact_hit_labels {A : Type*} [TopologicalSpace A] [T2Space A]
    {S : Set A} {T : ℝ} (hS : IsCompact S) {H : Set (ℝ × ℝ × A)}
    (hH : IsClosed H) :
    IsCompact {a | a ∈ S ∧ ∃ t ∈ Icc 0 T, ∃ s ∈ Icc 0 T, (t,s,a) ∈ H} := by
  have hc : IsCompact ((Icc 0 T ×ˢ (Icc 0 T ×ˢ S)) ∩ H) :=
    (isCompact_Icc.prod (isCompact_Icc.prod hS)).inter_right hH
  have heq : (fun p : ℝ × ℝ × A => p.2.2) '' ((Icc 0 T ×ˢ (Icc 0 T ×ˢ S)) ∩ H) =
      {a | a ∈ S ∧ ∃ t ∈ Icc 0 T, ∃ s ∈ Icc 0 T, (t,s,a) ∈ H} := by
    ext a
    constructor
    · rintro ⟨⟨t,s,b⟩,⟨⟨ht,hs,hb⟩,hh⟩,rfl⟩
      exact ⟨hb,t,ht,s,hs,hh⟩
    · rintro ⟨ha,t,ht,s,hs,hh⟩
      exact ⟨(t,s,a),⟨⟨ht,hs,ha⟩,hh⟩,rfl⟩
  rw [← heq]
  exact hc.image (continuous_snd.comp continuous_snd)

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

lemma isClosed_inClosedConeBin {α : Phase → ℝ → Phase}
    (hα : Continuous (fun p : ℝ × Phase => α p.2 p.1)) (zX : Phase) (B : ClosedConeBin) :
    IsClosed {p : ℝ × ℝ × Phase | InClosedConeBin α zX B p.1 p.2.1 p.2.2} := by
  have hX := hα.comp (continuous_fst.prodMk continuous_const :
    Continuous (fun p : ℝ × ℝ × Phase => (p.1,zX)))
  have hY := hα.comp (continuous_snd.fst.prodMk continuous_snd.snd :
    Continuous (fun p : ℝ × ℝ × Phase => (p.2.1,p.2.2)))
  have hR : Continuous (fun p : ℝ × ℝ × Phase => p.1-p.2.1) := continuous_fst.sub continuous_snd.fst
  have hΔ := hX.fst.sub hY.fst
  have hu := (contDiff_velocity (k:=1)).continuous.comp hY.snd
  have ha := (contDiff_velocity (k:=1)).continuous.comp hX.snd
  have hd := hR.sub (continuous_dot.comp (hΔ.prodMk hu))
  have hD := hR.sub (continuous_dot.comp (hΔ.prodMk ha))
  have he := continuous_const.sub (continuous_dot.comp (ha.prodMk hu)) (f:=fun _ => (1:ℝ))
  have hq := (contDiff_q (k:=1)).continuous.comp hY.snd
  have hw := (contDiff_q (k:=1)).continuous.comp hX.snd
  exact (isClosed_eq hR hΔ.norm).inter
    ((isClosed_Icc.preimage hR).inter ((isClosed_Icc.preimage hq).inter
      ((isClosed_Icc.preimage hw).inter
        (((isClosed_le (hR.mul continuous_const) hd).inter (isClosed_le hd (hR.mul continuous_const))).inter
          (((isClosed_le (hR.mul continuous_const) hD).inter (isClosed_le hD (hR.mul continuous_const))).inter
            (isClosed_Icc.preimage he))))))

lemma PhaseFlowOn.compact_closed_bin_hit_labels {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S) :
    IsCompact {z | z∈S ∧ ∃ t∈Icc 0 T, ∃ r∈Icc 0 T,
      t∈Icc a b ∧ r∈Icc c d ∧ InClosedConeBin F.flow zX B t r z} := by
  let H : Set (ℝ × ℝ × Phase) := {p | p.1∈Icc a b ∧ p.2.1∈Icc c d ∧
    InClosedConeBin (prefixFlow F.flow T) zX B p.1 p.2.1 p.2.2}
  have hH : IsClosed H := (isClosed_Icc.preimage continuous_fst).inter
    ((isClosed_Icc.preimage continuous_snd.fst).inter
      (isClosed_inClosedConeBin (F.continuous_prefixFlow hs hT) zX B))
  convert compact_hit_labels hS hH using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  constructor
  · rintro ⟨hz,t,ht,r,hr,htJ,hrC,hbin⟩
    refine ⟨hz,t,ht,r,hr,htJ,hrC,?_⟩
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq ht,prefixClamp_eq hr] using hbin
  · rintro ⟨hz,t,ht,r,hr,htJ,hrC,hbin⟩
    refine ⟨hz,t,ht,r,hr,htJ,hrC,?_⟩
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq ht,prefixClamp_eq hr] using hbin

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceCellLast
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Set

namespace RVM

lemma sourceCellLast_le {T len : ℝ} (hT : 0 ≤ T) (hlen : 0 < len) :
    (sourceCellLast T len:ℝ)*len ≤ T := by
  exact (le_div_iff₀ hlen).mp (Nat.floor_le (div_nonneg hT hlen.le))

lemma sourceCell_mem_prefix {T len : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i ≤ sourceCellLast T len) :
    0 ≤ sourceCellLo len i ∧ sourceCellLo len i ≤ sourceCellHi T len i ∧
      sourceCellHi T len i ≤ T ∧ sourceCellHi T len i-sourceCellLo len i ≤ len := by
  have hil : (i:ℝ)*len ≤ T := (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hlen.le).trans
    (sourceCellLast_le hT hlen)
  have his : (i:ℝ) ≤ (i+1:ℕ) := by exact_mod_cast Nat.le_succ i
  have hull : (i:ℝ)*len ≤ (i+1:ℕ)*len := mul_le_mul_of_nonneg_right his hlen.le
  refine ⟨by dsimp [sourceCellLo]; positivity,le_min hil hull,min_le_left _ _,?_⟩
  have hh : sourceCellHi T len i ≤ (i:ℝ)*len+len := by
    unfold sourceCellHi
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using (min_le_right T ((i+1:ℕ)*len))
  dsimp [sourceCellLo]
  linarith

lemma sourceCell_full {T len : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i < sourceCellLast T len) :
    sourceCellHi T len i-sourceCellLo len i=len := by
  have hh : ((i+1:ℕ):ℝ)*len ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hi) hlen.le).trans
      (sourceCellLast_le hT hlen)
  unfold sourceCellHi sourceCellLo
  rw [min_eq_right hh]
  push_cast
  ring

lemma sourceCell_cover {T len t : ℝ} (hlen : 0 < len) (ht : t ∈ Icc 0 T) :
    ∃ i ≤ sourceCellLast T len, t ∈ Icc (sourceCellLo len i) (sourceCellHi T len i) := by
  let i := ⌊t/len⌋₊
  have hi : i ≤ sourceCellLast T len := Nat.floor_mono ((div_le_div_iff_of_pos_right hlen).mpr ht.2)
  refine ⟨i,hi,?_,le_min ht.2 ?_⟩
  · exact (le_div_iff₀ hlen).mp (Nat.floor_le (div_nonneg ht.1 hlen.le))
  · have hh := Nat.lt_floor_add_one (t/len)
    apply le_of_lt
    have hf := (div_lt_iff₀ hlen).mp hh
    simpa only [Nat.cast_add,Nat.cast_one] using hf

lemma selectedSourceCells_cover {T len a b r : ℝ} (hlen : 0 < len) :
    Icc (max 0 (a-r)) (min T b) ⊆
      ⋃ i ∈ selectedSourceCells T len a b r, Icc (sourceCellLo len i) (sourceCellHi T len i) := by
  intro t ht
  obtain ⟨i,hi,htC⟩ := sourceCell_cover hlen ⟨(le_max_left _ _).trans ht.1,ht.2.trans (min_le_left _ _)⟩
  refine mem_iUnion₂.mpr ⟨i,?_,htC⟩
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    htC.1.trans (ht.2.trans (min_le_right _ _)),
    (le_max_right _ _).trans (ht.1.trans htC.2)⟩

lemma selectedSourceCells_subset_prefix {T len a b r : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i ∈ selectedSourceCells T len a b r) :
    0 ≤ sourceCellLo len i ∧ sourceCellLo len i ≤ sourceCellHi T len i ∧
      sourceCellHi T len i ≤ T ∧ sourceCellHi T len i-sourceCellLo len i ≤ len := by
  classical
  exact sourceCell_mem_prefix hT hlen (by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega)

lemma selectedSourceCells_enlargement {T len a b r : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i ∈ selectedSourceCells T len a b r) :
    Icc (sourceCellLo len i) (sourceCellHi T len i) ⊆
      Icc (max 0 (a-r-len)) (min T (b+len)) := by
  have hc := selectedSourceCells_subset_prefix hT hlen hi
  have hh := (Finset.mem_filter.mp hi).2
  intro t ht
  refine ⟨max_le (hc.1.trans ht.1) ?_,le_min (ht.2.trans hc.2.2.1) ?_⟩  <;> linarith [hc.2.2.2,hh.1,hh.2,ht.1,ht.2]

lemma sourceCells_pairwise_disjoint {T len : ℝ} (hlen : 0 < len) :
    Pairwise fun i j : ℕ => Disjoint
      (Ioc (sourceCellLo len i) (sourceCellHi T len i))
      (Ioc (sourceCellLo len j) (sourceCellHi T len j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  have hd (k : ℕ) : sourceCellHi T len k  ≤  ((k+1:ℕ):ℝ)*len := min_le_right _ _
  rcases lt_or_gt_of_ne hij with hh | hh
  · have hle : ((i+1:ℕ):ℝ)*len ≤ (j:ℝ)*len :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hh) hlen.le
    exact (not_lt_of_ge ((hi.2.trans (hd i)).trans hle)) hj.1
  · have hle : ((j+1:ℕ):ℝ)*len ≤ (i:ℝ)*len :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hh) hlen.le
    exact (not_lt_of_ge ((hj.2.trans (hd j)).trans hle)) hi.1

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

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

namespace RVM

lemma sum_cell_lintegral_le {ι : Type*} (S : Finset ι) (a b : ι → ℝ)
    (g : ℝ → ℝ≥0∞) {J : Set ℝ}
    (hdisj : Set.PairwiseDisjoint (↑S) (fun i => Ioc (a i) (b i)))
    (hsub : ∀ i∈S, Ioc (a i) (b i)⊆J) :
    (∑ i∈S, ∫⁻ t in Icc (a i) (b i), g t)≤∫⁻ t in J, g t := by
  have he (i : ι) : (∫⁻ t in Icc (a i) (b i), g t)=(∫⁻ t in Ioc (a i) (b i), g t) := by
    rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ:=volume) (a:=a i) (b:=b i))]
  simp_rw [he]
  rw [← lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_Ioc)]
  exact lintegral_mono_set (iUnion₂_subset fun i hi => hsub i hi)

end RVM

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


lemma PhaseFlowOn.compact_closedBinHits_labels {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) :
    IsCompact {z | (closedBinHits F.flow zX B S a b c d z).Nonempty} := by
  convert F.compact_closed_bin_hit_labels (a:=a) (b:=b) (c:=c) (d:=d) hs hT zX B hS using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  constructor
  · rintro ⟨r,hz,hr,t,ht,hbin⟩
    exact ⟨hz,t,hJ ht,r,hC hr,ht,hr,hbin⟩
  · rintro ⟨hz,t,_,r,_,ht,hr,hbin⟩
    exact ⟨r,hz,hr,t,ht,hbin⟩

lemma PhaseFlowOn.averaged_cell_occupation_interior {s : Solution} {T a b p D : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hCT : Icc a b ⊆ Icc (0:ℝ) T) {H : Phase → Set ℝ}
    {Z : Set Phase} (hZ : MeasurableSet Z) {G : Set (ℝ × Phase)}
    (hD : ∀ z, volume (H z) ≤ ENNReal.ofReal D)
    (hz : ∀ z, (H z).Nonempty → z∈Z)
    (hmom : ∀ t∈Ioo a b, ∀ z∈Z, p ≤ q (F.flow z t).2)
    (hG : ∀ t∈Ioo a b, ∀ z∈Z, (t,F.flow z t)∈G) :
    ENNReal.ofReal (b-a) * ENNReal.ofReal p * labelOccupation (fun z => s.f (0,z)) H ≤
      ENNReal.ofReal D * ∫⁻ t in Icc a b, ∫⁻ z : Phase,
        G.indicator (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z) := by
  have hbnd := lintegral_mono_ae (μ:=volume.restrict (Ioo a b))
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht =>
      F.restricted_label_mass_bound hs (hCT (Ioo_subset_Icc_self ht)) hZ (hmom t ht) (hG t ht)))
  rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo] at hbnd
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ:=volume) (a:=a) (b:=b))] at hbnd
  have hocc := labelOccupation_le_duration_mass hZ hD hz (f₀:=fun z => s.f (0,z))
  calc
    _ ≤ ENNReal.ofReal (b-a)*ENNReal.ofReal p*(ENNReal.ofReal D*
        ∫⁻ z in Z, ENNReal.ofReal (s.f (0,z))) := mul_le_mul' le_rfl hocc
    _ = ENNReal.ofReal D*((ENNReal.ofReal p * ∫⁻ z in Z, ENNReal.ofReal (s.f (0,z))) *
        ENNReal.ofReal (b-a)) := by ac_rfl
    _ ≤ _ := by gcongr

lemma dyadicWindow_momentum_enlarged {Q : ℝ} {n : ℕ} (hQ : 0 < Q)
    (hlo : (2:ℝ)^n/4 ≤ Q) (hhi : Q ≤ 4*(2:ℝ)^n) :
    DyadicWindow 4 n Q⁻¹ := by
  norm_num [DyadicWindow]
  rw [← div_eq_mul_inv,le_div_iff₀ hQ,div_le_iff₀ hQ]
  constructor <;> nlinarith [pow_pos (show (0:ℝ)<2 by norm_num) n]

lemma dyadicWindow_angle_enlarged {r : ℝ} {n : ℕ}
    (hlo : (2:ℝ)⁻¹^n/4 ≤ r) (hhi : r ≤ 6*(2:ℝ)⁻¹^n) :
    DyadicWindow 4 n r := by
  have he : (2:ℝ)^n*(2:ℝ)⁻¹^n=1 := by
    rw [← mul_pow]; norm_num
  have hl := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (2:ℝ)^n by positivity)
  have hh := mul_le_mul_of_nonneg_left hhi (show 0 ≤ (2:ℝ)^n by positivity)
  norm_num [DyadicWindow]
  constructor <;> nlinarith

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

lemma PhaseFlowOn.small_closed_bin_cell_data {s : Solution}
    {T M A P L lo hi a b c d massScale φ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ∀ z, (closedBinHits F.flow zX B S a b c d z).Nonempty →
      volume (closedBinHits F.flow zX B S a b c d z) ≤ ENNReal.ofReal (40*B.rmax) ∧
      ∀ t∈Icc c d, p/256 ≤ q (F.flow z t).2 ∧ q (F.flow z t).2 ≤ p/16 ∧
        φ/4 ≤ ‖velocity (F.flow z t).2-velocity (F.flow zX t).2‖ ∧
        ‖velocity (F.flow z t).2-velocity (F.flow zX t).2‖ ≤ 6*φ := by
  let U := Icc lo hi
  have hUT : U ⊆ Icc 0 T := Icc_subset_Icc hlo0 hhiT
  have hCT : Icc c d ⊆ Icc 0 T := hC.trans hUT
  have hstable (z : Phase) (H : IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
      (r : ℝ) (hr : r∈U) (hqm : massScale ≤ q (F.flow z r).2) :=
    H.velocity_stability_scale hlo0 hhiT hr ((F.continuousOn_time z).snd.mono hUT)
      hM hA hP hL hm hφ hφ1 hconst hqm hlen
  intro z hz
  obtain ⟨r₀,hzS,hr₀,t₀,ht₀,hbin₀⟩ := hz
  have hsource := hstable z (HZ z hzS) r₀ (hC hr₀) (hmq.trans hbin₀.2.2.1.1)
  have hreceiver := hstable zX HX t₀ (hJ ht₀) (hmw.trans hbin₀.2.2.2.1.1)
  obtain ⟨n₀,_,_,_,hsep₀,hupper₀⟩ := small_closed_bin_hit_geometry hbin₀ hr hφ hd hDlo hDhi hw
  have href (t : ℝ) (ht : t∈U) :
      ‖velocity (F.flow z t).2-velocity (F.flow zX t).2-
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)‖ ≤ φ/16 := by
    have hh := relative_ref_triangle (hsource t ht).2.1 (hreceiver t ht).2.1
    linarith
  constructor
  · have hsep (r : ℝ) (hrH : r∈closedBinHits F.flow zX B S a b c d z) :
        ‖(F.flow z r).1-(F.flow zX r).1‖ ≤ 5*B.rmax*φ := by
      obtain ⟨_,hrC,t,htJ,hbin⟩ := hrH
      obtain ⟨n,_,hgeom,hangle,_,_⟩ := small_closed_bin_hit_geometry hbin hr hφ hd hDlo hDhi hw
      have hrt : r ≤ t := by linarith [hbin.2.1.1]
      have hsub : Icc r t ⊆ U := Icc_subset_Icc (hC hrC).1 (hJ htJ).2
      have hh := retarded_same_time_separation hrt
        (fun u hu => ((F.ode zX u (hUT (hsub hu))).mono (hsub.trans hUT)).fst)
        (fun u hu => velocity_ref_triangle (hreceiver u (hsub hu)).2.1
          (hreceiver t (hJ htJ)).2.1 hangle) hgeom
      have hrad : 0 ≤ B.rmax := (sub_nonneg.mpr hrt).trans hbin.2.1.2
      calc
        _ ≤ (4*φ+2*(φ/32))*(t-r) := hh
        _ ≤ (5*φ)*B.rmax := mul_le_mul (by linarith) hbin.2.1.2
          (sub_nonneg.mpr hrt) (by positivity)
        _ = _ := by ring
    have hh := stable_cell_duration (convex_Icc c d)
      (show closedBinHits F.flow zX B S a b c d z ⊆ Icc c d from fun _ h => h.2.1)
      (half_pos hφ) hsep₀ ((F.continuousOn_time zX).fst.mono hCT)
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
          (velocity (F.flow z t).2-velocity (F.flow zX t).2)‖ ≤ φ/16 := by
        rw [norm_sub_rev]
        exact href t (hC ht)
      linarith
    · have hn := norm_sub_norm_le
        (velocity (F.flow z t).2-velocity (F.flow zX t).2)
        (velocity (F.flow z r₀).2-velocity (F.flow zX t₀).2)
      linarith [href t (hC ht)]

lemma PhaseFlowOn.small_closed_bin_cell_payment {s : Solution}
    {T M A P L lo hi a b c d massScale φ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ENNReal.ofReal (d-c) * ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ENNReal.ofReal (40*B.rmax) * ∫⁻ t in Icc c d, ∫⁻ z : Phase,
        (sameTimeBudgetSet F.flow zX T 4 (np,nf)).indicator
          (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z) := by
  have hUT : Icc lo hi ⊆ Icc 0 T := Icc_subset_Icc hlo0 hhiT
  have hCT := hC.trans hUT
  have hdata := F.small_closed_bin_cell_data zX B hlo0 hhiT hJ hC hM hA hP hL
    hm hφ hφ1 hconst hlen hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
  have hlabels := F.compact_closedBinHits_labels hs hT zX B hS (hJ.trans hUT) hCT
  apply F.averaged_cell_occupation_interior hs hCT hlabels.measurableSet
  · intro z
    by_cases hz : (closedBinHits F.flow zX B S a b c d z).Nonempty
    · exact (hdata z hz).1
    · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]
  · exact fun _ hz => hz
  · exact fun t ht z hz => ((hdata z hz).2 t (Ioo_subset_Icc_self ht)).1
  · intro t ht z hz
    obtain ⟨hqlo,hqhi,hvlo,hvhi⟩ := (hdata z hz).2 t (Ioo_subset_Icc_self ht)
    refine ⟨⟨?_,?_⟩,dyadicWindow_momentum_enlarged (q_pos _) ?_ ?_,
      dyadicWindow_angle_enlarged ?_ ?_⟩
    · have hct : 0 ≤ c := (hCT (left_mem_Icc.mpr (le_of_lt (ht.1.trans ht.2)))).1
      exact hct.trans_lt ht.1
    · have hdt : d ≤ T := (hCT (right_mem_Icc.mpr (le_of_lt (ht.1.trans ht.2)))).2
      exact ht.2.trans_le hdt
    · rw [hp] at hqlo
      linarith
    · rw [hp] at hqhi
      linarith
    · simpa only [← hφeq] using hvlo
    · simpa only [← hφeq] using hvhi

lemma sameTimeBudget_energy_le_joint {s : Solution} {α : Phase → ℝ → Phase}
    {zX : Phase} {T a b I : ℝ} {k : ℕ} {n : ℕ × ℕ}
    (hJ : Icc a b ⊆ Icc (0:ℝ) T) (hI : 0 < I) :
    (∫⁻ t in Icc a b, ∫⁻ z : Phase,
      (sameTimeBudgetSet α zX T k n).indicator
        (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z)) ≤
      ENNReal.ofReal I * jointEnergyBudget s α zX T k a b I n := by
  rw [jointEnergyBudget_eq k hJ n,← mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hI) ENNReal.ofReal_ne_top,one_mul]
  exact lintegral_mono fun t => lintegral_mono fun z => le_add_right le_rfl

lemma closedBinHits_clip_receiver (α : Phase → ℝ → Phase) (zX : Phase)
    (B : ClosedConeBin) (S : Set Phase) (a b c d : ℝ) :
    closedBinHits α zX B S a b c d =
      closedBinHits α zX B S (max a c) (min b (d+B.rmax)) c d := by
  funext z
  ext r
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    have hrt : r ≤ t := by
      have hh := hbin.1
      linarith [norm_nonneg ((α zX t).1-(α z r).1)]
    exact ⟨hz,hr,t,⟨max_le ht.1 (hr.1.trans hrt),le_min ht.2 (by
      have hh := hbin.2.1.2
      linarith [hr.2])⟩,hbin⟩
  · rintro ⟨hz,hr,t,ht,hbin⟩
    exact ⟨hz,hr,t,⟨(le_max_left a c).trans ht.1,ht.2.trans (min_le_left _ _)⟩,hbin⟩

lemma PhaseFlowOn.compact_closedBinHits_joint {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) :
    IsCompact {p : ℝ × Phase | p.1∈closedBinHits F.flow zX B S a b c d p.2} := by
  let K : Set (ℝ × ℝ × Phase) := (Icc a b ×ˢ (Icc c d ×ˢ S)) ∩
    {p | InClosedConeBin (prefixFlow F.flow T) zX B p.1 p.2.1 p.2.2}
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod hS)).inter_right
    (isClosed_inClosedConeBin (F.continuous_prefixFlow hs hT) zX B)
  convert hK.image continuous_snd using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    refine ⟨(t,p),⟨⟨ht,hr,hz⟩,?_⟩,rfl⟩
    change InClosedConeBin (prefixFlow F.flow T) zX B t p.1 p.2
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq (hJ ht),
      prefixClamp_eq (hC hr)] using hbin
  · rintro ⟨⟨t,r,z⟩,⟨⟨ht,hr,hz⟩,hbin⟩,rfl⟩
    refine ⟨hz,hr,t,ht,?_⟩
    change InClosedConeBin (prefixFlow F.flow T) zX B t r z at hbin
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq (hJ ht),
      prefixClamp_eq (hC hr)] using hbin

lemma PhaseFlowOn.measurable_closedBinHits_duration {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) :
    Measurable fun z => volume (closedBinHits F.flow zX B S a b c d z) :=
  measurable_measure_prodMk_right (F.compact_closedBinHits_joint hs hT zX B hS hJ hC).measurableSet

lemma PhaseFlowOn.closedBinHits_occupation_le_sum {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    {ι : Type*} (N : Finset ι) (l u : ι → ℝ)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : ∀ i∈N, Icc (l i) (u i) ⊆ Icc 0 T)
    (hcover : Icc c d ⊆ ⋃ i∈N, Icc (l i) (u i)) :
    labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ∑ i∈N, labelOccupation (fun z => s.f (0,z))
        (closedBinHits F.flow zX B S a b (l i) (u i)) := by
  have hfm : Measurable (fun z : Phase => ENNReal.ofReal (s.f (0,z))) :=
    (hs.f_smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨⟨le_rfl,hT⟩,mem_univ _⟩)).measurable.ennreal_ofReal
  have hsub (z : Phase) : closedBinHits F.flow zX B S a b c d z ⊆
      ⋃ i∈N, closedBinHits F.flow zX B S a b (l i) (u i) z := by
    rintro r ⟨hz,hr,t,ht,hbin⟩
    obtain ⟨i,hi,hrC⟩ := mem_iUnion₂.mp (hcover hr)
    exact mem_iUnion₂.mpr ⟨i,hi,hz,hrC,t,ht,hbin⟩
  unfold labelOccupation
  rw [← lintegral_finsetSum (f := fun i z => ENNReal.ofReal (s.f (0,z)) *
    volume (closedBinHits F.flow zX B S a b (l i) (u i) z)) N (fun i hi => hfm.mul
    (F.measurable_closedBinHits_duration hs hT zX B hS hJ (hC i hi)))]
  apply lintegral_mono
  intro z
  calc
    _ ≤ ENNReal.ofReal (s.f (0,z))*∑ i∈N,
        volume (closedBinHits F.flow zX B S a b (l i) (u i) z) :=
      mul_le_mul' le_rfl ((measure_mono (hsub z)).trans (measure_biUnion_finset_le _ _))
    _ = _ := Finset.mul_sum _ _ _

lemma PhaseFlowOn.small_closed_bin_cells_payment {s : Solution}
    {T M A P L a b massScale φ C p len aStar bStar I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    {ι : Type*} (N : Finset ι) (l u lo hi : ι → ℝ)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (hlo0 : ∀ i∈N, 0 ≤ lo i) (hhiT : ∀ i∈N, hi i ≤ T)
    (hJ : ∀ i∈N, Icc (max a (l i)) (min b (u i+B.rmax)) ⊆ Icc (lo i) (hi i))
    (hC : ∀ i∈N, Icc (l i) (u i) ⊆ Icc (lo i) (hi i))
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : ∀ i∈N, hi i-lo i ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
    (hlen : ∀ i∈N, u i-l i=len)
    (hdisj : Set.PairwiseDisjoint (↑N) (fun i => Ioc (l i) (u i)))
    (hsub : ∀ i∈N, Ioc (l i) (u i)⊆Icc aStar bStar)
    (hStar : Icc aStar bStar ⊆ Icc 0 T) (hI : 0 < I) :
    ENNReal.ofReal len * ENNReal.ofReal (p/256) *
        (∑ i∈N, labelOccupation (fun z => s.f (0,z))
          (closedBinHits F.flow zX B S a b (l i) (u i))) ≤
      ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal I *
        jointEnergyBudget s F.flow zX T 4 aStar bStar I (np,nf) := by
  let g : ℝ → ℝ≥0∞ := fun t => ∫⁻ z : Phase,
    (sameTimeBudgetSet F.flow zX T 4 (np,nf)).indicator
      (fun q => ENNReal.ofReal (RVM.q q.2.2*s.f q)) (t,z)
  calc
    _ = ∑ i∈N, ENNReal.ofReal len * ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z))
          (closedBinHits F.flow zX B S a b (l i) (u i)) := Finset.mul_sum _ _ _
    _ ≤ ∑ i∈N, ENNReal.ofReal (40*B.rmax) * ∫⁻ t in Icc (l i) (u i), g t := by
      apply Finset.sum_le_sum
      intro i hiN
      rw [closedBinHits_clip_receiver]
      exact hlen i hiN ▸ F.small_closed_bin_cell_payment hs hT zX B hS np nf hp hφeq
        (hlo0 i hiN) (hhiT i hiN) (hJ i hiN) (hC i hiN) hM hA hP hL hm hφ hφ1
        hconst (hstable i hiN) hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
    _ = ENNReal.ofReal (40*B.rmax) * (∑ i∈N, ∫⁻ t in Icc (l i) (u i), g t) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (40*B.rmax) * ∫⁻ t in Icc aStar bStar, g t :=
      mul_le_mul' le_rfl (sum_cell_lintegral_le N l u g hdisj hsub)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (sameTimeBudget_energy_le_joint hStar hI)

lemma PhaseFlowOn.small_closed_bin_cell_crude {s : Solution}
    {T M A P L lo hi a b c d massScale φ C p : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (t₀ : ℝ) (ht₀ : t₀∈Icc c d) (zX : Phase) (B : ClosedConeBin) {S : Set Phase}
    (hlo0 : 0 ≤ lo) (hhiT : hi ≤ T)
    (hJ : Icc a b ⊆ Icc lo hi) (hC : Icc c d ⊆ Icc lo hi)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hlen : hi-lo ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  have hdata := F.small_closed_bin_cell_data zX B hlo0 hhiT hJ hC hM hA hP hL
    hm hφ hφ1 hconst hlen hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
  apply F.label_occupation_cell_bound hs ((hC.trans (Icc_subset_Icc hlo0 hhiT)) ht₀)
  · intro z
    by_cases hz : (closedBinHits F.flow zX B S a b c d z).Nonempty
    · exact (hdata z hz).1
    · simp only [not_nonempty_iff_eq_empty.mp hz,measure_empty,zero_le]
  · exact fun z hz => ((hdata z hz).2 t₀ ht₀).1



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


lemma closedBinHits_clip_source (α : Phase → ℝ → Phase) (zX : Phase)
    (B : ClosedConeBin) (S : Set Phase) (a b T : ℝ) :
    closedBinHits α zX B S a b 0 T =
      closedBinHits α zX B S a b (max 0 (a-B.rmax)) (min T b) := by
  funext z
  ext r
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    have hrt : r ≤ t := by
      have hh := hbin.1
      linarith [norm_nonneg ((α zX t).1-(α z r).1)]
    refine ⟨hz,⟨max_le hr.1 ?_,le_min hr.2 (hrt.trans ht.2)⟩,t,ht,hbin⟩
    linarith [hbin.2.1.2,ht.1]
  · rintro ⟨hz,hr,t,ht,hbin⟩
    exact ⟨hz,⟨(le_max_left _ _).trans hr.1,hr.2.trans (min_le_left _ _)⟩,t,ht,hbin⟩

lemma ennreal_sum_le_erase_add {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) (f : ι → ℝ≥0∞) :
    ∑ j∈S, f j ≤ (∑ j∈S.erase i, f j)+f i := by
  classical
  by_cases hi : i∈S
  · exact le_of_eq (Finset.sum_erase_add _ _ hi).symm
  · rw [Finset.erase_eq_self.mpr hi]
    exact le_add_right le_rfl

lemma PhaseFlowOn.small_closed_bin_refined_stable_oai {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax) (hrad : B.rmax ≤ len)
    (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
    (hI : 0 < I) :
    ENNReal.ofReal len * ENNReal.ofReal (p/256) *
        labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) ≤
      ENNReal.ofReal (40*B.rmax) *
        (ENNReal.ofReal len * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) +
          ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 4
            (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf)) := by
  classical
  let l := sourceCellLo len
  let u := sourceCellHi T len
  let w := fun i => min T (u i+B.rmax)
  let N := selectedSourceCells T len a b B.rmax
  let last := sourceCellLast T len
  let full := N.erase last
  let O : ℕ → ℝ≥0∞ := fun i => labelOccupation (fun z => s.f (0,z))
    (closedBinHits F.flow zX B S a b (l i) (u i))
  have hgrid (i : ℕ) (hi : i ≤ last) :
      0 ≤ l i ∧ l i ≤ u i ∧ u i ≤ T ∧ u i-l i ≤ len :=
    sourceCell_mem_prefix hT hlen hi
  have hN (i : ℕ) (hi : i∈N) : i ≤ last := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega
  have hfullN (i : ℕ) (hi : i∈full) : i∈N := Finset.mem_of_mem_erase hi
  have hJC (i : ℕ) : Icc (max a (l i)) (min b (u i+B.rmax)) ⊆ Icc (l i) (w i) := by
    intro t ht
    exact ⟨(le_max_right _ _).trans ht.1,
      le_min ((ht.2.trans (min_le_left _ _)).trans hb) (ht.2.trans (min_le_right _ _))⟩
  have hCC (i : ℕ) (hi : i ≤ last) : Icc (l i) (u i) ⊆ Icc (l i) (w i) := by
    intro t ht
    exact ⟨ht.1,le_min (ht.2.trans (hgrid i hi).2.2.1) (by linarith [ht.2])⟩
  have hST (i : ℕ) (hi : i ≤ last) :
      w i-l i ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2 := by
    have hg := (hgrid i hi).2.2.2
    have hw : w i ≤ u i+B.rmax := min_le_right _ _
    linarith
  have hsum : labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) ≤
      (∑ i∈full, O i)+O last := by
    refine le_trans ?_ (ennreal_sum_le_erase_add N last O)
    rw [closedBinHits_clip_source]
    apply F.closedBinHits_occupation_le_sum hs hT zX B hS N l u (Icc_subset_Icc ha hb)
    · intro i hi
      exact Icc_subset_Icc (hgrid i (hN i hi)).1 (hgrid i (hN i hi)).2.2.1
    · exact selectedSourceCells_cover hlen
  have hpay : ENNReal.ofReal len * ENNReal.ofReal (p/256) * (∑ i∈full, O i) ≤
      ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 4
        (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf) := by
    apply F.small_closed_bin_cells_payment hs hT zX B hS full l u l w np nf hp hφeq
      (fun i hi => (hgrid i (hN i (hfullN i hi))).1) (fun _ _ => min_le_left _ _)
      (fun i _ => hJC i) (fun i hi => hCC i (hN i (hfullN i hi)))
      hM hA hP hL hm hφ hφ1 hconst (fun i hi => hST i (hN i (hfullN i hi)))
      hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
    · intro i hi
      apply sourceCell_full hT hlen
      have hn := hN i (hfullN i hi)
      have hne := (Finset.mem_erase.mp hi).1
      omega
    · exact fun i _ j _ hij => sourceCells_pairwise_disjoint hlen hij
    · intro i hi
      exact Ioc_subset_Icc_self.trans (selectedSourceCells_enlargement hT hlen (hfullN i hi))
    · exact Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    · exact hI
  have hclip : ENNReal.ofReal (p/256) * O last ≤
      ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
    dsimp only [O]
    rw [closedBinHits_clip_receiver]
    exact F.small_closed_bin_cell_crude hs (l last) (left_mem_Icc.mpr (hgrid last le_rfl).2.1)
      zX B (hgrid last le_rfl).1 (min_le_left _ _) (hJC last) (hCC last le_rfl)
      hM hA hP hL hm hφ hφ1 hconst (hST last le_rfl)
      hqmin hqmax hmq hmw hr hd hDlo hDhi hw HX HZ
  calc
    _ ≤ ENNReal.ofReal len * ENNReal.ofReal (p/256) * ((∑ i∈full, O i)+O last) :=
      mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal len * ENNReal.ofReal (p/256) * (∑ i∈full, O i)+
        ENNReal.ofReal len * (ENNReal.ofReal (p/256)*O last) := by ring
    _ ≤ ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal I * jointEnergyBudget s F.flow zX T 4
        (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf) +
        ENNReal.ofReal len * (ENNReal.ofReal (40*B.rmax) * ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x))) :=
      add_le_add hpay (mul_le_mul' le_rfl hclip)
    _ = _ := by ring



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

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable_oai := @OAI.RVM.PhaseFlowOn.small_closed_bin_refined_stable_oai
