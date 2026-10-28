-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.actualLabelCutoffCost_integrable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:41:14.702713+00:00
-- url     : https://prove2.me/submissions/48f84c53-b1af-461b-97a2-40d961570abf

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_PhaseFlowOn_labelConeKernel_integrable

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

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

lemma hasDerivAt_dot {f g : ℝ → Vec} {f' g' : Vec} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => dot (f t) (g t))
      (dot (f s) g' + dot f' (g s)) s := by
  simpa only [dot_eq_inner] using hf.inner ℝ hg

lemma scalar_clm_invertible (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) : L.IsInvertible := by
  let K : ℝ →L[ℝ] ℝ := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := K)
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      K, smul_apply, smul_eq_mul]
    rw [← smul_eq_mul, L.map_smul]
    have hx : L x = x * L 1 := by simpa using L.map_smul x (1 : ℝ)
    rw [smul_eq_mul, hx]
    field_simp
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      K, smul_apply, smul_eq_mul]
    have hx : L x = x * L 1 := by simpa using L.map_smul x (1 : ℝ)
    rw [hx]
    field_simp

lemma contDiffAt_squaredCone {X Y : ℝ → Vec} {s t : ℝ}
    (hX : ContDiffAt ℝ 1 X t) (hY : ContDiffAt ℝ 1 Y s) :
    ContDiffAt ℝ 1 (squaredCone X Y) (s,t) := by
  exact (contDiffAt_snd.sub contDiffAt_fst).pow 2 |>.sub
    (((hX.comp (s,t) contDiffAt_snd).sub
      (hY.comp (s,t) contDiffAt_fst)).norm_sq ℝ)

lemma hasDerivAt_squaredCone_receiver {X Y : ℝ → Vec} {a : Vec} {s t : ℝ}
    (hX : HasDerivAt X a t) :
    HasDerivAt (fun t' => squaredCone X Y (s,t'))
      (2*(t-s) - 2*dot (X t-Y s) a) t := by
  have h := ((hasDerivAt_id t).sub_const s).pow 2 |>.sub
    ((hX.sub_const (Y s)).norm_sq)
  convert h using 1 <;> try rfl
  simp [dot_eq_inner]

lemma receiver_partial_squaredCone {X Y : ℝ → Vec} {a : Vec} {s t : ℝ}
    (hX : ContDiffAt ℝ 1 X t) (hY : ContDiffAt ℝ 1 Y s)
    (hXd : HasDerivAt X a t) :
    (fderiv ℝ (squaredCone X Y) (s,t) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ) 1 = 2*(t-s) - 2*dot (X t-Y s) a := by
  have hF := (contDiffAt_squaredCone hX hY).differentiableAt one_ne_zero
  have hpair : HasFDerivAt (fun t' : ℝ => (s,t'))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) t := by
    convert (hasFDerivAt_const s t).prodMk (hasFDerivAt_id t) using 1 <;> try rfl
  exact ((hF.hasFDerivAt.comp t hpair).hasDerivAt.unique
    (hasDerivAt_squaredCone_receiver hXd))

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

lemma exists_local_retarded_branch {X Y : ℝ → Vec} {s t : ℝ} {a : Vec}
    (hst : s < t) (hcone : t-s = ‖X t-Y s‖)
    (hX : ContDiffAt ℝ 1 X t) (hY : ContDiffAt ℝ 1 Y s)
    (hXd : HasDerivAt X a t) (ha : ‖a‖ < 1) :
    ∃ τ : ℝ → ℝ, τ s = t ∧ ContDiffAt ℝ 1 τ s ∧
      ∀ᶠ z in nhds s, z < τ z ∧ τ z-z = ‖X (τ z)-Y z‖ := by
  have hF := contDiffAt_squaredCone hX hY
  have hbound := dot_le_norm (X t-Y s) a
  rw [← hcone] at hbound
  have hpos : 0 < 2*(t-s)-2*dot (X t-Y s) a := by
    have hgap := mul_pos (sub_pos.mpr hst) (sub_pos.mpr ha)
    nlinarith
  have hinv : (fderiv ℝ (squaredCone X Y) (s,t) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply scalar_clm_invertible
    rw [receiver_partial_squaredCone hX hY hXd]
    exact ne_of_gt hpos
  let τ := hF.implicitFunction one_ne_zero hinv
  have hτ : τ s = t := hF.implicitFunction_apply_self one_ne_zero hinv
  have hτc : ContDiffAt ℝ 1 τ s := hF.contDiffAt_implicitFunction one_ne_zero hinv
  refine ⟨τ, hτ, hτc, ?_⟩
  have hsign : 0 < τ s-s := by rw [hτ]; exact sub_pos.mpr hst
  have hevent : ∀ᶠ z in nhds s, 0 < τ z-z :=
    (hτc.continuousAt.sub continuousAt_id) (isOpen_Ioi.mem_nhds hsign)
  filter_upwards [hF.eventually_apply_implicitFunction one_ne_zero hinv, hevent]
    with z hz hzn
  refine ⟨by linarith, ?_⟩
  dsimp [squaredCone] at hz
  rw [hcone, sub_self] at hz
  change (τ z-z)^2 - ‖X (τ z)-Y z‖^2 = 0 at hz
  have hn := norm_nonneg (X (τ z)-Y z)
  nlinarith

lemma derivative_retarded_branch {X Y : ℝ → Vec} {τ : ℝ → ℝ}
    {s t k : ℝ} {a u n : Vec}
    (hτ : τ s = t) (hst : s < t) (hgeom : X t-Y s = (t-s) • n)
    (hD : 1-dot n a ≠ 0)
    (hXd : HasDerivAt X a t) (hYd : HasDerivAt Y u s)
    (hτd : HasDerivAt τ k s)
    (heq : ∀ᶠ z in nhds s, (τ z-z)^2 = ‖X (τ z)-Y z‖^2) :
    k = (1-dot n u)/(1-dot n a) := by
  have hXτ : HasDerivAt (fun z => X (τ z)) (k • a) s := by
    exact (hτ ▸ hXd).scomp s hτd
  have hleft := (hτd.sub (hasDerivAt_id s)).pow 2
  have hright := ((hXτ.sub hYd).norm_sq)
  have hsame := (hleft.congr_of_eventuallyEq (Filter.EventuallyEq.symm heq)).unique hright
  simp only [Pi.sub_apply, id_eq, hτ, Nat.cast_ofNat, Nat.reduceSub, pow_one, ← dot_eq_inner,
    hgeom, dot_smul_left, dot_sub_right, dot_smul_right] at hsame
  apply (eq_div_iff hD).mpr
  have hr : t-s ≠ 0 := ne_of_gt (sub_pos.mpr hst)
  apply (mul_left_cancel₀ hr)
  nlinarith

lemma exists_local_retarded_branch_with_derivative {X Y : ℝ → Vec}
    {s t : ℝ} {a u n : Vec}
    (hst : s < t) (hgeom : X t-Y s = (t-s) • n) (hn : ‖n‖ = 1)
    (hX : ContDiffAt ℝ 1 X t) (hY : ContDiffAt ℝ 1 Y s)
    (hXd : HasDerivAt X a t) (hYd : HasDerivAt Y u s) (ha : ‖a‖ < 1) :
    ∃ τ : ℝ → ℝ, τ s = t ∧ ContDiffAt ℝ 1 τ s ∧
      HasDerivAt τ ((1-dot n u)/(1-dot n a)) s ∧
      ∀ᶠ z in nhds s, z < τ z ∧ τ z-z = ‖X (τ z)-Y z‖ := by
  have hcone : t-s = ‖X t-Y s‖ := by
    rw [hgeom, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hst), hn, mul_one]
  have hD : 1-dot n a ≠ 0 := by
    have hb := dot_le_norm n a
    rw [hn, one_mul] at hb
    linarith
  obtain ⟨τ, hτ, hτc, hevent⟩ := exists_local_retarded_branch hst hcone hX hY hXd ha
  have hτd := (hτc.differentiableAt one_ne_zero).hasDerivAt
  have heq : ∀ᶠ z in nhds s, (τ z-z)^2 = ‖X (τ z)-Y z‖^2 := by
    filter_upwards [hevent] with z hz using congrArg (fun r : ℝ => r^2) hz.2
  have hk := derivative_retarded_branch hτ hst hgeom hD hXd hYd hτd heq
  rw [hk] at hτd
  exact ⟨τ, hτ, hτc, hτd, hevent⟩

lemma hasDerivAt_cone_direction {X Y : ℝ → Vec} {τ : ℝ → ℝ}
    {s t k : ℝ} {a u n : Vec}
    (hτ : τ s = t) (hst : s < t) (hgeom : X t-Y s = (t-s) • n)
    (hXd : HasDerivAt X a t) (hYd : HasDerivAt Y u s)
    (hτd : HasDerivAt τ k s) :
    HasDerivAt (fun z => (τ z-z)⁻¹ • (X (τ z)-Y z))
      ((t-s)⁻¹ • (k • (a-n)+n-u)) s := by
  have hXτ : HasDerivAt (fun z => X (τ z)) (k • a) s :=
    (hτ ▸ hXd).scomp s hτd
  have hrad := hτd.sub (hasDerivAt_id s)
  have hr : τ s-s ≠ 0 := by simpa [hτ] using ne_of_gt (sub_pos.mpr hst)
  have h := (hrad.inv hr).smul (hXτ.sub hYd)
  convert h using 1 <;> try rfl
  simp only [Pi.inv_apply, Pi.sub_apply, id_eq, hτ, hgeom]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have hts : t-s ≠ 0 := ne_of_gt (sub_pos.mpr hst)
  field_simp
  ring

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

lemma one_le_q (v : Vec) : 1 ≤ q v := by
  have := q_sq v
  have := q_pos v
  nlinarith [sq_nonneg ‖v‖]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ExtendedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM
section TimeFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma det_time_triangular (L : (ℝ × E) →ₗ[ℝ] (ℝ × E))
    (hL : (LinearMap.fst ℝ ℝ E).comp L = LinearMap.fst ℝ ℝ E) :
    L.det = ((LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inr ℝ ℝ E))).det := by
  classical
  let b := Module.Basis.singleton Unit ℝ
  let c := Module.finBasis ℝ E
  let C := (LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inl ℝ ℝ E))
  let D := (LinearMap.snd ℝ ℝ E).comp (L.comp (LinearMap.inr ℝ ℝ E))
  have hf (z : ℝ × E) : (L z).1 = z.1 := LinearMap.congr_fun hL z
  have hm : LinearMap.toMatrix (b.prod c) (b.prod c) L =
      Matrix.fromBlocks 1 0 (LinearMap.toMatrix b c C) (LinearMap.toMatrix c c D) := by
    ext (i | i) (j | j)
    · simp [LinearMap.toMatrix, b, hf]
    · simp [LinearMap.toMatrix, b, hf]
    · simp [LinearMap.toMatrix, C]
    · simp [LinearMap.toMatrix, D]
  rw [← LinearMap.det_toMatrix (b.prod c), hm, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, one_mul, LinearMap.det_toMatrix]

end TimeFlow

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

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma timeFlowDerivative_det (v : E) (A : E →L[ℝ] E) :
    (timeFlowDerivative v A).det = A.det := by
  have hh := det_time_triangular (timeFlowDerivative v A).toLinearMap (by apply LinearMap.ext; intro p; rfl)
  have he : (LinearMap.snd ℝ ℝ E).comp ((timeFlowDerivative v A).toLinearMap.comp (LinearMap.inr ℝ ℝ E)) = A.toLinearMap := by
    ext x
    simp [timeFlowDerivative]
  rwa [he] at hh

lemma inverse_timeFlowDerivative {v : E} {A : E →L[ℝ] E} (hA : A.det = 1) :
    ∃ e : (ℝ × E) ≃L[ℝ] (ℝ × E), ∃ D : E →L[ℝ] E,
      (e : (ℝ × E) →L[ℝ] (ℝ × E)) = timeFlowDerivative v A ∧ D.det = 1 ∧
      (ContinuousLinearMap.snd ℝ ℝ E).comp (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)) =
        (ContinuousLinearMap.toSpanSingleton ℝ (-D v)).coprod D := by
  have hdet : (timeFlowDerivative v A).toLinearMap.det = 1 := (timeFlowDerivative_det v A).trans hA
  have hunit : IsUnit (timeFlowDerivative v A).toLinearMap.det := hdet.symm ▸ isUnit_one
  let e : (ℝ × E) ≃L[ℝ] (ℝ × E) := (LinearMap.equivOfIsUnitDet hunit).toContinuousLinearEquiv
  have he : (e : (ℝ × E) →L[ℝ] (ℝ × E)) = timeFlowDerivative v A := by
    apply ContinuousLinearMap.ext
    intro z
    exact LinearMap.congr_fun (LinearMap.coe_equivOfIsUnitDet hunit) z
  have happ (z : ℝ × E) : e z = (z.1,z.1 • v+A z.2) := by
    rw [← ContinuousLinearEquiv.coe_coe,he]
    rfl
  have hfst (z : ℝ × E) : (e.symm z).1 = z.1 := by
    have hh := congrArg Prod.fst (e.apply_symm_apply z)
    simpa only [happ] using hh
  let D : E →L[ℝ] E := (ContinuousLinearMap.snd ℝ ℝ E).comp
    ((e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).comp (ContinuousLinearMap.inr ℝ ℝ E))
  have hD : D.det = 1 := by
    have hh := det_time_triangular (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).toLinearMap (by apply LinearMap.ext; intro z; exact hfst z)
    change (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)).det = D.det at hh
    rw [ContinuousLinearEquiv.det_coe_symm,he,timeFlowDerivative_det,hA,inv_one] at hh
    exact hh.symm
  have hi : e.symm (1,v) = (1,0) := by
    apply e.injective
    simp only [e.apply_symm_apply,happ,one_smul,map_zero,add_zero]
  refine ⟨e,D,he,hD,?_⟩
  apply ContinuousLinearMap.ext
  intro p
  change (e.symm p).2 = p.1 • (-D v)+D p.2
  have hp : p = p.1 • (1,v)+(0,p.2-p.1 • v) := by
    ext <;> simp
  calc
    (e.symm p).2 = (e.symm (p.1 • (1,v)+(0,p.2-p.1 • v))).2 := congrArg (fun z => (e.symm z).2) hp
    _ = D (p.2-p.1 • v) := by
      rw [map_add,map_smul,hi]
      change p.1 • (0 : E)+(e.symm (0,p.2-p.1 • v)).2 = D (p.2-p.1 • v)
      rw [smul_zero,zero_add]
      rfl
    _ = p.1 • (-D v)+D p.2 := by simp only [map_sub,map_smul,smul_neg]; abel

lemma hasStrictFDerivAt_inversePhase {α : E → ℝ → E} {v x : E} {A : E →L[ℝ] E} {T t : ℝ}
    (hbij : ∀ s ∈ Ioo 0 T, Function.Bijective (α · s)) (ht : t ∈ Ioo 0 T)
    (hA : A.det = 1)
    (hα : HasStrictFDerivAt (fun z : ℝ × E => α z.2 z.1)
      ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod A) (t,x)) :
    ∃ D : E →L[ℝ] E, D.det = 1 ∧
      HasStrictFDerivAt (inversePhase α)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-D v)).coprod D) (t,α x t) := by
  obtain ⟨e,D,he,hD,hder⟩ := inverse_timeFlowDerivative hA
  let Φ : ℝ × E → ℝ × E := fun z => (z.1,α z.2 z.1)
  have hΦ : HasStrictFDerivAt Φ (e : (ℝ × E) →L[ℝ] (ℝ × E)) (t,x) := by
    rw [he]
    exact hasStrictFDerivAt_fst.prodMk hα
  let Z := hΦ.localInverse Φ e (t,x)
  have hZ : HasStrictFDerivAt Z (e.symm : (ℝ × E) →L[ℝ] (ℝ × E)) (t,α x t) := hΦ.to_localInverse
  have hEq : (fun z => (Z z).2) =ᶠ[𝓝 (t,α x t)] inversePhase α := by
    have htime : ∀ᶠ z : ℝ × E in 𝓝 (t,α x t), z.1 ∈ Ioo 0 T :=
      continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds ht)
    filter_upwards [hΦ.eventually_right_inverse,htime] with z hz hzt
    have hf : (Z z).1 = z.1 := by
      have hh := congrArg Prod.fst hz
      exact hh
    have hy : α (Z z).2 z.1 = z.2 := by
      have hh := congrArg Prod.snd hz
      change α (Z z).2 (Z z).1 = z.2 at hh
      rwa [hf] at hh
    apply (hbij z.1 hzt).1
    exact hy.trans (Function.invFun_eq ((hbij z.1 hzt).2 z.2)).symm
  refine ⟨D,hD,?_⟩
  rw [← hder]
  exact hZ.snd.congr_of_eventuallyEq hEq

end

open Set MeasureTheory Filter
open scoped Topology ContDiff


lemma hasStrictFDerivAt_norm_nonzero {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x : F} (hx : x ≠ 0) :
    HasStrictFDerivAt (fun y : F => ‖y‖) (innerSL ℝ (‖x‖⁻¹ • x)) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hh := (Real.hasStrictDerivAt_sqrt (pow_ne_zero 2 hn)).comp_hasStrictFDerivAt x
    (hasStrictFDerivAt_norm_sq x)
  have hf : (Real.sqrt ∘ fun y : F => ‖y‖^2) = fun y : F => ‖y‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  rw [hf,Real.sqrt_sq (norm_nonneg x)] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro y
  simp only [smul_apply,innerSL_apply_apply,inner_smul_left,
    starRingEnd_apply,star_trivial,smul_eq_mul,two_smul,add_apply]
  ring

lemma norm_coneDirection {x y : Vec} (hxy : x ≠ y) : ‖‖x-y‖⁻¹ • (x-y)‖ = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)

lemma cone_deficit_positive {x y : Vec} (hxy : x ≠ y) (v : Vec) :
    0 < 1 - dot (‖x-y‖⁻¹ • (x-y)) (velocity v) := by
  have hh := real_inner_le_norm (‖x-y‖⁻¹ • (x-y)) (velocity v)
  rw [norm_coneDirection hxy,one_mul,← dot_eq_inner] at hh
  linarith [norm_velocity_lt_one v]


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

lemma PhaseFlowOn.timelike {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) :
    ∃ c : ℝ≥0, (c : ℝ) < 1 ∧ LipschitzOnWith c (fun t => (F.flow z t).1) (Icc 0 T) := by
  have hc : ContinuousOn (fun t => ‖velocity (F.flow z t).2‖) (Icc 0 T) :=
    ((contDiff_velocity (k := 1)).continuous.comp_continuousOn (F.continuousOn_time z).snd).norm
  obtain ⟨t₀,ht₀,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hc
  refine ⟨⟨‖velocity (F.flow z t₀).2‖,norm_nonneg _⟩,norm_velocity_lt_one _,?_⟩
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (F.ode z t ht).fst)
  intro t ht
  exact_mod_cast hmax ht

lemma PhaseFlowOn.flow_inversePhase {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) : F.flow (inversePhase F.flow (s,z)) s = z :=
  Function.invFun_eq ((F.bijective s hs).2 z)

open Set MeasureTheory Filter
open scoped Topology ContDiff


lemma PhaseFlowOn.inverse_differential {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Ioo 0 T) (z : Phase) :
    ∃ D : Phase →L[ℝ] Phase, D.det=1 ∧
      HasStrictFDerivAt (inversePhase F.flow)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-D (lorentzField E B (s,z)))).coprod D) (s,z) := by
  let y := Function.invFun (F.flow · s) z
  have hy : F.flow y s=z := Function.invFun_eq ((F.bijective s (Ioo_subset_Icc_self hs)).2 z)
  have hh := hasStrictFDerivAt_inversePhase
    (fun r hr => F.bijective r (Ioo_subset_Icc_self hr)) hs
    (F.det_one y s (Ioo_subset_Icc_self hs)) (F.joint y s hs)
  simpa only [hy] using hh

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverRadialDomain
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

lemma PhaseFlowOn.arrival_strictMono {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) (y : Vec) :
    StrictMonoOn (fun t => t-‖(F.flow z t).1-y‖) (Icc 0 T) := by
  obtain ⟨c,hc,hLip⟩ := F.timelike hT z
  intro a ha b hb hab
  have hbound := hLip.dist_le_mul a ha b hb
  rw [dist_eq_norm,Real.dist_eq,abs_of_neg (sub_neg.mpr hab)] at hbound
  have hn : ‖(F.flow z b).1-y‖ ≤ ‖(F.flow z a).1-(F.flow z b).1‖ + ‖(F.flow z a).1-y‖ := by
    calc
      _ = ‖((F.flow z b).1-(F.flow z a).1)+((F.flow z a).1-y)‖ := by congr 1; abel
      _ ≤ ‖(F.flow z b).1-(F.flow z a).1‖ + ‖(F.flow z a).1-y‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have hp := mul_pos (sub_pos.mpr hc) (sub_pos.mpr hab)
  nlinarith

lemma PhaseFlowOn.exists_arrival {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) {y : Vec}
    (hy : ‖(F.flow z T).1-y‖ < T-s) :
    ∃! t : ℝ, t ∈ Icc s T ∧ t-‖(F.flow z t).1-y‖=s := by
  have hsub : Icc s T ⊆ Icc 0 T := fun _ ht => ⟨hs.1.trans ht.1,ht.2⟩
  have hc : ContinuousOn (fun t => t-‖(F.flow z t).1-y‖) (Icc s T) :=
    continuousOn_id.sub ((((F.continuousOn_time z).mono hsub).fst.sub continuousOn_const).norm)
  have hstart : s-‖(F.flow z s).1-y‖ ≤ s := sub_le_self _ (norm_nonneg _)
  have hend : s ≤ T-‖(F.flow z T).1-y‖ := by linarith
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hs.2 hc ⟨hstart,hend⟩
  refine ⟨t,⟨ht,he⟩,?_⟩
  intro r hr
  apply (F.arrival_strictMono (hs.1.trans hs.2) z y).injOn (hsub hr.1) (hsub ht)
  exact hr.2.trans he.symm

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CollisionLabels
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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.position_contDiffOn {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (z : Phase) : ContDiffOn ℝ 1 (fun t => (F.flow z t).1) (Ioo 0 T) := by
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivWithinAt (fun t => (F.flow z t).1) (velocity (F.flow z t).2) (Ioo 0 T) t :=
    by
      have hx : HasDerivWithinAt (fun t => (F.flow z t).1)
          (velocity (F.flow z t).2) (Icc 0 T) t := (F.ode z t (Ioo_subset_Icc_self ht)).fst
      exact hx.mono Ioo_subset_Icc_self
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
  constructor
  · exact fun t ht => (hd t ht).differentiableWithinAt
  · have hc : ContinuousOn (fun t => velocity (F.flow z t).2) (Ioo 0 T) :=
      ((contDiff_velocity (k := 1)).continuous).comp_continuousOn
        ((F.continuousOn_time z).snd.mono Ioo_subset_Icc_self)
    apply hc.congr
    intro t ht
    exact ((hd t ht).derivWithin (isOpen_Ioo.uniqueDiffWithinAt ht))

lemma PhaseFlowOn.branch_spec {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T) :
    branchTime F.flow zX zY T s ∈ Icc s T ∧
      branchTime F.flow zX zY T s-s =
        ‖(F.flow zX (branchTime F.flow zX zY T s)).1-(F.flow zY s).1‖ := by
  have hy : ‖(F.flow zX T).1-(F.flow zY s).1‖ < T-s := by linarith [hs.2]
  obtain ⟨t,⟨ht,he⟩,_⟩ := F.exists_arrival (Ioo_subset_Icc_self hs.1) zX hy
  have hex : ∃ t, t ∈ Icc s T ∧ t-s=‖(F.flow zX t).1-(F.flow zY s).1‖ :=
    ⟨t,ht,by linarith⟩
  simpa only [branchTime,dite_eq_left hex] using hex.choose_spec

lemma PhaseFlowOn.branch_unique {E B : Field} {T s t : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (ht : t ∈ Icc s T) (he : t-s=‖(F.flow zX t).1-(F.flow zY s).1‖) :
    t=branchTime F.flow zX zY T s := by
  obtain ⟨hσ,hcone⟩ := F.branch_spec zX zY hs
  apply (F.arrival_strictMono (hs.1.1.le.trans hs.1.2.le) zX (F.flow zY s).1).injOn
    ⟨hs.1.1.le.trans ht.1,ht.2⟩ ⟨hs.1.1.le.trans hσ.1,hσ.2⟩
  dsimp only
  linarith

lemma PhaseFlowOn.branch_time_mem {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) :
    s < branchTime F.flow zX zY T s ∧ branchTime F.flow zX zY T s < T := by
  obtain ⟨ht,he⟩ := F.branch_spec zX zY hs
  constructor
  · by_contra h
    have hts := le_antisymm (le_of_not_gt h) ht.1
    rw [hts,sub_self] at he
    exact hne (sub_eq_zero.mp (norm_eq_zero.mp he.symm))
  · by_contra h
    have htT := le_antisymm ht.2 (le_of_not_gt h)
    rw [htT] at he
    linarith [hs.2]

lemma PhaseFlowOn.isOpen_branchDomain {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) : IsOpen (branchDomain F.flow zX zY T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hY := ((F.continuousOn_time zY).fst.continuousAt (Icc_mem_nhds hs.1.1 hs.1.2))
  have hc : ContinuousAt (fun r => r+‖(F.flow zX T).1-(F.flow zY r).1‖) s :=
    continuousAt_id.add ((continuousAt_const.sub hY).norm)
  exact inter_mem (isOpen_Ioo.mem_nhds hs.1) (hc (isOpen_Iio.mem_nhds hs.2))

lemma PhaseFlowOn.branch_differential {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) :
    let τ := branchTime F.flow zX zY T
    let n := (τ s-s)⁻¹ • ((F.flow zX (τ s)).1-(F.flow zY s).1)
    ContDiffAt ℝ 1 τ s ∧ HasDerivAt τ
      ((1-dot n (velocity (F.flow zY s).2))/(1-dot n (velocity (F.flow zX (τ s)).2))) s := by
  dsimp only
  let τ := branchTime F.flow zX zY T
  let t := τ s
  let n := (t-s)⁻¹ • ((F.flow zX t).1-(F.flow zY s).1)
  have ht := F.branch_time_mem zX zY hs hne
  have hti : t ∈ Ioo 0 T := ⟨hs.1.1.trans ht.1,ht.2⟩
  have hspec := (F.branch_spec zX zY hs).2
  have hgeom : (F.flow zX t).1-(F.flow zY s).1=(t-s) • n := by
    dsimp [n]
    rw [smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht.1)),one_smul]
  have hn : ‖n‖=1 := by
    dsimp [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sub_pos.mpr ht.1)),← hspec]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht.1))
  have hX := ((F.position_contDiffOn zX) t hti).contDiffAt (isOpen_Ioo.mem_nhds hti)
  have hY := ((F.position_contDiffOn zY) s hs.1).contDiffAt (isOpen_Ioo.mem_nhds hs.1)
  have hXd : HasDerivAt (fun r => (F.flow zX r).1) (velocity (F.flow zX t).2) t :=
    ((F.ode zX t (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)).fst
  have hYd : HasDerivAt (fun r => (F.flow zY r).1) (velocity (F.flow zY s).2) s :=
    ((F.ode zY s (Ioo_subset_Icc_self hs.1)).hasDerivAt (Icc_mem_nhds hs.1.1 hs.1.2)).fst
  obtain ⟨σ,hσ,hσc,hσd,hev⟩ := exists_local_retarded_branch_with_derivative ht.1 hgeom hn
    hX hY hXd hYd (norm_velocity_lt_one (F.flow zX t).2)
  have hupper : ∀ᶠ r in 𝓝 s, σ r < T := hσc.continuousAt (isOpen_Iio.mem_nhds (hσ ▸ ht.2))
  have heq : σ =ᶠ[𝓝 s] τ := by
    filter_upwards [hev,hupper,(F.isOpen_branchDomain zX zY).mem_nhds hs] with r hr hu hdom
    exact F.branch_unique zX zY hdom ⟨hr.1.le,hu.le⟩ hr.2
  exact ⟨hσc.congr_of_eventuallyEq heq.symm, hσd.congr_of_eventuallyEq heq.symm⟩

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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma exists_continuous_scalar_root {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] {H : ℝ × W → ℝ}
    {L : (ℝ × W) →L[ℝ] ℝ} {t : ℝ} {p : W}
    (hH : HasStrictFDerivAt H L (t,p)) (hzero : H (t,p)=0)
    (hk : L (1,0) ≠ 0) :
    ∃ τ : W → ℝ, τ p=t ∧ ContinuousAt τ p ∧ ∀ᶠ q in 𝓝 p, H (τ q,q)=0 := by
  have hL (x : ℝ × W) : L x = x.1 * L (1,0)+L (0,x.2) := by
    have he : x = x.1 • (1,(0 : W))+(0,x.2) := by ext <;> simp
    conv_lhs => rw [he]
    rw [map_add,map_smul,smul_eq_mul]
  let A : (ℝ × W) →L[ℝ] (ℝ × W) := L.prod (ContinuousLinearMap.snd ℝ ℝ W)
  have hi : Function.Injective A := by
    intro x y h
    have hh : L x = L y := congrArg Prod.fst h
    have he : x.2=y.2 := by
      have he := congrArg Prod.snd h
      exact he
    rw [hL x,hL y,he] at hh
    have hf : x.1=y.1 := (mul_right_cancel₀ hk) (add_right_cancel hh)
    exact Prod.ext hf he
  have hs : Function.Surjective A := by
    intro y
    refine ⟨((y.1-L (0,y.2))/L (1,0),y.2),?_⟩
    apply Prod.ext
    · change L ((y.1-L (0,y.2))/L (1,0),y.2)=y.1
      rw [hL]
      dsimp only
      field_simp
      ring
    · rfl
  let e : (ℝ × W) ≃L[ℝ] (ℝ × W) := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  let Φ : ℝ × W → ℝ × W := fun z => (H z,z.2)
  have hΦ : HasStrictFDerivAt Φ (e : (ℝ × W) →L[ℝ] (ℝ × W)) (t,p) :=
    hH.prodMk hasStrictFDerivAt_snd
  let Z := hΦ.localInverse Φ e (t,p)
  have hZ : HasStrictFDerivAt Z (e.symm : (ℝ × W) →L[ℝ] (ℝ × W)) (0,p) := by
    simpa only [Φ,hzero] using hΦ.to_localInverse
  have hZ₀ : Z (0,p)=(t,p) := by
    simpa only [Φ,hzero] using hΦ.localInverse_apply_image
  let τ : W → ℝ := fun q => (Z (0,q)).1
  have hc : ContinuousAt (fun q : W => ((0 : ℝ),q)) p := continuousAt_const.prodMk continuousAt_id
  refine ⟨τ,congrArg Prod.fst hZ₀,hZ.continuousAt.fst.comp hc,?_⟩
  have hev : ∀ᶠ z in 𝓝 (0,p), Φ (Z z)=z := by
    simpa only [Φ,hzero] using hΦ.eventually_right_inverse
  filter_upwards [hc.eventually hev] with q hq
  have he : (Z (0,q)).2=q := congrArg Prod.snd hq
  have hh : H (Z (0,q))=0 := congrArg Prod.fst hq
  have hz : Z (0,q) = (τ q,q) := Prod.ext rfl he
  rwa [hz] at hh

lemma PhaseFlowOn.joint_position_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {p : ℝ × Phase} (hp : p.1 ∈ Ioo 0 T) :
    ContinuousAt (fun q : ℝ × Phase => (F.flow q.2 q.1).1) p :=
  (F.joint p.2 p.1 hp).continuousAt.fst

lemma PhaseFlowOn.isOpen_jointBranchDomain {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) : IsOpen (jointBranchDomain F.flow zX T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hY := F.joint_position_continuousAt hp.1.1
  have hX : ContinuousAt (fun q : ℝ × Phase => (F.flow zX q.1).1) p :=
    (((F.continuousOn_time zX).fst.continuousAt (Icc_mem_nhds hp.1.1.1 hp.1.1.2)).comp
      continuousAt_fst)
  have hd : ContinuousAt (fun q : ℝ × Phase => q.1+‖(F.flow zX T).1-(F.flow q.2 q.1).1‖) p :=
    continuousAt_fst.add ((continuousAt_const.sub hY).norm)
  have ht : ∀ᶠ q : ℝ × Phase in 𝓝 p, q.1 ∈ Ioo 0 T :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds hp.1.1)
  have hb := hd.eventually (isOpen_Iio.mem_nhds hp.1.2)
  have hn := (hX.sub hY).eventually (isOpen_compl_singleton.mem_nhds (sub_ne_zero.mpr hp.2))
  filter_upwards [ht,hb,hn] with q hq hqt hqn
  exact ⟨⟨hq,hqt⟩,sub_ne_zero.mp hqn⟩

lemma PhaseFlowOn.joint_branch_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Phase} (hp : p ∈ jointBranchDomain F.flow zX T) :
    ContinuousAt (fun q : ℝ × Phase => branchTime F.flow zX q.2 T q.1) p := by
  let t := branchTime F.flow zX p.2 T p.1
  have ht := F.branch_time_mem zX p.2 hp.1 hp.2
  have hti : t ∈ Ioo 0 T := ⟨hp.1.1.1.trans ht.1,ht.2⟩
  have hspec := (F.branch_spec zX p.2 hp.1).2
  have hxy : (F.flow zX t).1 ≠ (F.flow p.2 p.1).1 := by
    intro he
    rw [he,sub_self,norm_zero] at hspec
    linarith [ht.1]
  let H : ℝ × (ℝ × Phase) → ℝ := fun q => q.1-q.2.1-‖(F.flow zX q.1).1-(F.flow q.2.2 q.2.1).1‖
  have hmap : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (q.1,zX))
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × Phase)).prod 0) (t,p) :=
    hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_const _ _)
  have hparam : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × Phase)) (t,p) := hasStrictFDerivAt_snd
  have hX : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (F.flow zX q.1).1)
      _ (t,p) := ((F.joint zX t hti).comp (t,p) hmap).fst
  have hY : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (F.flow q.2.2 q.2.1).1)
      _ (t,p) := ((F.joint p.2 p.1 hp.1.1).comp (t,p) hparam).fst
  have hN := (hasStrictFDerivAt_norm_nonzero (sub_ne_zero.mpr hxy)).comp (t,p) (hX.sub hY)
  have htproj : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × Phase)) (t,p) := hasStrictFDerivAt_fst
  have hsproj : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ Phase).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × Phase))) (t,p) :=
    hasStrictFDerivAt_fst.comp (t,p) hparam
  have hH := (htproj.sub hsproj).sub hN
  have hroot : ∃ L : (ℝ × (ℝ × Phase)) →L[ℝ] ℝ,
      HasStrictFDerivAt H L (t,p) ∧ L (1,0) =
        1-dot (‖(F.flow zX t).1-(F.flow p.2 p.1).1‖⁻¹ •
          ((F.flow zX t).1-(F.flow p.2 p.1).1)) (velocity (F.flow zX t).2) := by
    refine ⟨_,hH,?_⟩
    change 1 - (0 : ℝ) - inner ℝ
      (‖(F.flow zX t).1-(F.flow p.2 p.1).1‖⁻¹ •
        ((F.flow zX t).1-(F.flow p.2 p.1).1))
      (((1 : ℝ) • lorentzField E B (t,F.flow zX t) + F.differential zX t 0).1 -
        (((0 : ℝ) • lorentzField E B (p.1,F.flow p.2 p.1) + F.differential p.2 p.1 0).1)) = _
    simp only [map_zero,one_smul,zero_smul,add_zero,Prod.fst_zero,sub_zero,← dot_eq_inner]
    rfl
  obtain ⟨L,hL,hk⟩ := hroot
  have hkne : L (1,0) ≠ 0 := by
    rw [hk]
    exact ne_of_gt (cone_deficit_positive hxy (F.flow zX t).2)
  obtain ⟨τ,hτ,hτc,hev⟩ := exists_continuous_scalar_root hL
    (by dsimp [H]; linarith) hkne
  have hle : ∀ᶠ q in 𝓝 p, q.1 < τ q ∧ τ q < T := by
    have hpos : 0 < τ p-p.1 := by rw [hτ]; exact sub_pos.mpr ht.1
    have h1 : ∀ᶠ q in 𝓝 p, 0 < τ q-q.1 :=
      (hτc.sub continuousAt_fst).eventually (isOpen_Ioi.mem_nhds hpos)
    have hend : τ p < T := by rw [hτ]; exact ht.2
    have h2 := hτc.eventually (isOpen_Iio.mem_nhds hend)
    filter_upwards [h1,h2] with q hq hqT
    exact ⟨sub_pos.mp hq,hqT⟩
  apply hτc.congr_of_eventuallyEq
  filter_upwards [hev,hle,(F.isOpen_jointBranchDomain zX).mem_nhds hp] with q hq hqt hqd
  exact (F.branch_unique zX q.2 hqd.1 ⟨hqt.1.le,hqt.2.le⟩ (by change H (τ q,q)=0 at hq; dsimp [H] at hq; linarith)).symm

lemma PhaseFlowOn.measurable_joint_flow_zero {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) :
    Measurable ((Ioo 0 T ×ˢ (univ : Set Phase)).indicator
      (fun p : ℝ × Phase => F.flow p.2 p.1)) := by
  classical
  have hc : ContinuousOn (fun p : ℝ × Phase => F.flow p.2 p.1)
      (Ioo 0 T ×ˢ (univ : Set Phase)) :=
    fun p hp => (F.joint p.2 p.1 hp.1).continuousAt.continuousWithinAt
  have hh := hc.measurable_piecewise
    (continuousOn_const (c := (0 : Phase))) (measurableSet_Ioo.prod MeasurableSet.univ)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  by_cases hp : p ∈ Ioo 0 T ×ˢ (univ : Set Phase) <;>
    simp [Set.indicator,Set.piecewise,hp]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_LabelOccupation
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

lemma PhaseFlowOn.branchDirection_norm {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) :
    ‖branchDirection F.flow zX zY T s‖ = 1 := by
  have ht := (F.branch_time_mem zX zY hs hne).1
  have hr := (F.branch_spec zX zY hs).2
  dsimp only [branchDirection]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sub_pos.mpr ht)),← hr]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht))

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ArrivalDomain
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

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma PhaseFlowOn.arrivalLabel_mem {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    arrivalLabel F.flow p ∈ jointBranchDomain F.flow zX T := by
  have h := F.flow_inversePhase (Ioo_subset_Icc_self hp.1) (p.2,0)
  change (p.1 ∈ Ioo 0 T ∧ p.1+‖(F.flow zX T).1-(F.flow _ p.1).1‖<T) ∧
    (F.flow zX p.1).1 ≠ (F.flow _ p.1).1
  change (p.1 ∈ Ioo 0 T ∧ p.1+‖(F.flow zX T).1-(F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1‖<T) ∧
    (F.flow zX p.1).1 ≠ (F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1
  rw [h]
  exact ⟨⟨hp.1,hp.2.1⟩,hp.2.2⟩

lemma PhaseFlowOn.arrivalLabel_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {p : ℝ × Vec} (hp : p.1 ∈ Ioo 0 T) : ContinuousAt (arrivalLabel F.flow) p := by
  obtain ⟨D,_,hD⟩ := F.inverse_differential hp (p.2,0)
  exact continuousAt_fst.prodMk (hD.continuousAt.comp
    (f := fun q : ℝ × Vec => (q.1,(q.2,0)))
    (continuousAt_fst.prodMk (continuousAt_snd.prodMk continuousAt_const)))

lemma PhaseFlowOn.isOpen_arrivalDomain {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) : IsOpen (arrivalDomain F.flow zX T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hX : ContinuousAt (fun q : ℝ × Vec => (F.flow zX q.1).1) p :=
    (((F.continuousOn_time zX).fst.continuousAt (Icc_mem_nhds hp.1.1 hp.1.2)).comp
      continuousAt_fst)
  have ht : ∀ᶠ q : ℝ × Vec in 𝓝 p, q.1 ∈ Ioo 0 T :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds hp.1)
  have hd : ContinuousAt (fun q : ℝ × Vec => q.1+‖(F.flow zX T).1-q.2‖) p :=
    continuousAt_fst.add (continuousAt_const.sub continuousAt_snd).norm
  have hb := hd.eventually (isOpen_Iio.mem_nhds hp.2.1)
  have hn := (hX.sub continuousAt_snd).eventually
    (isOpen_compl_singleton.mem_nhds (sub_ne_zero.mpr hp.2.2))
  filter_upwards [ht,hb,hn] with q hq hqt hqn
  exact ⟨hq,hqt,sub_ne_zero.mp hqn⟩

lemma PhaseFlowOn.arrival_time_spec {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    arrivalTime F.flow zX T p ∈ Ioo p.1 T ∧
      arrivalTime F.flow zX T p-p.1=‖(F.flow zX (arrivalTime F.flow zX T p)).1-p.2‖ := by
  have h := F.arrivalLabel_mem zX hp
  have ht := F.branch_time_mem zX (arrivalLabel F.flow p).2 h.1 h.2
  have he := (F.branch_spec zX (arrivalLabel F.flow p).2 h.1).2
  have hh := F.flow_inversePhase (Ioo_subset_Icc_self hp.1) (p.2,0)
  change _-p.1=‖_- (F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1‖ at he
  rw [hh] at he
  exact ⟨ht,he⟩

lemma PhaseFlowOn.arrivalTime_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (arrivalTime F.flow zX T) p :=
  (F.joint_branch_continuousAt zX (F.arrivalLabel_mem zX hp)).comp
    (f := arrivalLabel F.flow) (F.arrivalLabel_continuousAt hp.1)

lemma PhaseFlowOn.arrivalRadius_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (arrivalRadius F.flow zX T) p :=
  (F.arrivalTime_continuousAt zX hp).sub continuousAt_fst

lemma PhaseFlowOn.arrivalFlow_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (fun q => F.flow zX (arrivalTime F.flow zX T q)) p := by
  have ht := (F.arrival_time_spec zX hp).1
  have hti : arrivalTime F.flow zX T p ∈ Ioo 0 T := ⟨hp.1.1.trans ht.1,ht.2⟩
  exact (F.joint zX _ hti).continuousAt.comp
    (f := fun q => (arrivalTime F.flow zX T q,zX))
    ((F.arrivalTime_continuousAt zX hp).prodMk continuousAt_const)

lemma PhaseFlowOn.arrivalDirection_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (arrivalDirection F.flow zX T) p := by
  have hn : arrivalRadius F.flow zX T p ≠ 0 := ne_of_gt (sub_pos.mpr (F.arrival_time_spec zX hp).1.1)
  exact ((F.arrivalRadius_continuousAt zX hp).inv₀ hn).smul
    ((F.arrivalFlow_continuousAt zX hp).fst.sub continuousAt_snd)

lemma PhaseFlowOn.norm_arrivalDirection {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ‖arrivalDirection F.flow zX T p‖=1 := by
  have ht := F.arrival_time_spec zX hp
  have hr : 0 < arrivalRadius F.flow zX T p := sub_pos.mpr ht.1.1
  rw [arrivalDirection,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),← ht.2]
  exact inv_mul_cancel₀ (ne_of_gt hr)

end RVM

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

namespace RVM

lemma PhaseFlowOn.branchDirection_hasDerivAt {E B : Field} {T s : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hs : s∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1≠(F.flow zY s).1) :
    HasDerivAt (branchDirection F.flow zX zY T)
      ((branchTime F.flow zX zY T s-s)⁻¹ •
        coneMotion (velocity (F.flow zX (branchTime F.flow zX zY T s)).2)
          (velocity (F.flow zY s).2) (branchDirection F.flow zX zY T s)) s := by
  let t := branchTime F.flow zX zY T s
  have ht := F.branch_time_mem zX zY hs hne
  have hti : t∈Ioo 0 T := ⟨hs.1.1.trans ht.1,ht.2⟩
  have hg : (F.flow zX t).1-(F.flow zY s).1=(t-s) • branchDirection F.flow zX zY T s := by
    unfold branchDirection
    rw [smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr ht.1.ne'),one_smul]
  exact hasDerivAt_cone_direction rfl ht.1 hg
    (((F.ode zX t (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)).fst)
    (((F.ode zY s (Ioo_subset_Icc_self hs.1)).hasDerivAt (Icc_mem_nhds hs.1.1 hs.1.2)).fst)
    (F.branch_differential zX zY hs hne).2

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

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

lemma PhaseFlowOn.flow_contDiffOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContDiffOn ℝ 1 (F.flow z) (Ioo 0 T) := by
  have hf : ContinuousOn (F.flow z) (Ioo 0 T) := (F.continuousOn_time z).mono Ioo_subset_Icc_self
  have hp : ContinuousOn (fun t => (t,(F.flow z t).1)) (Ioo 0 T) := continuousOn_id.prodMk hf.fst
  have hE : ContinuousOn (fun t => s.E (t,(F.flow z t).1)) (Ioo 0 T) :=
    hs.E_smooth.continuousOn.comp hp (fun t ht => ⟨Ioo_subset_Icc_self ht,mem_univ _⟩)
  have hB : ContinuousOn (fun t => s.B (t,(F.flow z t).1)) (Ioo 0 T) :=
    hs.B_smooth.continuousOn.comp hp (fun t ht => ⟨Ioo_subset_Icc_self ht,mem_univ _⟩)
  have hu : ContinuousOn (fun t => velocity (F.flow z t).2) (Ioo 0 T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  have hK : ContinuousOn (fun t => s.E (t,(F.flow z t).1)+
      cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) (Ioo 0 T) :=
    hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))
  have hd (t : ℝ) (ht : t∈Ioo 0 T) := (F.ode z t (Ioo_subset_Icc_self ht)).mono Ioo_subset_Icc_self
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
  refine ⟨fun t ht => (hd t ht).differentiableWithinAt,?_⟩
  apply (hu.prodMk hK).congr
  intro t ht
  exact (hd t ht).derivWithin (isOpen_Ioo.uniqueDiffWithinAt ht)

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

lemma inverseCoordinate_log_deriv {d : ℝ→ℝ} {d' t : ℝ}
    (hd : HasDerivAt d d' t) (hp : 0<d t) :
    deriv (fun s=>1/d s) t / (1/d t) = -d'/d t := by
  have hh := ((hasDerivAt_const t (1:ℝ)).div hd hp.ne').deriv
  change deriv ((fun _ : ℝ => (1:ℝ))/d) t / (1/d t) = -d'/d t
  rw [hh]
  field_simp
  ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ActualCutoffCoordinates
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

lemma PhaseFlowOn.actualCutoffCoordinates_pos {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    ∀ i,0<actualCutoffCoordinates F.flow T zX zY σ i :=
  physicalCutoffCoordinates_pos (F.branchDirection_norm zX zY hσ hne)
    (sub_pos.mpr (F.branch_time_mem zX zY hσ hne).1)

lemma PhaseFlowOn.actualCutoffCoordinates_contDiffAt {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    ∀ i,ContDiffAt ℝ 1 (fun r=>actualCutoffCoordinates F.flow T zX zY r i) σ := by
  let τ := branchTime F.flow zX zY T
  have ht := F.branch_time_mem zX zY hσ hne
  have hτ : ContDiffAt ℝ 1 τ σ := (F.branch_differential zX zY hσ hne).1
  have hX : ContDiffAt ℝ 1 (fun r=>F.flow zX (τ r)) σ :=
    ((F.flow_contDiffOn hs zX).contDiffAt (isOpen_Ioo.mem_nhds ⟨hσ.1.1.trans ht.1,ht.2⟩)).comp σ hτ
  have hY := (F.flow_contDiffOn hs zY).contDiffAt (isOpen_Ioo.mem_nhds hσ.1)
  have hr : ContDiffAt ℝ 1 (fun r=>τ r-r) σ := hτ.sub contDiffAt_id
  have hn : ContDiffAt ℝ 1 (branchDirection F.flow zX zY T) σ :=
    (hr.inv (sub_pos.mpr ht.1).ne').smul (hX.fst.sub hY.fst)
  have hunit := F.branchDirection_norm zX zY hσ hne
  have hu := (contDiff_velocity (k:=1)).contDiffAt.comp σ hY.snd
  have ha := (contDiff_velocity (k:=1)).contDiffAt.comp σ hX.snd
  have hd := (contDiffAt_const (c:=(1:ℝ))).sub ((contDiff_dot_pair (k:=1)).contDiffAt.comp σ (hn.prodMk hu))
  have hD := (contDiffAt_const (c:=(1:ℝ))).sub ((contDiff_dot_pair (k:=1)).contDiffAt.comp σ (hn.prodMk ha))
  intro i
  fin_cases i <;> simp only [actualCutoffCoordinates,physicalCutoffCoordinates]
  · exact contDiffAt_const.div ((contDiff_q (k:=1)).contDiffAt.comp σ hY.snd) (q_pos _).ne'
  · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hunit) (by norm_num)).ne'
  · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hunit) (by norm_num)).ne'
  · exact hr.div_const _

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

lemma PhaseFlowOn.retardedMomentum_hasDerivAt {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    let τ := branchTime F.flow zX zY T
    let n := branchDirection F.flow zX zY T σ
    let d := 1-dot n (velocity (F.flow zY σ).2)
    let D := 1-dot n (velocity (F.flow zX (τ σ)).2)
    HasDerivAt (fun r=>(F.flow zX (τ r)).2)
      ((d/D) • (lorentzField E B (τ σ,F.flow zX (τ σ))).2) σ := by
  have ht := F.branch_time_mem zX zY hσ hne
  have hti : branchTime F.flow zX zY T σ∈Ioo 0 T := ⟨hσ.1.1.trans ht.1,ht.2⟩
  have hW : HasDerivAt (fun r=>(F.flow zX r).2)
      (lorentzField E B (branchTime F.flow zX zY T σ,F.flow zX (branchTime F.flow zX zY T σ))).2
      (branchTime F.flow zX zY T σ) :=
    ((F.ode zX _ (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)).snd
  exact hW.scomp σ (F.branch_differential zX zY hσ hne).2



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_PhaseTimePullback
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

lemma PhaseFlowOn.measurable_phaseTimePullback {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) {W : Type*} [Zero W] [MeasurableSpace W]
    {g : ℝ×Phase→W} (hg : Measurable g) :
    Measurable (phaseTimePullback F.flow T g) := by
  classical
  have hm := (hg.comp (measurable_fst.prodMk F.measurable_joint_flow_zero)).indicator
    ((measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) T)).prod MeasurableSet.univ)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  by_cases hp : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase)
  · simp only [phaseTimePullback,Function.comp_apply,indicator_of_mem hp]
  · simp only [phaseTimePullback,indicator_of_notMem hp]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverQCLM
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

lemma PhaseFlowOn.isOpen_arrivalPhaseDomain {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) : IsOpen (arrivalPhaseDomain F.flow zX T) :=
  (F.isOpen_arrivalDomain zX).preimage (continuous_fst.prodMk continuous_snd.fst)

lemma PhaseFlowOn.arrivalKernelState_mem {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈arrivalPhaseDomain F.flow zX T) :
    arrivalKernelState F.flow zX T p∈coneKernelDomain T := by
  have ht := F.arrival_time_spec zX hp
  exact ⟨⟨⟨(hp.1.1.trans ht.1.1).le,ht.1.2.le⟩,Ioo_subset_Icc_self hp.1⟩,
    ⟨by simpa only [arrivalKernelState,mem_sphere,dist_zero_right] using F.norm_arrivalDirection zX hp,mem_univ _⟩⟩

lemma PhaseFlowOn.arrivalKernelState_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (arrivalKernelState F.flow zX T) (arrivalPhaseDomain F.flow zX T) := by
  intro p hp
  have hc : ContinuousAt (fun p : ℝ×Phase=>(p.1,p.2.1)) p :=
    continuousAt_fst.prodMk continuousAt_snd.fst
  exact (((F.arrivalTime_continuousAt zX hp).comp (f := fun p : ℝ×Phase=>(p.1,p.2.1)) hc).prodMk continuousAt_fst).prodMk
    (((F.arrivalDirection_continuousAt zX hp).comp (f := fun p : ℝ×Phase=>(p.1,p.2.1)) hc).prodMk continuousAt_snd) |>.continuousWithinAt

lemma PhaseFlowOn.measurable_arrivalConeKernel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    Measurable (arrivalConeKernel s F.flow zX T A) := by
  classical
  have hr : ContinuousOn (fun p : ℝ×Phase=>arrivalRadius F.flow zX T (p.1,p.2.1))
      (arrivalPhaseDomain F.flow zX T) := by
    intro p hp
    exact ((F.arrivalRadius_continuousAt zX hp).comp (f := fun p : ℝ×Phase=>(p.1,p.2.1))
      (continuousAt_fst.prodMk continuousAt_snd.fst)).continuousWithinAt
  have hr0 : ∀p∈arrivalPhaseDomain F.flow zX T,
      arrivalRadius F.flow zX T (p.1,p.2.1)≠0 := fun p hp=>
    (sub_pos.mpr (F.arrival_time_spec zX hp).1.1).ne'
  have hf : ContinuousOn s.f (arrivalPhaseDomain F.flow zX T) :=
    hs.f_smooth.continuousOn.mono (fun _ hp=>⟨Ioo_subset_Icc_self hp.1,mem_univ _⟩)
  have hc := ((hr.inv₀ hr0).pow 2).smul (hf.smul
    (hA.comp (F.arrivalKernelState_continuousOn zX) (fun _ hp=>F.arrivalKernelState_mem zX hp)))
  exact hc.measurable_piecewise continuousOn_const (F.isOpen_arrivalPhaseDomain zX).measurableSet

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

lemma labelBranchDomain_iff (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (p : ℝ×Phase) :
    p∈labelBranchDomain α zX T ↔ (p.1,α p.2 p.1)∈arrivalPhaseDomain α zX T := by
  change ((p.1∈Ioo 0 T ∧ p.1+‖(α zX T).1-(α p.2 p.1).1‖<T) ∧
    (α zX p.1).1≠(α p.2 p.1).1) ↔ _
  change _ ↔ (p.1∈Ioo 0 T ∧ p.1+‖(α zX T).1-(α p.2 p.1).1‖<T ∧
    (α zX p.1).1≠(α p.2 p.1).1)
  tauto

lemma PhaseFlowOn.arrivalTime_flow_eq_branchTime {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hp : (σ,zY)∈labelBranchDomain F.flow zX T) :
    arrivalTime F.flow zX T (σ,(F.flow zY σ).1)=branchTime F.flow zX zY T σ := by
  have hh := F.arrival_time_spec zX ((labelBranchDomain_iff _ _ _ _).mp hp)
  exact F.branch_unique zX zY hp.1 (Ioo_subset_Icc_self hh.1) hh.2

lemma normalisedPrimitive_eq {r : ℝ} (a u n : Vec) (hr : r≠0) :
    normalisedPrimitive r a u n=r^2 • retardedPrimitive r a u n := by
  rw [normalisedPrimitive,retardedPrimitive,smul_smul]
  congr 1
  field_simp

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

lemma PhaseFlowOn.labelKernelState_eq_arrival {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈labelBranchDomain F.flow zX T) :
    labelKernelState F.flow zX T p=arrivalKernelState F.flow zX T (p.1,F.flow p.2 p.1) := by
  simp only [labelKernelState,arrivalKernelState,arrivalDirection,arrivalRadius,branchDirection,
    F.arrivalTime_flow_eq_branchTime zX p.2 hp]

lemma PhaseFlowOn.labelConeKernel_eq_pullback {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (A : ConeKernelState→Vec) :
    labelConeKernel s F.flow zX T A=phaseTimePullback F.flow T (arrivalConeKernel s F.flow zX T A) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have he := (labelBranchDomain_iff _ _ _ _).mp hp
    have ht : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase) := ⟨hp.1.1,mem_univ _⟩
    rw [labelConeKernel,indicator_of_mem hp,phaseTimePullback,indicator_of_mem ht,
      arrivalConeKernel,indicator_of_mem he,F.labelKernelState_eq_arrival zX hp,
      F.transport hs.f_smooth hs.vlasov (Ioo_subset_Icc_self hp.1.1) p.2]
    simp only [arrivalRadius,F.arrivalTime_flow_eq_branchTime zX p.2 hp]
  · have he := mt (labelBranchDomain_iff _ _ _ _).mpr hp
    rw [labelConeKernel,indicator_of_notMem hp]
    by_cases ht : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase)
    · rw [phaseTimePullback,indicator_of_mem ht,arrivalConeKernel,indicator_of_notMem he]
    · rw [phaseTimePullback,indicator_of_notMem ht]

lemma PhaseFlowOn.measurable_labelConeKernel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    Measurable (labelConeKernel s F.flow zX T A) := by
  rw [F.labelConeKernel_eq_pullback hs zX]
  exact F.measurable_phaseTimePullback (F.measurable_arrivalConeKernel hs zX hA)

lemma PhaseFlowOn.actualLabelPrimitive_eq_normalised {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) :
    actualLabelPrimitive s F.flow zX T=labelConeKernel s F.flow zX T
      (fun p=>normalisedPrimitive (p.1.1-p.1.2) (velocity (F.flow zX p.1.1).2)
        (velocity p.2.2.2) p.2.1) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hr : branchTime F.flow zX p.2 T p.1-p.1≠0 :=
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1).ne'
    simp only [actualLabelPrimitive,labelConeKernel,indicator_of_mem hp,labelKernelState,
      normalisedPrimitive_eq _ _ _ hr]
    rw [smul_comm (s.f (0,p.2)),smul_smul,←mul_pow,inv_mul_cancel₀ hr,one_pow,one_smul]
  · simp only [actualLabelPrimitive,labelConeKernel,indicator_of_notMem hp]

lemma PhaseFlowOn.actualLabelPrimitive_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualLabelPrimitive s F.flow zX T) := by
  rw [F.actualLabelPrimitive_eq_normalised zX]
  exact F.measurable_labelConeKernel hs zX (F.normalised_primitive_continuousOn zX)

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

lemma PhaseFlowOn.branchCutoffState_hasDerivAt {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    HasDerivAt (branchCutoffState F.flow T zX zY)
      (branchCutoffStateRate E B F.flow T zX zY σ) σ := by
  have hτ := (F.branch_differential zX zY hσ hne).2
  have hY := ((F.ode zY σ (Ioo_subset_Icc_self hσ.1)).hasDerivAt
    (Icc_mem_nhds hσ.1.1 hσ.1.2)).snd
  exact (hτ.sub (hasDerivAt_id σ)).prodMk
    ((F.branchDirection_hasDerivAt zX zY hσ hne).prodMk
      (hY.prodMk (F.retardedMomentum_hasDerivAt zX zY hσ hne)))

lemma PhaseFlowOn.momentumForce_continuousOn_closed {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContinuousOn (fun t=>(lorentzField s.E s.B (t,F.flow z t)).2) (Icc 0 T) := by
  have hf := F.continuousOn_time z
  have hp : ContinuousOn (fun t => (t,(F.flow z t).1)) (Icc 0 T) := continuousOn_id.prodMk hf.fst
  have hE : ContinuousOn (fun t => s.E (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.E_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hB : ContinuousOn (fun t => s.B (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.B_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hu : ContinuousOn (fun t => velocity (F.flow z t).2) (Icc 0 T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_BranchCutoffStateContinuous
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

lemma PhaseFlowOn.branchCutoffState_continuousAt {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈jointBranchDomain F.flow zX T) :
    ContinuousAt (fun q : ℝ×Phase=>branchCutoffState F.flow T zX q.2 q.1) p := by
  have hτ := F.joint_branch_continuousAt zX hp
  have ht := F.branch_time_mem zX p.2 hp.1 hp.2
  have hX := ((F.continuousOn_time zX).continuousAt
    (Icc_mem_nhds (hp.1.1.1.trans ht.1) ht.2)).comp (f := fun q : ℝ×Phase=>branchTime F.flow zX q.2 T q.1) hτ
  have hY := (F.joint p.2 p.1 hp.1.1).continuousAt
  have hr := hτ.sub continuousAt_fst
  have hr0 : branchTime F.flow zX p.2 T p.1-p.1≠0 := (sub_pos.mpr ht.1).ne'
  exact hr.prodMk (((hr.inv₀ hr0).smul (hX.fst.sub hY.fst)).prodMk
    (hY.snd.prodMk hX.snd))

lemma PhaseFlowOn.joint_momentumForce_continuousAt {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) {p : ℝ×Phase}
    (hp : p.1∈Ioo 0 T) :
    ContinuousAt (fun q : ℝ×Phase=>(lorentzField s.E s.B (q.1,F.flow q.2 q.1)).2) p := by
  have hF := (F.joint p.2 p.1 hp).continuousAt
  have hx := continuousAt_fst.prodMk hF.fst
  have hm : (p.1,(F.flow p.2 p.1).1)∈interior (Icc 0 T ×ˢ (univ : Set Vec)) := by
    rw [interior_prod_eq,interior_Icc,interior_univ]
    exact ⟨hp,mem_univ _⟩
  have hE := (hs.E_smooth.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hm)).comp (f := fun q : ℝ×Phase=>(q.1,(F.flow q.2 q.1).1)) hx
  have hB := (hs.B_smooth.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hm)).comp (f := fun q : ℝ×Phase=>(q.1,(F.flow q.2 q.1).1)) hx
  have hu := (contDiff_velocity (k:=1)).continuous.continuousAt.comp hF.snd
  exact hE.add ((contDiff_cross (k:=1)).continuous.continuousAt.comp (hu.prodMk hB))

lemma PhaseFlowOn.branchCutoffStateRate_continuousAt {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈jointBranchDomain F.flow zX T) :
    ContinuousAt (fun q : ℝ×Phase=>branchCutoffStateRate s.E s.B F.flow T zX q.2 q.1) p := by
  have hz := F.branchCutoffState_continuousAt zX hp
  have hτ := F.joint_branch_continuousAt zX hp
  have ht := F.branch_time_mem zX p.2 hp.1 hp.2
  have hn := F.branchDirection_norm zX p.2 hp.1 hp.2
  have ha := (contDiff_velocity (k:=1)).continuous.continuousAt.comp hz.snd.snd.snd
  have hu := (contDiff_velocity (k:=1)).continuous.continuousAt.comp hz.snd.snd.fst
  have hd := (continuousAt_const (y:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=1)).continuous.continuousAt.comp (hz.snd.fst.prodMk hu))
  have hD := (continuousAt_const (y:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=1)).continuous.continuousAt.comp (hz.snd.fst.prodMk ha))
  have hD0 : 1-dot (branchDirection F.flow zX p.2 T p.1)
      (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2)≠0 :=
    (cone_denom_pos _ _ hn).ne'
  have hρ := hd.div hD hD0
  have hr0 : branchTime F.flow zX p.2 T p.1-p.1≠0 := (sub_pos.mpr ht.1).ne'
  have hN := (hz.fst.inv₀ hr0).smul
    (((hρ.smul (ha.sub hz.snd.fst)).add hz.snd.fst).sub hu)
  have hKY := F.joint_momentumForce_continuousAt hs hp.1.1
  have hKX := ((F.momentumForce_continuousOn_closed hs zX).continuousAt
    (Icc_mem_nhds (hp.1.1.1.trans ht.1) ht.2)).comp (f := fun q : ℝ×Phase=>branchTime F.flow zX q.2 T q.1) hτ
  exact (hρ.sub continuousAt_const).prodMk (hN.prodMk (hKY.prodMk (hρ.smul hKX)))

lemma PhaseFlowOn.branchSelectedRate_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) :
    Measurable ((jointBranchDomain F.flow zX T).indicator
      (fun p : ℝ×Phase=>branchSelectedRate s.E s.B F.flow T zX p.2 Q p.1)) := by
  classical
  have hc : ContinuousOn (fun p : ℝ×Phase=>branchSelectedRate s.E s.B F.flow T zX p.2 Q p.1)
      (jointBranchDomain F.flow zX T) := by
    intro p hp
    have hsc := contDiffAt_stateCutoff T Q (z:=branchCutoffState F.flow T zX p.2 p.1)
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1)
      (F.branchDirection_norm zX p.2 hp.1 hp.2)
    exact (((hsc.continuousAt_fderiv (by simp)).comp (f := fun q : ℝ×Phase=>branchCutoffState F.flow T zX q.2 q.1)
      (F.branchCutoffState_continuousAt zX hp)).clm_apply
        (F.branchCutoffStateRate_continuousAt hs zX hp)).continuousWithinAt
  exact hc.measurable_piecewise continuousOn_const (F.isOpen_jointBranchDomain zX).measurableSet

lemma norm_fderiv_velocity_apply_le (v h : Vec) :
    ‖fderiv ℝ velocity v h‖≤‖h‖ := by
  apply ((fderiv ℝ velocity v).le_opNorm h).trans
  have hi : (q v)⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_q v)
  exact (mul_le_mul_of_nonneg_right (norm_fderiv_velocity_le v) (norm_nonneg h)).trans
    (by simpa using mul_le_mul_of_nonneg_right hi (norm_nonneg h))

lemma deficit_rate_bound {N V : ℝ→Vec} {n' v' : Vec} {t : ℝ}
    (hN : HasDerivAt N n' t) (hV : HasDerivAt V v' t) (hn : ‖N t‖=1) :
    |deriv (fun s=>1-dot (N s) (velocity (V s))) t|≤‖n'‖+‖v'‖ := by
  have hu := ((contDiff_velocity (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  have hd := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot hN hu)
  change HasDerivAt (fun s=>1-dot (N s) (velocity (V s))) _ t at hd
  rw [hd.deriv]
  simp only [zero_sub,abs_neg]
  apply (abs_add_le _ _).trans
  have ha : |dot (N t) (fderiv ℝ velocity (V t) v')|≤‖v'‖ := by
    apply (abs_dot_le _ _).trans
    rw [hn,one_mul]
    exact norm_fderiv_velocity_apply_le _ _
  have hb : |dot n' (velocity (V t))|≤‖n'‖ :=
    (abs_dot_le _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left (norm_velocity_lt_one (V t)).le (norm_nonneg n'))
  simpa only [Function.comp_apply] using add_le_add ha hb |>.trans (le_of_eq (add_comm _ _))

lemma physical_cutoff_coarse_rates {T t : ℝ} {V W N : ℝ→Vec} {R : ℝ→ℝ}
    {v' w' n' : Vec} {r' : ℝ} (hn : ‖N t‖=1) (hr : 0<R t)
    (hV : HasDerivAt V v' t) (hW : HasDerivAt W w' t)
    (hN : HasDerivAt N n' t) (hR : HasDerivAt R r' t) :
    ∑ i : Fin 4,|deriv (fun s=>physicalCutoffCoordinates T (R s) (N s) (V s) (W s) i) t /
        physicalCutoffCoordinates T (R t) (N t) (V t) (W t) i| ≤
      ‖v'‖+(‖n'‖+‖v'‖)/(2*(1-dot (N t) (velocity (V t))))+
        (‖n'‖+‖w'‖)/(2*(1-dot (N t) (velocity (W t))))+|r'|/R t := by
  have hq := ((contDiff_q (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  rw [fderiv_q_apply] at hq
  change HasDerivAt (fun s=>q (V s)) _ t at hq
  have hu := ((contDiff_velocity (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  have ha := ((contDiff_velocity (k:=1)).differentiable one_ne_zero (W t)).hasFDerivAt.comp_hasDerivAt t hW
  have hd := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot hN hu)
  change HasDerivAt (fun s=>1-dot (N s) (velocity (V s))) _ t at hd
  have hD := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot hN ha)
  change HasDerivAt (fun s=>1-dot (N s) (velocity (W s))) _ t at hD
  have hdp := cone_denom_pos (V t) (N t) hn
  have hDp := cone_denom_pos (W t) (N t) hn
  have hed := angularCoordinate_log_deriv hd hdp
  have heD := angularCoordinate_log_deriv hD hDp
  have heq := inverseCoordinate_log_deriv hq (q_pos (V t))
  have hdb := deficit_rate_bound hN hV hn
  have hDb := deficit_rate_bound hN hW hn
  rw [hd.deriv] at hdb
  rw [hD.deriv] at hDb
  have hqb : |-dot (velocity (V t)) v'/q (V t)|≤‖v'‖ := by
    rw [abs_div,abs_neg,abs_of_pos (q_pos _)]
    apply (div_le_iff₀ (q_pos _)).mpr
    apply (abs_dot_le _ _).trans
    apply (mul_le_mul_of_nonneg_right (norm_velocity_lt_one _).le (norm_nonneg _)).trans
    rw [one_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_q _)
  have her : deriv (fun s=>R s/max 1 T) t/(R t/max 1 T)=r'/R t := by
    rw [(hR.div_const (max 1 T)).deriv]
    have hm : max 1 T≠0 := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'
    field_simp
  simp only [Fin.sum_univ_succ,Fin.isValue,physicalCutoffCoordinates,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  rw [heq,hed,heD,her]
  rw [abs_div,abs_neg,abs_of_pos (q_pos _)] at hqb
  simp only [abs_div,abs_neg,abs_of_pos (q_pos _),abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hdp),
    abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hDp),abs_of_pos hr]
  have hddiv := div_le_div_of_nonneg_right hdb (mul_pos (by norm_num : (0:ℝ)<2) hdp).le
  have hDdiv := div_le_div_of_nonneg_right hDb (mul_pos (by norm_num : (0:ℝ)<2) hDp).le
  linarith

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_CutoffRateMajorant
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

lemma cutoffRateMajorant_eq {r : ℝ} (hr : 0 < r) (a u n vy vx : Vec) :
    cutoffRateMajorant r a u n vy vx =
    r*(‖vy‖+(‖r⁻¹ • coneMotion a u n‖+‖vy‖)/(2*(1-dot n u))+
      (‖r⁻¹ • coneMotion a u n‖+‖((1-dot n u)/(1-dot n a)) • vx‖)/(2*(1-dot n a))+
        |(1-dot n u)/(1-dot n a)-1|/r) := by
  simp only [cutoffRateMajorant,abs_of_pos hr,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  field_simp [hr.ne']

lemma PhaseFlowOn.branchSelectedRate_coarse_bound {s : Solution} {T σ C : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1)
    (Q : Set (Fin 4→ℕ)) (hC0 : 0≤C)
    (hC : ∀ n : ℕ,∀ x : ℝ,|x*deriv (dyadicFactor n) x|≤C) :
    let τ := branchTime F.flow zX zY T σ
    (τ-σ)*|branchSelectedRate s.E s.B F.flow T zX zY Q σ| ≤
      (5:ℝ)^4*C*cutoffRateMajorant (τ-σ) (velocity (F.flow zX τ).2)
        (velocity (F.flow zY σ).2) (branchDirection F.flow zX zY T σ)
        (lorentzField s.E s.B (σ,F.flow zY σ)).2
        (lorentzField s.E s.B (τ,F.flow zX τ)).2 := by
  dsimp only
  have hr : 0<branchTime F.flow zX zY T σ-σ :=
    sub_pos.mpr (F.branch_time_mem zX zY hσ hne).1
  have hn := F.branchDirection_norm zX zY hσ hne
  have hχ := ((contDiffAt_stateCutoff T Q
    (z:=branchCutoffState F.flow T zX zY σ) hr hn).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt σ
      (F.branchCutoffState_hasDerivAt zX zY hσ hne)
  have hχeq : deriv (fun r=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY r)) σ=
      branchSelectedRate s.E s.B F.flow T zX zY Q σ := hχ.deriv
  have hb := selectedDyadicCutoff_uniform_log_bound hC0 hC
    (fun i=>(F.actualCutoffCoordinates_contDiffAt hs zX zY hσ hne i).differentiableAt one_ne_zero)
    (F.actualCutoffCoordinates_pos zX zY hσ hne) Q
  rw [hχeq] at hb
  have hY := ((F.ode zY σ (Ioo_subset_Icc_self hσ.1)).hasDerivAt
    (Icc_mem_nhds hσ.1.1 hσ.1.2)).snd
  have hX := F.retardedMomentum_hasDerivAt zX zY hσ hne
  have hN := F.branchDirection_hasDerivAt zX zY hσ hne
  have hR := (F.branch_differential zX zY hσ hne).2.sub (hasDerivAt_id σ)
  have hsumb := physical_cutoff_coarse_rates (T:=T)
    (R:=fun t=>branchTime F.flow zX zY T t-t) hn hr hY hX hN hR
  change ∑ i : Fin 4,|deriv (fun r=>actualCutoffCoordinates F.flow T zX zY r i) σ /
      actualCutoffCoordinates F.flow T zX zY σ i| ≤ _ at hsumb
  rw [cutoffRateMajorant_eq hr]
  simp only [Fintype.card_fin] at hb
  have hm := mul_le_mul_of_nonneg_left (hb.trans
    (mul_le_mul_of_nonneg_left hsumb (by positivity))) hr.le
  rw [mul_left_comm (5^4*C)]
  exact hm

lemma retardedPrimitive_eq_inverse_smul (r : ℝ) (a u n : Vec) :
    retardedPrimitive r a u n=r⁻¹ • normalisedPrimitive 1 a u n := by
  simp only [retardedPrimitive,normalisedPrimitive,smul_smul,one_div,mul_inv]

lemma cutoff_primitive_norm_bound {r c B : ℝ} (hr : 0 < r) (a u n : Vec)
    (hb : r*|c|≤B) :
    ‖c • retardedPrimitive r a u n‖ ≤ r⁻¹^2*‖B • normalisedPrimitive 1 a u n‖ := by
  have hB : 0≤B := (mul_nonneg hr.le (abs_nonneg _)).trans hb
  rw [retardedPrimitive_eq_inverse_smul,norm_smul,norm_smul,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),norm_smul,Real.norm_eq_abs,abs_of_nonneg hB]
  calc
    |c| * (r⁻¹ * ‖normalisedPrimitive 1 a u n‖) =
        (r*|c|)*(r⁻¹^2*‖normalisedPrimitive 1 a u n‖) := by
      field_simp [ne_of_gt hr]
    _ ≤ B*(r⁻¹^2*‖normalisedPrimitive 1 a u n‖) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = r⁻¹^2*(B*‖normalisedPrimitive 1 a u n‖) := by ring

lemma continuousOn_cutoffRateMajorant {Q : Type*} [TopologicalSpace Q]
    {r : Q→ℝ} {a u n vy vx : Q→Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S) (hu : ContinuousOn u S)
    (hn : ContinuousOn n S) (hvy : ContinuousOn vy S) (hvx : ContinuousOn vx S)
    (hd : ∀p∈S,1-dot (n p) (u p)≠0) (hD : ∀p∈S,1-dot (n p) (a p)≠0) :
    ContinuousOn (fun p=>cutoffRateMajorant (r p) (a p) (u p) (n p) (vy p) (vx p)) S := by
  have hdot {f g : Q→Vec} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun p=>dot (f p) (g p)) S := by
    simpa only [dot_eq_inner] using hf.inner hg
  have hdc := (continuousOn_const (c:=(1:ℝ))).sub (hdot hn hu)
  have hDc := (continuousOn_const (c:=(1:ℝ))).sub (hdot hn ha)
  have hρ := hdc.div hDc hD
  have hm : ContinuousOn (fun p=>coneMotion (a p) (u p) (n p)) S :=
    ((hρ.smul (ha.sub hn)).add hn).sub hu
  exact (((hr.abs.mul hvy.norm).add
    ((hm.norm.add (hr.abs.mul hvy.norm)).div (continuousOn_const.mul hdc)
      (fun p hp=>mul_ne_zero (by norm_num) (hd p hp)))).add
    ((hm.norm.add (hr.abs.mul (hρ.smul hvx).norm)).div (continuousOn_const.mul hDc)
      (fun p hp=>mul_ne_zero (by norm_num) (hD p hp)))).add
        (hρ.sub continuousOn_const).abs

lemma EnergyPrefix.continuousOn_momentumForce {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) :
    ContinuousOn (fun p : ℝ×Phase=>(lorentzField s.E s.B p).2)
      (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hp : Continuous (fun p : ℝ×Phase=>(p.1,p.2.1)) := continuous_fst.prodMk continuous_snd.fst
  have hE : ContinuousOn (fun p : ℝ×Phase=>s.E (p.1,p.2.1)) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    hs.E_smooth.continuousOn.comp hp.continuousOn (fun _ hp=>⟨hp.1,mem_univ _⟩)
  have hB : ContinuousOn (fun p : ℝ×Phase=>s.B (p.1,p.2.1)) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    hs.B_smooth.continuousOn.comp hp.continuousOn (fun _ hp=>⟨hp.1,mem_univ _⟩)
  have hu := (contDiff_velocity (k:=1)).continuous.comp (continuous_snd.snd : Continuous (fun p : ℝ×Phase=>p.2.2))
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.continuousOn.prodMk hB))

lemma PhaseFlowOn.normalisedCutoffPrimitive_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (K : ℝ) :
    ContinuousOn (normalisedCutoffPrimitive s F.flow zX K) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  have hn : Continuous (fun p : ConeKernelState=>p.2.1) := continuous_snd.fst
  have hvy : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.2,p.2.2)).2)
      (coneKernelDomain T) := hs.continuousOn_momentumForce.comp
        (continuous_fst.snd.prodMk continuous_snd.snd).continuousOn (fun _ hp=>⟨hp.1.2,mem_univ _⟩)
  have hvx : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.1,F.flow zX p.1.1)).2)
      (coneKernelDomain T) := (F.momentumForce_continuousOn_closed hs zX).comp
        continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)
  have hd : ∀p∈coneKernelDomain T,1-dot p.2.1 (velocity p.2.2.2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  have hD : ∀p∈coneKernelDomain T,1-dot p.2.1 (velocity (F.flow zX p.1.1).2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  exact (continuousOn_const.mul (continuousOn_cutoffRateMajorant
    (continuous_fst.fst.sub continuous_fst.snd).continuousOn ha hu.continuousOn hn.continuousOn hvy hvx hd hD)).smul
      (continuousOn_normalisedPrimitive continuousOn_const ha hu.continuousOn hn.continuousOn hd hD)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ActualLabelCutoffCost
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

lemma PhaseFlowOn.actualLabelCutoffCost_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    Measurable (actualLabelCutoffCost s F.flow zX T Q) :=
  (F.branchSelectedRate_measurable hs zX Q).smul (F.actualLabelPrimitive_measurable hs zX)

lemma PhaseFlowOn.actualLabelCutoffCost_integrable_oai {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    Integrable (actualLabelCutoffCost s F.flow zX T Q) := by
  classical
  obtain ⟨C,hC,hcb⟩ := dyadicFactor_log_derivative_bound
  let A := normalisedCutoffPrimitive s F.flow zX (5^4*C)
  have hA := F.normalisedCutoffPrimitive_continuousOn hs zX (5^4*C)
  apply (F.labelConeKernel_integrable hs zX hA).norm.mono'
    (F.actualLabelCutoffCost_measurable hs zX Q).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hj : p∈jointBranchDomain F.flow zX T := hp
    have hr : 0<branchTime F.flow zX p.2 T p.1-p.1 :=
      sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1
    have hb := F.branchSelectedRate_coarse_bound hs zX p.2 hp.1 hp.2 Q hC hcb
    have hv := cutoff_primitive_norm_bound hr (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2)
      (velocity (F.flow p.2 p.1).2) (branchDirection F.flow zX p.2 T p.1) hb
    rw [actualLabelCutoffCost,indicator_of_mem hj,actualLabelPrimitive,indicator_of_mem hp,
      labelConeKernel,indicator_of_mem hp]
    rw [smul_comm (branchSelectedRate s.E s.B F.flow T zX p.2 Q p.1) (s.f (0,p.2))]
    simp only [norm_smul,Real.norm_eq_abs] at hv ⊢
    rw [abs_of_nonneg (sq_nonneg ((branchTime F.flow zX p.2 T p.1-p.1)⁻¹))]
    convert mul_le_mul_of_nonneg_left hv (abs_nonneg (s.f (0,p.2))) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [normalisedCutoffPrimitive,labelKernelState,norm_smul,Real.norm_eq_abs]
    ring
  · have hj : p∉jointBranchDomain F.flow zX T := hp
    simp only [actualLabelCutoffCost,indicator_of_notMem hj,zero_smul,norm_zero,labelConeKernel,
      indicator_of_notMem hp,le_refl]

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.actualLabelCutoffCost_integrable_oai := @OAI.RVM.PhaseFlowOn.actualLabelCutoffCost_integrable_oai
