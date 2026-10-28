-- Prove2me | solution 1 for OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:51:12.26337+00:00
-- url     : https://prove2.me/submissions/c53052f7-2770-465b-b50c-8c559524cb6f

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V002
import Theorems.Thm_OAI_RVM_PhaseFlowOn_selectedMultiplier_integrable
import Theorems.Thm_OAI_RVM_PhaseFlowOn_unselectedLabelSignedForce_integrable
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_multiplier_retarded_force_label
import Theorems.Thm_OAI_RVM_selectedInitialKernel_integrable_bound

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

lemma hasDerivAt_dot {f g : ℝ → Vec} {f' g' : Vec} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => dot (f t) (g t))
      (dot (f s) g' + dot f' (g s)) s := by
  simpa only [dot_eq_inner] using hf.inner ℝ hg

lemma hasDerivAt_signedPrimitive {a u n : ℝ → Vec} {a' u' n' : Vec} {s : ℝ}
    (ha : HasDerivAt a a' s) (hu : HasDerivAt u u' s) (hn : HasDerivAt n n' s)
    (hD : 1 - dot (n s) (a s) ≠ 0) :
    HasDerivAt (fun t => signedPrimitive (a t) (u t) (n t))
      (signedPrimitiveRate (a s) (u s) (n s) a' u' n') s := by
  have he := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_dot ha hu)
  have hden := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_dot hn ha)
  have h := hu.sub ((he.div hden hD).smul hn)
  convert h using 1 <;> try rfl
  · dsimp [signedPrimitiveRate]
    congr 3
    ring

lemma hasDerivAt_retardedPrimitive {r : ℝ → ℝ} {a u n : ℝ → Vec}
    {r' : ℝ} {a' u' n' : Vec} {s : ℝ}
    (hr : HasDerivAt r r' s) (ha : HasDerivAt a a' s)
    (hu : HasDerivAt u u' s) (hn : HasDerivAt n n' s)
    (hr0 : r s ≠ 0) (hd : 1 - dot (n s) (u s) ≠ 0)
    (hD : 1 - dot (n s) (a s) ≠ 0) :
    HasDerivAt (fun t => retardedPrimitive (r t) (a t) (u t) (n t))
      (retardedPrimitiveRate (r s) (a s) (u s) (n s) r' a' u' n') s := by
  have hden := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_dot hn hu)
  have hinv := (hr.mul hden).inv (mul_ne_zero hr0 hd)
  have h := hinv.smul (hasDerivAt_signedPrimitive ha hu hn hD)
  convert h using 1 <;> try rfl
  · dsimp [retardedPrimitiveRate]
    congr 3
    ring

lemma signed_force_identity (r : ℝ) (a u n u' aₜ : Vec)
    (hr : r ≠ 0) (hd : 1 - dot n u ≠ 0) (hD : 1 - dot n a ≠ 0) :
    signedForceKernel r a u n u' =
      -retardedPrimitiveRate r a u n
        ((1 - dot n u) / (1 - dot n a) - 1)
        (((1 - dot n u) / (1 - dot n a)) • aₜ) u' (r⁻¹ • coneMotion a u n) +
      ((1 - dot a u) / (r^2 * (1 - dot n a)^2)) •
        (((1 - dot a a) / (1 - dot n a)) • n - a) +
      (dot aₜ (signedPrimitive a u n) / (r * (1 - dot n a)^2)) • n := by
  ext i
  simp only [signedForceKernel, retardedPrimitiveRate, signedPrimitiveRate,
    sourceVelocityRate, coneTransform, signedPrimitive, coneMotion,
    dot_add_left, dot_sub_left, dot_smul_left, dot_add_right, dot_sub_right,
    dot_smul_right, dot_comm a n, dot_comm u a, dot_comm aₜ n, dot_comm aₜ u,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
  field_simp
  ring

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


section HaarFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurePreserving_of_bijective_det_one {f : E → E} {f' : E → (E →L[ℝ] E)}
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hbij : Function.Bijective f) (hdet : ∀ x, (f' x).det = 1) :
    MeasurePreserving f μ μ := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  refine ⟨hc.measurable,?_⟩
  have hh := map_withDensity_abs_det_fderiv_eq_addHaar μ (s := univ)
    MeasurableSet.univ.nullMeasurableSet (fun x _ => (hf x).hasFDerivWithinAt) hbij.1.injOn
  simp only [Measure.restrict_univ,hdet,abs_one,ENNReal.ofReal_one,
    Set.image_univ,hbij.2.range_eq] at hh
  change Measure.map f (μ.withDensity 1) = μ at hh
  simpa only [withDensity_one] using hh

end HaarFlow

lemma PhaseFlowOn.measurePreserving {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) : MeasurePreserving (F.flow · t) :=
  measurePreserving_of_bijective_det_one volume (fun z => F.label z t ht)
    (F.bijective t ht) (fun z => F.det_one z t ht)

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

lemma PhaseFlowOn.emission_strictMono {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) (x : Vec) :
    StrictMonoOn (fun s => s+‖x-(F.flow z s).1‖) (Icc 0 T) := by
  obtain ⟨c,hc,hLip⟩ := F.timelike hT z
  intro a ha b hb hab
  have hbound := hLip.dist_le_mul a ha b hb
  rw [dist_eq_norm,Real.dist_eq,abs_of_neg (sub_neg.mpr hab)] at hbound
  have hn : ‖x-(F.flow z a).1‖ ≤ ‖(F.flow z a).1-(F.flow z b).1‖ + ‖x-(F.flow z b).1‖ := by
    calc
      _ = ‖((F.flow z b).1-(F.flow z a).1)+(x-(F.flow z b).1)‖ := by congr 1; abel
      _ ≤ ‖(F.flow z b).1-(F.flow z a).1‖ + ‖x-(F.flow z b).1‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have hp := mul_pos (sub_pos.mpr hc) (sub_pos.mpr hab)
  nlinarith

lemma PhaseFlowOn.inversePhase_flow {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) : inversePhase F.flow (s,F.flow z s) = z :=
  Function.leftInverse_invFun (F.bijective s hs).1 z

lemma PhaseFlowOn.flow_inversePhase {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) : F.flow (inversePhase F.flow (s,z)) s = z :=
  Function.invFun_eq ((F.bijective s hs).2 z)

lemma PhaseFlowOn.tip_null {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) : volume {z : Phase | (F.flow z t).1=x} = 0 := by
  have hz : (volume : Measure Phase) ({x} ×ˢ univ) = 0 := by
    change (volume.prod volume) ({x} ×ˢ (univ : Set Vec)) = 0
    rw [Measure.prod_prod,measure_singleton,zero_mul]
  have he : (F.flow · t) ⁻¹' ({x} ×ˢ univ) = {z : Phase | (F.flow z t).1=x} := by
    ext z
    simp
  rw [← he]
  exact (F.measurePreserving ht).preimage_null hz

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

lemma PhaseFlowOn.collision_image {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T) (z : Phase) :
    collisionLabels F.flow z T = collisionChart F.flow z '' (Ioo 0 T ×ˢ (univ : Set Vec)) := by
  ext y
  constructor
  · rintro ⟨t,ht,hy⟩
    refine ⟨(t,(F.flow y t).2),⟨ht,mem_univ _⟩,?_⟩
    change inversePhase F.flow (t,((F.flow z t).1,(F.flow y t).2)) = y
    rw [← hy,Prod.mk.eta,F.inversePhase_flow (Ioo_subset_Icc_self ht)]
  · rintro ⟨⟨t,v⟩,ht,rfl⟩
    refine ⟨t,ht.1,?_⟩
    change (F.flow (inversePhase F.flow (t,(F.flow z t).1,v)) t).1=(F.flow z t).1
    rw [F.flow_inversePhase (Ioo_subset_Icc_self ht.1)]

lemma PhaseFlowOn.collisionChart_strict {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (z : Phase) {p : ℝ × Vec} (hp : p.1 ∈ Ioo 0 T) :
    ∃ D : (ℝ × Vec) →L[ℝ] Phase, HasStrictFDerivAt (collisionChart F.flow z) D p := by
  have htime : HasStrictFDerivAt (fun p : ℝ × Vec => (p.1,z))
      ((ContinuousLinearMap.fst ℝ ℝ Vec).prod (0 : (ℝ × Vec) →L[ℝ] Phase)) p :=
    hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_const _ _)
  have hX := ((F.joint z p.1 hp).comp p htime).fst
  have hmap := hasStrictFDerivAt_fst.prodMk (hX.prodMk hasStrictFDerivAt_snd)
  obtain ⟨D,_,hD⟩ := F.inverse_differential hp ((F.flow z p.1).1,p.2)
  have hh := hD.comp p hmap
  exact ⟨_,hh⟩

lemma dimH_strict_image_le {A C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [SecondCountableTopology A] [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : A → C} {s : Set A} (hf : ∀ x ∈ s, ∃ D : A →L[ℝ] C, HasStrictFDerivAt f D x) :
    dimH (f '' s) ≤ dimH s := by
  apply dimH_image_le_of_locally_lipschitzOn
  intro x hx
  obtain ⟨D,hD⟩ := hf x hx
  obtain ⟨K,t,ht,hK⟩ := hD.exists_lipschitzOnWith
  exact ⟨K,t,mem_nhdsWithin_of_mem_nhds ht,hK⟩

lemma PhaseFlowOn.collision_null {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T) (z : Phase) :
    volume (collisionLabels F.flow z T) = 0 := by
  have hdim : dimH (collisionLabels F.flow z T) ≤ 4 := by
    rw [F.collision_image z]
    calc
      _ ≤ dimH (Ioo 0 T ×ˢ (univ : Set Vec)) :=
        dimH_strict_image_le (fun p hp => F.collisionChart_strict z hp.1)
      _ ≤ dimH (univ : Set (ℝ × Vec)) := dimH_mono (subset_univ _)
      _ = 4 := by rw [Real.dimH_univ_eq_finrank]; simp [Vec,Module.finrank_prod]
  have hrank : Module.finrank ℝ Phase = 6 := by simp [Phase,Vec,Module.finrank_prod]
  have hc : (volume : Measure Phase) ≪ Measure.hausdorffMeasure (6 : ℝ) := by
    have hh := Measure.absolutelyContinuous_isAddHaarMeasure (volume : Measure Phase)
      (Measure.hausdorffMeasure (Module.finrank ℝ Phase : ℝ))
    simpa only [hrank,Nat.cast_ofNat] using hh
  apply measure_zero_of_dimH_lt (d := (6 : ℝ≥0)) hc
  exact hdim.trans_lt (by norm_num)

lemma PhaseFlowOn.closed_collision_null {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) :
    volume {y : Phase | ∃ t ∈ Icc 0 T, (F.flow y t).1=(F.flow z t).1}=0 := by
  apply measure_mono_null (t := collisionLabels F.flow z T ∪
    {y : Phase | (F.flow y 0).1=(F.flow z 0).1} ∪
    {y : Phase | (F.flow y T).1=(F.flow z T).1})
  · rintro y ⟨t,ht,hy⟩
    rcases eq_or_lt_of_le ht.1 with he | hl
    · exact Or.inl (Or.inr (he.symm ▸ hy))
    rcases eq_or_lt_of_le ht.2 with he | hr
    · exact Or.inr (he ▸ hy)
    · exact Or.inl (Or.inl ⟨t,⟨hl,hr⟩,hy⟩)
  · exact measure_union_null (measure_union_null (F.collision_null z)
      (F.tip_null ⟨le_rfl,hT⟩ (F.flow z 0).1))
      (F.tip_null ⟨hT,le_rfl⟩ (F.flow z T).1)

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

lemma PhaseFlowOn.branchRate_pos {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) : 0 < branchRate F.flow zX zY T s := by
  have hn := F.branchDirection_norm zX zY hs hne
  have hpos (v : Vec) : 0 < 1-dot (branchDirection F.flow zX zY T s) (velocity v) := by
    have hd := dot_le_norm (branchDirection F.flow zX zY T s) (velocity v)
    rw [hn,one_mul] at hd
    linarith [norm_velocity_lt_one v]
  exact div_pos (hpos _) (hpos _)

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

lemma PhaseFlowOn.exists_emission {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (x : Vec) {z : Phase} (hz : z ∈ initialConeLabels t x) :
    ∃! s : ℝ, s ∈ Icc 0 t ∧ s+‖x-(F.flow z s).1‖=t := by
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hc : ContinuousOn (fun s => s+‖x-(F.flow z s).1‖) (Icc 0 t) :=
    continuousOn_id.add ((continuousOn_const.sub ((F.continuousOn_time z).mono hsub).fst).norm)
  have hzero : 0+‖x-(F.flow z 0).1‖ < t := by simpa only [F.initial,zero_add,initialConeLabels,mem_ofPred_eq] using hz
  have hend : t ≤ t+‖x-(F.flow z t).1‖ := le_add_of_nonneg_right (norm_nonneg _)
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc ht.1 hc ⟨hzero.le,hend⟩
  refine ⟨s,⟨hs,he⟩,?_⟩
  intro r hr
  apply (F.emission_strictMono (ht.1.trans ht.2) z x).injOn (hsub hr.1) (hsub hs)
  exact hr.2.trans he.symm

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SignedRemainder
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
open scoped Topology ContDiff

namespace RVM

lemma intervalIntegral_vec_apply {g : ℝ → Vec} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (i : Fin 3) :
    (∫ t in a..b, g t) i = ∫ t in a..b, g t i := by
  exact ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).intervalIntegral_comp_comm hg).symm

lemma continuousOn_signedRemainder {r : ℝ → ℝ} {a u n aₜ : ℝ → Vec} {S : Set ℝ}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S)
    (hu : ContinuousOn u S) (hn : ContinuousOn n S) (haₜ : ContinuousOn aₜ S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContinuousOn (fun s => signedRemainder (r s) (a s) (u s) (n s) (aₜ s)) S := by
  have hDa : ContinuousOn (fun s => 1-dot (n s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner ha)
  have hea : ContinuousOn (fun s => 1-dot (a s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (ha.inner hu)
  have haa : ContinuousOn (fun s => 1-dot (a s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (ha.inner ha)
  have hp : ContinuousOn (fun s => signedPrimitive (a s) (u s) (n s)) S :=
    hu.sub ((hea.div hDa hD).smul hn)
  have hatp : ContinuousOn (fun s => dot (aₜ s) (signedPrimitive (a s) (u s) (n s))) S := by
    simpa only [dot_eq_inner] using haₜ.inner hp
  exact ((hea.div ((hr.pow 2).mul (hDa.pow 2))
    (fun s hs => mul_ne_zero (pow_ne_zero _ (hr0 s hs)) (pow_ne_zero _ (hD s hs)))).smul
      (((haa.div hDa hD).smul hn).sub ha)).add
    ((hatp.div (hr.mul (hDa.pow 2))
      (fun s hs => mul_ne_zero (hr0 s hs) (pow_ne_zero _ (hD s hs)))).smul hn)

lemma continuousOn_signedForceKernel {r : ℝ → ℝ} {a u n u' : ℝ → Vec} {S : Set ℝ}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S)
    (hu : ContinuousOn u S) (hn : ContinuousOn n S) (hu' : ContinuousOn u' S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hd : ∀ s ∈ S, 1-dot (n s) (u s) ≠ 0)
    (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContinuousOn (fun s => signedForceKernel (r s) (a s) (u s) (n s) (u' s)) S := by
  have hdu : ContinuousOn (fun s => 1-dot (n s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner hu)
  have hDa : ContinuousOn (fun s => 1-dot (n s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner ha)
  have huu : ContinuousOn (fun s => 1-dot (u s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hu.inner hu)
  have hnu' : ContinuousOn (fun s => dot (n s) (u' s)) S := by
    simpa only [dot_eq_inner] using hn.inner hu'
  have hv : ContinuousOn (fun s => sourceVelocityRate (u s) (n s) (u' s)) S :=
    ((hdu.inv₀ hd).smul hu').add
      ((hnu'.div (hdu.pow 2) (fun s hs => pow_ne_zero _ (hd s hs))).smul (hu.sub hn))
  have hc {w : ℝ → Vec} (hw : ContinuousOn w S) :
      ContinuousOn (fun s => coneTransform (a s) (n s) (w s)) S := by
    have haw : ContinuousOn (fun s => dot (a s) (w s)) S := by
      simpa only [dot_eq_inner] using ha.inner hw
    exact hw.add ((haw.div hDa hD).smul hn)
  exact (((hr.inv₀ hr0).smul (hc hv)).neg).sub
    ((huu.div ((hr.pow 2).mul hdu)
      (fun s hs => mul_ne_zero (pow_ne_zero _ (hr0 s hs)) (hd s hs))).smul
        (hc ((hdu.inv₀ hd).smul (hu.sub hn))))

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

lemma PhaseFlowOn.velocity_hasDerivAt {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) (ht : t∈Ioo 0 T) :
    HasDerivAt (fun r => velocity (F.flow z r).2) (phaseAcceleration E B F.flow z t) t := by
  have hd := ((F.ode z t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).snd
  exact ((contDiff_velocity (k:=1)).differentiable one_ne_zero (F.flow z t).2).hasFDerivAt.comp_hasDerivAt t hd

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

lemma dyadicCut_zero {x : ℝ} (hx : 2≤x) : dyadicCut x=0 := by
  rw [dyadicCut,Real.smoothTransition.one_of_one_le (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]

lemma dyadicFactor_zero_large {x : ℝ} {n : ℕ} (hn : 2≤(2:ℝ)^n*x) :
    dyadicFactor n x=0 := dyadicBump_zero_right hn

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

lemma PhaseFlowOn.branch_spec_closed {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s∈closedBranchDomain F.flow zX zY T) :
    branchTime F.flow zX zY T s∈Icc s T ∧
      branchTime F.flow zX zY T s-s=
        ‖(F.flow zX (branchTime F.flow zX zY T s)).1-(F.flow zY s).1‖ := by
  have hsub : Icc s T⊆Icc 0 T := fun _ ht=>⟨hs.1.1.trans ht.1,ht.2⟩
  have hc : ContinuousOn (fun t=>t-‖(F.flow zX t).1-(F.flow zY s).1‖) (Icc s T) :=
    continuousOn_id.sub ((((F.continuousOn_time zX).mono hsub).fst.sub continuousOn_const).norm)
  have hstart : s-‖(F.flow zX s).1-(F.flow zY s).1‖ ≤ s := sub_le_self _ (norm_nonneg _)
  have hend : s ≤ T-‖(F.flow zX T).1-(F.flow zY s).1‖ := by linarith [hs.2]
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hs.1.2 hc ⟨hstart,hend⟩
  have hex : ∃ t,t∈Icc s T ∧ t-s=‖(F.flow zX t).1-(F.flow zY s).1‖ :=
    ⟨t,ht,by linarith⟩
  simpa only [branchTime,dite_eq_left hex] using hex.choose_spec

lemma PhaseFlowOn.branch_unique_closed {E B : Field} {T s t : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s∈closedBranchDomain F.flow zX zY T)
    (ht : t∈Icc s T) (he : t-s=‖(F.flow zX t).1-(F.flow zY s).1‖) :
    t=branchTime F.flow zX zY T s := by
  obtain ⟨hτ,hcone⟩ := F.branch_spec_closed zX zY hs
  apply (F.arrival_strictMono (hs.1.1.trans hs.1.2) zX (F.flow zY s).1).injOn
    ⟨hs.1.1.trans ht.1,ht.2⟩ ⟨hs.1.1.trans hτ.1,hτ.2⟩
  dsimp only
  linarith

lemma PhaseFlowOn.closedBranchDomain_eq {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX zY : Phase) {b : ℝ} (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T) :
    closedBranchDomain F.flow zX zY T=Icc 0 b := by
  have hm := F.emission_strictMono hT zY (F.flow zX T).1
  ext s
  constructor
  · intro hs
    refine ⟨hs.1.1,?_⟩
    by_contra h
    have hh := hm hb hs.1 (lt_of_not_ge h)
    linarith [hs.2]
  · intro hs
    have ht : s∈Icc 0 T := ⟨hs.1,hs.2.trans hb.2⟩
    refine ⟨ht,?_⟩
    have hh := hm.monotoneOn ht hb hs.2
    linarith

lemma PhaseFlowOn.branchDomain_eq {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX zY : Phase) {b : ℝ} (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T) :
    branchDomain F.flow zX zY T=Ioo 0 b := by
  have hm := F.emission_strictMono hT zY (F.flow zX T).1
  ext s
  constructor
  · intro hs
    refine ⟨hs.1.1,?_⟩
    by_contra h
    have hh := hm.monotoneOn hb (Ioo_subset_Icc_self hs.1) (le_of_not_gt h)
    linarith [hs.2]
  · intro hs
    have ht : s∈Ioo 0 T := ⟨hs.1,hs.2.trans_le hb.2⟩
    refine ⟨ht,?_⟩
    have hh := hm (Ioo_subset_Icc_self ht) hb hs.2
    linarith

lemma PhaseFlowOn.branch_final_endpoint {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) {b : ℝ} (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T) :
    branchTime F.flow zX zY T b=T := by
  symm
  apply F.branch_unique_closed zX zY ⟨hb,he.le⟩ ⟨hb.2,le_rfl⟩
  linarith

lemma PhaseFlowOn.branch_lipschitzOn_closed {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX zY : Phase) :
    ∃ C : ℝ≥0,LipschitzOnWith C (branchTime F.flow zX zY T)
      (closedBranchDomain F.flow zX zY T) := by
  obtain ⟨c,hc,hX⟩ := F.timelike hT zX
  obtain ⟨d,hd,hY⟩ := F.timelike hT zY
  let C : ℝ≥0 := ⟨2/(1-(c:ℝ)),by positivity⟩
  refine ⟨C,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro s hs r hr
  let t := branchTime F.flow zX zY T s
  let τ := branchTime F.flow zX zY T r
  obtain ⟨ht,hst⟩ := F.branch_spec_closed zX zY hs
  obtain ⟨hτ,hrt⟩ := F.branch_spec_closed zX zY hr
  have ht0 : t∈Icc 0 T := ⟨hs.1.1.trans ht.1,ht.2⟩
  have hτ0 : τ∈Icc 0 T := ⟨hr.1.1.trans hτ.1,hτ.2⟩
  have hdx := hX.dist_le_mul t ht0 τ hτ0
  have hdy := hY.dist_le_mul s hs.1 r hr.1
  have hy : dist (F.flow zY s).1 (F.flow zY r).1 ≤ dist s r :=
    hdy.trans (mul_le_of_le_one_left dist_nonneg hd.le)
  have heq : t-τ=(s-r)+(‖(F.flow zX t).1-(F.flow zY s).1‖-
      ‖(F.flow zX τ).1-(F.flow zY r).1‖) := by
    change t-s=_ at hst
    change τ-r=_ at hrt
    linarith
  have hn := abs_norm_sub_norm_le ((F.flow zX t).1-(F.flow zY s).1)
    ((F.flow zX τ).1-(F.flow zY r).1)
  have htriangle : ‖((F.flow zX t).1-(F.flow zY s).1)-
      ((F.flow zX τ).1-(F.flow zY r).1)‖ ≤
      dist (F.flow zX t).1 (F.flow zX τ).1+dist (F.flow zY s).1 (F.flow zY r).1 := by
    rw [dist_eq_norm,dist_eq_norm]
    calc
      _ = ‖((F.flow zX t).1-(F.flow zX τ).1)-((F.flow zY s).1-(F.flow zY r).1)‖ := by congr 1; abel
      _  ≤  _ := norm_sub_le _ _
  have hg : dist t τ ≤ dist s r+(c:ℝ)*dist t τ+dist s r := by
    have hab := abs_add_le (s-r)
      (‖(F.flow zX t).1-(F.flow zY s).1‖-‖(F.flow zX τ).1-(F.flow zY r).1‖)
    rw [← heq,← Real.dist_eq,← Real.dist_eq] at hab
    linarith [hn.trans htriangle]
  change dist t τ ≤ (2/(1-(c:ℝ)))*dist s r
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  nlinarith

lemma PhaseFlowOn.branch_radius_pos_closed {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈closedBranchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    0 < branchTime F.flow zX zY T σ-σ := by
  obtain ⟨ht,he⟩ := F.branch_spec_closed zX zY hσ
  apply sub_pos.mpr
  by_contra h
  have hh : branchTime F.flow zX zY T σ=σ := le_antisymm (le_of_not_gt h) ht.1
  rw [hh,sub_self] at he
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp he.symm))

lemma PhaseFlowOn.branchDirection_norm_closed {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈closedBranchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    ‖branchDirection F.flow zX zY T σ‖=1 := by
  have hp := F.branch_radius_pos_closed zX zY hσ hne
  have he := (F.branch_spec_closed zX zY hσ).2
  dsimp only [branchDirection]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),← he]
  exact inv_mul_cancel₀ hp.ne'

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

lemma continuousOn_retardedPrimitive {r : ℝ → ℝ} {a u n : ℝ → Vec} {S : Set ℝ}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S)
    (hu : ContinuousOn u S) (hn : ContinuousOn n S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hd : ∀ s ∈ S, 1-dot (n s) (u s) ≠ 0)
    (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContinuousOn (fun s => retardedPrimitive (r s) (a s) (u s) (n s)) S := by
  have hdu : ContinuousOn (fun s => 1-dot (n s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner hu)
  have hDa : ContinuousOn (fun s => 1-dot (n s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner ha)
  have hea : ContinuousOn (fun s => 1-dot (a s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (ha.inner hu)
  exact ((hr.mul hdu).inv₀ (fun s hs => mul_ne_zero (hr0 s hs) (hd s hs))).smul
    (hu.sub ((hea.div hDa hD).smul hn))

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

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_AbsolutelyContinuousIntervalContinuousDerivative
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
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma absolutelyContinuousOnInterval_of_continuous_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g g' : ℝ → V} {a b : ℝ} (hab : a<b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t∈Ioo a b,HasDerivAt g (g' t) t) :
    AbsolutelyContinuousOnInterval g a b := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'
  let M : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hLip : LipschitzOnWith M g (Ioo a b) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun t ht=>(hd t ht).differentiableAt) _ (convex_Ioo a b)
    intro t ht
    rw [(hd t ht).deriv]
    exact_mod_cast (hC t (Ioo_subset_Icc_self ht)).trans (le_max_left C 0)
  have hc : ContinuousOn g (closure (Ioo a b)) := by simpa only [closure_Ioo hab.ne] using hg
  have hLc := LipschitzOnWith.closure hc hLip
  rw [closure_Ioo hab.ne,← uIcc_of_le hab.le] at hLc
  exact hLc.absolutelyContinuousOnInterval

lemma ac_weighted_vector_ibp_closed {ψ : ℝ → ℝ} {g g' : ℝ → Vec} {a b : ℝ}
    (hab : a≤b) (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t∈Ioo a b,HasDerivAt g (g' t) t) :
    ∫ t in a..b, ψ t • g' t =
      ψ b • g b - ψ a • g a - ∫ t in a..b, deriv ψ t • g t := by
  rcases hab.eq_or_lt with rfl|hab
  · simp
  have hgu : ContinuousOn g (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hg
  have hg'u : ContinuousOn g' (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hg'
  have h₁ : IntervalIntegrable (fun t=>ψ t • g' t) volume a b :=
    (hψ.continuousOn.smul hg'u).intervalIntegrable
  have h₂ : IntervalIntegrable (fun t=>deriv ψ t • g t) volume a b :=
    hψ.intervalIntegrable_deriv.smul_continuousOn hgu
  ext i
  rw [intervalIntegral_vec_apply h₁,PiLp.sub_apply,PiLp.sub_apply,
    PiLp.smul_apply,PiLp.smul_apply,intervalIntegral_vec_apply h₂]
  simp only [PiLp.smul_apply,smul_eq_mul]
  have hdi : ∀ t∈Ioo a b,HasDerivAt (fun r=>g r i) (g' t i) t := fun t ht=>
    (PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hgi : AbsolutelyContinuousOnInterval (fun t=>g t i) a b :=
    absolutelyContinuousOnInterval_of_continuous_derivative hab
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).continuous.comp_continuousOn hg)
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).continuous.comp_continuousOn hg') hdi
  have he : (∫ t in a..b,ψ t*g' t i)=∫ t in a..b,ψ t*deriv (fun r=>g r i) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have hti : t∈Ioo a b := by simpa only [uIoo_of_le hab.le] using ht
    exact congrArg (fun x=>ψ t*x) (hdi t hti).deriv.symm
  rw [he]
  exact hψ.integral_mul_deriv_eq_deriv_mul hgi

lemma ac_weighted_signed_ibp_closed {ψ : ℝ → ℝ} {P K R : ℝ → Vec}
    {W W' : ℝ → Vec →L[ℝ] Vec} {a b : ℝ} (hab : a≤b)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hP : ContinuousOn P (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hW' : ContinuousOn W' (Icc a b))
    (hK : ContinuousOn K (Icc a b)) (hR : ContinuousOn R (Icc a b))
    (hPd : ∀ t∈Ioo a b,HasDerivAt P (-K t+R t) t)
    (hWd : ∀ t∈Ioo a b,HasDerivAt W (W' t) t) :
    ∫ t in a..b,ψ t • W t (K t) =
      ψ a • W a (P a)-ψ b • W b (P b)+
      ∫ t in a..b,deriv ψ t • W t (P t)+ψ t • (W' t (P t)+W t (R t)) := by
  have hg : ContinuousOn (fun t=>W t (P t)) (Icc a b) := hW.clm_apply hP
  have hg' : ContinuousOn (fun t=>W' t (P t)+W t (-K t+R t)) (Icc a b) :=
    (hW'.clm_apply hP).add (hW.clm_apply (hK.neg.add hR))
  have h := ac_weighted_vector_ibp_closed hab hψ hg hg'
    (fun t ht=>(hWd t ht).clm_apply (hPd t ht))
  have hI₁ : IntervalIntegrable (fun t=>ψ t • W t (K t)) volume a b :=
    (hψ.continuousOn.smul (by simpa only [uIcc_of_le hab] using hW.clm_apply hK)).intervalIntegrable
  have hI₂ : IntervalIntegrable (fun t=>ψ t • (W' t (P t)+W t (R t))) volume a b :=
    (hψ.continuousOn.smul (by simpa only [uIcc_of_le hab] using (show ContinuousOn (fun t=>W' t (P t)+W t (R t)) (Icc a b) from (hW'.clm_apply hP).add (hW.clm_apply hR)))).intervalIntegrable
  have hI₃ : IntervalIntegrable (fun t=>deriv ψ t • W t (P t)) volume a b :=
    hψ.intervalIntegrable_deriv.smul_continuousOn (by simpa only [uIcc_of_le hab] using hg)
  have he : (fun t=>ψ t • (W' t (P t)+W t (-K t+R t))) =
      (fun t=>ψ t • (W' t (P t)+W t (R t))-ψ t • W t (K t)) := by
    funext t
    simp only [map_add,map_neg,smul_add,smul_neg]
    abel
  rw [he,intervalIntegral.integral_sub hI₂ hI₁] at h
  rw [intervalIntegral.integral_add hI₃ hI₂]
  have hh := congrArg (fun v=>(∫ t in a..b,ψ t • (W' t (P t)+W t (R t)))-v) h
  convert hh using 1 <;> abel

lemma PhaseFlowOn.actual_weighted_signed_identity_closed {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    {ψ : ℝ→ℝ} {W W' : ℝ→Vec→L[ℝ]Vec}
    (hψ : AbsolutelyContinuousOnInterval ψ 0 b)
    (hW : ContinuousOn W (Icc 0 b)) (hW' : ContinuousOn W' (Icc 0 b))
    (hWd : ∀ σ∈Ioo 0 b,HasDerivAt W (W' σ) σ) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,ψ σ • W σ
      (signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)) =
      ψ 0 • W 0 (retardedPrimitive (r 0) (a 0) (u 0) (n 0))-
      ψ b • W b (retardedPrimitive (r b) (a b) (u b) (n b))+
      ∫ σ in 0..b,deriv ψ σ • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
        ψ σ • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  let τ := branchTime F.flow zX zY T
  let r := fun σ=>τ σ-σ
  let a := fun σ=>velocity (F.flow zX (τ σ)).2
  let u := fun σ=>velocity (F.flow zY σ).2
  let n := branchDirection F.flow zX zY T
  let P := fun σ=>retardedPrimitive (r σ) (a σ) (u σ) (n σ)
  let K := fun σ=>signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)
  let R := fun σ=>signedRemainder (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zX (τ σ))
  have hT : 0≤T := hb.1.trans hb.2
  have hsub : Icc 0 b⊆Icc 0 T := fun _ hx=>⟨hx.1,hx.2.trans hb.2⟩
  have hclosed := F.closedBranchDomain_eq hT zX zY hb he
  have hopen := F.branchDomain_eq hT zX zY hb he
  have hmem : ∀ σ∈Icc 0 b,σ∈closedBranchDomain F.flow zX zY T := by
    intro σ hσ
    rwa [hclosed]
  have htmem : ∀ σ∈Icc 0 b,τ σ∈Icc 0 T := fun σ hσ=>
    ⟨hσ.1.trans (F.branch_spec_closed zX zY (hmem σ hσ)).1.1,
      (F.branch_spec_closed zX zY (hmem σ hσ)).1.2⟩
  have hτ : ContinuousOn τ (Icc 0 b) := by
    obtain ⟨C,hC⟩ := F.branch_lipschitzOn_closed hT zX zY
    simpa only [hclosed] using hC.continuousOn
  have hr : ContinuousOn r (Icc 0 b) := hτ.sub continuousOn_id
  have hX := (F.continuousOn_time zX).comp hτ htmem
  have hY := (F.continuousOn_time zY).mono hsub
  have ha : ContinuousOn a (Icc 0 b) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hX.snd
  have hu : ContinuousOn u (Icc 0 b) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hY.snd
  have hr0 : ∀ σ∈Icc 0 b,r σ≠0 := fun σ hσ=>
    (F.branch_radius_pos_closed zX zY (hmem σ hσ) (hne σ (hsub hσ))).ne'
  have hn : ContinuousOn n (Icc 0 b) := (hr.inv₀ hr0).smul (hX.fst.sub hY.fst)
  have hnorm : ∀ σ∈Icc 0 b,‖n σ‖=1 := fun σ hσ=>
    F.branchDirection_norm_closed zX zY (hmem σ hσ) (hne σ (hsub hσ))
  have hd : ∀ σ∈Icc 0 b,1-dot (n σ) (u σ)≠0 := fun σ hσ=>
    (cone_denom_pos (F.flow zY σ).2 _ (hnorm σ hσ)).ne'
  have hD : ∀ σ∈Icc 0 b,1-dot (n σ) (a σ)≠0 := fun σ hσ=>
    (cone_denom_pos (F.flow zX (τ σ)).2 _ (hnorm σ hσ)).ne'
  have hP : ContinuousOn P (Icc 0 b) := continuousOn_retardedPrimitive hr ha hu hn hr0 hd hD
  have hK : ContinuousOn K (Icc 0 b) := continuousOn_signedForceKernel hr ha hu hn
    ((F.acceleration_continuousOn_closed hs zY).mono hsub) hr0 hd hD
  have hR : ContinuousOn R (Icc 0 b) := continuousOn_signedRemainder hr ha hu hn
    ((F.acceleration_continuousOn_closed hs zX).comp hτ htmem) hr0 hD
  have hder : ∀ σ∈Ioo 0 b,HasDerivAt P (R σ-K σ) σ := by
    intro σ hσ
    have hσ' : σ∈branchDomain F.flow zX zY T := by rwa [hopen]
    have hneσ := hne σ (hsub (Ioo_subset_Icc_self hσ))
    have ht := F.branch_time_mem zX zY hσ' hneσ
    have hτ' := (F.branch_differential zX zY hσ' hneσ).2
    have hr' : HasDerivAt r ((1-dot (n σ) (u σ))/(1-dot (n σ) (a σ))-1) σ :=
      hτ'.sub (hasDerivAt_id σ)
    have ha' : HasDerivAt a
        (((1-dot (n σ) (u σ))/(1-dot (n σ) (a σ))) • phaseAcceleration s.E s.B F.flow zX (τ σ)) σ :=
      (F.velocity_hasDerivAt zX ⟨hσ'.1.1.trans ht.1,ht.2⟩).scomp σ hτ'
    have hσc := Ioo_subset_Icc_self hσ
    have hp := hasDerivAt_retardedPrimitive hr' ha' (F.velocity_hasDerivAt zY hσ'.1)
      (F.branchDirection_hasDerivAt zX zY hσ' hneσ) (hr0 σ hσc) (hd σ hσc) (hD σ hσc)
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    have hh := signed_force_identity (r σ) (a σ) (u σ) (n σ)
      (phaseAcceleration s.E s.B F.flow zY σ) (phaseAcceleration s.E s.B F.flow zX (τ σ))
      (hr0 σ hσc) (hd σ hσc) (hD σ hσc)
    dsimp only [R,K]
    rw [hh]
    unfold signedRemainder
    abel
  apply ac_weighted_signed_ibp_closed hb.1 hψ hP hW hW' hK hR _ hWd
  intro σ hσ
  simpa only [sub_eq_neg_add] using hder σ hσ

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedRadiusSeparatedClosed
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

lemma PhaseFlowOn.branch_weight_ac {E B : Field} {T b : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    {ψ : ℝ→ℝ} {L : ℝ≥0} (hψ : LipschitzOnWith L ψ (Icc 0 T)) :
    AbsolutelyContinuousOnInterval (fun σ=>ψ (branchTime F.flow zX zY T σ)) 0 b := by
  have hT : 0≤T := hb.1.trans hb.2
  have hclosed := F.closedBranchDomain_eq hT zX zY hb he
  obtain ⟨C,hC⟩ := F.branch_lipschitzOn_closed hT zX zY
  have hm : MapsTo (branchTime F.flow zX zY T) (closedBranchDomain F.flow zX zY T) (Icc 0 T) := by
    intro σ hσ
    have ht := (F.branch_spec_closed zX zY hσ).1
    exact ⟨hσ.1.1.trans ht.1,ht.2⟩
  have h := hψ.comp hC hm
  rw [hclosed,← uIcc_of_le hb.1] at h
  exact h.absolutelyContinuousOnInterval

lemma PhaseFlowOn.actual_temporal_signed_identity_closed {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    {ψ : ℝ→ℝ} {L : ℝ≥0} (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : ContinuousOn W (Icc 0 b)) (hW' : ContinuousOn W' (Icc 0 b))
    (hWd : ∀ σ∈Ioo 0 b,HasDerivAt W (W' σ) σ) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,ψ (τ σ) • W σ
      (signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)) =
      ψ (τ 0) • W 0 (retardedPrimitive (r 0) (a 0) (u 0) (n 0))+
      ∫ σ in 0..b,deriv (fun σ=>ψ (τ σ)) σ • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
        ψ (τ σ) • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  have h := F.actual_weighted_signed_identity_closed hs zX zY hb he hne
    (F.branch_weight_ac zX zY hb he hψ) hW hW' hWd
  dsimp only at h ⊢
  simpa only [F.branch_final_endpoint zX zY hb he,hψT,zero_smul,sub_zero] using h
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
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma deriv_comp_of_nonzero_strict {f ψ : ℝ→ℝ} {x c : ℝ}
    (hf : HasStrictDerivAt f c x) (hc : c≠0) :
    deriv (fun r=>ψ (f r)) x=deriv ψ (f x)*c := by
  by_cases hψ : DifferentiableAt ℝ ψ (f x)
  · exact (hψ.hasDerivAt.comp x hf.hasDerivAt).deriv
  · have hnot : ¬DifferentiableAt ℝ (ψ ∘ f) x := by
      intro h
      let g := hf.localInverse f c x hc
      have hg : HasStrictDerivAt g c⁻¹ (f x) := hf.to_localInverse hc
      have hleft : g (f x)=x := (hf.eventually_left_inverse hc).self_of_nhds
      have hh : DifferentiableAt ℝ (ψ ∘ f) (g (f x)) := hleft.symm ▸ h
      have hi := hh.comp (f x) hg.hasDerivAt.differentiableAt
      apply hψ
      apply hi.congr_of_eventuallyEq
      filter_upwards [hf.eventually_right_inverse hc] with y hy
      exact congrArg ψ hy.symm
    rw [show (fun r=>ψ (f r))=ψ ∘ f from rfl,deriv_zero_of_not_differentiableAt hnot,
      deriv_zero_of_not_differentiableAt hψ,zero_mul]

lemma PhaseFlowOn.branch_weight_deriv {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) (ψ : ℝ→ℝ) :
    deriv (fun r=>ψ (branchTime F.flow zX zY T r)) σ=
      deriv ψ (branchTime F.flow zX zY T σ)*branchRate F.flow zX zY T σ := by
  obtain ⟨hc,hd⟩ := F.branch_differential zX zY hσ hne
  have hs : HasStrictDerivAt (branchTime F.flow zX zY T)
      (branchRate F.flow zX zY T σ) σ := hc.hasStrictDerivAt' hd (by norm_num)
  exact deriv_comp_of_nonzero_strict hs (F.branchRate_pos zX zY hσ hne).ne'

lemma PhaseFlowOn.branch_weight_deriv_integral {E B : Field} {T b : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    (ψ : ℝ→ℝ) (G H : ℝ→Vec) :
    (∫ σ in 0..b,deriv (fun r=>ψ (branchTime F.flow zX zY T r)) σ • G σ+H σ)=
      ∫ σ in 0..b,(deriv ψ (branchTime F.flow zX zY T σ)*branchRate F.flow zX zY T σ) • G σ+H σ := by
  apply intervalIntegral.integral_congr_uIoo
  intro σ hσ
  have hσo : σ∈Ioo 0 b := by simpa only [uIoo_of_le hb.1] using hσ
  have hdom : σ∈branchDomain F.flow zX zY T := by
    rwa [F.branchDomain_eq (hb.1.trans hb.2) zX zY hb he]
  dsimp only
  rw [F.branch_weight_deriv zX zY hdom (hne σ ⟨hσo.1.le,hσo.2.le.trans hb.2⟩) ψ]

lemma PhaseFlowOn.actual_temporal_signed_formula {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    {ψ : ℝ→ℝ} {L : ℝ≥0} (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : ContinuousOn W (Icc 0 b)) (hW' : ContinuousOn W' (Icc 0 b))
    (hWd : ∀ σ∈Ioo 0 b,HasDerivAt W (W' σ) σ) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,ψ (τ σ) • W σ
      (signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)) =
      ψ (τ 0) • W 0 (retardedPrimitive (r 0) (a 0) (u 0) (n 0))+
      ∫ σ in 0..b,(deriv ψ (τ σ)*branchRate F.flow zX zY T σ) • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
        ψ (τ σ) • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  have h := F.actual_temporal_signed_identity_closed hs zX zY hb he hne hψ hψT hW hW' hWd
  dsimp only at h ⊢
  rw [F.branch_weight_deriv_integral zX zY hb he hne ψ] at h
  exact h

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

lemma stateCutoff_closed_regularity {T a b : ℝ} (Q : Set (Fin 4→ℕ))
    {z z' : ℝ→CutoffState} (hz : ContinuousOn z (Icc a b))
    (hz' : ContinuousOn z' (Icc a b))
    (hr : ∀ t∈Icc a b,0<(z t).1) (hn : ∀ t∈Icc a b,‖(z t).2.1‖=1)
    (hd : ∀ t∈Ioo a b,HasDerivAt z (z' t) t) :
    ContinuousOn (fun t=>stateCutoff T Q (z t)) (Icc a b) ∧
    ContinuousOn (fun t=>fderiv ℝ (stateCutoff T Q) (z t) (z' t)) (Icc a b) ∧
    ∀ t∈Ioo a b,HasDerivAt (fun t=>stateCutoff T Q (z t))
      (fderiv ℝ (stateCutoff T Q) (z t) (z' t)) t := by
  have hsc t (ht : t∈Icc a b) := contDiffAt_stateCutoff T Q (hr t ht) (hn t ht)
  refine ⟨fun t ht => (hsc t ht).continuousAt.comp_continuousWithinAt (hz t ht),?_,?_⟩
  · apply ContinuousOn.clm_apply _ hz'
    intro t ht
    exact ((hsc t ht).continuousAt_fderiv (by simp)).comp_continuousWithinAt (hz t ht)
  · intro t ht
    exact ((hsc t (Ioo_subset_Icc_self ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hd t ht)

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

lemma PhaseFlowOn.branchCutoffState_closed_regularity {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1) :
    ContinuousOn (branchCutoffState F.flow T zX zY) (Icc 0 b) ∧
    ContinuousOn (branchCutoffStateRate s.E s.B F.flow T zX zY) (Icc 0 b) ∧
    (∀ σ∈Icc 0 b,0<(branchCutoffState F.flow T zX zY σ).1) ∧
    (∀ σ∈Icc 0 b,‖(branchCutoffState F.flow T zX zY σ).2.1‖=1) := by
  let τ := branchTime F.flow zX zY T
  let r := fun σ=>τ σ-σ
  let a := fun σ=>velocity (F.flow zX (τ σ)).2
  let u := fun σ=>velocity (F.flow zY σ).2
  let n := branchDirection F.flow zX zY T
  have hT : 0≤T := hb.1.trans hb.2
  have hsub : Icc 0 b⊆Icc 0 T := fun _ hx=>⟨hx.1,hx.2.trans hb.2⟩
  have hclosed := F.closedBranchDomain_eq hT zX zY hb he
  have hmem : ∀ σ∈Icc 0 b,σ∈closedBranchDomain F.flow zX zY T := by
    intro σ hσ
    rwa [hclosed]
  have htmem : ∀ σ∈Icc 0 b,τ σ∈Icc 0 T := fun σ hσ=>
    ⟨hσ.1.trans (F.branch_spec_closed zX zY (hmem σ hσ)).1.1,
      (F.branch_spec_closed zX zY (hmem σ hσ)).1.2⟩
  have hτ : ContinuousOn τ (Icc 0 b) := by
    obtain ⟨C,hC⟩ := F.branch_lipschitzOn_closed hT zX zY
    simpa only [hclosed] using hC.continuousOn
  have hr : ContinuousOn r (Icc 0 b) := hτ.sub continuousOn_id
  have hX := (F.continuousOn_time zX).comp hτ htmem
  have hY := (F.continuousOn_time zY).mono hsub
  have ha : ContinuousOn a (Icc 0 b) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hX.snd
  have hu : ContinuousOn u (Icc 0 b) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hY.snd
  have hrp : ∀ σ∈Icc 0 b,0 < r σ := fun σ hσ=>
    F.branch_radius_pos_closed zX zY (hmem σ hσ) (hne σ (hsub hσ))
  have hn : ContinuousOn n (Icc 0 b) := (hr.inv₀ (fun σ hσ=>(hrp σ hσ).ne')).smul (hX.fst.sub hY.fst)
  have hnorm : ∀ σ∈Icc 0 b,‖n σ‖=1 := fun σ hσ=>
    F.branchDirection_norm_closed zX zY (hmem σ hσ) (hne σ (hsub hσ))
  have hd : ContinuousOn (fun σ=>1-dot (n σ) (u σ)) (Icc 0 b) := by
    simp only [dot_eq_inner]
    exact (continuousOn_const (c:=(1:ℝ))).sub (hn.inner hu)
  have hD : ContinuousOn (fun σ=>1-dot (n σ) (a σ)) (Icc 0 b) := by
    simp only [dot_eq_inner]
    exact (continuousOn_const (c:=(1:ℝ))).sub (hn.inner ha)
  have hρ : ContinuousOn (branchRate F.flow zX zY T) (Icc 0 b) :=
    hd.div hD (fun σ hσ=>(cone_denom_pos _ _ (hnorm σ hσ)).ne')
  have hN : ContinuousOn (fun σ=>(r σ)⁻¹ • coneMotion (a σ) (u σ) (n σ)) (Icc 0 b) :=
    (hr.inv₀ (fun σ hσ=>(hrp σ hσ).ne')).smul
      (((hρ.smul (ha.sub hn)).add hn).sub hu)
  have hKY := (F.momentumForce_continuousOn_closed hs zY).mono hsub
  have hKX := (F.momentumForce_continuousOn_closed hs zX).comp hτ htmem
  exact ⟨hr.prodMk (hn.prodMk (hY.snd.prodMk hX.snd)),
    (hρ.sub continuousOn_const).prodMk (hN.prodMk (hKY.prodMk (hρ.smul hKX))),hrp,hnorm⟩

lemma PhaseFlowOn.actual_selected_closed_regularity {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1) (Q : Set (Fin 4→ℕ)) :
    let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY σ)
    let χ' := branchSelectedRate s.E s.B F.flow T zX zY Q
    ContinuousOn χ (Icc 0 b) ∧ ContinuousOn χ' (Icc 0 b) ∧
      ∀ σ∈Ioo 0 b,HasDerivAt χ (χ' σ) σ := by
  obtain ⟨hz,hz',hr,hn⟩ := F.branchCutoffState_closed_regularity hs zX zY hb he hne
  apply stateCutoff_closed_regularity Q hz hz' hr hn
  intro σ hσ
  have hdom : σ∈branchDomain F.flow zX zY T := by
    rwa [F.branchDomain_eq (hb.1.trans hb.2) zX zY hb he]
  exact F.branchCutoffState_hasDerivAt zX zY hdom (hne σ ⟨hσ.1.le,hσ.2.le.trans hb.2⟩)

lemma PhaseFlowOn.actual_selected_temporal_signed_formula {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : ContinuousOn W (Icc 0 b)) (hW' : ContinuousOn W' (Icc 0 b))
    (hWd : ∀ σ∈Ioo 0 b,HasDerivAt W (W' σ) σ) :
    let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY σ)
    let χ' := branchSelectedRate s.E s.B F.flow T zX zY Q
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,(ψ (τ σ)*χ σ) • W σ
      (signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)) =
      (ψ (τ 0)*χ 0) • W 0 (retardedPrimitive (r 0) (a 0) (u 0) (n 0))+
      ∫ σ in 0..b,(deriv ψ (τ σ)*branchRate F.flow zX zY T σ*χ σ+ψ (τ σ)*χ' σ) •
        W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
        (ψ (τ σ)*χ σ) • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  obtain ⟨hχ,hχ',hχd⟩ := F.actual_selected_closed_regularity hs zX zY hb he hne Q
  have h := F.actual_temporal_signed_formula hs zX zY hb he hne hψ hψT
    (hχ.smul hW) ((hχ.smul hW').add (hχ'.smul hW))
    (fun σ hσ=>(hχd σ hσ).smul (hWd σ hσ))
  dsimp only at h ⊢
  simp only [Pi.smul_apply',Pi.add_apply,smul_apply,smul_smul,add_apply,smul_add,add_smul] at h ⊢
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply intervalIntegral.integral_congr
  intro σ hσ
  abel_nf

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

lemma PhaseFlowOn.labelReceiverTime_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) : Measurable (labelReceiverTime F.flow zX T) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuousOn_const (F.isOpen_jointBranchDomain zX).measurableSet
  intro p hp
  exact (F.joint_branch_continuousAt zX hp).continuousWithinAt

lemma PhaseFlowOn.labelReceiverTime_mem {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) (p : ℝ×Phase) :
    labelReceiverTime F.flow zX T p∈Icc 0 T := by
  classical
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · rw [labelReceiverTime,indicator_of_mem hp]
    have ht := F.branch_time_mem zX p.2 hp.1 hp.2
    exact ⟨(hp.1.1.1.trans ht.1).le,ht.2.le⟩
  · simp only [labelReceiverTime,indicator_of_notMem hp,mem_Icc,le_refl,hT,and_self]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_InitialPuncturedCone
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

lemma PhaseFlowOn.branchDomain_empty_of_not_initial {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX z : Phase)
    (hz : z∉initialConeLabels T (F.flow zX T).1) :
    branchDomain F.flow zX z T=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  have ht : T≤‖(F.flow zX T).1-z.1‖ := le_of_not_gt hz
  have hh := F.emission_strictMono hT z (F.flow zX T).1 ⟨le_rfl,hT⟩
    (Ioo_subset_Icc_self hσ.1) hσ.1.1
  simp only [F.initial,zero_add] at hh
  linarith [hσ.2]

lemma integrable_bounded_clm_apply {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : α→Vec→L[ℝ]Vec} {f : α→Vec} {C : ℝ}
    (hf : Integrable f μ) (hG : AEStronglyMeasurable G μ)
    (hb : ∀ᵐ x∂μ,‖G x‖≤C) : Integrable (fun x=>G x (f x)) μ := by
  apply (hf.norm.const_mul C).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hG.prodMk hf.aestronglyMeasurable))
  filter_upwards [hb] with x hx
  exact (G x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

lemma PhaseFlowOn.integrable_receiver_multiplier {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase)
    {G : ℝ→Vec→L[ℝ]Vec} (hG : Continuous G) {f : ℝ×Phase→Vec} (hf : Integrable f) :
    Integrable (fun p=>G (labelReceiverTime F.flow zX T p) (f p)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  exact integrable_bounded_clm_apply hf
    (hG.measurable.comp (F.labelReceiverTime_measurable zX)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p=>hC _ (F.labelReceiverTime_mem hT zX p)))

lemma PhaseFlowOn.receiver_multiplier_closed_regularity {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX z : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow z b).1‖=T)
    (hne : ∀σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow z σ).1)
    {G G' : ℝ→Vec→L[ℝ]Vec} (hG : ContinuousOn G (Icc 0 T))
    (hG' : ContinuousOn G' (Icc 0 T)) (hGd : ∀t∈Ioo 0 T,HasDerivAt G (G' t) t) :
    let τ := branchTime F.flow zX z T
    ContinuousOn (fun σ=>G (τ σ)) (Icc 0 b) ∧
    ContinuousOn (fun σ=>branchRate F.flow zX z T σ • G' (τ σ)) (Icc 0 b) ∧
    ∀σ∈Ioo 0 b,HasDerivAt (fun σ=>G (τ σ))
      (branchRate F.flow zX z T σ • G' (τ σ)) σ := by
  dsimp only
  have hT : 0≤T := hb.1.trans hb.2
  have hclosed := F.closedBranchDomain_eq hT zX z hb he
  have hmem : ∀σ∈Icc 0 b,σ∈closedBranchDomain F.flow zX z T := fun σ hσ=>by
    rwa [hclosed]
  have ht : ∀σ∈Icc 0 b,branchTime F.flow zX z T σ∈Icc 0 T := fun σ hσ=>
    ⟨hσ.1.trans (F.branch_spec_closed zX z (hmem σ hσ)).1.1,
      (F.branch_spec_closed zX z (hmem σ hσ)).1.2⟩
  obtain ⟨C,hC⟩ := F.branch_lipschitzOn_closed hT zX z
  have hτ : ContinuousOn (branchTime F.flow zX z T) (Icc 0 b) := by
    simpa only [hclosed] using hC.continuousOn
  have hr := (F.branchCutoffState_closed_regularity hs zX z hb he hne).2.1.fst.add (continuousOn_const (c:=(1:ℝ)))
  have hrate : ContinuousOn (branchRate F.flow zX z T) (Icc 0 b) := by
    convert hr using 1
    all_goals try with_reducible_and_instances rfl
    ext σ
    simp only [Pi.add_apply,branchCutoffStateRate,sub_add_cancel]
  refine ⟨hG.comp hτ ht,hrate.smul (hG'.comp hτ ht),?_⟩
  intro σ hσ
  have hdom : σ∈branchDomain F.flow zX z T := by rwa [F.branchDomain_eq hT zX z hb he]
  have hsT : σ∈Icc 0 T := ⟨hσ.1.le,hσ.2.le.trans hb.2⟩
  have hti := F.branch_time_mem zX z hdom (hne σ hsT)
  exact (hGd _ ⟨hσ.1.trans hti.1,hti.2⟩).scomp σ (F.branch_differential zX z hdom (hne σ hsT)).2

lemma PhaseFlowOn.selected_multiplier_branch_formula {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX z : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow z b).1‖=T)
    (hne : ∀σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow z σ).1)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal}
    (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T))
    (hW' : ContinuousOn W' (Icc 0 T)) (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫σ : ℝ,selectedMultiplierForce s F.flow zX T Q ψ W (σ,z)) =
      (s.f (0,z)*ψ (branchTime F.flow zX z T 0)*
        selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX z 0)) •
      W (branchTime F.flow zX z T 0) (retardedPrimitive (branchTime F.flow zX z T 0) (velocity (F.flow zX (branchTime F.flow zX z T 0)).2)
        (velocity z.2) (branchDirection F.flow zX z T 0))+
        ∫σ : ℝ,selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z) := by
  classical
  have hT : 0≤T := hb.1.trans hb.2
  let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX z σ)
  let τ := branchTime F.flow zX z T
  let P := fun σ=>retardedPrimitive (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
  let K := fun σ=>signedForceKernel (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
    (phaseAcceleration s.E s.B F.flow z σ)
  let R := fun σ=>signedRemainder (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
    (phaseAcceleration s.E s.B F.flow zX (τ σ))
  let G := fun σ=>(ψ (τ σ)*χ σ) • W (τ σ) (K σ)
  let H := fun σ=>(deriv ψ (τ σ)*branchRate F.flow zX z T σ*χ σ+
      ψ (τ σ)*branchSelectedRate s.E s.B F.flow T zX z Q σ) • W (τ σ) (P σ) +
      (ψ (τ σ)*χ σ) • ((branchRate F.flow zX z T σ • W' (τ σ)) (P σ)+W (τ σ) (R σ))
  have hd : ∀σ,(σ,z)∈labelBranchDomain F.flow zX T ↔ σ∈Ioo 0 b := by
    intro σ
    change (σ∈branchDomain F.flow zX z T ∧ _) ↔ _
    rw [F.branchDomain_eq hT zX z hb he]
    constructor
    · exact And.left
    · intro hσ
      exact ⟨hσ,hne σ ⟨hσ.1.le,hσ.2.le.trans hb.2⟩⟩
  have hK : (fun σ=>selectedMultiplierForce s F.flow zX T Q ψ W (σ,z))=
      (Ioo (0:ℝ) b).indicator (fun σ=>s.f (0,z) • G σ) := by
    funext σ
    by_cases hσ : σ∈Ioo (0:ℝ) b
    · have hp := (hd σ).mpr hσ
      have hp' : (σ,z)∈jointBranchDomain F.flow zX T := hp
      simp only [selectedMultiplierForce,selectedLabelSignedForce,labelWeight,labelReceiverTime,labelSelectedCutoff,
        actualLabelSignedForce,indicator_of_mem hp,indicator_of_mem hp',indicator_of_mem hσ,
        G,K,τ,χ,sourceAcceleration,phaseAcceleration,smul_smul,map_smul]
      congr 1
      ring
    · have hp := mt (hd σ).mp hσ
      simp only [selectedMultiplierForce,selectedLabelSignedForce,actualLabelSignedForce,indicator_of_notMem hp,
        indicator_of_notMem hσ,smul_zero,map_zero]
  have hH : (fun σ=>selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z))=
      (Ioo (0:ℝ) b).indicator (fun σ=>s.f (0,z) • H σ) := by
    funext σ
    by_cases hσ : σ∈Ioo (0:ℝ) b
    · have hp := (hd σ).mpr hσ
      have hp' : (σ,z)∈jointBranchDomain F.flow zX T := hp
      simp only [selectedMultiplierCosts,selectedLabelCosts,labelWeight,labelReceiverTime,labelSelectedCutoff,
        actualLabelRatePrimitive,actualLabelCutoffCost,actualLabelPrimitive,actualLabelRemainder,
        indicator_of_mem hp,indicator_of_mem hp',indicator_of_mem hσ,H,P,R,τ,χ,
        smul_smul,smul_add,add_smul,map_smul,map_add,smul_apply]
      module
    · have hp := mt (hd σ).mp hσ
      simp only [selectedMultiplierCosts,selectedLabelCosts,actualLabelRatePrimitive,actualLabelCutoffCost,
        actualLabelPrimitive,actualLabelRemainder,indicator_of_notMem hp,
        indicator_of_notMem hσ,smul_zero,add_zero,map_zero]
  have hI : (∫σ in 0..b,G σ)=(ψ (τ 0)*χ 0) • W (τ 0) (P 0)+∫σ in 0..b,H σ := by
    obtain ⟨hA,hA',hAd⟩ := F.receiver_multiplier_closed_regularity hs zX z hb he hne hW hW' hWd
    exact F.actual_selected_temporal_signed_formula hs zX z hb he hne Q hψ hψT hA hA' hAd
  rw [hK,hH,integral_indicator measurableSet_Ioo,integral_indicator measurableSet_Ioo,
    integral_smul,integral_smul,restrict_Ioo_eq_restrict_Ioc,
    ←intervalIntegral.integral_of_le hb.1,←intervalIntegral.integral_of_le hb.1,hI,smul_add]
  congr 1
  simp only [P,τ,χ,sub_zero,F.initial,smul_smul]
  congr 1
  ring

lemma PhaseFlowOn.ae_selected_multiplier_formula {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal}
    (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T))
    (hW' : ContinuousOn W' (Icc 0 T)) (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    ∀ᵐ z : Phase,(∫σ : ℝ,selectedMultiplierForce s F.flow zX T Q ψ W (σ,z)) =
      selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z+
        ∫σ : ℝ,selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z) := by
  classical
  have hn : ∀ᵐ z ∂(volume : Measure Phase),
      z∉{y : Phase | ∃t∈Icc 0 T,(F.flow y t).1=(F.flow zX t).1} :=
    ae_iff.mpr (by simpa only [mem_ofPred_eq,not_not] using F.closed_collision_null hT zX)
  filter_upwards [hn] with z hz
  have hne : ∀t∈Icc 0 T,(F.flow zX t).1≠(F.flow z t).1 := fun t ht he=>hz ⟨t,ht,he.symm⟩
  by_cases hy : z∈initialConeLabels T (F.flow zX T).1
  · obtain ⟨b,⟨hb,he⟩,_⟩ := F.exists_emission ⟨hT,le_rfl⟩ (F.flow zX T).1 hy
    have hp : z∈initialPuncturedCone F.flow zX T := ⟨hy,by
      have hn0 := hne 0 ⟨le_rfl,hT⟩
      change (F.flow zX 0).1 ≠ (F.flow z 0).1 at hn0
      simpa only [F.initial,mem_ofPred_eq,ne_eq,eq_comm] using hn0⟩
    rw [F.selected_multiplier_branch_formula hs zX z hb he hne Q hψ hψT hW hW' hWd]
    congr 1
    simp only [selectedInitialKernel,indicator_of_mem hp,
      actualCutoffCoordinates,sub_zero,F.initial,stateCutoff,initialConeState]
  · have hd := F.branchDomain_empty_of_not_initial hT zX z hy
    have hp : z∉initialPuncturedCone F.flow zX T := fun hz=>hy hz.1
    have he : ∀σ,(σ,z)∉labelBranchDomain F.flow zX T := fun σ hh=>by
      have hh' := hh.1
      rw [hd] at hh'
      exact hh'
    have hK : (fun σ=>selectedMultiplierForce s F.flow zX T Q ψ W (σ,z))=0 := by
      funext σ
      simp only [selectedMultiplierForce,selectedLabelSignedForce,actualLabelSignedForce,indicator_of_notMem (he σ),
        smul_zero,Pi.zero_apply,map_zero]
    have hC : (fun σ=>selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z))=0 := by
      funext σ
      simp only [selectedMultiplierCosts,selectedLabelCosts,actualLabelCutoffCost,actualLabelRatePrimitive,
        actualLabelPrimitive,actualLabelRemainder,indicator_of_notMem (he σ),
        smul_zero,add_zero,Pi.zero_apply,map_zero]
    simp only [hK,hC,selectedInitialKernel,indicator_of_notMem hp]
    simp

lemma PhaseFlowOn.selected_multiplier_fubini {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : Continuous W) (hW' : Continuous W')
    (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫σ : ℝ,∫z : Phase,selectedMultiplierForce s F.flow zX T Q ψ W (σ,z)) =
      (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z)+
      ∫σ : ℝ,∫z : Phase,selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z) := by
  obtain ⟨hiK,hiC⟩ := F.selectedMultiplier_integrable hs hT zX Q hψ hψb hW hW'
  have hfc : Continuous (fun z=>s.f (0,z)) := hs.f_smooth.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _=>⟨⟨le_rfl,hT⟩,mem_univ _⟩)
  obtain ⟨K,hK,hcompact⟩ := hs.compact
  have hfs : HasCompactSupport (fun z=>s.f (0,z)) := hK.of_isClosed_subset (isClosed_tsupport _)
    (hcompact 0 ⟨le_rfl,hT⟩)
  obtain ⟨C,_,hb⟩ := selectedInitialKernel_integrable_bound hfc hfs (hs.nonnegative 0 ⟨le_rfl,hT⟩)
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hW.continuousOn
  have hiB := (hb s.E s.B T F zX Q ψ W (max M 0) hT (le_max_right _ _)
    hψ.continuous.continuousOn hW.continuousOn (fun t ht=>(hM t ht).trans (le_max_left _ _))).1
  have hKi : Integrable (Function.uncurry (fun σ z=>selectedMultiplierForce s F.flow zX T Q ψ W (σ,z)))
      (volume.prod volume) := hiK
  have hCi : Integrable (Function.uncurry (fun σ z=>selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z)))
      (volume.prod volume) := hiC
  rw [integral_integral_swap hKi]
  rw [integral_congr_ae (F.ae_selected_multiplier_formula hs hT zX Q hψ.lipschitzOnWith hψT
      hW.continuousOn hW'.continuousOn hWd),
    integral_add hiB hiC.integral_prod_right,←integral_integral_swap hCi]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceForceConeKernel
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

private lemma SmoothClassicalPrefix.sourceForceEnergyPrefix
    {datum : Datum} {solution : Solution} {horizon : ℝ}
    (hs : SmoothClassicalPrefix datum solution horizon) : EnergyPrefix solution horizon := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro time ht position momentum
    have hh := (hs.equations time ht.1.le ht.2).1 position momentum
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro time ht position
    have he := (hs.equations time ht.1.le ht.2).2.1 position
    have hb := (hs.equations time ht.1.le ht.2).2.2.1 position
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

lemma split_label_force (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) :
    ψ (labelReceiverTime α zX T p) • actualLabelSignedForce s α zX T p=
      unselectedLabelSignedForce s α zX T Q ψ p+selectedLabelSignedForce s α zX T Q ψ p := by
  rw [unselectedLabelSignedForce,selectedLabelSignedForce,labelWeight,mul_smul,
    smul_comm (ψ (labelReceiverTime α zX T p)),←add_smul]
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

lemma PhaseFlowOn.split_multiplier_force_integral {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : Continuous W) (hW' : Continuous W')
    (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫p,W (labelReceiverTime F.flow zX T p)
      (ψ (labelReceiverTime F.flow zX T p) • actualLabelSignedForce s F.flow zX T p))=
      (∫p,W (labelReceiverTime F.flow zX T p) (unselectedLabelSignedForce s F.flow zX T Q ψ p))+
      (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z)+
      ∫p,selectedMultiplierCosts s F.flow zX T Q ψ W W' p := by
  have hiU := F.integrable_receiver_multiplier hT zX hW
    (F.unselectedLabelSignedForce_integrable hs hT zX Q hψ.continuous.measurable hψb)
  obtain ⟨hiK,hiC⟩ := F.selectedMultiplier_integrable hs hT zX Q hψ hψb hW hW'
  simp_rw [split_label_force s F.flow zX T Q ψ,map_add]
  change Integrable (fun p=>W (labelReceiverTime F.flow zX T p)
    (selectedLabelSignedForce s F.flow zX T Q ψ p)) at hiK
  rw [integral_add hiU hiK]
  change _+(∫p,selectedMultiplierForce s F.flow zX T Q ψ W p)=_
  rw [show (∫p,selectedMultiplierForce s F.flow zX T Q ψ W p)=
      ∫σ : ℝ,∫z : Phase,selectedMultiplierForce s F.flow zX T Q ψ W (σ,z) from
        integral_prod _ hiK,
    F.selected_multiplier_fubini hs hT zX Q hψ hψb hψT hW hW' hWd,
    ←integral_prod _ hiC,add_assoc]
  rw [←Measure.volume_eq_prod]

lemma SmoothClassicalPrefix.selected_multiplier_decomposition_oai {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : Continuous W) (hW' : Continuous W')
    (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫t in Ioo (0:ℝ) T,ψ t • W t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
      (4*Real.pi)⁻¹ • ((∫p,W (labelReceiverTime F.flow zX T p)
        (unselectedLabelSignedForce s F.flow zX T Q ψ p))+
        (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z)+
        ∫p,selectedMultiplierCosts s F.flow zX T Q ψ W W' p) := by
  have he := hs.multiplier_retarded_force_label hT F zX
    (W:=fun t=>ψ t • W t) (hψ.continuous.smul hW).continuousOn
  change (∫t in Ioo (0:ℝ) T,ψ t • W t
    (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
      boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
    (4*Real.pi)⁻¹ • ∫p,ψ (labelReceiverTime F.flow zX T p) •
      W (labelReceiverTime F.flow zX T p) (actualLabelSignedForce s F.flow zX T p) at he
  rw [he]
  congr 1
  simp_rw [←map_smul]
  exact F.split_multiplier_force_integral hs.sourceForceEnergyPrefix hT zX Q hψ hψb hψT hW hW' hWd

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition_oai := @OAI.RVM.SmoothClassicalPrefix.selected_multiplier_decomposition_oai
