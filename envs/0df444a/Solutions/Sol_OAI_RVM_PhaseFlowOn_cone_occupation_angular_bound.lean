-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:49:59.605222+00:00
-- url     : https://prove2.me/submissions/b82ec38a-bb2d-4852-88ee-bbd5b67829cd

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

lemma determinant_retarded_graph {D : E →L[ℝ] E} (hD : D.det = 1) (v : E) (ℓ : E →L[ℝ] ℝ) :
    (D.comp ((ContinuousLinearMap.id ℝ E) - (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ)).det =
      1 - ℓ v := by
  have he : (((ContinuousLinearMap.id ℝ E) - (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ) : E →L[ℝ] E).toLinearMap =
      LinearMap.transvection ℓ.toLinearMap (-v) := by
    ext x
    simp [LinearMap.transvection,sub_eq_add_neg]
  change LinearMap.det (D.toLinearMap.comp _) = _
  rw [LinearMap.det_comp,he]
  change D.det * _ = _
  rw [hD,one_mul,LinearMap.transvection.det,map_neg]
  rfl

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

lemma isOpen_receiverRadialDomain (s T : ℝ) : IsOpen (receiverRadialDomain s T) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt (continuous_const.add continuous_norm) continuous_const)

lemma receiver_time_mem {s T : ℝ} (hs : 0 ≤ s) {w : Vec}
    (hw : w ∈ receiverRadialDomain s T) : s+‖w‖ ∈ Ioo 0 T := by
  constructor <;> linarith [hw.1,hw.2]

lemma PhaseFlowOn.receiver_injective {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) :
    InjOn (receiverRadial F.flow z s) (receiverRadialDomain s T) := by
  intro a ha b hb hab
  have hta := Ioo_subset_Icc_self (receiver_time_mem hs.1 ha)
  have htb := Ioo_subset_Icc_self (receiver_time_mem hs.1 hb)
  let y := receiverRadial F.flow z s a
  have hya : (F.flow z (s+‖a‖)).1-y=a := by dsimp [y,receiverRadial]; abel
  have hyb : (F.flow z (s+‖b‖)).1-y=b := by
    change (F.flow z (s+‖b‖)).1-receiverRadial F.flow z s a=b
    rw [hab]
    unfold receiverRadial
    abel
  have he : s+‖a‖=s+‖b‖ := by
    apply (F.arrival_strictMono (hs.1.trans hs.2) z y).injOn hta htb
    dsimp only
    rw [hya,hyb]
    ring
  rw [← hya,← hyb,he]

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

lemma PhaseFlowOn.receiver_image {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) :
    receiverRadial F.flow z s '' receiverRadialDomain s T =
      ball (F.flow z T).1 (T-s) \ {(F.flow z s).1} := by
  ext y
  constructor
  · rintro ⟨w,hw,rfl⟩
    let t := s+‖w‖
    let y := receiverRadial F.flow z s w
    have ht : t ∈ Ioo 0 T := receiver_time_mem hs.1 hw
    have hst : s < t := by dsimp [t]; linarith [hw.1]
    have he : t-‖(F.flow z t).1-y‖=s := by
      have hh : (F.flow z t).1-y=w := by dsimp [y,receiverRadial,t]; abel
      rw [hh]
      dsimp [t]
      ring
    have hm := F.arrival_strictMono (hs.1.trans hs.2) z y
    constructor
    · have hh := hm (Ioo_subset_Icc_self ht) ⟨hs.1.trans hs.2,le_rfl⟩ ht.2
      dsimp only at hh
      rw [he] at hh
      rw [mem_ball,dist_eq_norm,norm_sub_rev]
      linarith
    · intro hh
      change y=(F.flow z s).1 at hh
      have hh' := hm hs (Ioo_subset_Icc_self ht) hst
      dsimp only at hh'
      rw [he,hh,sub_self,norm_zero,sub_zero] at hh'
      exact (lt_irrefl s) hh'
  · rintro ⟨hy,hn⟩
    have hy' : ‖(F.flow z T).1-y‖ < T-s := by
      simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hy
    obtain ⟨t,⟨ht,he⟩,_⟩ := F.exists_arrival hs z hy'
    have hst : s < t := by
      by_contra h
      have ht' : t=s := le_antisymm (le_of_not_gt h) ht.1
      rw [ht'] at he
      have hh : ‖(F.flow z s).1-y‖=0 := by linarith
      exact hn (sub_eq_zero.mp (norm_eq_zero.mp hh)).symm
    have htT : t < T := by
      by_contra h
      have ht' : t=T := le_antisymm ht.2 (le_of_not_gt h)
      rw [ht'] at he
      linarith
    let w := (F.flow z t).1-y
    have hw : s+‖w‖=t := by dsimp [w]; linarith
    refine ⟨w,⟨?_,?_⟩,?_⟩
    · dsimp [w]; linarith
    · rw [hw]; exact htT
    · unfold receiverRadial
      rw [hw]
      dsimp [w]
      abel

lemma PhaseFlowOn.receiver_differential {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : 0 ≤ s) (z : Phase) {w : Vec} (hw : w ∈ receiverRadialDomain s T) :
    HasFDerivAt (receiverRadial F.flow z s)
      ((ContinuousLinearMap.toSpanSingleton ℝ (velocity (F.flow z (s+‖w‖)).2)).comp
        (innerSL ℝ (‖w‖⁻¹ • w)) - ContinuousLinearMap.id ℝ Vec) w := by
  have ht := receiver_time_mem hs hw
  have hX := ((F.ode z _ (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).fst
  change HasDerivAt (fun t => (F.flow z t).1) (velocity (F.flow z (s+‖w‖)).2) (s+‖w‖) at hX
  have hn := (hasStrictFDerivAt_norm_nonzero (norm_ne_zero_iff.mp (ne_of_gt hw.1))).hasFDerivAt
  convert! (hX.hasFDerivAt.comp w (hn.const_add s)).sub (hasFDerivAt_id w) using 1
  all_goals try with_reducible_and_instances rfl

lemma PhaseFlowOn.receiver_jacobian {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : 0 ≤ s) (z : Phase) {w : Vec} (hw : w ∈ receiverRadialDomain s T) :
    |(fderiv ℝ (receiverRadial F.flow z s) w).det| =
      1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2) := by
  rw [(F.receiver_differential hs z hw).fderiv]
  let v := velocity (F.flow z (s+‖w‖)).2
  let ℓ := innerSL ℝ (‖w‖⁻¹ • w)
  have hd := determinant_retarded_graph
    (D := ContinuousLinearMap.id ℝ Vec) (by exact LinearMap.det_id) v ℓ
  simp only [ContinuousLinearMap.id_comp] at hd
  have he : (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ - ContinuousLinearMap.id ℝ Vec =
      -((ContinuousLinearMap.id ℝ Vec) - (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ) := by abel
  have hneg (A : Vec →L[ℝ] Vec) : |(-A).det|=|A.det| := by
    change |LinearMap.det (-A.toLinearMap)|=|LinearMap.det A.toLinearMap|
    rw [← neg_one_smul ℝ A.toLinearMap,LinearMap.det_smul,abs_mul,abs_pow]
    norm_num
  change |((ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ - ContinuousLinearMap.id ℝ Vec).det| = _
  rw [he,hneg,hd]
  change |1 - inner ℝ (‖w‖⁻¹ • w) v| = _
  rw [← dot_eq_inner,abs_of_pos]
  apply cone_denom_pos
  simpa only [sub_zero] using norm_coneDirection (x := w) (y := 0)
    (norm_ne_zero_iff.mp (ne_of_gt hw.1))

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

lemma PhaseFlowOn.branch_strictMono {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) : StrictMonoOn (branchTime F.flow zX zY T) (branchDomain F.flow zX zY T) := by
  intro a ha b hb hab
  obtain ⟨hta,hea⟩ := F.branch_spec zX zY ha
  obtain ⟨htb,heb⟩ := F.branch_spec zX zY hb
  have hT : 0 ≤ T := ha.1.1.le.trans ha.1.2.le
  have he := F.emission_strictMono hT zY (F.flow zX (branchTime F.flow zX zY T a)).1
    (Ioo_subset_Icc_self ha.1) (Ioo_subset_Icc_self hb.1) hab
  have hat : branchTime F.flow zX zY T a ∈ Icc 0 T := ⟨ha.1.1.le.trans hta.1,hta.2⟩
  have hbt : branchTime F.flow zX zY T b ∈ Icc 0 T := ⟨hb.1.1.le.trans htb.1,htb.2⟩
  have hg := F.arrival_strictMono hT zX (F.flow zY b).1
  apply (hg.lt_iff_lt hat hbt).mp
  dsimp only at he ⊢
  linarith

lemma PhaseFlowOn.branch_volume_image {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) {H : Set ℝ} (hH : MeasurableSet H)
    (hsub : H ⊆ branchDomain F.flow zX zY T)
    (hne : ∀ s ∈ H, (F.flow zX s).1 ≠ (F.flow zY s).1) :
    (∫⁻ s in H, ENNReal.ofReal (branchRate F.flow zX zY T s)) =
      volume (branchTime F.flow zX zY T '' H) := by
  apply lintegral_deriv_eq_volume_image_of_monotoneOn hH
  · intro s hs
    exact (F.branch_differential zX zY (hsub hs) (hne s hs)).2.hasDerivWithinAt
  · exact (F.branch_strictMono zX zY).monotoneOn.mono hsub

lemma PhaseFlowOn.branch_duration_bound {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) {H : Set ℝ} (hH : MeasurableSet H)
    (hsub : H ⊆ branchDomain F.flow zX zY T)
    (hne : ∀ s ∈ H, (F.flow zX s).1 ≠ (F.flow zY s).1)
    {c a b : ℝ} (hder : ∀ s ∈ H, c ≤ branchRate F.flow zX zY T s)
    (himage : branchTime F.flow zX zY T '' H ⊆ Icc a b) :
    ENNReal.ofReal c * volume H ≤ ENNReal.ofReal (b-a) := by
  calc
    _ = ∫⁻ _s in H, ENNReal.ofReal c := by simp
    _ ≤ ∫⁻ s in H, ENNReal.ofReal (branchRate F.flow zX zY T s) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hH] with s hs
      exact ENNReal.ofReal_le_ofReal (hder s hs)
    _ = volume (branchTime F.flow zX zY T '' H) := F.branch_volume_image zX zY hH hsub hne
    _ ≤ volume (Icc a b) := measure_mono himage
    _ = _ := Real.volume_Icc

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

lemma PhaseFlowOn.branchRate_lower_bound {E B : Field} {T s δ Δ : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) (hδ : 0 ≤ δ) (hΔ : 0 < Δ)
    (hsource : δ ≤ 1-dot (branchDirection F.flow zX zY T s) (velocity (F.flow zY s).2))
    (hreceiver : 1-dot (branchDirection F.flow zX zY T s)
      (velocity (F.flow zX (branchTime F.flow zX zY T s)).2) ≤ Δ) :
    δ/Δ ≤ branchRate F.flow zX zY T s := by
  have hn := F.branchDirection_norm zX zY hs hne
  have hD : 0 < 1-dot (branchDirection F.flow zX zY T s)
      (velocity (F.flow zX (branchTime F.flow zX zY T s)).2) := by
    have hd := dot_le_norm (branchDirection F.flow zX zY T s)
      (velocity (F.flow zX (branchTime F.flow zX zY T s)).2)
    rw [hn,one_mul] at hd
    linarith [norm_velocity_lt_one (F.flow zX (branchTime F.flow zX zY T s)).2]
  apply (div_le_div_iff₀ hΔ hD).mpr
  change δ * (1-dot (branchDirection F.flow zX zY T s)
    (velocity (F.flow zX (branchTime F.flow zX zY T s)).2)) ≤
    (1-dot (branchDirection F.flow zX zY T s) (velocity (F.flow zY s).2))*Δ
  nlinarith

lemma PhaseFlowOn.label_occupation_angular_bound {E B : Field} {T δ Δ a b : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (f₀ : Phase → ℝ) {H : Phase → Set ℝ}
    (hδ : 0 ≤ δ) (hΔ : 0 < Δ) (hH : ∀ z, MeasurableSet (H z))
    (hsub : ∀ z, H z ⊆ branchDomain F.flow zX z T)
    (hsource : ∀ z s, s ∈ H z → δ ≤ 1-dot (branchDirection F.flow zX z T s) (velocity (F.flow z s).2))
    (hreceiver : ∀ z s, s ∈ H z → 1-dot (branchDirection F.flow zX z T s)
      (velocity (F.flow zX (branchTime F.flow zX z T s)).2) ≤ Δ)
    (himage : ∀ z, branchTime F.flow zX z T '' H z ⊆ Icc a b) :
    ENNReal.ofReal (δ/Δ) * labelOccupation f₀ H ≤
      ENNReal.ofReal (b-a) * ∫⁻ z, ENNReal.ofReal (f₀ z) := by
  have hnc : ∀ᵐ z ∂(volume : Measure Phase), z ∉ collisionLabels F.flow zX T :=
    (ae_iff.mpr (by simpa using F.collision_null zX))
  calc
    _ = ∫⁻ z, ENNReal.ofReal (δ/Δ) * (ENNReal.ofReal (f₀ z) * volume (H z)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ∫⁻ z, ENNReal.ofReal (b-a) * ENNReal.ofReal (f₀ z) := by
      apply lintegral_mono_ae
      filter_upwards [hnc] with z hz
      have hne : ∀ s ∈ H z, (F.flow zX s).1 ≠ (F.flow z s).1 := by
        intro s hs he
        exact hz ⟨s,(hsub z hs).1,he.symm⟩
      have hb := F.branch_duration_bound zX z (hH z) (hsub z) hne
        (fun s hs => F.branchRate_lower_bound zX z (hsub z hs) (hne s hs) hδ hΔ
          (hsource z s hs) (hreceiver z s hs)) (himage z)
      calc
        _ = ENNReal.ofReal (f₀ z) * (ENNReal.ofReal (δ/Δ) * volume (H z)) := by ac_rfl
        _ ≤ ENNReal.ofReal (f₀ z) * ENNReal.ofReal (b-a) := by gcongr
        _ = _ := mul_comm _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
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

lemma lintegral_radial_measure {f : ℝ → ENNReal} (hf : Measurable f) :
    (∫⁻ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^2) * f r := by
  have hpow : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1^2)) :=
    (measurable_subtype_coe.pow_const 2).ennreal_ofReal
  calc
    _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1^2) * f r.1 ∂volume.comap Subtype.val :=
      lintegral_withDensity_eq_lintegral_mul _ hpow (hf.comp measurable_subtype_coe)
    _ = _ := lintegral_subtype_comap (μ := volume) measurableSet_Ioi
      (fun r : ℝ => ENNReal.ofReal (r^2) * f r)

lemma lintegral_polar {f : Vec → ENNReal} (hf : Measurable f) :
    (∫⁻ y : Vec, f y) = ∫⁻ n : Sphere, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r^2) * f (r • n.1) ∂volume ∂sphereMeasure := by
  calc
    _ = ∫⁻ z : ({0}ᶜ : Set Vec), f z.1 ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl f,restrict_compl_singleton]
    _ = ∫⁻ p : Sphere × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂sphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
      simpa only [Homeomorph.symm_apply_apply,homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin,Nat.reduceSub] using h
    _ = ∫⁻ n : Sphere, ∫⁻ r : Ioi (0 : ℝ), f (r.1 • n.1) ∂Measure.volumeIoiPow 2
        ∂sphereMeasure := by
      apply lintegral_prod
      exact (hf.comp ((measurable_subtype_coe.comp measurable_snd).smul
        (measurable_subtype_coe.comp measurable_fst))).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro n
      exact lintegral_radial_measure (hf.comp (measurable_id.smul_const _))

lemma PhaseFlowOn.receiver_lintegral {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) (g : Vec → ENNReal) :
    ∫⁻ y in ball (F.flow z T).1 (T-s), g y =
      ∫⁻ w in receiverRadialDomain s T,
        ENNReal.ofReal (1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2)) *
          g (receiverRadial F.flow z s w) := by
  have hd : ∀ w ∈ receiverRadialDomain s T,
      HasFDerivWithinAt (receiverRadial F.flow z s)
        (fderiv ℝ (receiverRadial F.flow z s) w) (receiverRadialDomain s T) w := by
    intro w hw
    exact (F.receiver_differential hs.1 z hw).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  calc
    _ = ∫⁻ y in receiverRadial F.flow z s '' receiverRadialDomain s T, g y := by
      apply setLIntegral_congr
      rw [F.receiver_image hs z]
      exact (sdiff_null_ae_eq_self (measure_singleton (F.flow z s).1)).symm
    _ = ∫⁻ w in receiverRadialDomain s T,
        ENNReal.ofReal |(fderiv ℝ (receiverRadial F.flow z s) w).det| *
          g (receiverRadial F.flow z s w) :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (isOpen_receiverRadialDomain s T).measurableSet
        hd (F.receiver_injective hs z) g
    _ = _ := by
      apply setLIntegral_congr_fun (isOpen_receiverRadialDomain s T).measurableSet
      intro w hw
      dsimp only
      rw [F.receiver_jacobian hs.1 z hw]

lemma PhaseFlowOn.lintegral_comp {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (g : Phase → ENNReal) :
    ∫⁻ z, g (F.flow z t) = ∫⁻ z, g z := by
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (s := univ) MeasurableSet.univ
    (fun z _ => (F.label z t ht).hasFDerivWithinAt) (F.bijective t ht).1.injOn g
  simpa only [Set.image_univ,(F.bijective t ht).2.range_eq,setLIntegral_univ,
    F.det_one _ _ ht,abs_one,ENNReal.ofReal_one,one_mul] using hh.symm

lemma label_hit_tonelli {f₀ : Phase → ℝ} (hf₀ : Measurable f₀)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    (∫⁻ s : ℝ, ∫⁻ z : Phase, H.indicator
      (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2)) (s,z)) =
      ∫⁻ z : Phase, ENNReal.ofReal (f₀ z) * volume {s : ℝ | (s,z) ∈ H} := by
  have hm : Measurable (H.indicator (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2))) :=
    ((hf₀.comp measurable_snd).ennreal_ofReal).indicator hH
  rw [lintegral_lintegral_swap (f := fun s z => H.indicator
    (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2)) (s,z)) hm.aemeasurable]
  apply lintegral_congr
  intro z
  have hs : MeasurableSet {s : ℝ | (s,z) ∈ H} :=
    hH.preimage (measurable_id.prodMk measurable_const)
  calc
    _ = ∫⁻ s : ℝ, ENNReal.ofReal (f₀ z) * {s : ℝ | (s,z) ∈ H}.indicator 1 s := by
      apply lintegral_congr
      intro s
      by_cases h : (s,z) ∈ H <;> simp [Set.indicator,h]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator_one hs]

lemma PhaseFlowOn.transport_weight_lintegral {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) (g : Phase → ENNReal) :
    (∫⁻ z, ENNReal.ofReal (f (t,z)) * g z) =
      ∫⁻ z, ENNReal.ofReal (f (0,z)) * g (F.flow z t) := by
  rw [← F.lintegral_comp ht (fun z => ENNReal.ofReal (f (t,z)) * g z)]
  apply lintegral_congr
  intro z
  rw [F.transport hf heq ht]

lemma PhaseFlowOn.measurable_phaseHits {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    MeasurableSet (phaseHits F.flow T H) := by
  let α₀ := (Ioo 0 T ×ˢ (univ : Set Phase)).indicator (fun p : ℝ × Phase => F.flow p.2 p.1)
  have hm : Measurable (fun p : ℝ × Phase => (p.1,α₀ p)) :=
    measurable_fst.prodMk F.measurable_joint_flow_zero
  have he : phaseHits F.flow T H = (Ioo 0 T ×ˢ (univ : Set Phase)) ∩
      (fun p : ℝ × Phase => (p.1,α₀ p)) ⁻¹' H := by
    ext p
    by_cases hp : p.1 ∈ Ioo 0 T
    · simp only [phaseHits,mem_ofPred_eq,hp,true_and,mem_inter_iff,mem_prod,
        mem_univ,and_true,mem_preimage,α₀,Set.indicator_of_mem (show p ∈ Ioo 0 T ×ˢ (univ : Set Phase) from ⟨hp,mem_univ _⟩)]
    · simp only [phaseHits,mem_ofPred_eq,hp,false_and,mem_inter_iff,mem_prod,
        mem_univ,and_true]
  rw [he]
  exact (measurableSet_Ioo.prod MeasurableSet.univ).inter (hH.preimage hm)

lemma PhaseFlowOn.phase_occupation_identity {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    (∫⁻ t in Ioo 0 T, ∫⁻ z : Phase, H.indicator (fun p => ENNReal.ofReal (f p)) (t,z)) =
      labelOccupation (fun z => f (0,z)) (fun z => {t | (t,z) ∈ phaseHits F.flow T H}) := by
  have hf₀ : Measurable (fun z : Phase => f (0,z)) :=
    (hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨⟨le_rfl,hT⟩,mem_univ _⟩)).measurable
  have hfixed (t : ℝ) (ht : t ∈ Ioo 0 T) :
      (∫⁻ z : Phase, H.indicator (fun p => ENNReal.ofReal (f p)) (t,z)) =
        ∫⁻ z : Phase, (phaseHits F.flow T H).indicator
          (fun p : ℝ × Phase => ENNReal.ofReal (f (0,p.2))) (t,z) := by
    calc
      _ = ∫⁻ z : Phase, ENNReal.ofReal (f (t,z)) * H.indicator 1 (t,z) := by
        apply lintegral_congr
        intro z
        by_cases h : (t,z) ∈ H <;> simp [Set.indicator,h]
      _ = ∫⁻ z : Phase, ENNReal.ofReal (f (0,z)) * H.indicator 1 (t,F.flow z t) :=
        F.transport_weight_lintegral hf heq (Ioo_subset_Icc_self ht) _
      _ = _ := by
        apply lintegral_congr
        intro z
        by_cases h : (t,F.flow z t) ∈ H
        · rw [Set.indicator_of_mem h,Set.indicator_of_mem
              (show (t,z) ∈ phaseHits F.flow T H from ⟨ht,h⟩)]
          simp
        · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem
              (show (t,z) ∉ phaseHits F.flow T H from fun hh => h hh.2)]
          simp
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ z : Phase, (phaseHits F.flow T H).indicator
        (fun p : ℝ × Phase => ENNReal.ofReal (f (0,p.2))) (t,z) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Ioo 0 T
      · rw [Set.indicator_of_mem ht]
        exact hfixed t ht
      · rw [Set.indicator_of_notMem ht]
        symm
        calc
          _ = ∫⁻ _z : Phase, (0 : ENNReal) := by
            apply lintegral_congr
            intro z
            exact Set.indicator_of_notMem (fun h => ht h.1) _
          _ = _ := lintegral_zero
    _ = _ := label_hit_tonelli hf₀ (F.measurable_phaseHits hH)
end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SpaceConeDomain
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

lemma PhaseFlowOn.receiver_polar_lintegral {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) {g : Vec → ENNReal} (hg : Measurable g) :
    (∫⁻ y in ball (F.flow z T).1 (T-s), g y) =
      ∫⁻ n : Sphere, ∫⁻ r in Ioo (0 : ℝ) (T-s),
        ENNReal.ofReal (r^2*(1-dot n.1 (velocity (F.flow z (s+r)).2))) *
          g ((F.flow z (s+r)).1-r • n.1) ∂volume ∂sphereMeasure := by
  classical
  let S := receiverRadialDomain s T
  have hS : MeasurableSet S := (isOpen_receiverRadialDomain s T).measurableSet
  let Ψ : Vec → Phase := S.indicator (fun w => F.flow z (s+‖w‖))
  have hcΨ : ContinuousOn (fun w : Vec => F.flow z (s+‖w‖)) S := by
    intro w hw
    have ht : s+‖w‖ ∈ Ioo 0 T := ⟨by linarith [hw.1,hs.1],hw.2⟩
    have hc : ContinuousAt (fun v : Vec => (s+‖v‖,z)) w :=
      (continuousAt_const.add continuousAt_id.norm).prodMk continuousAt_const
    have hh := (F.joint z (s+‖w‖) ht).continuousAt.comp (f := fun v : Vec => (s+‖v‖,z)) hc
    exact hh.continuousWithinAt
  have hmΨ : Measurable Ψ := by
    have h := hcΨ.measurable_piecewise (continuousOn_const (c := (0 : Phase))) hS
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    by_cases hw : w ∈ S <;> simp [Ψ,Set.piecewise,hw]
  let R : Vec → Vec := S.indicator (receiverRadial F.flow z s)
  have hcR : ContinuousOn (receiverRadial F.flow z s) S :=
    fun w hw => (F.receiver_differential hs.1 z hw).continuousAt.continuousWithinAt
  have hmR : Measurable R := by
    have h := hcR.measurable_piecewise (continuousOn_const (c := (0 : Vec))) hS
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    by_cases hw : w ∈ S <;> simp [R,Set.piecewise,hw]
  have hmK : Measurable (fun w : Vec => ENNReal.ofReal
      (1-dot (‖w‖⁻¹ • w) (velocity (Ψ w).2)) * g (R w)) := by
    simp only [dot_eq_inner]
    exact ((measurable_const.sub
      ((measurable_id.norm.inv.smul measurable_id).inner
        ((contDiff_velocity (k := 1)).continuous.measurable.comp hmΨ.snd))).ennreal_ofReal).mul (hg.comp hmR)
  let H : Vec → ENNReal := S.indicator
    (fun w => ENNReal.ofReal (1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2)) *
      g (receiverRadial F.flow z s w))
  have hH : Measurable H := by
    convert hmK.indicator hS using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    by_cases hw : w ∈ S <;> simp [H,Ψ,R,Set.indicator,hw]
  rw [F.receiver_lintegral hs z g,← lintegral_indicator hS]
  change (∫⁻ w, H w) = _
  rw [lintegral_polar hH]
  apply lintegral_congr
  intro n
  let k : ℝ → ENNReal := fun r => ENNReal.ofReal
    (r^2*(1-dot n.1 (velocity (F.flow z (s+r)).2))) * g ((F.flow z (s+r)).1-r • n.1)
  have hn : ‖n.1‖=1 := mem_sphere_zero_iff_norm.mp n.2
  have he : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r^2) * H (r • n.1) =
      (Iio (T-s)).indicator k r := by
    intro r hr
    have hnorm : ‖r • n.1‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
    have hd : r • n.1 ∈ S ↔ r < T-s := by
      change 0 < ‖r • n.1‖ ∧ s+‖r • n.1‖ < T ↔ _
      rw [hnorm]
      constructor
      · intro h; linarith [h.2]
      · intro h; exact ⟨hr,by linarith⟩
    by_cases h : r < T-s
    · rw [show H (r • n.1) = _ from Set.indicator_of_mem (hd.mpr h) _,
        Set.indicator_of_mem (show r ∈ Iio (T-s) from h)]
      dsimp only [k,receiverRadial]
      have hnsmul : r⁻¹ • (r • n.1)=n.1 := by
        rw [smul_smul,inv_mul_cancel₀ (ne_of_gt (show 0 < r from hr)),one_smul]
      rw [hnorm,hnsmul,ENNReal.ofReal_mul (sq_nonneg r),mul_assoc]
    · rw [show H (r • n.1) = 0 from Set.indicator_of_notMem (fun hh => h (hd.mp hh)) _,mul_zero,
        Set.indicator_of_notMem (show r ∉ Iio (T-s) from h)]
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), (Iio (T-s)).indicator k r :=
      setLIntegral_congr_fun measurableSet_Ioi he
    _ = ∫⁻ r in Ioi (0 : ℝ) ∩ Iio (T-s), k r := by
      simpa only [inter_comm] using (setLIntegral_indicator (μ := (volume : Measure ℝ))
        (t := Ioi (0 : ℝ)) measurableSet_Iio k)
    _ = _ := rfl

lemma PhaseFlowOn.cone_occupation_identity {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX : Phase) {f : Particle}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase))) (heq : VlasovOn f E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H)
    (hsub : H ⊆ spaceConeDomain F.flow zX T) :
    coneOccupation F.flow zX T f H =
      labelOccupation (fun z => f (0,z)) (fun z => {t | (t,z) ∈ phaseHits F.flow T H}) := by
  rw [← F.phase_occupation_identity hT hf heq hH]
  unfold coneOccupation
  symm
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hs
  have hfs : Continuous (fun z : Phase => f (s,z)) :=
    hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨Ioo_subset_Icc_self hs,mem_univ _⟩)
  have hm : Measurable (fun z : Phase => H.indicator (fun p => ENNReal.ofReal (f p)) (s,z)) := by
    exact hfs.measurable.ennreal_ofReal.indicator
      (hH.preimage (measurable_const.prodMk measurable_id))
  let g : Vec → ENNReal := fun y => ∫⁻ v : Vec,
    H.indicator (fun p => ENNReal.ofReal (f p)) (s,(y,v))
  have hgm : Measurable g := hm.lintegral_prod_right'
  calc
    _ = ∫⁻ y : Vec, g y := lintegral_prod _ hm.aemeasurable
    _ = ∫⁻ y in ball (F.flow zX T).1 (T-s), g y := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ ball (F.flow zX T).1 (T-s)
      · exact (Set.indicator_of_mem hy g).symm
      · rw [Set.indicator_of_notMem hy]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro v
        have hp : (s,(y,v)) ∉ H := fun hp => hy (hsub hp).2
        exact Set.indicator_of_notMem hp (fun p => ENNReal.ofReal (f p))
    _ = _ := F.receiver_polar_lintegral (Ioo_subset_Icc_self hs) zX hgm

lemma PhaseFlowOn.phaseHits_in_branch {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX z : Phase) {H : Set (ℝ × Phase)} (hsub : H ⊆ spaceConeDomain F.flow zX T) :
    {s | (s,z) ∈ phaseHits F.flow T H} ⊆ branchDomain F.flow zX z T := by
  intro s hs
  have hh := (hsub hs.2).2
  rw [mem_ball,dist_eq_norm, norm_sub_rev] at hh
  exact ⟨hs.1,by linarith⟩

lemma PhaseFlowOn.cone_occupation_angular_bound_oai {E B : Field} {T δ Δ a b : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0 ≤ T) (zX : Phase) {f : Particle}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase))) (heq : VlasovOn f E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H)
    (hsub : H ⊆ spaceConeDomain F.flow zX T) (hδ : 0 ≤ δ) (hΔ : 0 < Δ)
    (hsource : ∀ z s, (s,z) ∈ phaseHits F.flow T H →
      δ ≤ 1-dot (branchDirection F.flow zX z T s) (velocity (F.flow z s).2))
    (hreceiver : ∀ z s, (s,z) ∈ phaseHits F.flow T H →
      1-dot (branchDirection F.flow zX z T s)
        (velocity (F.flow zX (branchTime F.flow zX z T s)).2) ≤ Δ)
    (himage : ∀ z, branchTime F.flow zX z T '' {s | (s,z) ∈ phaseHits F.flow T H} ⊆ Icc a b) :
    ENNReal.ofReal (δ/Δ) * coneOccupation F.flow zX T f H ≤
      ENNReal.ofReal (b-a) * ∫⁻ z, ENNReal.ofReal (f (0,z)) := by
  rw [F.cone_occupation_identity hT zX hf heq hH hsub]
  apply F.label_occupation_angular_bound zX _ hδ hΔ
    (fun z => (F.measurable_phaseHits hH).preimage (measurable_id.prodMk measurable_const))
    (fun z => F.phaseHits_in_branch zX z hsub) hsource hreceiver himage

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound_oai := @OAI.RVM.PhaseFlowOn.cone_occupation_angular_bound_oai
