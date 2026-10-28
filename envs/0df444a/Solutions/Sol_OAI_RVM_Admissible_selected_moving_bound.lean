-- Prove2me | solution 1 for OAI.RVM.Admissible.selected_moving_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:18:50.721886+00:00
-- url     : https://prove2.me/submissions/c7842d6a-2337-486b-9e28-a00bd18581a2

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_label_moving_primitive_near_constant

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

lemma hasDerivAt_dot {f g : ℝ → Vec} {f' g' : Vec} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => dot (f t) (g t))
      (dot (f s) g' + dot f' (g s)) s := by
  simpa only [dot_eq_inner] using hf.inner ℝ hg

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


lemma dot_zero_right_rvm (a : Vec) : dot a 0=0 := by simp [dot]

lemma hasDerivAt_norm_nonzero {Y : ℝ → Vec} {u : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h0 : Y s≠0) :
    HasDerivAt (fun t => ‖Y t‖) (dot (Y s) u / ‖Y s‖) s := by
  have hn := (hY.differentiableAt.norm ℝ h0).hasDerivAt
  have he := (hn.pow 2).unique hY.norm_sq
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,← dot_eq_inner] at he
  have hr : ‖Y s‖≠0 := norm_ne_zero_iff.mpr h0
  have he' : deriv (fun t => ‖Y t‖) s = dot (Y s) u / ‖Y s‖ := by
    apply (eq_div_iff hr).mpr
    linarith
  rwa [he'] at hn

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


lemma hasDerivAt_momentumDirection {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) :
    HasDerivAt (momentumDirection ∘ V)
      (‖V t‖⁻¹ • transverseProjection (V t) K) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hh := (hn.inv (norm_ne_zero_iff.mpr hv)).smul hV
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,transverseProjection,velocityProjection,dot_smul_left,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp
  ring

lemma hasDerivAt_angularMultiplier {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) (w : ℝ) (h : Vec) :
    HasDerivAt (fun r => angularMultiplier w (V r) h)
      ((-w/‖V t‖^2) •
        (dot (momentumDirection (V t)) K • transverseProjection (V t) h +
         dot (momentumDirection (V t)) h • transverseProjection (V t) K +
         dot (transverseProjection (V t) K) h • momentumDirection (V t))) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hξ := hasDerivAt_momentumDirection hV hv
  have hP := (hasDerivAt_const t h).sub
    ((hasDerivAt_dot hξ (hasDerivAt_const t h)).smul hξ)
  have hh := ((hasDerivAt_const t w).div hn (norm_ne_zero_iff.mpr hv)).smul hP
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.div_apply,Pi.sub_apply,Pi.smul_apply',momentumDirection,transverseProjection,velocityProjection,dot_smul_left,
      dot_sub_left,dot_zero_right_rvm,Function.comp_apply,zero_add,zero_sub,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,smul_eq_mul,
      zero_mul]
  field_simp
  ring

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

lemma dyadicBand_source_range {n : ℕ} {v : Vec} (h : DyadicBand n (1/q v)) :
    sourceRepresentative n/128≤q v ∧ q v≤ sourceRepresentative n/32 := by
  have hlo := h.1
  have hhi := h.2
  rw [mul_one_div] at hlo hhi
  have ha := (le_div_iff₀ (q_pos v)).mp hlo
  have hb := (div_le_iff₀ (q_pos v)).mp hhi
  dsimp [sourceRepresentative]
  constructor <;> linarith

lemma transverseCLM_apply (v h : Vec) : transverseCLM v h=transverseProjection v h := by
  simp only [transverseCLM,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]
  rfl

lemma angularMultiplierCLM_apply (w : ℝ) (v h : Vec) :
    angularMultiplierCLM w v h=angularMultiplier w v h := by
  simp only [angularMultiplierCLM,smul_apply,transverseCLM_apply,angularMultiplier]

lemma contDiffAt_transverseCLM {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k transverseCLM v := by
  have hξ : ContDiffAt ℝ k momentumDirection v :=
    ((contDiffAt_id.norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id
  exact contDiffAt_const.sub (((InnerProductSpace.toDual ℝ Vec).contDiff.of_le hk).contDiffAt.comp v hξ |>.smulRight hξ)

lemma contDiffAt_angularMultiplierCLM (w : ℝ) {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k (angularMultiplierCLM w) v := by
  exact (contDiffAt_const.div (contDiffAt_id.norm ℝ hv) (norm_ne_zero_iff.mpr hv)).smul
    (contDiffAt_transverseCLM hv hk)

lemma angularDerivativeCLM_apply (w : ℝ) (v K h : Vec) :
    angularDerivativeCLM w v K h = (-w/‖v‖^2) •
      (dot (momentumDirection v) K • transverseProjection v h +
       dot (momentumDirection v) h • transverseProjection v K +
       dot (transverseProjection v K) h • momentumDirection v) := by
  simp only [angularDerivativeCLM,smul_apply,add_apply,
    transverseCLM_apply,ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]

lemma hasDerivAt_angularMultiplierCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t≠0) (w : ℝ) :
    HasDerivAt (fun r=>angularMultiplierCLM w (V r)) (angularDerivativeCLM w (V t) K) t := by
  have hd := ((contDiffAt_angularMultiplierCLM w hv (k:=1) (by simp)).differentiableAt one_ne_zero).comp t hV.differentiableAt
  have he : deriv (fun r=>angularMultiplierCLM w (V r)) t=angularDerivativeCLM w (V t) K := by
    apply ContinuousLinearMap.ext
    intro h
    have hh := hd.hasDerivAt.clm_apply (hasDerivAt_const t h)
    simp only [ContinuousLinearMap.map_zero,add_zero,Function.comp_apply,angularMultiplierCLM_apply] at hh
    exact hh.unique (by simpa only [angularDerivativeCLM_apply] using hasDerivAt_angularMultiplier hV hv w h)
  rw [←he]
  exact hd.hasDerivAt



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

lemma extendedAngularCLM_contDiff (w : ℝ) (hw : 0<w) :
    ContDiff ℝ ∞ (extendedAngularCLM w hw) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v=0
  · subst v
    apply (contDiffAt_const (c:=(0:Vec→L[ℝ]Vec))).congr_of_eventuallyEq
    have he := (angularZeroBump w hw).eventuallyEq_one_of_mem_ball
      (show (0:Vec)∈ball 0 (angularZeroBump w hw).rIn by simpa only [mem_ball,dist_self,angularZeroBump] using div_pos hw (by norm_num : (0:ℝ)<64))
    filter_upwards [he] with v hv
    change (1-angularZeroBump w hw v) • angularMultiplierCLM w v=0
    simp only [hv,Pi.one_apply,sub_self]
    exact zero_smul ℝ (angularMultiplierCLM w v)
  · exact ((contDiffAt_const.sub (angularZeroBump w hw).contDiff.contDiffAt).smul
      (contDiffAt_angularMultiplierCLM w hv le_rfl))

lemma extendedAngularCLM_eq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32≤‖v‖) :
    extendedAngularCLM w hw v=angularMultiplierCLM w v := by
  have hz := (angularZeroBump w hw).zero_of_le_dist (by simpa only [dist_zero_right,angularZeroBump] using hv)
  simp only [extendedAngularCLM,hz,sub_zero,one_smul]

lemma extendedAngularCLM_eventuallyEq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) :
    extendedAngularCLM w hw =ᶠ[𝓝 v] angularMultiplierCLM w := by
  have he : ∀ᶠ z : Vec in 𝓝 v,w/32<‖z‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds hv)
  filter_upwards [he] with z hz
  exact extendedAngularCLM_eq w hw hz.le

lemma hasDerivAt_extendedAngularCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (w : ℝ) (hw : 0<w) :
    HasDerivAt (fun r=>extendedAngularCLM w hw (V r))
      (fderiv ℝ (extendedAngularCLM w hw) (V t) K) t :=
  ((extendedAngularCLM_contDiff w hw).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hV

lemma extendedAngularCLM_fderiv (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) (K : Vec) :
    fderiv ℝ (extendedAngularCLM w hw) v K=angularDerivativeCLM w v K := by
  have hv0 : v≠0 := norm_pos_iff.mp ((div_pos hw (by norm_num : (0:ℝ)<32)).trans hv)
  have hcurve : HasDerivAt (fun r : ℝ=>v+r • K) K 0 := by
    convert (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const K) using 1 <;> first | rfl | simp only [one_smul,zero_add]
  have ht : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 v) := by
    have hc : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 (v+(0:ℝ) • K)) := hcurve.continuousAt
    simpa only [zero_smul,add_zero] using hc
  have he := (extendedAngularCLM_eventuallyEq w hw hv).comp_tendsto ht
  have ha := (hasDerivAt_angularMultiplierCLM hcurve (by simpa using hv0) w).congr_of_eventuallyEq he
  have hb := hasDerivAt_extendedAngularCLM hcurve w hw
  simpa only [zero_smul,add_zero] using hb.unique ha

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixMomentumForce
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

lemma PhaseFlowOn.continuous_prefixMomentumForce {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (z : Phase) :
    Continuous (prefixMomentumForce s F.flow T z) := by
  have hα : Continuous (prefixFlow F.flow T z) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have ht : Continuous (prefixClamp T) := continuous_const.max (continuous_const.min continuous_id)
  have hZ := ht.prodMk hα.fst
  have hE := hs.E_smooth.continuousOn.comp_continuous hZ (fun t=>⟨prefixClamp_mem hT t,mem_univ _⟩)
  have hB := hs.B_smooth.continuousOn.comp_continuous hZ (fun t=>⟨prefixClamp_mem hT t,mem_univ _⟩)
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp (((contDiff_velocity (k:=1)).continuous.comp hα.snd).prodMk hB))

lemma PhaseFlowOn.prefixMomentum_hasDerivAt {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) (ht : t∈Ioo 0 T) :
    HasDerivAt (fun r=>(prefixFlow F.flow T z r).2)
      (lorentzField E B (t,F.flow z t)).2 t := by
  have hd : HasDerivAt (fun r=>(F.flow z r).2) (lorentzField E B (t,F.flow z t)).2 t :=
    ((F.ode z t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).snd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  simp only [prefixFlow,prefixClamp_eq hr]

lemma PhaseFlowOn.prefixAngular_regular {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (hw : 0<w) (z : Phase) :
    Continuous (prefixAngularMultiplier s F.flow T w hw z) ∧
    Continuous (prefixAngularRate s F.flow T w hw z) ∧
    ∀t∈Ioo 0 T,HasDerivAt (prefixAngularMultiplier s F.flow T w hw z)
      (prefixAngularRate s F.flow T w hw z t) t := by
  have hV : Continuous (fun t=>(prefixFlow F.flow T z t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd
  have hd := extendedAngularCLM_contDiff w hw
  refine ⟨hd.continuous.comp hV,(hd.continuous_fderiv (by simp)).comp hV |>.clm_apply
    (F.continuous_prefixMomentumForce hs hT z),?_⟩
  intro t ht
  change HasDerivAt (fun r=>extendedAngularCLM w hw (prefixFlow F.flow T z r).2)
    (fderiv ℝ (extendedAngularCLM w hw) (prefixFlow F.flow T z t).2
      (prefixMomentumForce s F.flow T z t)) t
  have he : prefixMomentumForce s F.flow T z t=(lorentzField s.E s.B (t,F.flow z t)).2 := by
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht)]
  rw [he]
  exact hasDerivAt_extendedAngularCLM (F.prefixMomentum_hasDerivAt z ht) w hw

lemma prefixAngular_highband {s : Solution} {α : Phase→ℝ→Phase} {T t w : ℝ}
    (hw : 0<w) (z : Phase) (ht : t∈Icc 0 T) (hv : w/16≤‖(α z t).2‖) :
    prefixAngularMultiplier s α T w hw z t=angularMultiplierCLM w (α z t).2 ∧
    prefixAngularRate s α T w hw z t=angularDerivativeCLM w (α z t).2
      (lorentzField s.E s.B (t,α z t)).2 := by
  have hnorm : w/32<‖(α z t).2‖ := by linarith
  simp only [prefixAngularMultiplier,prefixAngularRate,prefixMomentumForce,prefixFlow,prefixClamp_eq ht]
  exact ⟨extendedAngularCLM_eq w hw hnorm.le,extendedAngularCLM_fderiv w hw hnorm _⟩

end RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

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

lemma PhaseFlowOn.normalisedRatePrimitive_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (normalisedRatePrimitive F.flow zX) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  have hn : Continuous (fun p : ConeKernelState=>p.2.1) := continuous_snd.fst
  have hD : ∀p∈coneKernelDomain T,1-dot p.2.1 (velocity (F.flow zX p.1.1).2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  have hr : ContinuousOn (fun p : ConeKernelState=>(1-dot p.2.1 (velocity p.2.2.2))/
      (1-dot p.2.1 (velocity (F.flow zX p.1.1).2))) (coneKernelDomain T) := by
    simp only [dot_eq_inner]
    exact (continuousOn_const.sub (hn.continuousOn.inner hu.continuousOn)).div
      (continuousOn_const.sub (hn.continuousOn.inner ha))
      (fun p hp=>by simpa only [dot_eq_inner] using hD p hp)
  refine hr.smul (continuousOn_normalisedPrimitive
    (continuous_fst.fst.sub continuous_fst.snd).continuousOn ha hu.continuousOn hn.continuousOn ?_ hD)
  intro p hp
  exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

lemma PhaseFlowOn.actualLabelRatePrimitive_eq {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (s : Solution) (zX : Phase) :
    actualLabelRatePrimitive s F.flow zX T =
      labelConeKernel s F.flow zX T (normalisedRatePrimitive F.flow zX) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hr : branchTime F.flow zX p.2 T p.1-p.1≠0 :=
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1).ne'
    rw [actualLabelRatePrimitive,actualLabelPrimitive,indicator_of_mem hp,labelConeKernel,indicator_of_mem hp]
    simp only [normalisedRatePrimitive,labelKernelState,normalisedPrimitive_eq _ _ _ hr]
    simp only [branchRate,smul_smul]
    congr 1
    simp only [branchDirection]
    field_simp
  · simp only [actualLabelRatePrimitive,actualLabelPrimitive,labelConeKernel,indicator_of_notMem hp,smul_zero]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedMomentumForce
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


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal



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


lemma selected_radial_factor {x h : ℝ} (hx : 0≤x) (hh : 0≤h)
    (hsel : x*Real.sqrt h≤1) : x^3*h^2≤Real.sqrt h := by
  have hs : 0≤Real.sqrt h := Real.sqrt_nonneg h
  have hsq := Real.sq_sqrt hh
  calc
    x^3*h^2 = (x*Real.sqrt h)^3*Real.sqrt h := by
      nth_rw 1 [←hsq]
      ring
    _ ≤ 1^3*Real.sqrt h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hx hs) hsel 3) hs
    _ = _ := by norm_num

lemma selected_radial_width {x h r R : ℝ} (hx : 0≤x) (hh : 0≤h)
    (hsel : x*Real.sqrt h≤1) (_hR : 0≤R) (hwidth : r≤R)
    (hhi : R≤2*h) (hw : R-r≤2*h) :
    x^3*R*(R-r)≤4*Real.sqrt h := by
  calc
    _ = x^3*(R*(R-r)) := by ring
    _ ≤ x^3*((2*h)*(2*h)) := mul_le_mul_of_nonneg_left
      (mul_le_mul hhi hw (sub_nonneg.mpr hwidth) (by positivity)) (by positivity)
    _ = 4*(x^3*h^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (selected_radial_factor hx hh hsel) (by norm_num)

lemma selected_moving_coefficient {C p θ φ w h r R : ℝ}
    (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0≤φ) (hw₀ : 0≤w) (hh : 0≤h)
    (hsel : p*θ*Real.sqrt h≤1) (hR : 0≤R) (hwidth : r≤R)
    (hhi : R≤2*h) (hw : R-r≤2*h) :
    C*(p*θ)^3*φ/w*R*(R-r)≤4*C*Real.sqrt h*φ/w := by
  have h := mul_le_mul_of_nonneg_left (selected_radial_width (mul_nonneg hp hθ) hh hsel hR hwidth hhi hw)
    (div_nonneg (mul_nonneg hC hφ) hw₀)
  convert h using 1 <;> first | rfl | ring

lemma radial_half_decay (n : ℕ) : Real.sqrt ((1/2:ℝ)^n)≤(3/4:ℝ)^n := by
  have hs : Real.sqrt (1/2:ℝ)≤3/4 := (Real.sqrt_le_iff).mpr (by norm_num)
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ,Real.sqrt_mul (by positivity),pow_succ]
      exact mul_le_mul ih hs (Real.sqrt_nonneg _) (by positivity)

lemma sum_radial_half_decay (N : ℕ) : ∑n∈Finset.range N,Real.sqrt ((1/2:ℝ)^n)≤4 := by
  calc
    _ ≤ ∑n∈Finset.range N,(3/4:ℝ)^n := Finset.sum_le_sum (fun n _=>radial_half_decay n)
    _ ≤ ∑'n : ℕ,(3/4:ℝ)^n := (summable_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖<1)).sum_le_tsum
      (Finset.range N) (fun n _=>by positivity)
    _ = 4 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖<1)]; norm_num

lemma sum_angular_half_decay (N : ℕ) : ∑n∈Finset.range N,(1/2:ℝ)^n≤2 := by
  calc
    _ ≤ ∑'n : ℕ,(1/2:ℝ)^n := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).sum_le_tsum
      (Finset.range N) (fun n _=>by positivity)
    _ = 2 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]; norm_num

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

lemma PhaseFlowOn.coneDyadicFactor_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k : Fin 4→ℕ) :
    ContinuousOn (coneDyadicFactor F.flow zX T k) (coneKernelDomain T) := by
  have hV : ContinuousOn (fun p : ConeKernelState=>(F.flow zX p.1.1).2) (coneKernelDomain T) :=
    ((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd
  have hv : Continuous (fun p : ConeKernelState=>p.2.2.2) := continuous_snd.snd.snd
  have hn : Continuous (fun p : ConeKernelState=>p.2.1) := continuous_snd.fst
  have hu := (contDiff_velocity (k:=1)).continuous.comp hv
  have ha := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hV
  have hq := (contDiff_q (k:=1)).continuous.comp hv
  have hc : ∀i,ContinuousOn (fun p : ConeKernelState=>physicalCutoffCoordinates T (p.1.1-p.1.2)
      p.2.1 p.2.2.2 (F.flow zX p.1.1).2 i) (coneKernelDomain T) := by
    intro i
    fin_cases i
    · exact continuousOn_const.div hq.continuousOn (fun p _=>(q_pos p.2.2.2).ne')
    · exact ((continuousOn_const.sub (continuous_dot.comp_continuousOn
        (hn.continuousOn.prodMk hu.continuousOn))).div_const 2).sqrt
    · exact ((continuousOn_const.sub (continuous_dot.comp_continuousOn
        (hn.continuousOn.prodMk ha))).div_const 2).sqrt
    · exact (continuous_fst.fst.sub continuous_fst.snd).continuousOn.div_const _
  exact continuousOn_finsetProd Finset.univ (fun i _=>
    (contDiff_dyadicFactor (k i)).continuous.comp_continuousOn (hc i))

lemma PhaseFlowOn.projectedDyadicRateKernel_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k : Fin 4→ℕ)
    {G : ℝ→Vec→L[ℝ]Vec} (hG : Continuous G) :
    ContinuousOn (projectedDyadicRateKernel F.flow zX T k G) (coneKernelDomain T) :=
  (F.coneDyadicFactor_continuousOn zX k).smul
    ((hG.comp continuous_fst.fst).continuousOn.clm_apply (F.normalisedRatePrimitive_continuousOn zX))

lemma weighted_labelProjected_congr (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (k : Fin 4→ℕ) {J : Set ℝ}
    {G H : ℝ→Vec→L[ℝ]Vec} (hGH : EqOn G H J)
    {b : ℝ→ℝ} (hbJ : ∀t∉J,b t=0) (p : ℝ×Phase) :
    ENNReal.ofReal (b (labelReceiverTime α zX T p))*
      ENNReal.ofReal ‖labelConeKernel s α zX T (projectedDyadicRateKernel α zX T k G) p‖=
    ENNReal.ofReal (b (labelReceiverTime α zX T p))*
      ENNReal.ofReal ‖labelConeKernel s α zX T (projectedDyadicRateKernel α zX T k H) p‖ := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelReceiverTime,labelConeKernel,indicator_of_mem hp]
    by_cases ht : branchTime α zX p.2 T p.1∈J
    · simp only [projectedDyadicRateKernel,labelKernelState,hGH ht]
    · simp only [hbJ _ ht,ENNReal.ofReal_zero,zero_mul]
  · simp only [labelConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero,mul_zero]

lemma finset_subset_dyadicBox {ι : Type*} [Fintype ι] (S : Finset (ι→ℕ)) :
    ∃M : ℕ,S⊆dyadicBox ι M := by
  classical
  obtain ⟨M,hM⟩ := (S.biUnion (fun k=>Finset.univ.image k)).exists_nat_subset_range
  refine ⟨M,?_⟩
  intro k hk
  simp only [dyadicBox,Fintype.mem_piFinset]
  intro i
  apply hM
  exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

lemma directionWeightMajorant_nonneg (N : ℕ) (k : Fin 4→ℕ) :
    0≤directionWeightMajorant N k := by
  unfold directionWeightMajorant
  positivity

lemma sum_range_indicator_lt (M N : ℕ) :
    (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)≤N := by
  classical
  rw [Finset.sum_boole,Nat.cast_le]
  have h : (Finset.range M).filter (fun i=>i<N)⊆Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  simpa only [Finset.card_range] using Finset.card_le_card h

lemma sum_directionWeightMajorant_box (M N : ℕ) :
    ∑k∈dyadicBox (Fin 4) M,directionWeightMajorant N k≤8*(N:ℝ)^2 := by
  classical
  let g : Fin 4→ℕ→ℝ := ![fun i=>if i<N then 1 else 0,
    fun i=>if i<N then 1 else 0,fun i=>(1/2:ℝ)^i,fun i=>Real.sqrt ((1/2:ℝ)^i)]
  have he : ∑k∈dyadicBox (Fin 4) M,directionWeightMajorant N k=
      ∏j,∑i∈Finset.range M,g j i := by
    have heq : (instDecidableEqFin 4 : DecidableEq (Fin 4))=
        (fun a b=>Classical.propDecidable (a=b)) := Subsingleton.elim _ _
    have hh := Finset.sum_prod_piFinset (Finset.range M) g
    rw [heq] at hh
    simpa [dyadicBox,Fin.prod_univ_four,directionWeightMajorant,g] using hh
  rw [he,Fin.prod_univ_four]
  change (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)*
    (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)*
    (∑i∈Finset.range M,(1/2:ℝ)^i)*(∑i∈Finset.range M,Real.sqrt ((1/2:ℝ)^i))≤_
  have hN : 0≤(∑i∈Finset.range M,if i<N then (1:ℝ) else 0) :=
    Finset.sum_nonneg (fun i _=>by positivity)
  have ha : 0≤∑i∈Finset.range M,(1/2:ℝ)^i := Finset.sum_nonneg (fun i _=>by positivity)
  have hs : 0≤∑i∈Finset.range M,Real.sqrt ((1/2:ℝ)^i) := Finset.sum_nonneg (fun i _=>by positivity)
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul (sum_range_indicator_lt M N) (sum_range_indicator_lt M N) hN (by positivity))
      (sum_angular_half_decay M) ha (by positivity))
    (sum_radial_half_decay M) hs (by positivity)
  exact h.trans_eq (by ring)

lemma sum_directionWeightMajorant (S : Finset (Fin 4→ℕ)) (N : ℕ) :
    ∑k∈S,directionWeightMajorant N k≤8*(N:ℝ)^2 := by
  obtain ⟨M,hM⟩ := finset_subset_dyadicBox S
  exact (Finset.sum_le_sum_of_subset_of_nonneg hM
    (fun k _ _=>directionWeightMajorant_nonneg N k)).trans (sum_directionWeightMajorant_box M N)

lemma tsum_directionWeightMajorant (N : ℕ) :
    (∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k))≤ENNReal.ofReal (8*(N:ℝ)^2) := by
  have hs : Summable (directionWeightMajorant N) :=
    summable_of_sum_le (directionWeightMajorant_nonneg N) (fun S=>sum_directionWeightMajorant S N)
  rw [←ENNReal.ofReal_tsum_of_nonneg (directionWeightMajorant_nonneg N) hs]
  exact ENNReal.ofReal_le_ofReal (hs.tsum_le_of_sum_le (fun S=>sum_directionWeightMajorant S N))

lemma selectedDyadicCutoff_ofReal {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hx : ∀i,0<x i) (Q : Set (ι→ℕ)) :
    ENNReal.ofReal (selectedDyadicCutoff Q x)=
      ∑'k : ι→ℕ,Q.indicator (fun k=>ENNReal.ofReal (dyadicMultiFactor k x)) k := by
  classical
  obtain ⟨N,_hN,he⟩ := dyadicMultiFactor_curve_locally_finite
    (t:=(0:ℝ)) (g:=fun i (_ : ℝ)=>x i) (fun _=>continuousAt_const) hx
  have hz : ∀k,k∉dyadicBox ι N→dyadicMultiFactor k x=0 := he.self_of_nhds
  have hs : Summable (Q.indicator (fun k=>dyadicMultiFactor k x)) := by
    apply summable_of_hasFiniteSupport
    apply (Finset.finite_toSet (dyadicBox ι N)).subset
    intro k hk
    by_contra hkn
    apply hk
    by_cases hQ : k∈Q
    · rw [indicator_of_mem hQ,hz k hkn]
    · exact indicator_of_notMem hQ _
  rw [selectedDyadicCutoff,ENNReal.ofReal_tsum_of_nonneg (fun k=>by
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk]; exact dyadicMultiFactor_nonneg k x
    · rw [indicator_of_notMem hk]) hs]
  apply tsum_congr
  intro k
  by_cases hk : k∈Q
  · simp only [indicator_of_mem hk]
  · simp only [indicator_of_notMem hk,ENNReal.ofReal_zero]

lemma PhaseFlowOn.label_projected_dyadic_eq {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (s : Solution) (zX : Phase)
    (k : Fin 4→ℕ) (G : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) :
    labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p=
      dyadicMultiFactor k (actualCutoffCoordinates F.flow T zX p.2 p.1) •
        G (labelReceiverTime F.flow zX T p) (actualLabelRatePrimitive s F.flow zX T p) := by
  classical
  rw [F.actualLabelRatePrimitive_eq s zX]
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · simp only [labelConeKernel,indicator_of_mem hp,projectedDyadicRateKernel,
      coneDyadicFactor,labelKernelState,actualCutoffCoordinates,labelReceiverTime,
      map_smul,smul_smul]
    congr 1
    ring
  · simp only [labelConeKernel,indicator_of_notMem hp,map_zero,smul_zero]

lemma PhaseFlowOn.selected_receiver_rate_norm_sum {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (s : Solution) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (b : ℝ→ℝ) (G : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) :
    ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
      (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖=
    ∑'k : Fin 4→ℕ,Q.indicator (fun k=>
      ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) k := by
  classical
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hj : p∈jointBranchDomain F.flow zX T := hp
    have hx : ∀i,0<actualCutoffCoordinates F.flow T zX p.2 p.1 i :=
      physicalCutoffCoordinates_pos (F.branchDirection_norm zX p.2 hp.1 hp.2)
        (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1)
    have hle : ∀i,actualCutoffCoordinates F.flow T zX p.2 p.1 i≤1 := by
      apply physicalCutoffCoordinates_le_one (F.branchDirection_norm zX p.2 hp.1 hp.2)
      linarith [(F.branch_time_mem zX p.2 hp.1 hp.2).2,hp.1.1.1,le_max_right (1:ℝ) T]
    have hχ := (selectedDyadicCutoff_mem_unit hx hle Q).1
    rw [map_smul,norm_smul,Real.norm_eq_abs,labelWeight,abs_mul,labelSelectedCutoff,
      indicator_of_mem hj,abs_of_nonneg hχ,ENNReal.ofReal_mul (by positivity :
        0≤|b (labelReceiverTime F.flow zX T p)| *selectedDyadicCutoff Q
          (actualCutoffCoordinates F.flow T zX p.2 p.1)),
      ENNReal.ofReal_mul (abs_nonneg _),selectedDyadicCutoff_ofReal hx Q]
    rw [mul_assoc,←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro k
    by_cases hk : k∈Q
    · simp only [indicator_of_mem hk]
      rw [F.label_projected_dyadic_eq s zX k G p]
      simp only [norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (dyadicMultiFactor_nonneg _ _),
        ENNReal.ofReal_mul (dyadicMultiFactor_nonneg _ _)]
    · simp only [indicator_of_notMem hk,zero_mul,mul_zero]
  · rw [F.actualLabelRatePrimitive_eq s zX]
    simp only [labelConeKernel,indicator_of_notMem hp,smul_zero,map_zero,norm_zero,ENNReal.ofReal_zero,mul_zero,
      indicator_zero,tsum_zero]

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

namespace RVM

lemma selectedDyadicCutoff_restrict {ι : Type*} [Fintype ι] (Q R : Set (ι→ℕ))
    (x : ι→ℝ) (hR : ∀k,dyadicMultiFactor k x≠0→k∈R) :
    selectedDyadicCutoff Q x=selectedDyadicCutoff (Q∩R) x := by
  classical
  apply tsum_congr
  intro k
  by_cases hk : k∈R
  · by_cases hQ : k∈Q
    · simp only [indicator_of_mem hQ,indicator_of_mem (show k∈Q∩R from ⟨hQ,hk⟩)]
    · simp only [indicator_of_notMem hQ,indicator_of_notMem (show k∉Q∩R from fun h=>hQ h.1)]
  · have hz : dyadicMultiFactor k x=0 := by by_contra hc; exact hk (hR k hc)
    by_cases hQ : k∈Q
    · simp only [indicator_of_mem hQ,indicator_of_notMem (show k∉Q∩R from fun h=>hk h.2),hz]
    · simp only [indicator_of_notMem hQ,indicator_of_notMem (show k∉Q∩R from fun h=>hQ h.1)]

lemma PhaseFlowOn.labelWeight_rate_source_truncate {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (s : Solution) (zX : Phase) (N : ℕ)
    (hP : ∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N)
    (Q : Set (Fin 4→ℕ)) (b : ℝ→ℝ) (p : ℝ×Phase) :
    labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p=
      labelWeight F.flow zX T (Q∩{k | k 0<N ∧ k 1<N}) b p • actualLabelRatePrimitive s F.flow zX T p := by
  classical
  by_cases hf : s.f (0,p.2)=0
  · rw [F.actualLabelRatePrimitive_eq s zX]
    by_cases hp : p∈labelBranchDomain F.flow zX T
    · simp only [labelConeKernel,indicator_of_mem hp,hf,zero_smul,smul_zero]
    · simp only [labelConeKernel,indicator_of_notMem hp,smul_zero]
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have he : selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX p.2 p.1)=
        selectedDyadicCutoff (Q∩{k | k 0<N ∧ k 1<N}) (actualCutoffCoordinates F.flow T zX p.2 p.1) := by
      apply selectedDyadicCutoff_restrict
      intro k hk
      exact physicalCutoff_positive_source_indices (F.branchDirection_norm zX p.2 hp.1 hp.2)
        (hP p.2 hf p.1 (Ioo_subset_Icc_self hp.1.1))
        (lt_of_le_of_ne (dyadicMultiFactor_nonneg _ _) (Ne.symm hk))
    have hj : p∈jointBranchDomain F.flow zX T := hp
    simp only [labelWeight,labelSelectedCutoff,indicator_of_mem hj,he]
  · rw [F.actualLabelRatePrimitive_eq s zX]
    simp only [labelConeKernel,indicator_of_notMem hp,smul_zero]

lemma selected_representative_moving_bound {T C w : ℝ} {k : Fin 4→ℕ} {N : ℕ}
    (hC : 0≤C) (hw : 0≤w) (h0 : k 0<N) (h1 : k 1<N)
    (hsel : sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) :
    C*(sourceRepresentative (k 0)*cappedRepresentative (k 1))^3*
      cappedRepresentative (k 2)/w*(representativeClosedBin T w k).rmax*
      ((representativeClosedBin T w k).rmax-(representativeClosedBin T w k).rmin)≤
      (4*C*Real.sqrt (max 1 T)/w)*directionWeightMajorant N k := by
  have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  have hp : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hc (i : Fin 4) : 0 < cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
  have hb := selected_moving_coefficient hC hp.le (hc 1).le (hc 2).le hw
    (mul_nonneg hT.le (hc 3).le) hsel
    (R:=(representativeClosedBin T w k).rmax) (r:=(representativeClosedBin T w k).rmin)
    (by exact mul_nonneg (mul_nonneg (by norm_num) hT.le) (hc 3).le)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
    (by dsimp [representativeClosedBin]; ring_nf; exact le_rfl)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
  calc
    _ ≤ 4*C*Real.sqrt (max 1 T*cappedRepresentative (k 3))*cappedRepresentative (k 2)/w := hb
    _ = _ := by
      rw [Real.sqrt_mul hT.le]
      simp only [directionWeightMajorant,ite_eq_left h0,ite_eq_left h1,one_mul,cappedRepresentative]
      norm_num
      ring

lemma Admissible.selected_moving_bound_finite_sources {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularDerivativeCLM w (F.flow zX (labelReceiverTime F.flow zX T p)).2
        (lorentzField s.E s.B (labelReceiverTime F.flow zX T p,F.flow zX (labelReceiverTime F.flow zX T p))).2
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖)≤
      (∫⁻t in J,ENNReal.ofReal |b t| * ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  classical
  obtain ⟨C,hC,hnear⟩ := hd.label_moving_primitive_near_constant
  refine ⟨32*C,by positivity,?_⟩
  intro s T F hs hT h0 zX J w N Q hQ hJ hJT hw hband hv b hb hbJ
  let G := prefixAngularRate s F.flow T w hw zX
  let W := ∫⁻t in J,ENNReal.ofReal |b t| * ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖
  have hG := (F.prefixAngular_regular hs hT hw zX).2.1
  have hGe : ∀t∈J,G t=angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2 :=
    fun t ht=>(prefixAngular_highband (s:=s) hw zX (hJT ht) (hv t ht)).2
  have h0abs : ∀t∉J,|b t|=0 := fun t ht=>by rw [hbJ t ht,abs_zero]
  have hbnorm (k : Fin 4→ℕ) : Measurable (fun p : ℝ×Phase=>
      ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) :=
    ((hb.comp (F.labelReceiverTime_measurable zX)).norm.ennreal_ofReal).mul
      ((F.measurable_labelConeKernel hs zX (F.projectedDyadicRateKernel_continuousOn zX k hG)).norm.ennreal_ofReal)
  have hbound (k : Fin 4→ℕ) (hk : k∈Q) :
      (∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖)≤
      W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)*ENNReal.ofReal (directionWeightMajorant N k)) := by
    have hc (i : Fin 4) : 0 < cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
    have hp : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
    have he : (∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖)=
      ∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T
          (projectedDyadicRateKernel F.flow zX T k (fun t=>angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2)) p‖ := by
      apply lintegral_congr
      intro p
      exact weighted_labelProjected_congr s F.flow zX T k (fun t ht=>hGe t ht) h0abs p
    rw [he]
    have hn := hnear s T F hs hT h0 zX J w (sourceRepresentative (k 0))
      (cappedRepresentative (k 1)) (cappedRepresentative (k 2)) k hJ hJT hw hp.le (hc 1).le (hc 2)
      (by dsimp [cappedRepresentative]; exact pow_le_one₀ (by norm_num) (by norm_num))
      (hQ k hk).2.2.1 le_rfl le_rfl le_rfl (by
        change sourceRepresentative (k 0)/32 ≤ sourceRepresentative (k 0)
        linarith) hband hv (fun t=>|b t|) hb.norm h0abs
    refine hn.trans (mul_le_mul' (a:=W) (b:=W) le_rfl ?_)
    rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T)/w)]
    exact ENNReal.ofReal_le_ofReal
      (selected_representative_moving_bound hC hw.le (hQ k hk).1 (hQ k hk).2.1 (hQ k hk).2.2.2)
  calc
    _ = ∫⁻p : ℝ×Phase,ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖ := by
      apply lintegral_congr
      intro p
      by_cases ht : labelReceiverTime F.flow zX T p∈J
      · rw [hGe _ ht]
      · simp only [labelWeight,hbJ _ ht,zero_mul,zero_smul,map_zero]
    _ = ∫⁻p : ℝ×Phase,∑'k : Fin 4→ℕ,Q.indicator (fun k=>
        ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
          ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) k := by
      apply lintegral_congr
      intro p
      exact F.selected_receiver_rate_norm_sum s zX Q b G p
    _ = ∑'k : Fin 4→ℕ,∫⁻p : ℝ×Phase,Q.indicator (fun k=>
        ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
          ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) k := by
      apply lintegral_tsum
      intro k
      by_cases hk : k∈Q
      · simpa only [indicator_of_mem hk] using (hbnorm k).aemeasurable
      · simp only [indicator_of_notMem hk]
        exact aemeasurable_const
    _ ≤ ∑'k : Fin 4→ℕ,W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)*
        ENNReal.ofReal (directionWeightMajorant N k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈Q
      · simpa only [indicator_of_mem hk] using hbound k hk
      · simp only [indicator_of_notMem hk,lintegral_zero]
        exact bot_le
    _ = W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)*
        ∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k)) := by
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
    _ ≤ W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)*ENNReal.ofReal (8*(N:ℝ)^2)) :=
      mul_le_mul' (a:=W) (b:=W) le_rfl (mul_le_mul' (a:=ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w))
        (b:=ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)) le_rfl (tsum_directionWeightMajorant N))
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T)/w)]
      congr 2
      ring

lemma Admissible.selected_moving_bound_oai {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
      (∀k∈Q,cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularDerivativeCLM w (F.flow zX (labelReceiverTime F.flow zX T p)).2
        (lorentzField s.E s.B (labelReceiverTime F.flow zX T p,F.flow zX (labelReceiverTime F.flow zX T p))).2
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖)≤
      (∫⁻t in J,ENNReal.ofReal |b t| * ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  obtain ⟨C,hC,hb⟩ := hd.selected_moving_bound_finite_sources
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv b hbm hbJ
  have he : (fun p : ℝ×Phase=>labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)=
      fun p : ℝ×Phase=>labelWeight F.flow zX T (Q∩{k | k 0<N ∧ k 1<N}) b p • actualLabelRatePrimitive s F.flow zX T p :=
    funext (F.labelWeight_rate_source_truncate s zX N hP Q b)
  simp_rw [congr_fun he]
  exact hb s T F hs hT h0 zX J w N _ (fun k hk=>⟨hk.2.1,hk.2.2,hQ k hk.1⟩)
    hJ hJT hw hband hv b hbm hbJ

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.selected_moving_bound_oai := @OAI.RVM.Admissible.selected_moving_bound_oai
