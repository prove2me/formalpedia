-- Prove2me | solution 1 for OAI.RVM.Admissible.force_bulk_receiver_residual_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:47:33.064701+00:00
-- url     : https://prove2.me/submissions/60e907a2-5208-4341-a58d-99742bc6c9a0

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V002
import Theorems.Thm_OAI_RVM_Admissible_bulk_rate_uniform
import Theorems.Thm_OAI_RVM_Admissible_bulk_selected_family_uniform
import Theorems.Thm_OAI_RVM_Admissible_unselected_label_uniform
import Theorems.Thm_OAI_RVM_PhaseFlowOn_selectedConeTriangle_norm_transfer
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_selected_multiplier_decomposition
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

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

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

lemma normalisedRemainder_eq {r : ℝ} (a u n b : Vec) (hr : r≠0) :
    normalisedRemainder r a u n b=r^2 • signedRemainder r a u n b := by
  simp only [normalisedRemainder,signedRemainder,smul_add,smul_smul]
  congr 2 <;> field_simp

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

lemma PhaseFlowOn.actualLabelRemainder_eq_normalised {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) :
    actualLabelRemainder s F.flow zX T=labelConeKernel s F.flow zX T
      (fun p=>normalisedRemainder (p.1.1-p.1.2) (velocity (F.flow zX p.1.1).2)
        (velocity p.2.2.2) p.2.1 (phaseAcceleration s.E s.B F.flow zX p.1.1)) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hr : branchTime F.flow zX p.2 T p.1-p.1≠0 :=
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1).ne'
    simp only [actualLabelRemainder,labelConeKernel,indicator_of_mem hp,labelKernelState,
      normalisedRemainder_eq _ _ _ _ hr]
    rw [smul_comm (s.f (0,p.2)),smul_smul,←mul_pow,inv_mul_cancel₀ hr,one_pow,one_smul]
  · simp only [actualLabelRemainder,labelConeKernel,indicator_of_notMem hp]

lemma PhaseFlowOn.actualLabelPrimitive_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualLabelPrimitive s F.flow zX T) := by
  rw [F.actualLabelPrimitive_eq_normalised zX]
  exact F.measurable_labelConeKernel hs zX (F.normalised_primitive_continuousOn zX)

lemma PhaseFlowOn.actualLabelRemainder_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualLabelRemainder s F.flow zX T) := by
  rw [F.actualLabelRemainder_eq_normalised zX]
  exact F.measurable_labelConeKernel hs zX (F.normalised_remainder_continuousOn hs zX)

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

lemma PhaseFlowOn.selectedCutoff_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    Measurable ((jointBranchDomain F.flow zX T).indicator
      (fun p : ℝ×Phase=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX p.2 p.1))) := by
  classical
  have hc : ContinuousOn (fun p : ℝ×Phase=>stateCutoff T Q (branchCutoffState F.flow T zX p.2 p.1))
      (jointBranchDomain F.flow zX T) := by
    intro p hp
    exact ((contDiffAt_stateCutoff T Q (z:=branchCutoffState F.flow T zX p.2 p.1)
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1)
      (F.branchDirection_norm zX p.2 hp.1 hp.2)).continuousAt.comp (f := fun q : ℝ×Phase=>branchCutoffState F.flow T zX q.2 q.1)
        (F.branchCutoffState_continuousAt zX hp)).continuousWithinAt
  exact hc.measurable_piecewise continuousOn_const (F.isOpen_jointBranchDomain zX).measurableSet

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

lemma PhaseFlowOn.actualLabelRatePrimitive_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualLabelRatePrimitive s F.flow zX T) := by
  rw [F.actualLabelRatePrimitive_eq s zX]
  exact F.measurable_labelConeKernel hs zX (F.normalisedRatePrimitive_continuousOn zX)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_LabelWeight
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

lemma PhaseFlowOn.labelWeight_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} (hψ : Measurable ψ) :
    Measurable (labelWeight F.flow zX T Q ψ) :=
  (hψ.comp (F.labelReceiverTime_measurable zX)).mul (F.selectedCutoff_measurable zX Q)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal

namespace RVM

lemma selectedMultiplierCosts_norm_le (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W W' : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) :
    ENNReal.ofReal ‖selectedMultiplierCosts s α zX T Q ψ W W' p‖ ≤
      selectedMultiplierWeightDensity s α zX T Q ψ W p +
      ENNReal.ofReal |ψ (labelReceiverTime α zX T p)| *
        selectedMultiplierBulkDensity s α zX T Q W p +
      selectedMultiplierMovingDensity s α zX T Q ψ W' p := by
  let τ := labelReceiverTime α zX T p
  have he : selectedMultiplierCosts s α zX T Q ψ W W' p =
      W τ (labelWeight α zX T Q (deriv ψ) p • actualLabelRatePrimitive s α zX T p) +
      (ψ τ • W τ (actualLabelCutoffCost s α zX T Q p) +
       ψ τ • W τ (labelSelectedCutoff α zX T Q p • actualLabelRemainder s α zX T p)) +
      W' τ (labelWeight α zX T Q ψ p • actualLabelRatePrimitive s α zX T p) := by
    simp only [selectedMultiplierCosts,selectedLabelCosts,map_add,map_smul,
      labelWeight,mul_smul,add_assoc,τ]
  rw [he]
  have hn (x y : Vec) : ENNReal.ofReal ‖x+y‖ ≤ ENNReal.ofReal ‖x‖+ENNReal.ofReal ‖y‖ := by
    rw [←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  dsimp only [selectedMultiplierWeightDensity,selectedMultiplierMovingDensity]
  apply (hn _ _).trans
  apply add_le_add _ le_rfl
  apply (hn _ _).trans
  apply add_le_add le_rfl
  apply (hn _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,ENNReal.ofReal_mul (abs_nonneg _),
    selectedMultiplierBulkDensity,mul_add,τ,le_refl]

lemma measurable_vec_clm_apply {Ω : Type*} [MeasurableSpace Ω]
    {W : Ω→Vec→L[ℝ]Vec} {f : Ω→Vec} (hW : Measurable W) (hf : Measurable f) :
    Measurable (fun p=>W p (f p)) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp (hW.prodMk hf)

lemma PhaseFlowOn.selectedMultiplierBulkDensity_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p))) :
    Measurable (selectedMultiplierBulkDensity s F.flow zX T Q W) := by
  have hWt := hW
  exact ((measurable_vec_clm_apply hWt (F.actualLabelCutoffCost_measurable hs zX Q)).norm.ennreal_ofReal).add
    ((measurable_vec_clm_apply hWt ((F.selectedCutoff_measurable zX Q).smul
      (F.actualLabelRemainder_measurable hs zX))).norm.ennreal_ofReal)

lemma PhaseFlowOn.selectedMultiplierWeightDensity_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p))) :
    Measurable (selectedMultiplierWeightDensity s F.flow zX T Q ψ W) := by
  exact ((measurable_vec_clm_apply hW
    ((F.labelWeight_measurable zX Q (measurable_deriv ψ)).smul
      (F.actualLabelRatePrimitive_measurable hs zX))).norm.ennreal_ofReal)

lemma PhaseFlowOn.selectedMultiplierCosts_integral_bound {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} (hψ : Measurable ψ)
    {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable (fun p : ℝ×Phase=>W (labelReceiverTime F.flow zX T p))) :
    ENNReal.ofReal ‖∫p,selectedMultiplierCosts s F.flow zX T Q ψ W W' p‖ ≤
      (∫⁻p,selectedMultiplierWeightDensity s F.flow zX T Q ψ W p) +
      (∫⁻p,ENNReal.ofReal |ψ (labelReceiverTime F.flow zX T p)| *
        selectedMultiplierBulkDensity s F.flow zX T Q W p) +
      ∫⁻p,selectedMultiplierMovingDensity s F.flow zX T Q ψ W' p := by
  have hm₁ := F.selectedMultiplierWeightDensity_measurable hs zX Q ψ hW
  have hm₂ : Measurable (fun p : ℝ×Phase =>
      ENNReal.ofReal |ψ (labelReceiverTime F.flow zX T p)| *
        selectedMultiplierBulkDensity s F.flow zX T Q W p) := by
    convert ((hψ.comp (F.labelReceiverTime_measurable zX)).norm.ennreal_ofReal).mul
        (F.selectedMultiplierBulkDensity_measurable hs zX Q hW) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [Pi.mul_apply,Function.comp_apply,Real.norm_eq_abs]
  have hm₁₂ : Measurable (fun p : ℝ×Phase =>
      selectedMultiplierWeightDensity s F.flow zX T Q ψ W p +
      ENNReal.ofReal |ψ (labelReceiverTime F.flow zX T p)| *
        selectedMultiplierBulkDensity s F.flow zX T Q W p) := hm₁.add hm₂
  calc
    _ ≤ ∫⁻p,ENNReal.ofReal ‖selectedMultiplierCosts s F.flow zX T Q ψ W W' p‖ := by
      simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm
        (selectedMultiplierCosts s F.flow zX T Q ψ W W')
    _ ≤ ∫⁻p,selectedMultiplierWeightDensity s F.flow zX T Q ψ W p +
      ENNReal.ofReal |ψ (labelReceiverTime F.flow zX T p)| *
        selectedMultiplierBulkDensity s F.flow zX T Q W p +
      selectedMultiplierMovingDensity s F.flow zX T Q ψ W' p :=
        lintegral_mono (selectedMultiplierCosts_norm_le s F.flow zX T Q ψ W W')
    _ = _ := by rw [lintegral_add_left hm₁₂,lintegral_add_left hm₁]

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BulkWeightCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma labelConeKernel_const_smul (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T c : ℝ) (A : ConeKernelState→Vec) (p : ℝ×Phase) :
    labelConeKernel s α zX T (fun x=>c • A x) p=c • labelConeKernel s α zX T A p := by
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelConeKernel,indicator_of_mem hp]
    simp only [smul_smul]
    congr 1
    ring
  · simp only [labelConeKernel,indicator_of_notMem hp,smul_zero]

lemma PhaseFlowOn.selected_weight_cost_bound {s : Solution} {T I D a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (Q : Set (Fin 4→ℕ)) (hI : 0<I) (hD : 0≤D)
    {ψ : ℝ→ℝ} (hψd : ∀t∈Icc a b,|deriv ψ t|≤D/I)
    (hψout : ∀t∉Icc a b,deriv ψ t=0) :
    (∫⁻p : ℝ×Phase,selectedMultiplierWeightDensity s F.flow zX T Q ψ
      (fun _=>ContinuousLinearMap.id ℝ Vec) p)≤
      ENNReal.ofReal D*(∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q
        (fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p)
        (fun _=>ContinuousLinearMap.id ℝ Vec) (Icc a b) p‖ ∂trianglePhaseMeasure) := by
  have ht := F.selectedConeTriangle_norm_transfer (J:=Icc a b)
    (A:=fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p)
    hs hT zX Q ((continuousOn_const : ContinuousOn (fun _ : ConeKernelState=>I⁻¹) (coneKernelInterior T)).smul
      ((F.normalisedRatePrimitive_continuousOn zX).mono inter_subset_left))
    (W:=fun _=>ContinuousLinearMap.id ℝ Vec) measurable_const measurableSet_Icc
  rw [←ht,←lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro p
  let τ := labelReceiverTime F.flow zX T p
  by_cases hp : τ∈Icc a b
  · simp only [selectedMultiplierWeightDensity,ContinuousLinearMap.id_apply,
      labelWeight,←smul_smul, norm_smul,Real.norm_eq_abs]
    rw [indicator_of_mem hp,ContinuousLinearMap.id_apply,labelConeKernel_const_smul,
      ←F.actualLabelRatePrimitive_eq s zX,smul_comm (labelSelectedCutoff F.flow zX T Q p),
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hI),
      ENNReal.ofReal_mul (inv_nonneg.mpr hI.le)]
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    apply (mul_le_mul' (ENNReal.ofReal_le_ofReal (hψd τ hp)) le_rfl).trans_eq
    rw [div_eq_mul_inv,ENNReal.ofReal_mul hD,mul_assoc,norm_smul,Real.norm_eq_abs]
  · have hz := hψout τ hp
    change deriv ψ (labelReceiverTime F.flow zX T p)=0 at hz
    simp only [selectedMultiplierWeightDensity,labelWeight,hz,zero_mul,zero_smul,
      ContinuousLinearMap.id_apply,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma selected_bulk_weight_le (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) {a b : ℝ} {ψ : ℝ→ℝ}
    (hψ : ∀t,|ψ t|≤1) (hout : ∀t∉Icc a b,ψ t=0) (p : ℝ×Phase) :
    ENNReal.ofReal |ψ (labelReceiverTime α zX T p)| *
      selectedMultiplierBulkDensity s α zX T Q (fun _=>ContinuousLinearMap.id ℝ Vec) p ≤
    selectedMultiplierBulkDensity s α zX T Q
      ((Icc a b).indicator (fun _=>ContinuousLinearMap.id ℝ Vec)) p := by
  by_cases hp : labelReceiverTime α zX T p∈Icc a b
  · simp only [selectedMultiplierBulkDensity,indicator_of_mem hp,ContinuousLinearMap.id_apply]
    have hb : ENNReal.ofReal |ψ (labelReceiverTime α zX T p)|≤1 := by
      simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_ofReal (hψ (labelReceiverTime α zX T p)))
    exact (mul_le_mul' hb le_rfl).trans_eq (one_mul _)
  · rw [hout _ hp,abs_zero,ENNReal.ofReal_zero,zero_mul]
    exact bot_le

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.bulk_signed_cost_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ ψ : ℝ→ℝ, Measurable ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) →
      ENNReal.ofReal ‖∫p : ℝ×Phase,selectedMultiplierCosts s F.flow zX T
        (bulkSelection P M A w I) ψ (fun _=>ContinuousLinearMap.id ℝ Vec) (fun _=>0) p‖ ≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  obtain ⟨Cb,hCb,hbulk⟩ := hd.bulk_selected_family_uniform T₀
  obtain ⟨Cr,hCr,hrate⟩ := hd.bulk_rate_uniform T₀
  let C := D*Cr+Cb
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hbulk M A hM hA] with P hbu
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ hψ hψ1 hout hψd hdout
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let K := ∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖
  let Q := bulkSelection P M A w I
  let Id : ℝ→Vec→L[ℝ]Vec := fun _=>ContinuousLinearMap.id ℝ Vec
  have hId : ∀t∈Icc a b,‖Id t‖≤1 := fun _ _=>ContinuousLinearMap.norm_id_le
  have hB : 0≤B := by dsimp [B]; positivity
  have hbc := hbu hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ Id measurable_const hId
  have hrc := hrate M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP HZ hphysical hband Id measurable_const hId
  have hwc := (F.selected_weight_cost_bound hs.energyPrefix hT zX Q hI hD hψd hdout).trans
    (mul_le_mul' le_rfl hrc)
  have hbl := (lintegral_mono (selected_bulk_weight_le s F.flow zX T Q hψ1 hout)).trans hbc
  have hc := F.selectedMultiplierCosts_integral_bound hs.energyPrefix zX Q hψ
    (W:=Id) (W':=fun _=>0) measurable_const
  have hz : (∫⁻p : ℝ×Phase,selectedMultiplierMovingDensity s F.flow zX T Q ψ (fun _=>0) p)=0 := by
    simp only [selectedMultiplierMovingDensity,zero_apply,norm_zero,ENNReal.ofReal_zero,lintegral_zero]
  rw [hz,add_zero] at hc
  apply (hc.trans (add_le_add hwc hbl)).trans
  change ENNReal.ofReal D*ENNReal.ofReal (Cr*B)+(ENNReal.ofReal (Cb*B)+ENNReal.ofReal (Cb*w^(-1/2:ℝ))*K)≤_
  rw [←ENNReal.ofReal_mul hD,←add_assoc,←ENNReal.ofReal_add (by positivity) (by positivity)]
  have he : D*(Cr*B)+Cb*B=C*B := by dsimp [C]; ring
  rw [he]
  exact add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [mul_nonneg hD hCr]) (Real.rpow_nonneg (zero_le_one.trans hw) _))) le_rfl)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BulkTestWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma bounded_supported_test_mass {a b T : ℝ} {ψ : ℝ→ℝ}
    (hab : a≤b) (hψ : Continuous ψ) (hψ1 : ∀t,|ψ t|≤1)
    (hout : ∀t∉Icc a b,ψ t=0) : (∫t in Ioo (0:ℝ) T,|ψ t|)≤b-a := by
  have hs : tsupport ψ⊆Icc a b := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra hn
    exact ht (hout t hn)
  have hc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ψ) hs
  have hi : Integrable ψ := hψ.integrable_of_hasCompactSupport hc
  have hone : Integrable ((Icc a b).indicator (fun _ : ℝ=>(1:ℝ))) :=
    (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  calc
    _≤∫t : ℝ,|ψ t| := setIntegral_le_integral hi.norm (ae_of_all _ (fun t=>abs_nonneg _))
    _≤∫t : ℝ,(Icc a b).indicator (fun _ : ℝ=>(1:ℝ)) t := by
      apply integral_mono hi.norm hone
      intro t
      by_cases ht : t∈Icc a b
      · rw [indicator_of_mem ht]; exact hψ1 t
      · simp [indicator_of_notMem ht,hout t ht]
    _=b-a := by rw [integral_indicator measurableSet_Icc, integral_const]; simp [hab]

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma ofReal_norm_three_add (u v w : Vec) :
    ENNReal.ofReal ‖u+v+w‖≤ENNReal.ofReal ‖u‖+ENNReal.ofReal ‖v‖+ENNReal.ofReal ‖w‖ := by
  rw [←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ←ENNReal.ofReal_add (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))

lemma Admissible.selected_force_residual_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal ((4*Real.pi)⁻¹) *
        (ENNReal.ofReal ‖∫p : ℝ×Phase,unselectedLabelSignedForce s F.flow zX T
          (bulkSelection P M A w I) ψ p‖+
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) := by
  obtain ⟨Cb,hCb,hcost⟩ := hd.bulk_signed_cost_uniform T₀ D hD
  obtain ⟨Ci,hCi,hinit⟩ := selectedInitialKernel_integrable_bound hd.1.continuous hd.2.1 hd.2.2.1
  let C := Ci*(max 0 T₀)+Cb
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hcost M A hM hA] with P hco
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let K := ∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖
  let Q := bulkSelection P M A w I
  let Id : ℝ→Vec→L[ℝ]Vec := fun _=>ContinuousLinearMap.id ℝ Vec
  have hB : 0≤B := by dsimp [B]; positivity
  have hIB : I≤B := by
    have hi : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I]
    calc
      I≤Real.sqrt I := hi
      _≤P*Real.sqrt I := le_mul_of_one_le_left (Real.sqrt_nonneg I) hP
      _≤B := le_add_of_nonneg_right (by positivity)
  have hc := hco hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ hψ.continuous.measurable hψ1 hout hψd hdout
  have hdata : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
  have hi := (hinit s.E s.B T F zX Q ψ Id 1 hT zero_le_one hψ.continuous.continuousOn
    continuous_const.continuousOn (fun _ _=>ContinuousLinearMap.norm_id_le)).2
  rw [mul_one] at hi
  have hmass := (bounded_supported_test_mass hab hψ.continuous hψ1 hout (T:=T)).trans hJI
  have hi' : ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ Id z‖≤Ci*(max 0 T₀)*B := by
    rw [hdata]
    apply hi.trans
    apply (mul_le_mul_of_nonneg_left hmass (mul_nonneg hCi hT)).trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (hTT.trans (le_max_right _ _)) hCi
    · exact hIB
    · exact hI.le
    · positivity
  have he := hs.selected_multiplier_decomposition hT F zX Q hψ (fun t _=>hψ1 t) hψT
    (W:=Id) (W':=fun _=>0) continuous_const continuous_const (fun t _=>hasDerivAt_const t _)
  simp only [Id,ContinuousLinearMap.id_apply] at he
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)),
    ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹)]
  apply mul_le_mul' le_rfl
  have hn := ofReal_norm_three_add
    (∫p : ℝ×Phase,unselectedLabelSignedForce s F.flow zX T Q ψ p)
    (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ Id z)
    (∫p : ℝ×Phase,selectedMultiplierCosts s F.flow zX T Q ψ Id (fun _=>0) p)
  apply (hn.trans (add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hi')) hc)).trans
  have heq : ENNReal.ofReal (Ci*(max 0 T₀)*B)+ENNReal.ofReal (Cb*B)=ENNReal.ofReal (C*B) := by
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    dsimp [C]
    ring
  change _≤ENNReal.ofReal ‖∫p : ℝ×Phase,unselectedLabelSignedForce s F.flow zX T Q ψ p‖+
    ENNReal.ofReal (C*B)+ENNReal.ofReal (C*w^(-1/2:ℝ))*K
  rw [add_assoc,←add_assoc (ENNReal.ofReal (Ci*(max 0 T₀)*B)),heq,←add_assoc]
  apply add_le_add le_rfl
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [mul_nonneg hCi (le_max_left (0:ℝ) T₀)])
    (Real.rpow_nonneg (zero_le_one.trans hw) _)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BulkReceiverResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.force_bulk_receiver_residual_uniform_oai {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ) (Lψ : NNReal), LipschitzWith Lψ ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) → ψ T=0 →
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ t •
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal ((4*Real.pi)⁻¹) *
        (ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) := by
  obtain ⟨Cs,hCs,hselected⟩ := hd.selected_force_residual_uniform T₀ D hD
  obtain ⟨Cu,hCu,hunselected⟩ := hd.unselected_label_uniform T₀
  refine ⟨Cu+Cs,add_nonneg hCu hCs,?_⟩
  intro M A hM hA
  filter_upwards [hselected M A hM (zero_lt_one.trans_le hA),hunselected M A hM hA] with P hsel hun
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  have hc := hsel hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ Lψ hψ hψ1 hout hψd hdout hψT
  have hu := hun hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ hψ.continuous.measurable hψ1 hout
  apply hc.trans
  apply mul_le_mul' le_rfl
  apply add_le_add
  · apply (add_le_add hu le_rfl).trans_eq
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  · apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCu)
      (Real.rpow_nonneg (zero_le_one.trans hw) _)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.force_bulk_receiver_residual_uniform_oai := @OAI.RVM.Admissible.force_bulk_receiver_residual_uniform_oai
