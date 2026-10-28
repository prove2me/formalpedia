-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.physicalBin_magneticField
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:55:21.852543+00:00
-- url     : https://prove2.me/submissions/cf5dade5-95fb-4966-b9d6-f98b35fe004d

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

end RVM

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

end RVM

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

lemma PhaseFlowOn.arrivalVelocity_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    ContinuousAt (arrivalVelocity F.flow zX T) p :=
  (contDiff_velocity (k := 1)).continuous.continuousAt.comp
    (f := fun q => (F.flow zX (arrivalTime F.flow zX T q)).2)
    (F.arrivalFlow_continuousAt zX hp).snd

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

lemma measurableSet_dyadicWindow (k n : ℕ) : MeasurableSet {x : ℝ | DyadicWindow k n x} :=
  ((isClosed_le continuous_const (continuous_const.mul continuous_id)).inter
    (isClosed_le (continuous_const.mul continuous_id) continuous_const)).measurableSet

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RetardedSameTimeSeparation
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceCellLast
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma PhaseFlowOn.measurable_arrivalAngularSet {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k j : ℕ) :
    MeasurableSet (arrivalAngularSet F.flow zX T k j) := by
  classical
  let U := arrivalDomain F.flow zX T
  let b : ℝ × Vec → ℝ := fun p => Real.sqrt ((1-dot
    (arrivalDirection F.flow zX T p) (arrivalVelocity F.flow zX T p))/2)
  have hb : ContinuousOn b U := by
    intro p hp
    exact (((continuousAt_const.sub (continuous_dot.continuousAt.comp ((F.arrivalDirection_continuousAt zX hp).prodMk
      (F.arrivalVelocity_continuousAt zX hp)))).div_const 2).sqrt).continuousWithinAt
  have hm : Measurable (U.indicator b) := hb.measurable_piecewise continuousOn_const
    (F.isOpen_arrivalDomain zX).measurableSet
  have hopen : MeasurableSet {p | p∈U ∧ DyadicWindow k j (b p)} := by
    convert (F.isOpen_arrivalDomain zX).measurableSet.inter
      ((measurableSet_dyadicWindow k j).preimage hm) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    change (p∈U ∧ DyadicWindow k j (b p)) ↔
      (p∈U ∧ DyadicWindow k j (U.indicator b p))
    by_cases hp : p∈U <;> simp [hp]
  have hfinal : MeasurableSet (arrivalFinalDomain F.flow zX T) :=
    (measurable_fst (measurableSet_Ioo)).inter
      (measurableSet_eq_fun (measurable_fst.add (measurable_const.sub measurable_snd).norm) measurable_const)
  have hbfinal : Measurable (fun p : ℝ × Vec => Real.sqrt ((1-dot
      ((T-p.1)⁻¹ • ((F.flow zX T).1-p.2)) (velocity (F.flow zX T).2))/2)) := by
    unfold dot
    fun_prop
  exact hopen.union (hfinal.inter ((measurableSet_dyadicWindow k j).preimage hbfinal))

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

lemma continuous_prefixField {E : Field} {T : ℝ}
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec))) (hT : 0 ≤ T) :
    Continuous (prefixField E T) :=
  hE.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

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

lemma PhaseFlowOn.arrival_polar_mem {E B : Field} {T s r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T)
    (hr : r∈Ioo (0:ℝ) (T-s)) (n : Sphere) :
    (s,(F.flow zX (s+r)).1-r • n.1)∈arrivalDomain F.flow zX T := by
  have hn := sphere_norm n
  have hw : r • n.1∈receiverRadialDomain s T := by
    change 0<‖r • n.1‖ ∧ s+‖r • n.1‖<T
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,hn,mul_one]
    exact ⟨hr.1,by linarith [hr.2]⟩
  have him := F.receiver_image (Ioo_subset_Icc_self hs) zX
  have hy : receiverRadial F.flow zX s (r • n.1) ∈
      ball (F.flow zX T).1 (T-s)\{(F.flow zX s).1} := by
    rw [←him]
    exact mem_image_of_mem _ hw
  have he : receiverRadial F.flow zX s (r • n.1)=
      (F.flow zX (s+r)).1-r • n.1 := by
    simp only [receiverRadial,norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,hn,mul_one]
  rw [he] at hy
  refine ⟨hs,?_,?_⟩
  · have hh := hy.1
    rw [mem_ball,dist_eq_norm,norm_sub_rev] at hh
    linarith
  · exact fun hh=>hy.2 (mem_singleton_iff.mpr hh.symm)

lemma PhaseFlowOn.arrival_polar_time {E B : Field} {T s r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T)
    (hr : r∈Ioo (0:ℝ) (T-s)) (n : Sphere) :
    arrivalTime F.flow zX T (s,(F.flow zX (s+r)).1-r • n.1)=s+r := by
  have hd := F.arrival_polar_mem zX hs hr n
  have hl := F.arrivalLabel_mem zX hd
  have hh : F.flow (arrivalLabel F.flow (s,(F.flow zX (s+r)).1-r • n.1)).2 s =
      ((F.flow zX (s+r)).1-r • n.1,0) :=
    F.flow_inversePhase (Ioo_subset_Icc_self hs) _
  symm
  apply F.branch_unique (s:=s) zX _ hl.1 ⟨by linarith [hr.1],by linarith [hr.2]⟩
  rw [hh]
  simp only [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,
    sphere_norm,mul_one]
  ring

lemma PhaseFlowOn.arrival_polar_radius {E B : Field} {T s r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T)
    (hr : r∈Ioo (0:ℝ) (T-s)) (n : Sphere) :
    arrivalRadius F.flow zX T (s,(F.flow zX (s+r)).1-r • n.1)=r := by
  rw [arrivalRadius,F.arrival_polar_time zX hs hr n]
  ring

lemma PhaseFlowOn.arrival_polar_direction {E B : Field} {T s r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T)
    (hr : r∈Ioo (0:ℝ) (T-s)) (n : Sphere) :
    arrivalDirection F.flow zX T (s,(F.flow zX (s+r)).1-r • n.1)=n.1 := by
  rw [arrivalDirection,F.arrival_polar_radius zX hs hr n,F.arrival_polar_time zX hs hr n]
  simp only [sub_sub_cancel,smul_smul,inv_mul_cancel₀ (ne_of_gt hr.1),one_smul]

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


lemma lintegral_add_left_Ioo (s T : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r)) = ∫⁻ t in Ioo s T, f t := by
  rw [← lintegral_indicator measurableSet_Ioo,← lintegral_indicator measurableSet_Ioo]
  calc
    _ = ∫⁻ r : ℝ, (Ioo s T).indicator f (s+r) := by
      apply lintegral_congr
      intro r
      have he : r∈Ioo 0 (T-s) ↔ s+r∈Ioo s T := by
        simp only [mem_Ioo]
        constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
      by_cases hr : r∈Ioo 0 (T-s)
      · rw [indicator_of_mem hr,indicator_of_mem (he.mp hr)]
      · rw [indicator_of_notMem hr,indicator_of_notMem (mt he.mpr hr)]
    _ = _ := lintegral_add_left_eq_self _ _

lemma lintegral_retarded_triangle (T : ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r,s)) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t, f (t,s) := by
  let H : Set (ℝ × ℝ) := {p | 0<p.1 ∧ p.1<p.2 ∧ p.2<T}
  let g : ℝ × ℝ → ℝ≥0∞ := H.indicator (fun p => f (p.2,p.1))
  have hH : MeasurableSet H :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hg : Measurable g := (hf.comp (measurable_snd.prodMk measurable_fst)).indicator hH
  calc
    _ = ∫⁻ s : ℝ, ∫⁻ t : ℝ, g (s,t) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro s
      by_cases hs : s∈Ioo 0 T
      · rw [indicator_of_mem hs,lintegral_add_left_Ioo s T (fun t => f (t,s)),← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro t
        have he : (s,t)∈H ↔ t∈Ioo s T := by simp only [H,mem_ofPred_eq,mem_Ioo,hs.1,true_and]
        by_cases ht : t∈Ioo s T
        · simp only [g,indicator_of_mem ht,indicator_of_mem (he.mpr ht)]
        · simp only [g,indicator_of_notMem ht,indicator_of_notMem (mt he.mp ht)]
      · rw [indicator_of_notMem hs]
        symm
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro t
        exact indicator_of_notMem (fun hh => hs ⟨hh.1,hh.2.1.trans hh.2.2⟩) _
    _ = ∫⁻ t : ℝ, ∫⁻ s : ℝ, g (s,t) := lintegral_lintegral_swap hg.aemeasurable
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro t
      by_cases ht : t∈Ioo 0 T
      · rw [indicator_of_mem ht,← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro s
        have he : (s,t)∈H ↔ s∈Ioo 0 t := by simp only [H,mem_ofPred_eq,mem_Ioo,ht.2,and_true]
        by_cases hs : s∈Ioo 0 t
        · simp only [g,indicator_of_mem hs,indicator_of_mem (he.mpr hs)]
        · simp only [g,indicator_of_notMem hs,indicator_of_notMem (mt he.mp hs)]
      · rw [indicator_of_notMem ht]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro s
        exact indicator_of_notMem (fun hh => ht ⟨hh.1.trans hh.2.1,hh.2.2⟩) _

lemma lintegral_retarded_triangle_parameter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (T : ℝ) {f : ℝ × ℝ × Ω → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioo (0:ℝ) T, ∫⁻ n : Ω, ∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r,s,n) ∂volume ∂μ) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t, ∫⁻ n : Ω, f (t,s,n) ∂μ := by
  have hm : Measurable (fun p : (ℝ × ℝ) × Ω => f (p.1.1,p.1.2,p.2)) :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  calc
    _ = ∫⁻ s in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) (T-s), ∫⁻ n : Ω, f (s+r,s,n) ∂μ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro s _
      have hg : Measurable (fun p : Ω × ℝ => f (s+p.2,s,p.1)) :=
        hf.comp ((measurable_const.add measurable_snd).prodMk
          (measurable_const.prodMk measurable_fst))
      exact lintegral_lintegral_swap hg.aemeasurable
    _ = _ := lintegral_retarded_triangle T hm.lintegral_prod_right'

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeEulerianIntegrand
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
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma physicalBin_integral_eq_triangle {V : ℝ → Vec} (hV : Measurable V)
    (C : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) {T : ℝ} (hJT : J⊆Icc 0 T)
    {g : ConeCoordinate → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z,g z ∂physicalBinMeasure V C J) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) t, ∫⁻ n : Sphere,
        (physicalBinBase V C J).indicator g (t,r,n) ∂sphereMeasure := by
  have hbase := measurableSet_physicalBinBase hV C hJ
  unfold physicalBinMeasure
  rw [← lintegral_indicator hbase,lintegral_prod _ (hg.indicator hbase).aemeasurable]
  simp_rw [restrict_Ioo_eq_restrict_Icc]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  have hm : Measurable (fun p : ℝ × Sphere => (physicalBinBase V C J).indicator g (t,p)) :=
    (hg.indicator hbase).comp (measurable_const.prodMk measurable_id)
  by_cases ht : t∈Icc 0 T
  · rw [indicator_of_mem ht,lintegral_prod _ hm.aemeasurable,← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro r
    by_cases hr : r∈Icc 0 t
    · rw [indicator_of_mem hr]
    · rw [indicator_of_notMem hr]
      apply lintegral_eq_zero_of_ae_eq_zero
      apply ae_of_all
      intro n
      exact indicator_of_notMem (fun hz => hr hz.2.1) _
  · rw [indicator_of_notMem ht]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro p
    exact indicator_of_notMem (fun hz => ht (hJT hz.1)) _

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalProjectedRemainderDensity
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

lemma measurable_coneFoot {X : ℝ→Vec} (hX : Measurable X) : Measurable (coneFoot X) := by
  exact (measurable_fst.comp measurable_snd).prodMk
    ((hX.comp measurable_fst).sub ((measurable_fst.sub (measurable_fst.comp measurable_snd)).smul
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))))

lemma measurable_coneReceiverJacobian {V : ℝ→Vec} (hV : Measurable V) :
    Measurable (coneReceiverJacobian V) := by
  exact ((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2).mul
    (measurable_const.sub (continuous_dot.measurable.comp
      ((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).prodMk
        ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst)))))

lemma PhaseFlowOn.physicalBin_spatial_budget {s : Solution} {T a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) (k j : ℕ) (hJ : Icc a b⊆Icc 0 T)
    (hangle : ∀D∈Icc C.Dmin C.Dmax,DyadicWindow k j (Real.sqrt (D/2)))
    {g : ℝ×Vec→ℝ≥0∞} (hg : Measurable g) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    (∫⁻ z : ConeCoordinate,ENNReal.ofReal (coneReceiverJacobian V z)*g (coneFoot X z)
      ∂physicalBinMeasure V C (Icc a b)) ≤
    ∫⁻ σ in Icc (max 0 (a-C.rmax)) (min T (b-C.rmin)),∫⁻ y : Vec,
      (arrivalAngularSet F.flow zX T k j).indicator g (σ,y) := by
  classical
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let J' := Icc (max 0 (a-C.rmax)) (min T (b-C.rmin))
  let U := arrivalAngularSet F.flow zX T k j
  let H : Set (ℝ×Vec) := {p | p.1∈J'} ∩ U
  let G := H.indicator g
  have hU : MeasurableSet U := F.measurable_arrivalAngularSet zX k j
  have hH : MeasurableSet H := (measurableSet_Icc.preimage measurable_fst).inter hU
  have hG : Measurable G := hg.indicator hH
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  let K : ConeCoordinate→ℝ≥0∞ := fun z=>ENNReal.ofReal (coneReceiverJacobian V z)*g (coneFoot X z)
  have hK : Measurable K := (measurable_coneReceiverJacobian hV).ennreal_ofReal.mul
    (hg.comp (measurable_coneFoot hX))
  change (∫⁻z,K z ∂physicalBinMeasure V C (Icc a b))≤_
  rw [physicalBin_integral_eq_triangle hV C measurableSet_Icc hJ hK,
    ←lintegral_retarded_triangle_parameter sphereMeasure T
      (hK.indicator (measurableSet_physicalBinBase hV C measurableSet_Icc))]
  calc
    _ ≤ ∫⁻σ in Ioo (0:ℝ) T,∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),
        ENNReal.ofReal (r^2*(1-dot n.1 (velocity (F.flow zX (σ+r)).2)))*
          G (σ,(F.flow zX (σ+r)).1-r • n.1) ∂volume ∂sphereMeasure := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro σ hσ
      apply lintegral_mono
      intro n
      apply setLIntegral_mono' measurableSet_Ioo
      intro r hr
      have ht : σ+r∈Icc 0 T := ⟨by linarith [hσ.1,hr.1],by linarith [hr.2]⟩
      by_cases hz : (σ+r,σ,n)∈physicalBinBase V C (Icc a b)
      · rw [indicator_of_mem hz]
        have hσJ : σ∈J' := by
          refine ⟨max_le hσ.1.le ?_,le_min hσ.2.le ?_⟩
          · linarith [hz.1.1,hz.2.2.1.2]
          · linarith [hz.1.2,hz.2.2.1.1]
        have hdom := F.arrival_polar_mem zX hσ hr n
        have htime := F.arrival_polar_time zX hσ hr n
        have hdir := F.arrival_polar_direction zX hσ hr n
        have hmem : (σ,(F.flow zX (σ+r)).1-r • n.1)∈U := by
          apply Or.inl
          refine ⟨hdom,?_⟩
          rw [hdir,arrivalVelocity,htime]
          apply hangle
          simpa only [V,prefixFlow,prefixClamp_eq ht] using hz.2.2.2.2
        rw [show G (σ,(F.flow zX (σ+r)).1-r • n.1)=
          g (σ,(F.flow zX (σ+r)).1-r • n.1) from indicator_of_mem (show (σ,(F.flow zX (σ+r)).1-r • n.1)∈H from ⟨hσJ,hmem⟩) g]
        exact le_of_eq (by simp only [K,coneReceiverJacobian,coneFoot,X,V,prefixFlow,
          prefixClamp_eq ht,add_sub_cancel_left])
      · rw [indicator_of_notMem hz]
        exact zero_le
    _ = ∫⁻σ in Ioo (0:ℝ) T,∫⁻y in ball (F.flow zX T).1 (T-σ),G (σ,y) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      exact (F.receiver_polar_lintegral (Ioo_subset_Icc_self hσ) zX
        (hG.comp (measurable_const.prodMk measurable_id))).symm
    _ ≤ ∫⁻σ in Ioo (0:ℝ) T,∫⁻y : Vec,G (σ,y) := by
      apply lintegral_mono
      intro σ
      exact setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻σ : ℝ,∫⁻y : Vec,G (σ,y) := setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [←lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro σ
      by_cases hσ : σ∈J'
      · rw [indicator_of_mem hσ]
        apply lintegral_congr
        intro y
        change G (σ,y)=U.indicator g (σ,y)
        by_cases hy : (σ,y)∈U
        · simp only [G,indicator_of_mem (show (σ,y)∈H from ⟨hσ,hy⟩),indicator_of_mem hy]
        · simp only [G,indicator_of_notMem (show (σ,y)∉H from fun h=>hy h.2),indicator_of_notMem hy]
      · rw [indicator_of_notMem hσ]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro y
        exact indicator_of_notMem (show (σ,y)∉H from fun h=>hσ h.1) g

lemma PhaseFlowOn.physicalBin_magneticField_oai {s : Solution} {T a b I φ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) (k j : ℕ) (hJ : Icc a b⊆Icc 0 T)
    (hI : 0<I) (hD : φ^2/2≤C.Dmin)
    (hangle : ∀D∈Icc C.Dmin C.Dmax,DyadicWindow k j (Real.sqrt (D/2))) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    (∫⁻z : ConeCoordinate,ENNReal.ofReal ((z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2)
      ∂physicalBinMeasure V C (Icc a b)) ≤
    ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
      (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j := by
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let J' := Icc (max 0 (a-C.rmax)) (min T (b-C.rmin))
  have hclip : J'⊆Icc 0 T := fun _ h=>⟨(le_max_left _ _).trans h.1,h.2.trans (min_le_left _ _)⟩
  let g : ℝ×Vec→ℝ≥0∞ := fun p=>ENNReal.ofReal (‖prefixField s.B T p‖^2)
  have hg : Measurable g := ((continuous_prefixField hs.B_smooth.continuousOn hT).measurable.norm.pow_const 2).ennreal_ofReal
  have ho := F.physicalBin_spatial_budget hs hT zX C k j hJ hangle hg
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hsp : (∫⁻σ in J',∫⁻y : Vec,(arrivalAngularSet F.flow zX T k j).indicator g (σ,y))=
      ENNReal.ofReal I*magneticFieldBudget s F.flow zX T k
        (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j := by
    rw [magneticFieldBudget,←mul_assoc,ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hI).ne'
      ENNReal.ofReal_ne_top,one_mul]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro σ hσ
    apply lintegral_congr
    intro y
    by_cases hy : (σ,y)∈arrivalAngularSet F.flow zX T k j
    · simp only [indicator_of_mem hy,g,prefixField,prefixClamp_eq (hclip hσ)]
    · simp only [indicator_of_notMem hy]
  change (∫⁻z : ConeCoordinate,ENNReal.ofReal ((z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2)
    ∂physicalBinMeasure V C (Icc a b))≤_
  calc
    _ ≤ ∫⁻z : ConeCoordinate,(2:ℝ≥0∞)*(ENNReal.ofReal (coneReceiverJacobian V z)*g (coneFoot X z))
        ∂physicalBinMeasure V C (Icc a b) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable C measurableSet_Icc)] with z hz
      have hDz : φ^2≤2*(1-dot z.2.2.1 (velocity (V z.1))) := by
        linarith [hD.trans hz.2.2.2.2.1]
      have hpos : 0 ≤ coneReceiverJacobian V z :=
        mul_nonneg (sq_nonneg _) (cone_denom_pos _ _ (sphere_norm _)).le
      rw [←ENNReal.ofReal_mul hpos]
      calc
        _ ≤ ENNReal.ofReal (2*(coneReceiverJacobian V z*‖prefixField s.B T (coneFoot X z)‖^2)) := by
          apply ENNReal.ofReal_le_ofReal
          change (z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2≤
            2*((z.1-z.2.1)^2*(1-dot z.2.2.1 (velocity (V z.1)))*prefixConeMagnetic s T X z^2)
          nlinarith [mul_le_mul_of_nonneg_left hDz (mul_nonneg (sq_nonneg (z.1-z.2.1))
            (sq_nonneg (prefixConeMagnetic s T X z)))]
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]; norm_num
    _ = (2:ℝ≥0∞)*(∫⁻z : ConeCoordinate,ENNReal.ofReal (coneReceiverJacobian V z)*g (coneFoot X z)
        ∂physicalBinMeasure V C (Icc a b)) := lintegral_const_mul' _ _ (by norm_num)
    _ ≤ (2:ℝ≥0∞)*(ENNReal.ofReal I*magneticFieldBudget s F.flow zX T k
        (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j) :=
      mul_le_mul' le_rfl (ho.trans_eq hsp)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]; norm_num; ring

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

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.physicalBin_magneticField_oai := @OAI.RVM.PhaseFlowOn.physicalBin_magneticField_oai
