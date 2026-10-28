-- Prove2me | solution 1 for OAI.RVM.Admissible.bulk_selected_family_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:30:43.865587+00:00
-- url     : https://prove2.me/submissions/40e26e2b-fe37-46fe-bb16-f959f65f2a7a

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_bulk_geometry_uniform
import Theorems.Thm_OAI_RVM_Admissible_bulk_remainder_uniform
import Theorems.Thm_OAI_RVM_Admissible_bulk_source_uniform
import Theorems.Thm_OAI_RVM_Admissible_representative_receiver_envelope
import Theorems.Thm_OAI_RVM_PhaseFlowOn_bulkReceiver_selected_sum
import Theorems.Thm_OAI_RVM_PhaseFlowOn_cutoff_label_integral_split
import Theorems.Thm_OAI_RVM_PhaseFlowOn_partialCutoffLabelCost_triangle
import Theorems.Thm_OAI_RVM_PhaseFlowOn_selectedConeTriangle_norm_transfer

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

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

lemma unsafe_selected_actual_margins
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z + c = 1) (hΔ : Δ = (α + b + y + H) / 100000)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hfar₁ : H ≤ 2*c → b < H/2 - α + Δ)
    (hfar₂ : 2*c < H → b < H - c - α + Δ)
    (hu₁ : 2*H/3 + z/6 - Δ/3 < b) :
    0 < z ∧ Δ < z/1000 ∧ 2*c < H ∧
      (496/1000 : ℝ)*z + 3*(α+c) < H ∧
      (35/10 : ℝ)*α + (15/10 : ℝ)*c + 2*y < (753/1000 : ℝ)*z ∧
      (500/751 : ℝ) < z ∧
      y < (377/1000 : ℝ)*z - (175/100 : ℝ)*α - (75/100 : ℝ)*c ∧
      (623/1000 : ℝ) < z-y ∧ (623/1000 : ℝ) < 1-α-y := by
  have hb : b < H - α + Δ := by
    by_cases hh : H ≤ 2*c
    · have h := hfar₁ hh
      linarith
    · have h := hfar₂ (lt_of_not_ge hh)
      linarith
  have hdsmall : 99995*Δ < 4*z := by linarith
  have hzpos : 0 < z := by
    by_contra hh
    have hz0 : z = 0 := le_antisymm (le_of_not_gt hh) hz
    subst z
    have hdneg : Δ < 0 := by linarith
    linarith
  have hd : Δ < z/1000 := by linarith
  have hh : 2*c < H := by
    by_contra hh
    have hf := hfar₁ (le_of_not_gt hh)
    linarith
  have hf := hfar₂ hh
  have hlow : (496/1000 : ℝ)*z + 3*(α+c) < H := by linarith
  have hm : (35/10 : ℝ)*α + (15/10 : ℝ)*c + 2*y < (753/1000 : ℝ)*z := by
    linarith
  refine ⟨hzpos, hd, hh, hlow, hm, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma unsafe_selected_improved_window
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z + c = 1) (hΔ : Δ = (α + b + y + H) / 100000)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hfar₁ : H ≤ 2*c → b < H/2 - α + Δ)
    (hfar₂ : 2*c < H → b < H - c - α + Δ)
    (hu₁ : 2*H/3 + z/6 - Δ/3 < b)
    (hu₂ : b < H + 2*y - z/2 + Δ)
    (hactual : b < H/2 - min α c + y + (2/1000 : ℝ)*z) :
    (9/10 : ℝ) < z ∧ (895/1000 : ℝ) < 1-α ∧
      (16/100 : ℝ)*max z (1-α) < y ∧ y < (49/100 : ℝ)*min z (1-α) := by
  obtain ⟨hzpos, hd, _, hlow, hm, _, hym, _, _⟩ :=
    unsafe_selected_actual_margins hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁
  have hm0 : 0 ≤ min α c := le_min hα hc
  have hHup : H < (81/100 : ℝ)*z := by linarith
  have hac : α+c < (105/1000 : ℝ)*z := by linarith
  have hz9 : (9/10 : ℝ) < z := by linarith
  have hp : (895/1000 : ℝ) < 1-α := by linarith
  have hy19 : (19/100 : ℝ)*z < y := by linarith
  refine ⟨hz9, hp, ?_, ?_⟩
  · rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 16/100), max_lt_iff]
    constructor <;> linarith
  · rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 49/100), lt_min_iff]
    constructor <;> linarith

lemma unsafe_selected_improved_contradiction
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 < z) (hc : 0 ≤ c)
    (hsmall : Δ < z/1000)
    (hlow : (496/1000 : ℝ)*z + 3*(α+c) < H)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hu : 2*H/3 + z/6 - Δ/3 < b)
    (himproved : b < H/2 - min α c + (29/50 : ℝ)*y + Δ) : False := by
  have hm : 0 ≤ min α c := le_min hα hc
  linarith

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
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_support : tsupport dyadicBump ⊆ Icc (1/2) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    exact hx (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hx (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionWeight
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

namespace RVM

lemma max_growth_bound {P c H E : ℝ} (hP : 1 < P)
    (hHc : 2*c ≤ H) (hE : 2*c ≤ E) :
    max 1 (max (P^(-2*c)*P^E) (P^(-H)*P^E)) ≤ P^(-2*c+E) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  refine max_le ?_ (max_le ?_ ?_)
  · exact Real.one_le_rpow hP.le (by linarith)
  · rw [← Real.rpow_add hP0]
  · rw [← Real.rpow_add hP0]
    exact (Real.rpow_le_rpow_left_iff hP).mpr (by linarith)

lemma selected_coefficient_power_table
    {P C₀ α z c b y H Δ k Λ : ℝ} (hP : 1 < P)
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z+c=1) (hΔ : Δ=(α+b+y+H)/100000)
    (hnear : 2*α+H/2+2*y < z+Δ)
    (hk : 0 ≤ k) (hfar : P^(α+b-H-Δ) < k)
    (henergy : k^2 ≤ P^(-min (2*c) H))
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hΛ : (66/100 : ℝ) < z → Λ^2 ≤ P^(2*max α c+2*y+2*z/1000))
    (hactual : C₀ < P^(min z (1-α)-y) →
      k^2 ≤ P^(-H)*max 1 (max (P^(-2*c)*Λ^2) (P^(-H)*Λ^2)))
    (himproved : (7/10 : ℝ) ≤ z → (7/10 : ℝ) ≤ 1-α →
      (16/100 : ℝ)*max z (1-α) ≤ y →
      y ≤ (49/100 : ℝ)*min z (1-α) →
      k^2 ≤ P^(-H+(29/25 : ℝ)*y)*
        max 1 (max (P^(-2*c)*P^(2*max α c)) (P^(-H)*P^(2*max α c)))) :
    min (P^(-z-2*H+3*b)) (P^(-z-b+H+2*y)) ≤ P^(-z/2-Δ) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hkfar : P^((α+b-H-Δ)*2) < k^2 := by
    rw [Real.rpow_mul hP0.le, Real.rpow_two]
    exact (sq_lt_sq₀ (Real.rpow_nonneg hP0.le _) hk).mpr hfar
  have hfarE := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le henergy)
  have hfar₁ : H ≤ 2*c → b < H/2-α+Δ := by
    intro hh
    rw [min_eq_right hh] at hfarE
    linarith
  have hfar₂ : 2*c < H → b < H-c-α+Δ := by
    intro hh
    rw [min_eq_left hh.le] at hfarE
    linarith
  by_contra hbad
  have hb' := lt_of_not_ge hbad
  have hl := (Real.rpow_lt_rpow_left_iff hP).mp
    (hb'.trans_le (min_le_left _ _))
  have hr := (Real.rpow_lt_rpow_left_iff hP).mp
    (hb'.trans_le (min_le_right _ _))
  have hu₁ : 2*H/3+z/6-Δ/3 < b := by linarith
  have hu₂ : b < H+2*y-z/2+Δ := by linarith
  obtain ⟨hzp,hd,hHc,hlow,_,hzlarge,_,hm₁,hm₂⟩ :=
    unsafe_selected_actual_margins hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁
  have ham : (623/1000 : ℝ) < min z (1-α)-y := by
    rw [← min_sub_sub_right]; exact lt_min hm₁ hm₂
  have hC : C₀ < P^(min z (1-α)-y) :=
    hC₀.trans_lt ((Real.rpow_lt_rpow_left_iff hP).mpr (by linarith))
  have hΛ' := hΛ (by linarith)
  have hmax : max 1 (max (P^(-2*c)*Λ^2) (P^(-H)*Λ^2)) ≤
      P^(-2*c+(2*max α c+2*y+2*z/1000)) := by
    calc
      _ ≤ max 1 (max (P^(-2*c)*P^(2*max α c+2*y+2*z/1000))
          (P^(-H)*P^(2*max α c+2*y+2*z/1000))) := by gcongr
      _ ≤ _ := max_growth_bound hP hHc.le (by have := le_max_right α c; linarith)
  have hka := (hactual hC).trans
    (mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg hP0.le _))
  rw [← Real.rpow_add hP0] at hka
  have hfa := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le hka)
  have hmaxmin : max α c + min α c = α+c := max_add_min α c
  have hactual' : b < H/2-min α c+y+(2/1000 : ℝ)*z := by linarith
  obtain ⟨hz',hpa',hyl,hyu⟩ := unsafe_selected_improved_window
    hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁ hu₂ hactual'
  have hki := (himproved (by linarith) (by linarith) hyl.le hyu.le).trans
    (mul_le_mul_of_nonneg_left
      (max_growth_bound hP hHc.le (by have := le_max_right α c; linarith))
      (Real.rpow_nonneg hP0.le _))
  rw [← Real.rpow_add hP0] at hki
  have hfi := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le hki)
  have himproved' : b < H/2-min α c+(29/50 : ℝ)*y+Δ := by linarith
  exact unsafe_selected_improved_contradiction hα hzp hc hd hlow hnear hu₁ himproved'

lemma eventually_selection_constants (C₀ C₁ M A : ℝ)
    (hC₁ : 0 ≤ C₁) (hA : 0 ≤ A) :
    ∀ᶠ P : ℝ in atTop, 1 < P ∧ C₀ ≤ P^(3/10 : ℝ) ∧
      C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ) := by
  have he : (0 : ℝ) < 66/100000 := by norm_num
  have hconst : (fun _ : ℝ => C₁*M) =o[atTop]
      (fun P : ℝ => P^(66/100000 : ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop _).comp_tendsto (tendsto_rpow_atTop he)
  have hsqrt := (isLittleO_log_rpow_rpow_atTop (1/2 : ℝ) he).const_mul_left
    (C₁*Real.sqrt (2*A))
  have hsum := hconst.add hsqrt
  filter_upwards [hsum.bound (by norm_num : (0 : ℝ) < 1),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/10)).eventually_ge_atTop C₀,
    eventually_ge_atTop (2 : ℝ)] with P hsum hC₀ hP
  have hP0 : 0 < P := by linarith
  refine ⟨by linarith,hC₀,?_⟩
  have hlog : Real.log (2+P) ≤ 2*Real.log P := by
    calc
      _ ≤ Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hs : Real.sqrt (A*Real.log (2+P)) ≤
      Real.sqrt (2*A)*Real.sqrt (Real.log P) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*A)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hb : C₁*M+(C₁*Real.sqrt (2*A))*Real.log P^(1/2 : ℝ) ≤ P^(66/100000 : ℝ) := by
    have := (le_abs_self (C₁*M+(C₁*Real.sqrt (2*A))*Real.log P^(1/2 : ℝ))).trans hsum
    simpa only [Real.norm_eq_abs, one_mul, abs_of_pos (Real.rpow_pos_of_pos hP0 _)] using this
  rw [← Real.sqrt_eq_rpow] at hb
  nlinarith

lemma div_stabilityLength (P C₁ M A p w φ t : ℝ) :
    t/stabilityLength P C₁ M A p w φ =
      t*(stabilityRate P C₁ M A p w φ)^2 := by
  simp [stabilityLength, div_eq_mul_inv, inv_pow]

lemma sqrt_div_le_small_denominator {a x : ℝ} (ha : 0 ≤ a)
    (hx : 0 < x) (hx₁ : x ≤ 1) : Real.sqrt (a/x) ≤ Real.sqrt a/x := by
  rw [Real.sqrt_div ha]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg a) hx
    (Real.le_sqrt_self_iff.mpr hx₁)

lemma rpow_min_exponent {P a b : ℝ} (hP : 1 < P) :
    min (P^a) (P^b) = P^(min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left ((Real.rpow_le_rpow_left_iff hP).mpr h)]
  · rw [min_eq_right h, min_eq_right ((Real.rpow_le_rpow_left_iff hP).mpr h)]

lemma sqrt_rpow_base {P : ℝ} (hP : 0 ≤ P) (a : ℝ) :
    Real.sqrt (P^a) = P^(a/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP]
  congr 1
  ring

lemma stabilityRate_power_bound {P C₁ M A p w φ α z c y : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hA : 0 ≤ A)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y))
    (hφ₁ : φ ≤ 1) (hzc : z+c=1) (hz : (66/100 : ℝ) < z)
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ)) :
    stabilityRate P C₁ M A p w φ ≤ P^(max α c+y+z/1000) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hφ0 : 0 < φ := hφ ▸ Real.rpow_pos_of_pos hP0 _
  have hm : min p w = P^(1-max α c) := by
    rw [hp,hw,rpow_min_exponent hP]
    congr 1
    rcases le_total α c with hh | hh
    · rw [max_eq_right hh,min_eq_right (by linarith)]; linarith
    · rw [max_eq_left hh,min_eq_left (by linarith)]
  have hm0 : 0 < min p w := hm ▸ Real.rpow_pos_of_pos hP0 _
  have hAL : 0 ≤ A*Real.log (2+P) := mul_nonneg hA (Real.log_nonneg (by linarith))
  have hs := sqrt_div_le_small_denominator hAL hφ0 hφ₁
  have hfactor : P/min p w/φ = P^(max α c+y) := by
    rw [hm,hφ]
    nth_rw 1 [← Real.rpow_one P]
    rw [← Real.rpow_sub hP0,← Real.rpow_sub hP0]
    congr 1
    ring
  calc
    _ ≤ C₁*(P/min p w)*(M/φ+Real.sqrt (A*Real.log (2+P))/φ) := by
      unfold stabilityRate
      gcongr
    _ = (C₁*(M+Real.sqrt (A*Real.log (2+P)))) * P^(max α c+y) := by
      rw [← hfactor]
      ring
    _ ≤ P^(66/100000 : ℝ) * P^(max α c+y) := by gcongr
    _ = P^((66/100000 : ℝ)+(max α c+y)) := (Real.rpow_add hP0 _ _).symm
    _ ≤ _ := (Real.rpow_le_rpow_left_iff hP).mpr (by linarith)

lemma nat_pow_rpow_base {P : ℝ} (hP : 0 ≤ P) (a : ℝ) (n : ℕ) :
    (P^a)^n = P^(a*n) := (Real.rpow_mul_natCast hP a n).symm

lemma selectionWeight_power {P p θ φ h α b y H : ℝ} (hP : 0 < P)
    (hp : p=P^(1-α)) (hpθ : p*θ=P^b) (hφ : φ=P^(-y)) (hh : h=P^(-H)) :
    selectionWeight P θ φ h = P^(-(α+b+y+H)/100000) := by
  have hp0 : p ≠ 0 := hp ▸ (Real.rpow_pos_of_pos hP _).ne'
  have hPθ : P*θ = P^(α+b) := by
    calc
      _ = (P*(p*θ))/p := by field_simp
      _ = (P*P^b)/P^(1-α) := by rw [hpθ,hp]
      _ = P^(1+b)/P^(1-α) := by rw [Real.rpow_add hP,Real.rpow_one]
      _ = P^((1+b)-(1-α)) := (Real.rpow_sub hP _ _).symm
      _ = _ := by congr 1; ring
  unfold selectionWeight
  rw [hPθ,hφ,hh,← Real.rpow_mul hP.le,← Real.rpow_mul hP.le,
    ← Real.rpow_mul hP.le,← Real.rpow_add hP,← Real.rpow_add hP]
  congr 1
  ring

lemma receiverCoefficient_power {P w p θ φ h z b y H : ℝ} (hP : 0 < P)
    (hw : w=P^z) (hpθ : p*θ=P^b) (hφ : φ=P^(-y)) (hh : h=P^(-H)) :
    receiverCoefficient w p θ φ h =
      min (P^(-z-2*H+3*b)) (P^(-z-b+H+2*y)) := by
  unfold receiverCoefficient
  rw [hw,hpθ,hφ,hh,mul_min_of_nonneg _ _ (inv_nonneg.mpr (Real.rpow_nonneg hP.le _)),
    ← Real.rpow_neg hP.le, nat_pow_rpow_base hP.le, nat_pow_rpow_base hP.le,
    nat_pow_rpow_base hP.le]
  norm_num only [Nat.cast_ofNat]
  simp only [← Real.rpow_add hP,← Real.rpow_neg hP.le]
  congr 2 <;> ring

lemma selected_near_far_powers
    {P p w θ φ h I μ α z c b y H Δ : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hpθ : p*θ=P^b)
    (hφ : φ=P^(-y)) (hh : h=P^(-H))
    (hzc : z+c=1) (hΔ : Δ=(α+b+y+H)/100000)
    (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    2*α+H/2+2*y < z+Δ ∧ P^(α+b-H-Δ) < Real.sqrt (p*μ) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
  have hθ0 : 0 < θ := (mul_pos_iff.mp (hpθ ▸ Real.rpow_pos_of_pos hP0 _)).resolve_right
    (by rintro ⟨hh,_⟩; linarith) |>.2
  have hh0 : 0 < h := hh ▸ Real.rpow_pos_of_pos hP0 _
  have hWI : selectionWeight P θ φ h = P^(-Δ) := by
    rw [selectionWeight_power hP0 hp hpθ hφ hh,hΔ,neg_div]
  have hI' : I ≤ P^(-2*c) := by
    calc
      I ≤ (w/P)^2 := hI
      _ = (P^(z-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hw]
      _ = P^(-2*c) := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; linarith
  have hsI : 0 < Real.sqrt I := Real.sqrt_pos.mpr hI0
  have hsI' : Real.sqrt I ≤ P^(-c) := by
    calc
      _ ≤ Real.sqrt (P^(-2*c)) := Real.sqrt_le_sqrt hI'
      _ = _ := by rw [sqrt_rpow_base hP0.le]; congr 1; ring
  have hθeq : θ=P^(α+b-1) := by
    calc
      θ = (p*θ)/p := by field_simp
      _ = P^b/P^(1-α) := by rw [hpθ,hp]
      _ = P^(b-(1-α)) := (Real.rpow_sub hP0 _ _).symm
      _ = _ := by congr 1; ring
  have hn := hselected.trans_le (min_le_left _ _)
  have hf := hselected.trans_le (min_le_right _ _)
  have hn' : P*selectionWeight P θ φ h < Real.sqrt I*Real.sqrt h*p^2*φ^2 := by
    apply (mul_lt_mul_iff_right₀ hsI).mp
    calc
      _ = P*Real.sqrt I*selectionWeight P θ φ h := by ring
      _ < _ := hn
      _ = (Real.sqrt I)^2*Real.sqrt h*p^2*φ^2 := by rw [Real.sq_sqrt hI0.le]
      _ = _ := by ring
  have hnb : P^(1-Δ) < P^(-c-H/2+2*(1-α)-2*y) := by
    calc
      _ = P*selectionWeight P θ φ h := by
        rw [hWI,Real.rpow_sub hP0,Real.rpow_one,Real.rpow_neg hP0.le,div_eq_mul_inv]
      _ < _ := hn'
      _ ≤ P^(-c)*Real.sqrt h*p^2*φ^2 := by gcongr
      _ = _ := by
        rw [hh,hp,hφ,sqrt_rpow_base hP0.le,nat_pow_rpow_base hP0.le,nat_pow_rpow_base hP0.le]
        norm_num only [Nat.cast_ofNat]
        simp only [← Real.rpow_add hP0]
        congr 1
        ring
  have hne := (Real.rpow_lt_rpow_left_iff hP).mp hnb
  have hf' : P*selectionWeight P θ φ h*(θ*h) < Real.sqrt (p*μ) := by
    have ht := (lt_div_iff₀ (mul_pos hθ0 hh0)).mp hf
    apply (mul_lt_mul_iff_right₀ hsI).mp
    convert ht using 1 <;> first | rfl | ring
  have hfb : P*selectionWeight P θ φ h*(θ*h) = P^(α+b-H-Δ) := by
    rw [hWI,hθeq,hh]
    have ee : P*P^(-Δ)=P^(1-Δ) := by
      rw [Real.rpow_sub hP0,Real.rpow_one,Real.rpow_neg hP0.le,div_eq_mul_inv]
    rw [ee,← Real.rpow_add hP0,← Real.rpow_add hP0]
    congr 1
    ring
  exact ⟨by linarith, hfb ▸ hf'⟩

lemma improvedWindow_of_powers {P p w φ α z y : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y))
    (hp' : (7/10 : ℝ) ≤ 1-α) (hw' : (7/10 : ℝ) ≤ z)
    (hyl : (16/100 : ℝ)*max z (1-α) ≤ y)
    (hyu : y ≤ (49/100 : ℝ)*min z (1-α)) : ImprovedWindow P p w φ := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hzlo := le_max_left z (1-α)
  have hplo := le_max_right z (1-α)
  have hzup := min_le_left z (1-α)
  have hpup := min_le_right z (1-α)
  unfold ImprovedWindow
  rw [hp,hw,hφ]
  refine ⟨(Real.rpow_le_rpow_left_iff hP).mpr hp',
    (Real.rpow_le_rpow_left_iff hP).mpr hw',?_,?_,?_,?_⟩ <;>
    rw [← Real.rpow_mul hP0.le] <;>
    apply (Real.rpow_le_rpow_left_iff hP).mpr <;> linarith

lemma pureOccupationBounds_power_table
    {P C₀ C₁ M A p w φ h I μ α z c y H : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y)) (hh : h=P^(-H))
    (hzc : z+c=1) (hμ : 0 ≤ μ) (hI : I ≤ (w/P)^2)
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ) :
    (Real.sqrt (p*μ))^2 ≤ P^(-min (2*c) H) ∧
    (C₀ < P^(min z (1-α)-y) →
      (Real.sqrt (p*μ))^2 ≤ P^(-H)*max 1
        (max (P^(-2*c)*(stabilityRate P C₁ M A p w φ)^2)
          (P^(-H)*(stabilityRate P C₁ M A p w φ)^2))) ∧
    ((7/10 : ℝ) ≤ z → (7/10 : ℝ) ≤ 1-α →
      (16/100 : ℝ)*max z (1-α) ≤ y → y ≤ (49/100 : ℝ)*min z (1-α) →
      (Real.sqrt (p*μ))^2 ≤ P^(-H+(29/25 : ℝ)*y)*
        max 1 (max (P^(-2*c)*P^(2*max α c)) (P^(-H)*P^(2*max α c)))) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
  have hw0 : 0 < w := hw ▸ Real.rpow_pos_of_pos hP0 _
  have hm0 : 0 < min p w := lt_min hp0 hw0
  have hh0 : 0 < h := hh ▸ Real.rpow_pos_of_pos hP0 _
  have hI' : I ≤ P^(-2*c) := by
    calc
      I ≤ (w/P)^2 := hI
      _ = (P^(z-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hw]
      _ = P^(-2*c) := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; linarith
  have hm : min p w = P^(1-max α c) := by
    rw [hp,hw,rpow_min_exponent hP]
    congr 1
    rcases le_total α c with hh | hh
    · rw [max_eq_right hh,min_eq_right (by linarith)]; linarith
    · rw [max_eq_left hh,min_eq_left (by linarith)]
  have hIm : (min p w/P)^2 = P^(-2*max α c) := by
    calc
      _ = (P^((1-max α c)-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hm]
      _ = _ := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; ring
  have hmp : min p w*φ = P^(min z (1-α)-y) := by
    rw [hp,hw,hφ,rpow_min_exponent hP,← Real.rpow_add hP0,min_comm]
    congr 1
  rw [Real.sq_sqrt (mul_nonneg hp0.le hμ)]
  rcases hbounds with ⟨he,ha,hi⟩
  refine ⟨?_,?_,?_⟩
  · calc
      p*μ ≤ p*(max I h/p) := mul_le_mul_of_nonneg_left he hp0.le
      _ = max I h := by field_simp
      _ ≤ P^(-min (2*c) H) := by
        apply max_le
        · exact hI'.trans ((Real.rpow_le_rpow_left_iff hP).mpr (by have := min_le_left (2*c) H; linarith))
        · rw [hh]; exact (Real.rpow_le_rpow_left_iff hP).mpr (by have := min_le_right (2*c) H; linarith)
  · intro hC
    have hC' : C₀/min p w < φ := (div_lt_iff₀ hm0).mpr (by rw [mul_comm,hmp]; exact hC)
    calc
      p*μ ≤ p*((h/p)*max 1 (max (I/stabilityLength P C₁ M A p w φ)
        (h/stabilityLength P C₁ M A p w φ))) := mul_le_mul_of_nonneg_left (ha hC') hp0.le
      _ = h*max 1 (max (I*(stabilityRate P C₁ M A p w φ)^2)
          (h*(stabilityRate P C₁ M A p w φ)^2)) := by
        rw [div_stabilityLength,div_stabilityLength]
        field_simp
      _ ≤ _ := by rw [hh]; gcongr
  · intro hz' hp' hyl hyu
    have hi' := hi (improvedWindow_of_powers hP hp hw hφ hp' hz' hyl hyu)
    calc
      p*μ ≤ p*((h/p)*φ^(-29/25 : ℝ)*max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2))) :=
        mul_le_mul_of_nonneg_left hi' hp0.le
      _ = (h*φ^(-29/25 : ℝ))*max 1 (max (I*P^(2*max α c)) (h*P^(2*max α c))) := by
        rw [hIm,show -2*max α c = -(2*max α c) by ring,Real.rpow_neg hP0.le]
        simp only [div_inv_eq_mul]
        field_simp
      _ ≤ (h*φ^(-29/25 : ℝ))*max 1 (max (P^(-2*c)*P^(2*max α c)) (h*P^(2*max α c))) := by
        gcongr
        exact mul_nonneg hh0.le (Real.rpow_nonneg (hφ ▸ Real.rpow_nonneg hP0.le _) _)
      _ = _ := by
        rw [hh,hφ,← Real.rpow_mul hP0.le,← Real.rpow_add hP0]
        congr 2
        ring

lemma selected_receiverCoefficient_of_powers
    {P C₀ C₁ M A p w θ φ h I μ α z c b y H : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hp : p=P^(1-α)) (hw : w=P^z) (hpθ : p*θ=P^b)
    (hφ : φ=P^(-y)) (hh : h=P^(-H)) (hφ₁ : φ ≤ 1)
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z+c=1) (hμ : 0 ≤ μ) (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ))
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  let Δ := (α+b+y+H)/100000
  obtain ⟨hn,hf⟩ := selected_near_far_powers hP hp hw hpθ hφ hh hzc (show Δ=_ from rfl)
    hI0 hI hselected
  obtain ⟨he,ha,hi⟩ := pureOccupationBounds_power_table hP hp hw hφ hh hzc hμ hI hbounds
  have hr0 : 0 ≤ stabilityRate P C₁ M A p w φ := by
    have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
    have hw0 : 0 < w := hw ▸ Real.rpow_pos_of_pos hP0 _
    have hm0 : 0 < min p w := lt_min hp0 hw0
    have hφ0 : 0 < φ := hφ ▸ Real.rpow_pos_of_pos hP0 _
    unfold stabilityRate
    positivity
  have hr : (66/100 : ℝ) < z → (stabilityRate P C₁ M A p w φ)^2 ≤
      P^(2*max α c+2*y+2*z/1000) := by
    intro hz'
    have hrate := stabilityRate_power_bound hP hC₁ hA hp hw hφ hφ₁ hzc hz' hconst
    calc
      _ ≤ (P^(max α c+y+z/1000))^2 := (sq_le_sq₀ hr0 (Real.rpow_nonneg hP0.le _)).mpr hrate
      _ = _ := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; ring
  have hb := selected_coefficient_power_table hP hα hz hc hy hH hzc (show Δ=_ from rfl)
    hn (Real.sqrt_nonneg _) hf he hC₀ hr ha hi
  rw [receiverCoefficient_power hP0 hw hpθ hφ hh,
    selectionWeight_power hP0 hp hpθ hφ hh,hw,← Real.rpow_mul hP0.le,← Real.rpow_add hP0]
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [Δ]
  congr 1
  ring

lemma selected_receiverCoefficient
    {P C₀ C₁ M A p w θ φ h I μ : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hp0 : 0 < p) (hpP : p ≤ P) (hw1 : 1 ≤ w) (hwP : w ≤ P)
    (hθ : 0 < θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hμ : 0 ≤ μ) (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ))
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp' : p=P^(1-(1-Real.logb P p)) := by
    rw [sub_sub_cancel,Real.rpow_logb hP0 hP.ne' hp0]
  have hw' : w=P^(Real.logb P w) := (Real.rpow_logb hP0 hP.ne' (zero_lt_one.trans_le hw1)).symm
  have hpθ' : p*θ=P^(Real.logb P (p*θ)) := (Real.rpow_logb hP0 hP.ne' (mul_pos hp0 hθ)).symm
  have hφ' : φ=P^(-(-Real.logb P φ)) := by rw [neg_neg,Real.rpow_logb hP0 hP.ne' hφ]
  have hh' : h=P^(-(-Real.logb P h)) := by rw [neg_neg,Real.rpow_logb hP0 hP.ne' hh]
  have hα : 0 ≤ 1-Real.logb P p := sub_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hp0).mpr (by simpa using hpP))
  have hc : 0 ≤ 1-Real.logb P w := sub_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP (zero_lt_one.trans_le hw1)).mpr (by simpa using hwP))
  have hy : 0 ≤ -Real.logb P φ := neg_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hφ).mpr (by simpa using hφ1))
  have hH : 0 ≤ -Real.logb P h := neg_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hh).mpr (by simpa using hh1))
  exact selected_receiverCoefficient_of_powers hP hC₁ hM hA hp' hw' hpθ' hφ' hh' hφ1
    hα (Real.logb_nonneg hP hw1) hc hy hH (by ring) hμ hI0 hI hC₀ hconst hbounds hselected

lemma pureOccupationEnvelope_bounds (P C₀ C₁ M A p w φ h I : ℝ) :
    PureOccupationBounds P C₀ C₁ M A p w φ h I
      (pureOccupationEnvelope P C₀ C₁ M A p w φ h I) := by
  classical
  unfold PureOccupationBounds pureOccupationEnvelope
  dsimp only
  refine ⟨?_,?_,?_⟩
  · exact (min_le_left _ _).trans (by split_ifs <;> simp only [min_le_left,le_refl])
  · intro ha
    rw [ite_eq_left ha]
    exact (min_le_left _ _).trans (min_le_right _ _)
  · intro hb
    rw [ite_eq_left hb]
    exact (min_le_right _ _).trans (min_le_right _ _)

lemma pureOccupationEnvelope_nonneg
    {P C₀ C₁ M A p w φ h I : ℝ} (hp : 0 ≤ p) (hφ : 0 ≤ φ)
    (hh : 0 ≤ h) (hI : 0 ≤ I) :
    0 ≤ pureOccupationEnvelope P C₀ C₁ M A p w φ h I := by
  classical
  unfold pureOccupationEnvelope
  dsimp only
  split_ifs <;> positivity

theorem receiverCoefficient_on_selected_bins
    (C₀ C₁ M A : ℝ) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A) :
    ∀ᶠ P in atTop, ∀ p w θ φ h I : ℝ,
      0 < p → p ≤ P → 1 ≤ w → w ≤ P → 0 < θ →
      0 < φ → φ ≤ 1 → 0 < h → h ≤ 1 → 0 < I → I ≤ (w/P)^2 →
      P*Real.sqrt I*selectionWeight P θ φ h <
        min (I*Real.sqrt h*p^2*φ^2)
          (Real.sqrt I*Real.sqrt (p*pureOccupationEnvelope P C₀ C₁ M A p w φ h I)/(θ*h)) →
      receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  filter_upwards [eventually_selection_constants C₀ C₁ M A hC₁ hA] with P hP
  intro p w θ φ h I hp hpP hw hwP hθ hφ hφ1 hh hh1 hI0 hI hselected
  exact selected_receiverCoefficient hP.1 hC₁ hM hA hp hpP hw hwP hθ hφ hφ1 hh hh1
    (pureOccupationEnvelope_nonneg hp.le hφ.le hh.le hI0.le) hI0 hI hP.2.1 hP.2.2
    (pureOccupationEnvelope_bounds ..) hselected

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeKernelInterior
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.coneCutoffRate_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneCutoffRate s F.flow zX) (coneKernelInterior T) := by
  let S := coneKernelInterior T
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2) S :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn
      (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1.1)).snd)
  have hu : ContinuousOn (fun p : ConeKernelState=>velocity p.2.2.2) S :=
    ((contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd).continuousOn
  have hn : ContinuousOn (fun p : ConeKernelState=>p.2.1) S := continuous_snd.fst.continuousOn
  have hD : ∀p∈S,1-dot p.2.1 (velocity (F.flow zX p.1.1).2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.1.2.1)).ne'
  have hρ : ContinuousOn (fun p : ConeKernelState=>
      (1-dot p.2.1 (velocity p.2.2.2))/(1-dot p.2.1 (velocity (F.flow zX p.1.1).2))) S := by
    simp only [dot_eq_inner] at hD ⊢
    exact (continuousOn_const.sub (hn.inner hu)).div (continuousOn_const.sub (hn.inner ha)) hD
  have hN := (hρ.smul (ha.sub hn)).add hn |>.sub hu
  have hr := (continuous_fst.fst.sub continuous_fst.snd).continuousOn.inv₀
    (show ∀p∈S,p.1.1-p.1.2≠0 from fun _ hp=>(sub_pos.mpr hp.2).ne')
  have hKY : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.2,p.2.2)).2) S :=
    hs.continuousOn_momentumForce.comp (continuous_fst.snd.prodMk continuous_snd.snd).continuousOn
      (fun _ hp=>⟨hp.1.1.2,mem_univ _⟩)
  have hKX : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.1,F.flow zX p.1.1)).2) S :=
    (F.momentumForce_continuousOn_closed hs zX).comp continuous_fst.fst.continuousOn
      (fun _ hp=>hp.1.1.1)
  exact (hρ.sub continuousOn_const).prodMk ((hr.smul hN).prodMk (hKY.prodMk (hρ.smul hKX)))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_PhysicalBinPhaseSet
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.coneReceiverCutoffTangent_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneReceiverCutoffTangent s F.flow zX) (coneKernelInterior T) :=
  continuousOn_const.prodMk (continuousOn_const.prodMk (continuousOn_const.prodMk
    (F.coneCutoffRate_continuousOn hs zX).snd.snd.snd))

lemma coneReceiverCutoffTangent_pullback (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) :
    coneReceiverCutoffTangent s α zX ∘ labelKernelState α zX T =
      fun p=>cutoffReceiverTangent (branchRate α zX p.2 T p.1)
        (lorentzField s.E s.B (branchTime α zX p.2 T p.1,α zX (branchTime α zX p.2 T p.1))).2 := by
  rfl

lemma PhaseFlowOn.coneSourceCutoffTangent_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneSourceCutoffTangent s F.flow zX) (coneKernelInterior T) :=
  continuousOn_const.prodMk (continuousOn_const.prodMk
    ((F.coneCutoffRate_continuousOn hs zX).snd.snd.fst.prodMk continuousOn_const))

lemma PhaseFlowOn.coneGeometryCutoffTangent_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneGeometryCutoffTangent s F.flow zX) (coneKernelInterior T) :=
  (F.coneCutoffRate_continuousOn hs zX).fst.prodMk
    ((F.coneCutoffRate_continuousOn hs zX).snd.fst.prodMk
      (continuousOn_const.prodMk continuousOn_const))

lemma coneSourceCutoffTangent_pullback (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) :
    coneSourceCutoffTangent s α zX ∘ labelKernelState α zX T =
      fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,α p.2 p.1)).2 := rfl

lemma coneGeometryCutoffTangent_pullback (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) :
    coneGeometryCutoffTangent s α zX ∘ labelKernelState α zX T =
      fun p=>cutoffGeometryTangent (branchTime α zX p.2 T p.1-p.1) (branchRate α zX p.2 T p.1)
        (velocity (α zX (branchTime α zX p.2 T p.1)).2) (velocity (α p.2 p.1).2)
        (branchDirection α zX p.2 T p.1) := rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CappedRepresentativePos
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

lemma cappedRepresentative_pos (n : ℕ) : 0 < cappedRepresentative n := by
  dsimp [cappedRepresentative]
  positivity

lemma cappedRepresentative_le_one (n : ℕ) : cappedRepresentative n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

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

lemma measurable_vec_clm_apply {Ω : Type*} [MeasurableSpace Ω]
    {W : Ω→Vec→L[ℝ]Vec} {f : Ω→Vec} (hW : Measurable W) (hf : Measurable f) :
    Measurable (fun p=>W p (f p)) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp (hW.prodMk hf)

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionCounts
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

lemma selectionDecay_pos : 0 < selectionDecay := Real.rpow_pos_of_pos (by norm_num) _
lemma selectionDecay_lt_one : selectionDecay<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma selectionDecay_pow (n : ℕ) :
    selectionDecay^n=((2:ℝ)^n)^(-1/100000:ℝ) := by
  rw [selectionDecay,←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma cappedRepresentative_selection_pow (n : ℕ) :
    (cappedRepresentative n)^(1/100000:ℝ)=selectionDecay^n := by
  rw [selectionDecay_pow]
  dsimp [cappedRepresentative]
  rw [inv_pow,Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity)]
  congr 1
  norm_num

lemma sourceRepresentative_two_pow (n : ℕ) : sourceRepresentative n=(2:ℝ)^(n+6) := by
  simp only [sourceRepresentative,pow_add]
  ring

lemma selection_angle_index {np nt : ℕ}
    (h : 1/sourceRepresentative np ≤ cappedRepresentative nt) : nt≤np+6 := by
  rw [sourceRepresentative_two_pow] at h
  have he : (2:ℝ)^nt≤2^(np+6) := by
    have hp : 0<(2:ℝ)^nt := by positivity
    have hq : 0<(2:ℝ)^(np+6) := by positivity
    dsimp [cappedRepresentative] at h
    rw [inv_pow,one_div] at h
    exact (inv_le_inv₀ hq hp).mp h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp he

lemma selectionWeight_gap_bound {P : ℝ} {N : ℕ} {k : Fin 4→ℕ}
    (hP : sourceRepresentative N≤P) (h0 : k 0≤N) (h1 : k 1≤k 0+6) :
    selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤
      selectionDecay^(N-k 0)*selectionDecay^(k 0+6-k 1)*selectionDecay^(k 2)*selectionDecay^(k 3) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hN := sourceRepresentative_two_pow N
  have hle : k 1≤N+6 := by omega
  have hid : sourceRepresentative N*cappedRepresentative (k 1)=(2:ℝ)^(N+6-k 1) := by
    rw [hN]
    dsimp [cappedRepresentative]
    rw [inv_pow, pow_sub₀ (2:ℝ) (by norm_num) hle]
  have hdec : (P*cappedRepresentative (k 1))^(-1/100000:ℝ)≤ selectionDecay^(N+6-k 1) := by
    rw [selectionDecay_pow,←hid]
    exact Real.rpow_le_rpow_of_nonpos (by rw [hN]; positivity)
      (mul_le_mul_of_nonneg_right hP hθ.le) (by norm_num)
  have he : N+6-k 1=(N-k 0)+(k 0+6-k 1) := by omega
  unfold selectionWeight
  rw [cappedRepresentative_selection_pow,cappedRepresentative_selection_pow]
  rw [he,pow_add] at hdec
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdec
    (pow_nonneg selectionDecay_pos.le _)) (pow_nonneg selectionDecay_pos.le _)

lemma sum_selectionDecay (N : ℕ) :
    ∑n∈Finset.range N,selectionDecay^n≤(1-selectionDecay)⁻¹ := by
  have hr : |selectionDecay|<1 := by rw [abs_of_pos selectionDecay_pos]; exact selectionDecay_lt_one
  exact ((summable_geometric_of_abs_lt_one hr).sum_le_tsum (Finset.range N)
    (fun _ _=>pow_nonneg selectionDecay_pos.le _)).trans_eq (tsum_geometric_of_abs_lt_one hr)

lemma sum_selectionDecay_box (N : ℕ) :
    ∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  classical
  have heq : (instDecidableEqFin 4 : DecidableEq (Fin 4))=
      (fun a b=>Classical.propDecidable (a=b)) := Subsingleton.elim _ _
  have hh := Finset.sum_prod_piFinset (Finset.range N) (fun (_i : Fin 4) (n : ℕ)=>selectionDecay^n)
  rw [heq] at hh
  have hsum : (∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i))=
      (∑n∈Finset.range N,selectionDecay^n)^4 := by
    simpa [dyadicBox,Fin.prod_univ_four,pow_succ] using hh
  rw [hsum]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))
    (sum_selectionDecay N) 4

lemma sum_selectionDecay_finset (S : Finset (Fin 4→ℕ)) :
    ∑k∈S,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  obtain ⟨N,hN⟩ := finset_subset_dyadicBox S
  exact (Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _=>Finset.prod_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))).trans
    (sum_selectionDecay_box N)

lemma sum_selectionWeight (S : Finset (Fin 4→ℕ)) {P : ℝ}
    (hP : ∀k∈S,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈S,1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1)) :
    ∑k∈S,selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤((1-selectionDecay)⁻¹)^4 := by
  classical
  by_cases hS : S.Nonempty
  · let N := S.sup (fun k=>k 0)
    have hN (k) (hk : k∈S) : k 0≤N := Finset.le_sup (f:=fun k : Fin 4→ℕ=>k 0) hk
    have hNP : sourceRepresentative N≤P := by
      obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup S hS (fun k=>k 0)
      change sourceRepresentative (S.sup (fun k : Fin 4→ℕ=>k 0))≤P
      rw [he]
      exact hP k hk
    let g : (Fin 4→ℕ)→(Fin 4→ℕ) := fun k=>![N-k 0,k 0+6-k 1,k 2,k 3]
    have hg : Set.InjOn g ↑S := by
      intro k hk l hl hkl
      have hk1 := selection_angle_index (hθ k hk)
      have hl1 := selection_angle_index (hθ l hl)
      have h00 := congrFun hkl 0
      have h11 := congrFun hkl 1
      have h22 := congrFun hkl 2
      have h33 := congrFun hkl 3
      change N-k 0=N-l 0 at h00
      change k 0+6-k 1=l 0+6-l 1 at h11
      change k 2=l 2 at h22
      change k 3=l 3 at h33
      have hk0 := hN k hk
      have hl0 := hN l hl
      have h0e : k 0=l 0 := by omega
      have h1e : k 1=l 1 := by omega
      apply funext
      intro i
      fin_cases i
      · exact h0e
      · exact h1e
      · exact h22
      · exact h33
    calc
      _≤∑k∈S,∏i,selectionDecay^(g k i) := Finset.sum_le_sum (fun k hk=>by
        simpa [g,Fin.prod_univ_four] using selectionWeight_gap_bound hNP (hN k hk) (selection_angle_index (hθ k hk)))
      _=∑k∈S.image g,∏i,selectionDecay^(k i) := (Finset.sum_image (f:=fun k : Fin 4→ℕ=>∏i,selectionDecay^(k i)) (fun k hk l hl he=>hg hk hl he)).symm
      _≤_ := sum_selectionDecay_finset _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    positivity

lemma selectionWeight_nonneg {P θ φ h : ℝ} (hP : 0≤P) (hθ : 0≤θ) (hφ : 0≤φ) (hh : 0≤h) :
    0 ≤ selectionWeight P θ φ h := by unfold selectionWeight; positivity

lemma selection_weighted_tsum {P c : ℝ} (hP0 : 0≤P) (hc : 0 ≤ c)
    (Q : Set (Fin 4→ℕ)) (hP : ∀k∈Q,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈Q,1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1))
    (f : (Fin 4→ℕ)→ℝ≥0∞)
    (hf : ∀k∈Q,f k≤ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) :
    (∑'k,Q.indicator f k)≤ENNReal.ofReal (c*((1-selectionDecay)⁻¹)^4) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun k=>k∈Q)
  have hU (k) (hk : k∈U) : k∈Q := (Finset.mem_filter.mp hk).2
  have hsum : (∑k∈S,Q.indicator f k)=∑k∈U,f k := by simp [U,Finset.sum_filter,indicator_apply]
  rw [hsum]
  calc
    _ ≤ ∑k∈U,ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3))) := Finset.sum_le_sum (fun k hk=>hf k (hU k hk))
    _ = ENNReal.ofReal (c*(∑k∈U,selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun k _=>mul_nonneg hc
        (selectionWeight_nonneg hP0 (cappedRepresentative_pos _).le
          (cappedRepresentative_pos _).le (cappedRepresentative_pos _).le)),Finset.mul_sum]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (sum_selectionWeight U (fun k hk=>hP k (hU k hk)) (fun k hk=>hθ k (hU k hk))) hc)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_ReceiverWeights
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


lemma Admissible.selected_receiver_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ) (g : ℝ→ℝ≥0∞),
      0≤a → b≤T → 1≤w → w≤P → 0<I → I≤(w/P)^2 →
      Measurable g → (∀t,g t≠⊤) →
      let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeReceiverCost s F zX w k a b g) k)≤
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,g t) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_receiver_envelope T₀
  refine ⟨C*((1-selectionDecay)⁻¹)^4,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [receiverCoefficient_on_selected_bins 512 16384 M A (by norm_num) hM.le hA.le,
    eventually_ge_atTop (1:ℝ)] with P hsafe hP
  intro s T F hs hT hTT zX a b I w g ha hb hw hwP hI hIP hg hgf
  dsimp only
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  let L := ∫⁻t in Icc a b,g t
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hpt (k : Fin 4→ℕ) (hk : k∈Q) :
      representativeReceiverCost s F zX w k a b g≤
        ENNReal.ofReal ((C*w^(-1/2:ℝ))*selectionWeight P (cappedRepresentative (k 1))
          (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))*L := by
    have he := hbound s T F hs hT hTT zX k a b w g ha hb hw0 hg hgf
    have hu := hsafe (sourceRepresentative (k 0)) w (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) I
      (by unfold sourceRepresentative; positivity) hk.1.1 hw hwP (cappedRepresentative_pos _)
      (cappedRepresentative_pos _) (cappedRepresentative_le_one _) (cappedRepresentative_pos _)
      (cappedRepresentative_le_one _) hI hIP hk.2
    apply he.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu hC
  have hwgt := selection_weighted_tsum (zero_le_one.trans hP) (by positivity : 0≤C*w^(-1/2:ℝ))
    Q (fun _ hk=>hk.1.1) (fun _ hk=>hk.1.2.1)
    (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*selectionWeight P (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) (fun _ _=>le_rfl)
  classical
  calc
    _ ≤ ∑'k : Fin 4→ℕ,Q.indicator (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*
        selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
        (cappedRepresentative (k 3)))*L) k := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈Q
      · change Q.indicator _ k≤_
        simpa only [indicator_of_mem hk] using hpt k hk
      · change Q.indicator _ k≤_
        simp only [indicator_of_notMem hk,le_refl]
    _ = (∑'k : Fin 4→ℕ,Q.indicator (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*
        selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
        (cappedRepresentative (k 3)))) k)*L := by
      simp_rw [indicator_mul_left]
      exact ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal ((C*w^(-1/2:ℝ))*((1-selectionDecay)⁻¹)^4)*L := mul_le_mul' hwgt le_rfl
    _ = _ := by congr 2; ring



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BulkReceiverScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.bulk_receiver_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 1≤w → w≤P → 0<I → I≤(w/P)^2 →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
        (coneReceiverCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  obtain ⟨Cs,hCs,hreceiver⟩ := hd.selected_receiver_uniform T₀
  obtain ⟨Cd,hCd,hder⟩ := dyadicFactor_log_derivative_bound
  refine ⟨2080000*Cd*Cs,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hreceiver M A hM hA] with P hr
  intro s T F hs hT hTT zX a b I w ha hb hw hwP hI hIP hphysical hband W hW hW1
  have hg := (F.continuous_prefixMomentumForce hs.energyPrefix hT zX).norm.measurable.ennreal_ofReal
  have hbnd := hr s T F hs hT hTT zX a b I w
    (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) ha hb hw hwP hI hIP hg
    (fun _=>ENNReal.ofReal_ne_top)
  apply (F.bulkReceiver_selected_sum hs.energyPrefix hT zX (zero_lt_one.trans_le hw)
    ha hb hband hphysical hW hW1 hCd hder).trans
  apply (mul_le_mul' le_rfl hbnd).trans
  rw [←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤2080000*Cd)]
  exact le_of_eq (by congr 2; ring)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.bulk_selected_family_uniform_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
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
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p : ℝ×Phase,selectedMultiplierBulkDensity s F.flow zX T (bulkSelection P M A w I)
        ((Icc a b).indicator W) p)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  obtain ⟨Cs,hCs,hsource⟩ := hd.bulk_source_uniform T₀
  obtain ⟨Cg,hCg,hgeometry⟩ := hd.bulk_geometry_uniform T₀
  obtain ⟨Cr,hCr,hreceiver⟩ := hd.bulk_receiver_uniform T₀
  obtain ⟨Cb,hCb,hremainder⟩ := hd.bulk_remainder_uniform T₀
  let C := Cs+Cg+Cr+Cb
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hsource M A hM hA,hgeometry M A hM hA,
    hreceiver M A (zero_lt_one.trans_le hM) hA,hremainder M A hM hA] with P hso hge hre hrm
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ W hW hW1
  let Q := bulkSelection P M A w I
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let K := ∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖
  let V := (Icc a b).indicator W
  have hV : Measurable V := hW.indicator measurableSet_Icc
  have hB : 0≤B := by dsimp [B]; positivity
  have hsc := hso hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsrc hphysical hband HZ W hW hW1
  have hgc := hge hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsrc hphysical hband HZ W hW hW1
  have hrc := hre s T F hs hT hTT zX a b I w ha hb hw hwP hI hIP hphysical hband W hW hW1
  have hbc := hrm s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP hIP HZ hphysical hband W hW hW1
  have htr (H : ConeKernelState→CutoffState) (hH : ContinuousOn H (coneKernelInterior T)) :=
    F.partialCutoffLabelCost_triangle (J:=Icc a b) hs.energyPrefix hT zX Q hH hW measurableSet_Icc
  have hts := htr _ (F.coneSourceCutoffTangent_continuousOn hs.energyPrefix zX)
  have htg := htr _ (F.coneGeometryCutoffTangent_continuousOn hs.energyPrefix zX)
  have htrc := htr _ (F.coneReceiverCutoffTangent_continuousOn hs.energyPrefix zX)
  rw [coneSourceCutoffTangent_pullback] at hts
  rw [coneGeometryCutoffTangent_pullback] at htg
  rw [coneReceiverCutoffTangent_pullback] at htrc
  have hcut := F.cutoff_label_integral_split hs.energyPrefix zX Q hV
  dsimp only [V] at hcut
  rw [hts,htg,htrc] at hcut
  have hcut' := hcut.trans (add_le_add (add_le_add hsc hgc) hrc)
  have hrem : (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖V (labelReceiverTime F.flow zX T p)
        (labelSelectedCutoff F.flow zX T Q p • actualLabelRemainder s F.flow zX T p)‖)≤
      ENNReal.ofReal (Cb*B)+ENNReal.ofReal (Cb*w^(-1/2:ℝ))*K := by
    rw [F.actualLabelRemainder_eq_normalised zX]
    change (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator W (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Q p • labelConeKernel s F.flow zX T (remainderConeKernel s F.flow zX) p)‖)≤_
    have ht := F.selectedConeTriangle_norm_transfer (J:=Icc a b) (A:=remainderConeKernel s F.flow zX)
      hs.energyPrefix hT zX Q
      ((F.normalised_remainder_continuousOn hs.energyPrefix zX).mono inter_subset_left) hW measurableSet_Icc
    exact ht.le.trans hbc
  have hmeas := (measurable_vec_clm_apply (hV.comp (F.labelReceiverTime_measurable zX))
    (F.actualLabelCutoffCost_measurable hs.energyPrefix zX Q)).norm.ennreal_ofReal
  change Measurable (fun x=>ENNReal.ofReal ‖V (labelReceiverTime F.flow zX T x)
    (actualLabelCutoffCost s F.flow zX T Q x)‖) at hmeas
  change (∫⁻p : ℝ×Phase,selectedMultiplierBulkDensity s F.flow zX T Q V p)≤_
  simp only [selectedMultiplierBulkDensity]
  rw [lintegral_add_left hmeas]
  apply (add_le_add hcut' hrem).trans
  have heq : (ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cg*B)+ENNReal.ofReal (Cr*w^(-1/2:ℝ))*K)+
      (ENNReal.ofReal (Cb*B)+ENNReal.ofReal (Cb*w^(-1/2:ℝ))*K)=
      ENNReal.ofReal ((Cs+Cg+Cb)*B)+ENNReal.ofReal ((Cr+Cb)*w^(-1/2:ℝ))*K := by
    rw [add_mul,add_mul,add_mul,ENNReal.ofReal_add (add_nonneg (mul_nonneg hCs hB) (mul_nonneg hCg hB)) (mul_nonneg hCb hB),
      ENNReal.ofReal_add (mul_nonneg hCs hB) (mul_nonneg hCg hB),
      ENNReal.ofReal_add (by positivity : 0≤Cr*w^(-1/2:ℝ)) (by positivity : 0≤Cb*w^(-1/2:ℝ)),add_mul]
    ring
  change (ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cg*B)+ENNReal.ofReal (Cr*w^(-1/2:ℝ))*K)+
      (ENNReal.ofReal (Cb*B)+ENNReal.ofReal (Cb*w^(-1/2:ℝ))*K)≤_
  rw [heq]
  apply add_le_add
  · apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hB
  · apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg (zero_le_one.trans hw) _)

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.bulk_selected_family_uniform_oai := @OAI.RVM.Admissible.bulk_selected_family_uniform_oai
