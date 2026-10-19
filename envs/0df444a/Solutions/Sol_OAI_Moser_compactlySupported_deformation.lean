-- Prove2me | solution 1 for OAI.Moser.compactlySupported_deformation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:31:12.4785+00:00
-- url     : https://prove2.me/submissions/8705cffb-b17f-496c-a5f1-67d6e877517c

import Mathlib
import Definitions.Def_OAIQWSP000

section
-- module Solutions.OAIQW_SymmetricPolar.LocalODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u3 u4 u5 u6

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u6} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem tangentPath_eq {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    tangentPath hV h hh x v =
      ContinuousMap.const Time v + h • primitive
        (SmoothPaths.applyField
          (SmoothPaths.superpose (hVs.continuous_fderiv (by simp)) (trajectory hV h hh x))
          (tangentPath hV h hh x v)) := by
  let Q := trajectory hV h hh
  let DQ := fderiv ℝ Q x
  let A := SmoothPaths.applyField
    (SmoothPaths.superpose (hVs.continuous_fderiv (by simp)) (Q x))
  have hQ : HasFDerivAt Q DQ x :=
    (contDiff_trajectory hV hVs h hh).differentiable (by simp) x |>.hasFDerivAt
  have hS := (SmoothPaths.hasFDerivAt_superpose
    (hVs.differentiable (by simp)) (hVs.continuous_fderiv (by simp)) (Q x)).comp x hQ
  have hP := (primitiveCLM (E := E)).hasFDerivAt.comp x hS
  have hC := (ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)).hasFDerivAt (x := x)
  have hD := hC.add (hP.const_smul h)
  have hD' : HasFDerivAt Q
      ((ContinuousLinearMap.const ℝ Time : E →L[ℝ] C(Time, E)) +
        h • primitiveCLM.comp (A.comp DQ)) x := by
    apply hD.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun y => (trajectory_eq hV h hh y).symm)
  exact congrArg (fun L : E →L[ℝ] C(Time, E) => L v) (hQ.unique hD')

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.CompleteFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u7 u8 u9 u10 u11 u12 u13

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u7} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem variation_coe {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : Time) :
    variation hV h hh x v t = tangentPath hV h hh x v t :=
  (congrArg (fun u : C(Time, E) => u t) (tangentPath_eq hV hVs h hh x v)).symm

omit [ProperSpace E] in
theorem continuous_variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    Continuous (variation hV h hh x v) := by
  have hc := ((hVs.continuous_fderiv (by simp)).comp
    (continuous_extend (trajectory hV h hh x))).clm_apply
      (continuous_extend (tangentPath hV h hh x v))
  exact continuous_const.add
    ((intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).const_smul h)

theorem hasDerivAt_variation {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) (t : Time) :
    HasDerivAt (variation hV h hh x v)
      (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x v t)) (t : ℝ) := by
  have hc := ((hVs.continuous_fderiv (by simp)).comp
    (continuous_extend (trajectory hV h hh x))).clm_apply
      (continuous_extend (tangentPath hV h hh x v))
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter volume (𝓝 (t : ℝ)))
      hc.continuousAt
  rw [curve_coe, variation_coe hV hVs]
  change HasDerivAt (fun s : ℝ => v + h • ∫ r in 0..s,
    fderiv ℝ V (extend (trajectory hV h hh x) r) (extend (tangentPath hV h hh x v) r))
    _ (t : ℝ)
  simpa only [Pi.smul_apply, Function.comp_apply, extend_coe] using (hd.const_smul h).const_add v

theorem tangentPath_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    tangentPath hV h hh x v ⟨1, by constructor <;> norm_num⟩ = fderiv ℝ (step hV h hh) x v := by
  let t : Time := ⟨1, by constructor <;> norm_num⟩
  have hd := (ContinuousMap.evalCLM ℝ (M := E) t).hasFDerivAt.comp x
    ((contDiff_trajectory hV hVs h hh).differentiable (by simp) x).hasFDerivAt
  exact (congrArg (fun L : E →L[ℝ] E => L v) hd.fderiv).symm

theorem variation_one {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E) :
    variation hV h hh x v 1 = fderiv ℝ (step hV h hh) x v :=
  (variation_coe hV hVs h hh x v ⟨1, by constructor <;> norm_num⟩).trans
    (tangentPath_one hV hVs h hh x v)

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u9} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

omit [CompleteSpace E] [ProperSpace E] in

theorem contDiff_homeomorph_pow (f : E ≃ₜ E) (hf : ContDiff ℝ ∞ (f : E → E))
    (n : ℕ) : ContDiff ℝ ∞ ((f ^ n : E ≃ₜ E) : E → E) := by
  induction n with
  | zero =>
    rw [pow_zero]
    change ContDiff ℝ ∞ (id : E → E)
    exact contDiff_id
  | succ n ih =>
    rw [pow_succ']
    change ContDiff ℝ ∞ ((f : E → E) ∘ (f ^ n : E ≃ₜ E))
    exact hf.comp ih

omit [ProperSpace E] in

theorem curve_linear_component {F : Type u10} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (L : E →L[ℝ] F) (v : F)
    (hL : ∀ z, L (V z) = v) (x : E) (t : Time) :
    L (curve hV h hh x t) = L x + (t : ℝ) • h • v := by
  let G : ℝ → F := fun s => L (curve hV h hh x s) - s • h • v
  have hc : Continuous G :=
    (L.continuous.comp (continuous_curve hV h hh x)).sub (continuous_id.smul continuous_const)
  have hd : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt G 0 (Ici s) s := by
    intro s hs
    have hd := L.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_curve hV h hh x ⟨s, hs.1, hs.2.le⟩)
    have hlin := (hasDerivAt_id s).smul_const (h • v)
    have hh' : HasDerivAt G 0 s := by
      change HasDerivAt ((L ∘ curve hV h hh x) - fun s : ℝ => s • h • v) 0 s
      simpa only [id_eq, map_smul, hL, one_smul, sub_self] using hd.sub hlin
    exact hh'.hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc.continuousOn hd (t : ℝ) t.property
  simpa only [G, curve_zero, zero_smul, sub_zero, sub_eq_iff_eq_add] using he

omit [ProperSpace E] in
@[simp] theorem step_linear_component {F : Type u11} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (L : E →L[ℝ] F) (v : F)
    (hL : ∀ z, L (V z) = v) (x : E) :
    L (step hV h hh x) = L x + h • v := by
  simpa only [curve_one, one_smul] using
    curve_linear_component hV h hh L v hL x (⟨1, by constructor <;> norm_num⟩ : Time)

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_linear_component {F : Type u12} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E ≃ₜ E) (L : E →L[ℝ] F) (v : F) (hL : ∀ x, L (f x) = L x + v)
    (n : ℕ) (x : E) : L ((f ^ n) x) = L x + n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Homeomorph.mul_apply, hL, ih, succ_nsmul]
    abel

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.SmoothFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u14 u15 u16

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u14} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable section

theorem curve_injective {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (t : Time) :
    Function.Injective (fun x => curve hV h hh x t) := by
  intro x y he
  have heq : EqOn (curve hV h hh x) (curve hV h hh y) (Icc 0 t) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun _ y => h • V y) (s := fun _ => univ) (K := ‖h‖₊ * K)
    · intro _ _
      exact ((lipschitzWith_smul h).comp hV).lipschitzOnWith
    · exact (continuous_curve hV h hh x).continuousOn
    · intro s hs
      exact (hasDerivAt_curve hV h hh x ⟨s, hs.1.le, hs.2.trans t.property.2⟩).hasDerivWithinAt
    · intro _ _; trivial
    · exact (continuous_curve hV h hh y).continuousOn
    · intro s hs
      exact (hasDerivAt_curve hV h hh y ⟨s, hs.1.le, hs.2.trans t.property.2⟩).hasDerivWithinAt
    · intro _ _; trivial
    · exact he
  simpa only [curve_zero] using heq (show 0 ∈ Icc (0 : ℝ) t from ⟨le_rfl, t.property.1⟩)

theorem curve_of_const_along {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (h : ℝ) (hh : ‖h‖₊ * K < 1) (x v : E)
    (hc : ∀ t : Time, V (x + (t : ℝ) • h • v) = v) :
    EqOn (curve hV h hh x) (fun t => x + t • h • v) (Icc 0 1) := by
  apply EqOn.symm
  apply curve_unique hV h hh x
  · exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  · intro t ht
    have he := hc ⟨t, ht.1, ht.2.le⟩
    have hd := ((hasDerivAt_id t).smul_const (h • v)).const_add x
    simpa only [he, one_smul, id_eq] using hd.hasDerivWithinAt (s := Ici t)
  · simp

theorem curve_spaceTime_outside {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {U : Set E} (hTime : ∀ z, (V z).1 = 1)
    (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0) (x : ℝ × E) (hx : x.2 ∉ U) (t : Time) :
    curve hV h hh x t = (x.1 + (t : ℝ) * h, x.2) := by
  have hc : ∀ s : Time, V (x + (s : ℝ) • h • (1, (0 : E))) = (1, 0) := by
    intro s
    apply Prod.ext
    · exact hTime _
    · exact hOut _ (by simpa using hx)
  have he := curve_of_const_along hV h hh x (1, (0 : E)) hc t.property
  calc
    curve hV h hh x t = x + (t : ℝ) • h • (1, (0 : E)) := he
    _ = (x.1 + (t : ℝ) * h, x.2) := by ext <;> simp [smul_eq_mul]

theorem curve_spaceTime_mapsTo {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {U : Set E} (hTime : ∀ z, (V z).1 = 1)
    (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0) (x : ℝ × E) (hx : x.2 ∈ U) (t : Time) :
    (curve hV h hh x t).2 ∈ U := by
  by_contra hout
  let y : ℝ × E := (x.1, (curve hV h hh x t).2)
  have he : curve hV h hh y t = curve hV h hh x t := by
    rw [curve_spaceTime_outside hV h hh hTime hOut y hout]
    apply Prod.ext
    · have he := curve_linear_component hV h hh (ContinuousLinearMap.fst ℝ ℝ E) 1 hTime x t
      simpa only [ContinuousLinearMap.coe_fst', smul_eq_mul, mul_one, y] using he.symm
    · rfl
  have hy := curve_injective hV h hh t he
  have hxy := congrArg Prod.snd hy
  exact hout (hxy ▸ hx)

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u15} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem step_preserves_tensor_on {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    (hVs : ContDiff ℝ ∞ V) (h : ℝ) (hh : ‖h‖₊ * K < 1)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E}
    (hB : ∀ z ∈ U, DifferentiableAt ℝ B z)
    (hInv : ∀ z ∈ U, ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0) (x : E) (hpath : ∀ t : Time, curve hV h hh x t ∈ U) (a b : E) :
    B (step hV h hh x) (fderiv ℝ (step hV h hh) x a)
      (fderiv ℝ (step hV h hh) x b) = B x a b := by
  let F : ℝ → ℝ := fun t => B (curve hV h hh x t)
    (variation hV h hh x a t) (variation hV h hh x b t)
  have hBc : ContinuousOn B U := fun z hz => (hB z hz).continuousAt.continuousWithinAt
  have hc : ContinuousOn F (Icc 0 1) :=
    ((hBc.comp (continuous_curve hV h hh x).continuousOn (fun t ht => hpath ⟨t, ht⟩)).clm_apply
      (continuous_variation hV hVs h hh x a).continuousOn).clm_apply
      (continuous_variation hV hVs h hh x b).continuousOn
  have hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt F 0 (Ici t) t := by
    intro t ht
    let T : Time := ⟨t, ht.1, ht.2.le⟩
    have hv := hasDerivAt_curve hV h hh x T
    have ha := hasDerivAt_variation hV hVs h hh x a T
    have hb := hasDerivAt_variation hV hVs h hh x b T
    have hdb : HasDerivAt (fun s : ℝ => B (curve hV h hh x s))
        (fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t))) t :=
      (hB (curve hV h hh x t) (hpath T)).hasFDerivAt.comp_hasDerivAt (l := B)
        (l' := fderiv ℝ B (curve hV h hh x t)) t hv
    have hdf := (hdb.clm_apply ha).clm_apply hb
    have hz :
        ((fderiv ℝ B (curve hV h hh x t) (h • V (curve hV h hh x t)))
          (variation hV h hh x a t) +
          B (curve hV h hh x t)
            (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x a t)))
          (variation hV h hh x b t) +
          B (curve hV h hh x t) (variation hV h hh x a t)
            (h • fderiv ℝ V (curve hV h hh x t) (variation hV h hh x b t)) = 0 := by
      simp only [map_smul, smul_apply,
        add_apply, smul_eq_mul]
      calc
        _ = h * (fderiv ℝ B (curve hV h hh x t) (V (curve hV h hh x t))
            (variation hV h hh x a t) (variation hV h hh x b t) +
          B (curve hV h hh x t)
            (fderiv ℝ V (curve hV h hh x t) (variation hV h hh x a t))
            (variation hV h hh x b t) +
          B (curve hV h hh x t) (variation hV h hh x a t)
            (fderiv ℝ V (curve hV h hh x t) (variation hV h hh x b t))) := by ring
        _ = 0 := by rw [hInv _ (hpath T), mul_zero]
    exact (hdf.congr_deriv hz).hasDerivWithinAt
  have he := constant_of_has_deriv_right_zero hc hd 1
    (show 1 ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa only [F, curve_one, variation_one hV hVs, curve_zero, variation_zero] using he

end
end SmoothODE

namespace SmoothODE

open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

variable {E : Type u16} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_preserves_tensor_on (f : E ≃ₜ E)
    (hf : ContDiff ℝ ∞ (f : E → E)) {U : Set E} (hU : MapsTo f U U)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x ∈ U, ∀ a b, B (f x) (fderiv ℝ (f : E → E) x a)
      (fderiv ℝ (f : E → E) x b) = B x a b) (n : ℕ) (x : E) (hx : x ∈ U) :
    (f ^ n) x ∈ U ∧ ∀ a b,
      B ((f ^ n) x) (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x a)
        (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x b) = B x a b := by
  induction n with
  | zero =>
    refine ⟨hx, ?_⟩
    intro a b
    change B x (fderiv ℝ (id : E → E) x a) (fderiv ℝ (id : E → E) x b) = _
    simp
  | succ n ih =>
    rw [pow_succ']
    refine ⟨hU ih.1, ?_⟩
    intro a b
    change B (f ((f ^ n) x)) (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x a)
      (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x b) = _
    rw [fderiv_comp x (hf.differentiable (by simp) _)
      ((contDiff_homeomorph_pow f hf n).differentiable (by simp) _)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hB _ ih.1]
    exact ih.2 a b

theorem exists_spaceTime_transport {V : ℝ × E → ℝ × E} {K : ℝ≥0}
    (hV : LipschitzWith K V) (hVs : ContDiff ℝ ∞ V) {U : Set E}
    (hTime : ∀ z, (V z).1 = 1) (hOut : ∀ z, z.2 ∉ U → (V z).2 = 0)
    {B : (ℝ × E) → (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ}
    (hB : ∀ z, z.2 ∈ U → DifferentiableAt ℝ B z)
    (hInv : ∀ z, z.2 ∈ U → ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0) (T : ℝ) :
    ∃ f : (ℝ × E) ≃ₜ (ℝ × E),
      ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E)) ∧
      ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E)) ∧
      (∀ x, (f x).1 = x.1 + T) ∧
      (∀ x, x.2 ∉ U → (f x).2 = x.2) ∧
      (∀ x, x.2 ∈ U → (f x).2 ∈ U ∧ ∀ a b,
        B (f x) (fderiv ℝ (f : (ℝ × E) → (ℝ × E)) x a)
          (fderiv ℝ (f : (ℝ × E) → (ℝ × E)) x b) = B x a b) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (‖T‖ * (K : ℝ)) 0)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  let h : ℝ := T / N
  have hh : ‖h‖₊ * K < 1 := by
    change ‖h‖ * (K : ℝ) < (1 : ℝ)
    dsimp [h]
    rw [abs_div, abs_of_pos hN0, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr ((le_max_left _ _).trans_lt hN)
  let f := stepHomeomorph hV hVs h hh
  have hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E)) := contDiff_step hV hVs h hh
  have hfi : ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E)) :=
    contDiff_step hV hVs (-h) (by simpa using hh)
  have hm : ∀ x, x.2 ∈ U → (f x).2 ∈ U := by
    intro x hx
    simpa only [Prod.mk.eta, curve_one, f, stepHomeomorph_apply] using
      curve_spaceTime_mapsTo hV h hh hTime hOut x hx ⟨1, by constructor <;> norm_num⟩
  have ho : ∀ x, x.2 ∉ U → (f x).2 = x.2 := by
    intro x hx
    have he := curve_spaceTime_outside hV h hh hTime hOut x hx ⟨1, by constructor <;> norm_num⟩
    simpa only [curve_one, f, stepHomeomorph_apply] using congrArg Prod.snd he
  refine ⟨f ^ N, contDiff_homeomorph_pow f hf N, ?_, ?_, ?_, ?_⟩
  · change ContDiff ℝ ∞ ((f ^ N)⁻¹ : (ℝ × E) ≃ₜ (ℝ × E))
    rw [← inv_pow]
    exact contDiff_homeomorph_pow f⁻¹ hfi N
  · intro x
    have hs : (N : ℝ) * h = T := by dsimp [h]; field_simp
    have he := homeomorph_pow_linear_component f (ContinuousLinearMap.fst ℝ ℝ E) h
      (by intro z; simpa only [smul_eq_mul, mul_one, f, stepHomeomorph_apply] using
        step_linear_component hV h hh (ContinuousLinearMap.fst ℝ ℝ E) 1 hTime z) N x
    simpa only [ContinuousLinearMap.coe_fst', nsmul_eq_mul, hs] using he
  · intro x hx
    have hi : ∀ n : ℕ, ((f ^ n) x).2 = x.2 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Homeomorph.mul_apply, ho _ (by simpa only [ih] using hx), ih]
    exact hi N
  · intro x hx
    apply homeomorph_pow_preserves_tensor_on f hf (U := Prod.snd ⁻¹' U)
      (fun _ hz => hm _ hz) (fun z hz a b => ?_) N x hx
    exact step_preserves_tensor_on hV hVs h hh (U := Prod.snd ⁻¹' U)
      (fun y hy => hB y hy) (fun y hy => hInv y hy) z
      (fun t => curve_spaceTime_mapsTo hV h hh hTime hOut z hz t) a b

end
end SmoothODE

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.TensorCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u17 u18 u19 u20 u21 u22

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

open Set Filter Function
open scoped Topology ContDiff

namespace TensorCalculus

variable {E : Type u17} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

attribute [local instance] OAI.TensorCalculus.oneTensorGroup
attribute [local instance] OAI.TensorCalculus.oneTensorSpace
attribute [local instance] OAI.TensorCalculus.twoTensorGroup
attribute [local instance] OAI.TensorCalculus.twoTensorSpace
theorem fderiv_evalTensor {D : Type u19} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {B : D → TwoTensor E} {x : D} (hB : DifferentiableAt ℝ B x)
    (d : D) (a b : E) : fderiv ℝ (fun y => B y a b) x d = fderiv ℝ B x d a b := by
  rw [fderiv_clm_apply (hB.clm_apply (differentiableAt_const a))
    (differentiableAt_const b)]
  rw [fderiv_clm_apply hB (differentiableAt_const a)]
  simp

theorem fderiv_skew_at {B : E → TwoTensor E} {x : E} (hB : DifferentiableAt ℝ B x)
    (hsk : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = -B y b a) (d a b : E) :
    fderiv ℝ B x d a b = -fderiv ℝ B x d b a := by
  have he : (fun y => B y a b) =ᶠ[𝓝 x] (fun y => -B y b a) :=
    hsk.mono (fun y hy => hy a b)
  have he' := congrArg (fun L : E →L[ℝ] ℝ => L d) he.fderiv_eq
  rw [fderiv_fun_neg] at he'
  simpa only [fderiv_evalTensor hB, neg_apply] using he'

theorem derivative_kernel_at {B : E → TwoTensor E} {V : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hV : DifferentiableAt ℝ V x)
    (hker : ∀ᶠ y in 𝓝 x, B y (V y) = 0) (a b : E) :
    B x (fderiv ℝ V x a) b + fderiv ℝ B x a (V x) b = 0 := by
  have hd : HasFDerivAt (fun y => B y (V y))
      ((B x).comp (fderiv ℝ V x) + (fderiv ℝ B x).flip (V x)) x :=
    hB.hasFDerivAt.clm_apply hV.hasFDerivAt
  have hz : HasFDerivAt (fun y => B y (V y)) 0 x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x).congr_of_eventuallyEq hker
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) (hd.unique hz)
  simpa using he

theorem invariant_of_closed_kernel_at {B : E → TwoTensor E} {V : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hV : DifferentiableAt ℝ V x)
    (hsk : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = -B y b a)
    (hclosed : ∀ a b c, fderiv ℝ B x a b c +
      fderiv ℝ B x b c a + fderiv ℝ B x c a b = 0)
    (hker : ∀ᶠ y in 𝓝 x, B y (V y) = 0) (a b : E) :
    fderiv ℝ B x (V x) a b + B x (fderiv ℝ V x a) b +
      B x a (fderiv ℝ V x b) = 0 := by
  have h1 := derivative_kernel_at hB hV hker a b
  have h2 := derivative_kernel_at hB hV hker b a
  have h3 := hclosed (V x) a b
  have h4 := fderiv_skew_at hB hsk a b (V x)
  have h5 := (hsk.self_of_nhds) a (fderiv ℝ V x b)
  linarith

theorem exteriorD_skew (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = -exteriorD γ x b a := by
  simp only [exteriorD_apply]; ring

theorem fderiv_exteriorD {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : DifferentiableAt ℝ (fderiv ℝ γ) x) (d a b : E) :
    fderiv ℝ (exteriorD γ) x d a b =
      fderiv ℝ (fderiv ℝ γ) x d a b - fderiv ℝ (fderiv ℝ γ) x d b a := by
  change fderiv ℝ (alt ∘ fderiv ℝ γ) x d a b = _
  rw [fderiv_comp x (ContinuousLinearMap.differentiableAt (alt (E := E))) hγ]
  simp

theorem contDiff_exteriorD {γ : E → E →L[ℝ] ℝ}
    (hγ : ContDiff ℝ ∞ γ) : ContDiff ℝ ∞ (exteriorD γ) := by
  change ContDiff ℝ ∞ ((alt (E := E)) ∘ fderiv ℝ γ)
  exact (alt (E := E)).contDiff.comp (hγ.fderiv_right (m := ∞) (by simp))

theorem exteriorD_closed {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : ContDiffAt ℝ ∞ γ x) (a b c : E) :
    fderiv ℝ (exteriorD γ) x a b c + fderiv ℝ (exteriorD γ) x b c a +
      fderiv ℝ (exteriorD γ) x c a b = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ γ) x :=
    (hγ.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiableAt (by simp)
  have hs := hγ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [fderiv_exteriorD hd]
  have h1 := congrArg (fun L : E →L[ℝ] ℝ => L c) (hs.eq a b)
  have h2 := congrArg (fun L : E →L[ℝ] ℝ => L a) (hs.eq b c)
  have h3 := congrArg (fun L : E →L[ℝ] ℝ => L b) (hs.eq c a)
  linarith

end
end TensorCalculus

namespace TensorCalculus

open Set Filter Function
open scoped Topology ContDiff

variable {E : Type u20} {F : Type u21} {D : Type u22} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

noncomputable section

theorem contDiffAt_pullLinear (L : F →L[ℝ] E) {B : D → TwoTensor E} {z : D}
    (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun x => pullLinear L (B x)) z := by
  let P : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ F E ℝ).flip L
  change ContDiffAt ℝ ∞ (fun x => P.comp ((B x).comp L)) z
  exact contDiffAt_const.clm_comp (hB.clm_comp contDiffAt_const)

theorem fderiv_pullLinear_eval (L : F →L[ℝ] E) {B : D → TwoTensor E} {z : D}
    (hB : DifferentiableAt ℝ B z)
    (hP : DifferentiableAt ℝ (fun x => pullLinear L (B x)) z) (d : D) (a b : F) :
    fderiv ℝ (fun x => pullLinear L (B x)) z d a b =
      fderiv ℝ B z d (L a) (L b) := by
  rw [← fderiv_evalTensor hP, ← fderiv_evalTensor hB]
  rfl

theorem pullLinear_closed (L : F →L[ℝ] E) {B : E → TwoTensor E} {z : F}
    (hB : ContDiffAt ℝ ∞ B (L z))
    (hclosed : ∀ a b c, fderiv ℝ B (L z) a b c +
      fderiv ℝ B (L z) b c a + fderiv ℝ B (L z) c a b = 0) (a b c : F) :
    fderiv ℝ (fun x => pullLinear L (B (L x))) z a b c +
      fderiv ℝ (fun x => pullLinear L (B (L x))) z b c a +
      fderiv ℝ (fun x => pullLinear L (B (L x))) z c a b = 0 := by
  have hs : ContDiffAt ℝ ∞ (fun x => B (L x)) z := hB.comp z L.contDiff.contDiffAt
  have ht := contDiffAt_pullLinear L hs
  have he (d u v : F) :
      fderiv ℝ (fun x => pullLinear L (B (L x))) z d u v =
        fderiv ℝ B (L z) (L d) (L u) (L v) := by
    rw [fderiv_pullLinear_eval L (hs.differentiableAt (by simp))
      (ht.differentiableAt (by simp))]
    rw [fderiv_fun_comp z (hB.differentiableAt (by simp)) L.differentiableAt]
    simp
  simp only [he]
  exact hclosed (L a) (L b) (L c)

end
end TensorCalculus

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.MoserField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u23 u24

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff

open Set Filter Function
open scoped Topology ContDiff NNReal

namespace Moser

variable {E : Type u23} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable section

omit [CompleteSpace E] in
theorem spatialField_eq_zero_of_oneForm_eq_zero
    (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) (hz : γ z.2 = 0) :
    spatialField A γ ρ z = 0 := by simp [spatialField, hz]

omit [CompleteSpace E] in
theorem contract_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E) (hA : (A z).IsInvertible) :
    A z (spatialField A γ ρ z) = -(ρ z.1) • γ z.2 := by
  simp only [spatialField, map_smul, hA.self_apply_inverse]

omit [CompleteSpace E] in

theorem oneForm_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    (γ : E → E →L[ℝ] ℝ) (ρ : ℝ → ℝ) (z : ℝ × E)
    (hA : (A z).IsInvertible) (hsk : ∀ a b, A z a b = -A z b a) :
    γ z.2 (spatialField A γ ρ z) = 0 := by
  let v := (A z).inverse (γ z.2)
  have he : A z v = γ z.2 := hA.self_apply_inverse _
  have hh := hsk v v
  have hz : A z v v = 0 := by linarith
  have hγv : γ z.2 v = 0 := by rw [← he]; exact hz
  simpa [spatialField, v, map_smul, smul_eq_mul] using
    congrArg (fun t : ℝ => -(ρ z.1) * t) hγv

theorem contDiff_spatialField {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ} {U : Set E}
    (hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z)
    (hi : ∀ z, z.2 ∈ U → (A z).IsInvertible)
    (hγ : ContDiff ℝ ∞ γ) (hρ : ContDiff ℝ ∞ ρ) (hs : tsupport γ ⊆ U) :
    ContDiff ℝ ∞ (spatialField A γ ρ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ U
  · have hv : ContDiffAt ℝ ∞ (fun x => (A x).inverse) z :=
      (hi z hz).contDiffAt_map_inverse.comp z (hA z hz)
    exact ((hρ.contDiffAt.comp z contDiffAt_fst).neg).smul
      (hv.clm_apply (hγ.contDiffAt.comp z contDiffAt_snd))
  · have ht : z.2 ∉ tsupport γ := fun hc => hz (hs hc)
    have he : ∀ᶠ y in 𝓝 z, y.2 ∉ tsupport γ :=
      continuous_snd.continuousAt ((isClosed_tsupport γ).isOpen_compl.mem_nhds ht)
    have heq : spatialField A γ ρ =ᶠ[𝓝 z] fun _ => 0 := he.mono (fun y hy =>
      spatialField_eq_zero_of_oneForm_eq_zero A γ ρ y (image_eq_zero_of_notMem_tsupport hy))
    exact contDiffAt_const.congr_of_eventuallyEq heq

omit [CompleteSpace E] in

theorem hasCompactSupport_spatialField
    (A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ)
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ}
    (hγ : HasCompactSupport γ) (hρ : HasCompactSupport ρ) :
    HasCompactSupport (spatialField A γ ρ) := by
  apply HasCompactSupport.of_support_subset_isCompact (hρ.prod hγ)
  intro z hz
  constructor
  · by_contra ht
    apply hz
    simp [spatialField, image_eq_zero_of_notMem_tsupport ht]
  · by_contra hx
    apply hz
    exact spatialField_eq_zero_of_oneForm_eq_zero A γ ρ z
      (image_eq_zero_of_notMem_tsupport hx)

theorem exists_lipschitz_spaceTimeField
    {A : (ℝ × E) → E →L[ℝ] E →L[ℝ] ℝ}
    {γ : E → E →L[ℝ] ℝ} {ρ : ℝ → ℝ} {U : Set E}
    (hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z)
    (hi : ∀ z, z.2 ∈ U → (A z).IsInvertible)
    (hγ : ContDiff ℝ ∞ γ) (hρ : ContDiff ℝ ∞ ρ) (hs : tsupport γ ⊆ U)
    (hcγ : HasCompactSupport γ) (hcρ : HasCompactSupport ρ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun z => ((1 : ℝ), spatialField A γ ρ z)) := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_spatialField A hcγ hcρ)
    (contDiff_spatialField hA hi hγ hρ hs) (by simp)
  exact ⟨max 0 K, (LipschitzWith.const (1 : ℝ)).prodMk hK⟩

end
end Moser

namespace Moser

open Set Filter Function TensorCalculus
open scoped Topology ContDiff

variable {E : Type u24} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

attribute [local instance] OAI.Moser.oneTensorGroup
attribute [local instance] OAI.Moser.oneTensorSpace
attribute [local instance] OAI.Moser.twoTensorGroup
attribute [local instance] OAI.Moser.twoTensorSpace
theorem contDiff_extendedOneForm {γ : E → E →L[ℝ] ℝ} {β : ℝ → ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (extendedOneForm γ β) := by
  exact (hβ.comp contDiff_fst).smul ((hγ.comp contDiff_snd).clm_comp contDiff_const)

theorem fderiv_extendedOneForm {γ : E → E →L[ℝ] ℝ} {β : ℝ → ℝ} {z : ℝ × E}
    (hγ : DifferentiableAt ℝ γ z.2) (hβ : DifferentiableAt ℝ β z.1)
    (a b : ℝ × E) :
    fderiv ℝ (extendedOneForm γ β) z a b =
      deriv β z.1 * a.1 * γ z.2 b.2 + β z.1 * fderiv ℝ γ z.2 a.2 b.2 := by
  have hα : DifferentiableAt ℝ (extendedOneForm γ β) z :=
    (hβ.comp z differentiableAt_fst).smul
      ((hγ.comp z differentiableAt_snd).clm_comp (differentiableAt_const _))
  have he : fderiv ℝ (fun y => extendedOneForm γ β y b) z a =
      fderiv ℝ (extendedOneForm γ β) z a b := by
    rw [fderiv_clm_apply hα (differentiableAt_const b)]; simp
  rw [← he]
  simp only [extendedOneForm_apply]
  have hb : DifferentiableAt ℝ (fun y : ℝ × E => β y.1) z :=
    hβ.comp z differentiableAt_fst
  have hg : DifferentiableAt ℝ (fun y : ℝ × E => γ y.2 b.2) z :=
    (hγ.comp z differentiableAt_snd).clm_apply (differentiableAt_const b.2)
  rw [fderiv_fun_mul hb hg]
  rw [fderiv_fun_comp z hβ differentiableAt_fst]
  have hg' : DifferentiableAt ℝ (fun y : ℝ × E => γ y.2) z :=
    hγ.comp z differentiableAt_snd
  rw [fderiv_clm_apply hg' (differentiableAt_const b.2)]
  rw [fderiv_fun_comp z hγ differentiableAt_snd]
  simp [fderiv_eq_smul_deriv, fderiv_fst, fderiv_snd, mul_comm, add_comm]

theorem contDiffAt_spatialTensor {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiffAt ℝ ∞ (spatialTensor W γ β) z := by
  have hd : ContDiff ℝ ∞ (exteriorD γ) :=
    contDiff_exteriorD hγ
  exact (hW.comp z contDiffAt_snd).add
    ((hβ.contDiffAt.comp z contDiffAt_fst).smul (hd.contDiffAt.comp z contDiffAt_snd))

theorem contDiffAt_spaceTimeTensor {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β) :
    ContDiffAt ℝ ∞ (spaceTimeTensor W γ β) z := by
  have hα := contDiff_extendedOneForm hγ hβ
  have hd : ContDiff ℝ ∞ (exteriorD (extendedOneForm γ β)) :=
    contDiff_exteriorD hα
  exact (contDiffAt_pullLinear (ContinuousLinearMap.snd ℝ ℝ E)
    (hW.comp z contDiffAt_snd)).add hd.contDiffAt

theorem spaceTimeTensor_apply {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hγ : DifferentiableAt ℝ γ z.2)
    (hβ : DifferentiableAt ℝ β z.1) (a b : ℝ × E) :
    spaceTimeTensor W γ β z a b = spatialTensor W γ β z a.2 b.2 +
      deriv β z.1 * (a.1 * γ z.2 b.2 - b.1 * γ z.2 a.2) := by
  simp only [spaceTimeTensor, add_apply, pullLinear_apply,
    ContinuousLinearMap.coe_snd', exteriorD_apply, fderiv_extendedOneForm hγ hβ,
    spatialTensor, smul_apply, smul_eq_mul]
  ring

theorem spaceTimeTensor_skew (W : E → TwoTensor E) (γ : E → E →L[ℝ] ℝ)
    (β : ℝ → ℝ) {z : ℝ × E} (hW : ∀ a b, W z.2 a b = -W z.2 b a) (a b : ℝ × E) :
    spaceTimeTensor W γ β z a b = -spaceTimeTensor W γ β z b a := by
  simp only [spaceTimeTensor, add_apply, pullLinear_apply,
    ContinuousLinearMap.coe_snd']
  rw [hW a.2 b.2, exteriorD_skew (extendedOneForm γ β) z a b]
  ring

theorem spaceTimeTensor_closed {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hW : ContDiffAt ℝ ∞ W z.2)
    (hγ : ContDiff ℝ ∞ γ) (hβ : ContDiff ℝ ∞ β)
    (hclosed : ∀ a b c, fderiv ℝ W z.2 a b c +
      fderiv ℝ W z.2 b c a + fderiv ℝ W z.2 c a b = 0) (a b c : ℝ × E) :
    fderiv ℝ (spaceTimeTensor W γ β) z a b c +
      fderiv ℝ (spaceTimeTensor W γ β) z b c a +
      fderiv ℝ (spaceTimeTensor W γ β) z c a b = 0 := by
  have hα := contDiff_extendedOneForm hγ hβ
  have hd : ContDiff ℝ ∞ (exteriorD (extendedOneForm γ β)) :=
    contDiff_exteriorD hα
  have hp : ContDiffAt ℝ ∞ (fun y : ℝ × E =>
      pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (W y.2)) z :=
    contDiffAt_pullLinear (ContinuousLinearMap.snd ℝ ℝ E) (hW.comp z contDiffAt_snd)
  have he := pullLinear_closed (ContinuousLinearMap.snd ℝ ℝ E) hW hclosed a b c
  have hf := exteriorD_closed (x := z) hα.contDiffAt a b c
  unfold spaceTimeTensor
  simp only [fderiv_fun_add (hp.differentiableAt (by simp))
    (hd.differentiable (by simp) z), add_apply]
  dsimp only [ContinuousLinearMap.coe_snd'] at he
  linarith

theorem spaceTimeTensor_kernel {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    {β : ℝ → ℝ} {z : ℝ × E} (hγ : DifferentiableAt ℝ γ z.2)
    (hβ : DifferentiableAt ℝ β z.1)
    (hi : (spatialTensor W γ β z).IsInvertible)
    (hsk : ∀ a b, W z.2 a b = -W z.2 b a) :
    spaceTimeTensor W γ β z (1, spatialField (spatialTensor W γ β) γ (deriv β) z) = 0 := by
  have hs : ∀ a b, spatialTensor W γ β z a b = -spatialTensor W γ β z b a := by
    intro a b
    simp only [spatialTensor, add_apply, smul_apply,
      smul_eq_mul]
    rw [hsk a b, exteriorD_skew γ z.2 a b]; ring
  have hc := contract_spatialField γ (deriv β) z hi
  have hz := oneForm_spatialField γ (deriv β) z hi hs
  apply ContinuousLinearMap.ext
  intro a
  rw [spaceTimeTensor_apply hγ hβ]
  simp only [one_mul, hz, mul_zero, sub_zero]
  have hc' := congrArg (fun L : E →L[ℝ] ℝ => L a.2) hc
  simp only [smul_apply, smul_eq_mul] at hc'
  simp only [zero_apply]
  linarith

end
end Moser

open Set Filter
open scoped Topology ContDiff

namespace Moser

noncomputable section

theorem timeCutoff_smooth : ContDiff ℝ ∞ timeCutoff := Real.smoothTransition.contDiff

theorem timeCutoff_mem (t : ℝ) : timeCutoff t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩

theorem timeCutoff_deriv_smooth : ContDiff ℝ ∞ (deriv timeCutoff) :=
  (show ContDiff ℝ (∞ + 1) timeCutoff by simpa using timeCutoff_smooth).deriv'

theorem timeCutoff_deriv_hasCompactSupport : HasCompactSupport (deriv timeCutoff) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  intro t ht
  by_contra h
  have hd : deriv timeCutoff t = 0 := by
    rw [mem_Icc, not_and_or] at h
    rcases h with h | h
    · have hn : ∀ᶠ y in 𝓝 t, y < 0 := Iio_mem_nhds (lt_of_not_ge h)
      have he : timeCutoff =ᶠ[𝓝 t] fun _ => 0 :=
        hn.mono (fun y hy =>
          Real.smoothTransition.zero_of_nonpos hy.le)
      rw [he.deriv_eq, deriv_const]
    · have hn : ∀ᶠ y in 𝓝 t, 1 < y := Ioi_mem_nhds (lt_of_not_ge h)
      have he : timeCutoff =ᶠ[𝓝 t] fun _ => 1 :=
        hn.mono (fun y hy =>
          Real.smoothTransition.one_of_one_le hy.le)
      rw [he.deriv_eq, deriv_const]
  exact ht hd

end
end Moser

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.MoserFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u25 u26

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter Function
open scoped Topology ContDiff

namespace SmoothODE

variable {E : Type u25} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

theorem contDiff_fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E))) :
    ContDiff ℝ ∞ (fiberHomeomorph f T hTime t : E → E) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).snd

theorem contDiff_fiberHomeomorph_symm (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f.symm : (ℝ × E) → (ℝ × E))) :
    ContDiff ℝ ∞ ((fiberHomeomorph f T hTime t).symm : E → E) :=
  (hf.comp (contDiff_const.prodMk contDiff_id)).snd

theorem fderiv_fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E))) (x a : E) :
    fderiv ℝ (f : (ℝ × E) → (ℝ × E)) (t, x) (0, a) =
      (0, fderiv ℝ (fiberHomeomorph f T hTime t : E → E) x a) := by
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x := by
    have hh := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
    have he : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) =
        ContinuousLinearMap.inr ℝ ℝ E := by
      ext y <;> rfl
    rw [he] at hh
    exact hh
  have hd := (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp x hi
  change HasFDerivAt (fun y : E => f (t, y)) _ x at hd
  have he : (fun y : E => f (t, y)) =
      fun y => (t + T, fiberHomeomorph f T hTime t y) := by
    funext y
    exact Prod.ext (hTime (t, y)) rfl
  have hd' := (hasFDerivAt_const (𝕜 := ℝ) (t + T) x).prodMk
    ((contDiff_fiberHomeomorph f T hTime t hf).differentiable (by simp) x).hasFDerivAt
  have hu := congrArg (fun L : E →L[ℝ] (ℝ × E) => L a)
    ((he ▸ hd).unique hd')
  simpa using hu

omit [NormedSpace ℝ E] in

theorem fiberHomeomorph_mapsTo (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ) {U : Set E}
    (hOut : ∀ z, z.2 ∉ U → (f z).2 = z.2) :
    ∀ x, fiberHomeomorph f T hTime t x ∈ U ↔ x ∈ U := by
  intro x
  constructor
  · intro hx
    by_contra hc
    rw [fiberHomeomorph_apply, hOut (t, x) hc] at hx
    exact hc hx
  · intro hx
    by_contra hc
    have he : fiberHomeomorph f T hTime t (fiberHomeomorph f T hTime t x) =
        fiberHomeomorph f T hTime t x := hOut _ hc
    have hu := (fiberHomeomorph f T hTime t).injective he
    exact hc (hu.symm ▸ hx)

end
end SmoothODE

namespace Moser

open Set Filter Function TensorCalculus SmoothODE
open scoped Topology ContDiff NNReal

variable {E : Type u26} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem compactlySupported_deformation_oai {U : Set E} (hU : IsOpen U)
    {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    (hW : ∀ x ∈ U, ContDiffAt ℝ ∞ W x)
    (hsk : ∀ x ∈ U, ∀ a b, W x a b = -W x b a)
    (hclosed : ∀ x ∈ U, ∀ a b c,
      fderiv ℝ W x a b c + fderiv ℝ W x b c a + fderiv ℝ W x c a b = 0)
    (hγ : ContDiff ℝ ∞ γ) (hcγ : HasCompactSupport γ) (hs : tsupport γ ⊆ U)
    (hi : ∀ x ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, (W x + s • exteriorD γ x).IsInvertible) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x, x ∉ U → F x = x) ∧ (∀ x, F x ∈ U ↔ x ∈ U) ∧
      ∀ x ∈ U, ∀ a b,
        (W (F x) + exteriorD γ (F x)) (fderiv ℝ (F : E → E) x a)
          (fderiv ℝ (F : E → E) x b) = W x a b := by
  let A := spatialTensor W γ timeCutoff
  let Y := spatialField A γ (deriv timeCutoff)
  let V : (ℝ × E) → (ℝ × E) := fun z => (1, Y z)
  let B := spaceTimeTensor W γ timeCutoff
  have hA : ∀ z, z.2 ∈ U → ContDiffAt ℝ ∞ A z := by
    intro z hz
    exact contDiffAt_spatialTensor (hW z.2 hz) hγ timeCutoff_smooth
  have hAi : ∀ z, z.2 ∈ U → (A z).IsInvertible := by
    intro z hz
    exact hi z.2 hz _ (timeCutoff_mem z.1)
  have hY : ContDiff ℝ ∞ Y :=
    contDiff_spatialField hA hAi hγ timeCutoff_deriv_smooth hs
  have hV : ContDiff ℝ ∞ V := contDiff_const.prodMk hY
  obtain ⟨K, hK⟩ := exists_lipschitz_spaceTimeField hA hAi hγ
    timeCutoff_deriv_smooth hs hcγ timeCutoff_deriv_hasCompactSupport
  have hOut : ∀ z, z.2 ∉ U → (V z).2 = 0 := by
    intro z hz
    exact spatialField_eq_zero_of_oneForm_eq_zero A γ (deriv timeCutoff) z
      (image_eq_zero_of_notMem_tsupport (fun hc => hz (hs hc)))
  have hB : ∀ z, z.2 ∈ U → DifferentiableAt ℝ B z := by
    intro z hz
    exact (contDiffAt_spaceTimeTensor (hW z.2 hz) hγ timeCutoff_smooth).differentiableAt
      (by simp)
  have hIv : ∀ z, z.2 ∈ U → ∀ a b, fderiv ℝ B z (V z) a b +
      B z (fderiv ℝ V z a) b + B z a (fderiv ℝ V z b) = 0 := by
    intro z hz a b
    have hn : ∀ᶠ y in 𝓝 z, y.2 ∈ U := continuous_snd.continuousAt (hU.mem_nhds hz)
    apply invariant_of_closed_kernel_at (hB z hz) (hV.differentiable (by simp) z)
      (hn.mono (fun y hy => spaceTimeTensor_skew W γ timeCutoff (hsk y.2 hy)))
      (spaceTimeTensor_closed (hW z.2 hz) hγ timeCutoff_smooth (hclosed z.2 hz))
      (hn.mono (fun y hy => spaceTimeTensor_kernel (hγ.differentiable (by simp) y.2)
        (timeCutoff_smooth.differentiable (by simp) y.1) (hAi y hy) (hsk y.2 hy)))
  obtain ⟨f, hf, hfi, htime, hout, htrans⟩ :=
    exists_spaceTime_transport hK hV (fun _ => rfl) hOut hB hIv 1
  let F := fiberHomeomorph f 1 htime 0
  have hF : ContDiff ℝ ∞ (F : E → E) := contDiff_fiberHomeomorph f 1 htime 0 hf
  have hFi : ContDiff ℝ ∞ (F.symm : E → E) := contDiff_fiberHomeomorph_symm f 1 htime 0 hfi
  refine ⟨F, hF, hFi, ?_, fiberHomeomorph_mapsTo f 1 htime 0 hout, ?_⟩
  · intro x hx
    exact hout (0, x) hx
  · intro x hx a b
    have hh := (htrans (0, x) hx).2 (0, a) (0, b)
    rw [fderiv_fiberHomeomorph f 1 htime 0 hf x a,
      fderiv_fiberHomeomorph f 1 htime 0 hf x b] at hh
    have he : f (0, x) = (1, F x) := by
      apply Prod.ext
      · simpa using htime (0, x)
      · rfl
    rw [he] at hh
    have hb (z : ℝ × E) (a b : E) : B z (0, a) (0, b) = A z a b := by
      dsimp only [B, A]
      rw [spaceTimeTensor_apply (hγ.differentiable (by simp) z.2)
        (timeCutoff_smooth.differentiable (by simp) z.1)]
      simp
    rw [hb, hb] at hh
    simpa only [A, spatialTensor, timeCutoff_zero, timeCutoff_one,
      one_smul, zero_smul, add_zero, add_apply, smul_apply, smul_eq_mul, zero_mul] using hh

end
end Moser

end LowerBoundInline

end OAI
end

theorem solution.{u26} : type_of% @OAI.Moser.compactlySupported_deformation_oai.{u26} := @OAI.Moser.compactlySupported_deformation_oai.{u26}
