-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.exists_actual_off_pulse_cauchy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:06:03.030401+00:00
-- url     : https://prove2.me/submissions/902f1743-78a0-4b9b-b799-f2898ffbedaa

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Flow_uniform_finite_varying_lowerCap_L2
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_bounded_patch_cauchy_bound

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators
open Filter

namespace SmoothLocal.Geometry

section Height
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {F : Coord → V} {p : Coord} {U : Set Coord}

theorem partial_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordPartial i F) U := by
  exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

end Height
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval ContDiff

namespace SmoothLocal.ODE

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_continuousMap_of_eval
    {a b : ℝ} {F P : ℝ → C(X, E)}
    (hP : ContinuousOn P (Ioo a b))
    (hpoint : ∀ t ∈ Ioo a b, ∀ x : X,
      HasDerivAt (fun s => F s x) (P t x) t)
    {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt F (P t) t := by
  have hmeas : StronglyMeasurableAtFilter P (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hP t ht
  have hprim : HasDerivAt (fun y => F t + ∫ s in t..y, P s) (P t) t :=
    (intervalIntegral.integral_hasDerivAt_right
      (IntervalIntegrable.refl : IntervalIntegrable P volume t t)
      hmeas (hP.continuousAt (Ioo_mem_nhds ht.1 ht.2))).const_add (F t)
  have heq : F =ᶠ[𝓝 t] (fun y => F t + ∫ s in t..y, P s) := by
    apply Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
    intro y hy
    have hseg : uIcc t y ⊆ Ioo a b := by
      intro s hs
      exact ⟨lt_of_lt_of_le (lt_min ht.1 hy.1) hs.1,
        lt_of_le_of_lt hs.2 (max_lt ht.2 hy.2)⟩
    have hPI : IntervalIntegrable P volume t y := (hP.mono hseg).intervalIntegrable
    apply ContinuousMap.ext
    intro x
    have hPIx : IntervalIntegrable (fun s => P s x) volume t y :=
      ((ContinuousMap.evalCLM ℝ x).continuous.comp_continuousOn
        (hP.mono hseg)).intervalIntegrable
    have hscalar : (∫ s in t..y, P s x) = F y x - F t x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hpoint s (hseg hs) x) hPIx
    change F y x = F t x + (ContinuousMap.evalCLM ℝ x) (∫ s in t..y, P s)
    rw [← (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hPI]
    change F y x = F t x + ∫ s in t..y, P s x
    rw [hscalar]
    abel
  exact hprim.congr_of_eventuallyEq heq

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.ODE

abbrev IntervalFunctions (r : ℝ) := C(Icc (-r) r, ℝ)

def intervalExtension (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) : C(ℝ, ℝ) :=
  letI : Fact (-r ≤ r) := ⟨by linarith⟩
  ContinuousMap.IccExtendCM h

theorem intervalExtension_apply_of_mem (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) {x : ℝ} (hx : x ∈ Icc (-r) r) :
    intervalExtension r hr h x = h ⟨x, hx⟩ := by
  let : Fact (-r ≤ r) := ⟨by linarith⟩
  exact ContinuousMap.IccExtendCM_of_mem hx

theorem intervalExtension_norm_le (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : ℝ) :
    ‖intervalExtension r hr h x‖ ≤ ‖h‖ := by
  exact h.norm_coe_le_norm _

@[simp]
theorem intervalExtension_add (r : ℝ) (hr : 0 < r)
    (h k : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (h + k) x =
      intervalExtension r hr h x + intervalExtension r hr k x := rfl

@[simp]
theorem intervalExtension_smul (r : ℝ) (hr : 0 < r)
    (c : ℝ) (h : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (c • h) x = c • intervalExtension r hr h x := rfl

def primitiveFunction (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) (x : ℝ) : ℝ :=
  ∫ t in 0..x, intervalExtension r hr h t

theorem primitiveFunction_continuous (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) : Continuous (primitiveFunction r hr h) :=
  (intervalIntegral.differentiable_integral_of_continuous
    (intervalExtension r hr h).continuous).continuous

theorem primitiveFunction_hasDerivAt (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : ℝ) :
    HasDerivAt (primitiveFunction r hr h) (intervalExtension r hr h x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((intervalExtension r hr h).continuous.intervalIntegrable 0 x)
    ((intervalExtension r hr h).continuous.stronglyMeasurableAtFilter volume (𝓝 x))
    (intervalExtension r hr h).continuous.continuousAt

def primitiveMap (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) : IntervalFunctions r :=
  ⟨fun x => primitiveFunction r hr h x,
    (primitiveFunction_continuous r hr h).comp continuous_subtype_val⟩

@[simp]
theorem primitiveMap_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    primitiveMap r hr h x = ∫ t in 0..(x : ℝ), intervalExtension r hr h t := rfl

def primitiveLinearMap (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →ₗ[ℝ] IntervalFunctions r where
  toFun := primitiveMap r hr
  map_add' h k := by
    apply ContinuousMap.ext
    intro x
    change (∫ t in 0..(x : ℝ), intervalExtension r hr (h + k) t) =
      (∫ t in 0..(x : ℝ), intervalExtension r hr h t) +
      (∫ t in 0..(x : ℝ), intervalExtension r hr k t)
    simp only [intervalExtension_add]
    exact intervalIntegral.integral_add
      ((intervalExtension r hr h).continuous.intervalIntegrable 0 x)
      ((intervalExtension r hr k).continuous.intervalIntegrable 0 x)
  map_smul' c h := by
    apply ContinuousMap.ext
    intro x
    change (∫ t in 0..(x : ℝ), intervalExtension r hr (c • h) t) =
      c • (∫ t in 0..(x : ℝ), intervalExtension r hr h t)
    simp only [intervalExtension_smul]
    exact intervalIntegral.integral_smul c (fun t => intervalExtension r hr h t)

theorem primitiveMap_norm_le (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) :
    ‖primitiveMap r hr h‖ ≤ r * ‖h‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hr.le (norm_nonneg h))).mpr
  intro x
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (x : ℝ)) (C := ‖h‖)
    (f := fun t => intervalExtension r hr h t)
    (fun t _ => intervalExtension_norm_le r hr h t)
  have hx : |(x : ℝ)| ≤ r := abs_le.mpr x.2
  change ‖∫ t in 0..(x : ℝ), intervalExtension r hr h t‖ ≤ r * ‖h‖
  calc
    ‖∫ t in 0..(x : ℝ), intervalExtension r hr h t‖ ≤ ‖h‖ * |(x : ℝ)| := by
      simpa only [sub_zero] using hi
    _ ≤ ‖h‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg h)
    _ = r * ‖h‖ := mul_comm _ _

def primitiveCLM (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →L[ℝ] IntervalFunctions r :=
  (primitiveLinearMap r hr).mkContinuous r (primitiveMap_norm_le r hr)

@[simp]
theorem primitiveCLM_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    primitiveCLM r hr h x = ∫ t in 0..(x : ℝ), intervalExtension r hr h t := rfl

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def jointDifferential (fx fy : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight fx +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight fy

theorem jointDifferential_eq_coprod (fx fy : ℝ) :
    jointDifferential fx fy =
      (ContinuousLinearMap.toSpanSingleton ℝ fx).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ fy) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [jointDifferential]

theorem hasFDerivAt_of_continuous_partials
    {s : Set (ℝ × ℝ)} (hs : IsOpen s) {f fx fy : (ℝ × ℝ) → ℝ}
    (hcx : ContinuousOn fx s) (hcy : ContinuousOn fy s)
    (hdx : ∀ p ∈ s, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hdy : ∀ p ∈ s, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2)
    {p : ℝ × ℝ} (hp : p ∈ s) :
    HasFDerivAt f (jointDifferential (fx p) (fy p)) p := by
  have hspan : Continuous (ContinuousLinearMap.toSpanSingleton ℝ :
      ℝ → (ℝ →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous
  have hfirst : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun x => f (x, q.2))
        (ContinuousLinearMap.toSpanSingleton ℝ (fx q)) q.1 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hdx q hq).hasFDerivAt
  have hsecond : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun y => f (q.1, y))
        (ContinuousLinearMap.toSpanSingleton ℝ (fy q)) q.2 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hdy q hq).hasFDerivAt
  have hfull := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ)
    (f := fun x y => f (x, y))
    (f₁ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (fx (x, y)))
    (f₂ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (fy (x, y)))
    hfirst hsecond
    (hspan.continuousAt.comp (hcx.continuousAt (hs.mem_nhds hp)))
    (hspan.continuousAt.comp (hcy.continuousAt (hs.mem_nhds hp)))
  rw [jointDifferential_eq_coprod]
  exact hfull.hasFDerivAt

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.Sobolev

theorem abs_two_mul_le_squares (a b : ℝ) : |2 * a * b| ≤ a^2 + b^2 := by
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]

theorem square_difference_le_interval_energy
    {f df : ℝ → ℝ} {a b x v : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t)
    (hx : x ∈ Icc a b) (hv : v ∈ Icc a b) :
    f x ^ 2 - f v ^ 2 ≤ ∫ t in a..b, (f t ^ 2 + df t ^ 2) := by
  have hsub : uIcc v x ⊆ Icc a b := uIcc_subset_Icc hv hx
  have hsq (t : ℝ) (ht : t ∈ uIcc v x) :
      HasDerivAt (fun r => f r ^ 2) (2 * f t * df t) t := by
    have hp := (hd t (hsub ht)).fun_pow 2
    simpa using hp
  have hcd : ContinuousOn (fun t => 2 * f t * df t) (uIcc v x) :=
    ((continuousOn_const.mul hf).mul hdf).mono hsub
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hsq hcd.intervalIntegrable
  have hE : ContinuousOn (fun t => f t ^ 2 + df t ^ 2) (Icc a b) :=
    (hf.pow 2).add (hdf.pow 2)
  have hbound : ∀ᵐ t ∂volume.restrict (uIoc v x),
      ‖2 * f t * df t‖ ≤ f t ^ 2 + df t ^ 2 :=
    Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using abs_two_mul_le_squares (f t) (df t))
  have hnorm := intervalIntegral.norm_integral_le_abs_of_norm_le hbound
    ((hE.mono hsub).intervalIntegrable)
  have hu : uIoc v x ⊆ uIoc a b :=
    uIoc_subset_uIoc_of_uIcc_subset_uIcc (by simpa only [uIcc_of_le hab] using hsub)
  have hnonneg : ∀ᵐ t ∂volume.restrict (uIoc a b), 0 ≤ f t ^ 2 + df t ^ 2 :=
    Filter.Eventually.of_forall (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmono := intervalIntegral.abs_integral_mono_interval hu hnonneg
    (hE.intervalIntegrable_of_Icc hab)
  have hI : 0 ≤ ∫ t in a..b, (f t ^ 2 + df t ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall hab
      (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hFTC, Real.norm_eq_abs] at hnorm
  rw [abs_of_nonneg hI] at hmono
  exact (le_abs_self _).trans (hnorm.trans hmono)

theorem interval_point_square_bound
    {f df : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t) (hx : x ∈ Icc a b) :
    f x ^ 2 ≤ (1 + 1 / (b - a)) * (∫ t in a..b, f t ^ 2) +
      ∫ t in a..b, df t ^ 2 := by
  let E : ℝ := ∫ t in a..b, (f t ^ 2 + df t ^ 2)
  have hpoint : ∀ v ∈ Icc a b, f x ^ 2 ≤ f v ^ 2 + E := by
    intro v hv
    have h := square_difference_le_interval_energy hab.le hf hdf hd hx hv
    dsimp only [E]
    linarith
  have hfi : IntervalIntegrable (fun t => f t^2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab.le
  have hdi : IntervalIntegrable (fun t => df t^2) volume a b :=
    (hdf.pow 2).intervalIntegrable_of_Icc hab.le
  have havg := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f x ^ 2) volume a b)
    (hfi.add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add hfi intervalIntegrable_const] at havg
  simp only [intervalIntegral.integral_const, smul_eq_mul] at havg
  have hE : E = (∫ t in a..b, f t ^ 2) + ∫ t in a..b, df t ^ 2 := by
    exact intervalIntegral.integral_add hfi hdi
  rw [hE] at havg
  have hw : 0 < b - a := sub_pos.mpr hab
  have hi : (b - a) * (1 / (b - a)) = 1 := by field_simp [ne_of_gt hw]
  have hiscale := congrArg (fun r : ℝ => r * (∫ t in a..b, f t ^ 2)) hi
  have hscaled : (b - a) * (f x^2) ≤ (b - a) *
      ((1 + 1 / (b - a)) * (∫ t in a..b, f t^2) + ∫ t in a..b, df t^2) := by
    nlinarith only [havg, hiscale]
  exact le_of_mul_le_mul_left hscaled hw

end SmoothLocal.Sobolev

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinatePoint_hasDerivAt_y (x y : ℝ) :
    HasDerivAt (coordinatePoint x) (Pi.single 1 (1 : ℝ) : Coord) y := by
  change HasDerivAt (fun t : ℝ => x • (Pi.single 0 (1 : ℝ) : Coord) +
    t • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) y
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id y).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (x • (Pi.single 0 (1 : ℝ) : Coord))

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace HessianCalculus

variable {f h : Coord → ℝ} {p : Coord}

theorem coordPartial_add_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q + h q) p = coordPartial i f p + coordPartial i h p := by
  simp [coordPartial, fderiv_fun_add hf hh]

theorem coordPartial_mul_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

end HessianCalculus

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def intervalExtensionEvalCLM (r : ℝ) (hr : 0 < r) (x : ℝ) :
    IntervalFunctions r →L[ℝ] ℝ :=
  letI : Fact (-r ≤ r) := ⟨by linarith⟩
  ContinuousMap.evalCLM ℝ (ContinuousMap.projIccCM (a := -r) (b := r) x)

theorem intervalExtension_family_continuousOn (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} {F : ℝ → IntervalFunctions r} (hF : ContinuousOn F s) :
    ContinuousOn (fun p : ℝ × ℝ => intervalExtension r hr (F p.2) p.1)
      (univ ×ˢ s) := by
  let : Fact (-r ≤ r) := ⟨by linarith⟩
  have hext : ContinuousOn (fun y => intervalExtension r hr (F y)) s :=
    ContinuousMap.IccExtendCM.continuous.comp_continuousOn hF
  exact (hext.comp continuous_snd.continuousOn (fun _ hp => hp.2)).eval
    continuous_fst.continuousOn

theorem intervalExtension_family_hasDerivAt (r : ℝ) (hr : 0 < r)
    {F : ℝ → IntervalFunctions r} {F' : IntervalFunctions r} {y : ℝ}
    (hF : HasDerivAt F F' y) (x : ℝ) :
    HasDerivAt (fun t => intervalExtension r hr (F t) x)
      (intervalExtension r hr F' x) y := by
  exact (intervalExtensionEvalCLM r hr x).hasFDerivAt.comp_hasDerivAt y hF

theorem intervalExtension_primitive_hasDerivAt (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (fun t => intervalExtension r hr (primitiveCLM r hr h) t)
      (intervalExtension r hr h x) x := by
  apply (primitiveFunction_hasDerivAt r hr h x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  rw [intervalExtension_apply_of_mem r hr _ ⟨ht.1.le, ht.2.le⟩]
  rfl

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Geometry
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Coord → V} {U : Set Coord} {p : Coord}

theorem normed_coordPartial_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordPartial i F) U :=
  (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

theorem coordPartial_eq_of_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f p = coordPartial i h p := by
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem eventuallyEq_zero_of_not_mem_tsupport
    {V : Type*} [Zero V] (f : Coord → V) {p : Coord} (hp : p ∉ tsupport f) :
    f =ᶠ[𝓝 p] 0 := by
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hp] with q hq
  change f q = 0
  by_contra hne
  exact hq (subset_tsupport f hne)

theorem metric_coeff_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (i j : Fin 2) :
    (fun q => g q i j) =ᶠ[𝓝 p] (fun q => h q i j) :=
  heq.mono fun _ hq => congrFun (congrFun hq i) j

theorem metric_add_eventuallyEq_of_not_mem_tsupport (g η : MetricField)
    {p : Coord} (hp : p ∉ tsupport η) : g + η =ᶠ[𝓝 p] g := by
  filter_upwards [eventuallyEq_zero_of_not_mem_tsupport η hp] with q hq
  change g q + η q = g q
  simp only [hq, Pi.zero_apply, add_zero]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
namespace LowQuotient

variable {U : Set Coord} {a b : Coord → ℝ} {p : Coord}

theorem iterated_contDiffOn (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (ds : List (Fin 2)) : ContDiffOn ℝ ∞ (iteratedCoordPartial ds a) U := by
  induction ds with
  | nil => exact ha
  | cons i ds ih => exact partial_contDiffOn ih hU i

theorem iterated_differentiableAt (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (hp : p ∈ U) (ds : List (Fin 2)) :
    DifferentiableAt ℝ (iteratedCoordPartial ds a) p :=
  ((iterated_contDiffOn ha hU ds).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)

end LowQuotient
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem contDiffOn_succ_of_continuous_partials
    {s : Set (ℝ × ℝ)} (hs : IsOpen s) {f fx fy : (ℝ × ℝ) → ℝ} (n : ℕ)
    (hfx : ContDiffOn ℝ n fx s) (hfy : ContDiffOn ℝ n fy s)
    (hdx : ∀ p ∈ s, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hdy : ∀ p ∈ s, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) :
    ContDiffOn ℝ (n + 1 : ℕ) f s := by
  have hd (p : ℝ × ℝ) (hp : p ∈ s) :
      HasFDerivAt f (jointDifferential (fx p) (fy p)) p :=
    hasFDerivAt_of_continuous_partials hs hfx.continuousOn hfy.continuousOn hdx hdy hp
  have hnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1) f s := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hfield : ContDiffOn ℝ n (fun p => jointDifferential (fx p) (fy p)) s :=
      (contDiffOn_const.smulRight hfx).add (contDiffOn_const.smulRight hfy)
    exact hfield.congr (fun p hp => (hd p hp).fderiv)
  simpa only [Nat.cast_add, Nat.cast_one] using hnext

end SmoothLocal.ODE

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem boxPoint_mem {tl tr sb st t s : ℝ}
    (ht : t ∈ Icc tl tr) (hs : s ∈ Icc sb st) :
    boxPoint t s ∈ closedRectangle tl tr sb st := by
  simpa [boxPoint, closedRectangle] using And.intro ht hs

theorem boxPoint_hasDerivAt_t (t s : ℝ) :
    HasDerivAt (fun x => boxPoint x s) (Pi.single 0 (1 : ℝ) : Coord) t := by
  simpa [boxPoint] using
    ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (s • (Pi.single 1 (1 : ℝ) : Coord))

theorem boxPoint_hasDerivAt_s (t s : ℝ) :
    HasDerivAt (boxPoint t) (Pi.single 1 (1 : ℝ) : Coord) s := by
  change HasDerivAt (fun x : ℝ => t • (Pi.single 0 (1 : ℝ) : Coord) +
    x • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) s
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id s).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (t • (Pi.single 0 (1 : ℝ) : Coord))

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

theorem rectangle_area_integrable
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Icc tl tr ×ˢ Icc sb st) :=
    hf.comp (by unfold boxPoint; fun_prop) (fun p hp => boxPoint_mem hp.1 hp.2)
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem rectangleIntegral_swap (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ t in tl..tr, ∫ s in sb..st, f (boxPoint t s) := by
  have hi : IntegrableOn (Function.uncurry (fun t s => f (boxPoint t s)))
      (uIoc tl tr ×ˢ uIoc sb st) := by
    simpa only [uIoc_of_le ht, uIoc_of_le hs, Function.uncurry_def] using rectangle_area_integrable hf
  exact (intervalIntegral_intervalIntegral_swap hi).symm

theorem rectangleIntegral_eq_area (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ p in Ioc tl tr ×ˢ Ioc sb st, f (boxPoint p.1 p.2) := by
  rw [rectangleIntegral_swap ht hs hf]
  simp_rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs]
  have hi : IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using rectangle_area_integrable hf
  simpa only [← Measure.volume_eq_prod] using
    (setIntegral_prod (fun p : ℝ × ℝ => f (boxPoint p.1 p.2)) hi).symm

variable {U : Set Coord}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

namespace CoordinateBound

theorem mono {f : Coord → ℝ} {U : Set Coord} {n m : ℕ} {M N : ℝ}
    (hf : CoordinateBound f U n M) (hm : m ≤ n) (hMN : M ≤ N) :
    CoordinateBound f U m N := fun ds hds p hp => (hf ds (hds.trans hm) p hp).trans hMN

theorem iterated_add {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => f x + h x) p =
      iteratedCoordPartial ds f p + iteratedCoordPartial ds h p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => f x + h x) =ᶠ[𝓝 p]
        (fun x => iteratedCoordPartial ds f x + iteratedCoordPartial ds h x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => f x + h x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    exact HessianCalculus.coordPartial_add_at
      (LowQuotient.iterated_differentiableAt hf hU hp ds)
      (LowQuotient.iterated_differentiableAt hh hU hp ds) i

theorem iterated_const_mul {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (c : ℝ)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => c * f x) p = c * iteratedCoordPartial ds f p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => c * f x) =ᶠ[𝓝 p]
        (fun x => c * iteratedCoordPartial ds f x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => c * f x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i,
      HessianCalculus.coordPartial_mul_at (f := fun _ : Coord => c) (h := iteratedCoordPartial ds f)
        (differentiableAt_const c)
        (LowQuotient.iterated_differentiableAt hf hU hp ds) i]
    simp [coordPartial, iteratedCoordPartial]

end CoordinateBound
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry SmoothLocal.Weighted

variable {tl tr sb st : ℝ}

theorem rectangle_vertical_integral_intervalIntegrable
    {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    IntervalIntegrable (fun t => ∫ s in sb..st, F (boxPoint t s)) volume tl tr := by
  have hi : Integrable (fun p : ℝ × ℝ => F (boxPoint p.1 p.2))
      ((volume.restrict (Ioc tl tr)).prod (volume.restrict (Ioc sb st))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact rectangle_area_integrable hF
  have hj := hi.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  simpa only [intervalIntegral.integral_of_le hs, IntegrableOn] using hj

theorem rectangle_vertical_trace_square_bound
    {F Fs : Coord → ℝ} (ht : tl ≤ tr) (hs : sb < st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hFs : ContinuousOn Fs (closedRectangle tl tr sb st))
    (hd : ∀ t ∈ Icc tl tr, ∀ s ∈ Icc sb st,
      HasDerivAt (fun r => F (boxPoint t r)) (Fs (boxPoint t s)) s)
    {y : ℝ} (hy : y ∈ Icc sb st) :
    (∫ t in tl..tr, F (boxPoint t y) ^ 2) ≤
      (1 + 1 / (st - sb)) * rectangleIntegral tl tr sb st (fun p => F p ^ 2) +
        rectangleIntegral tl tr sb st (fun p => Fs p ^ 2) := by
  have hv (t : ℝ) (ht' : t ∈ Icc tl tr) :
      F (boxPoint t y) ^ 2 ≤
      (1 + 1 / (st - sb)) * (∫ s in sb..st, F (boxPoint t s) ^ 2) +
        ∫ s in sb..st, Fs (boxPoint t s) ^ 2 := by
    have hcF : ContinuousOn (fun s => F (boxPoint t s)) (Icc sb st) :=
      hF.comp (by unfold boxPoint; fun_prop) (fun s hs' => boxPoint_mem ht' hs')
    have hcFs : ContinuousOn (fun s => Fs (boxPoint t s)) (Icc sb st) :=
      hFs.comp (by unfold boxPoint; fun_prop) (fun s hs' => boxPoint_mem ht' hs')
    exact interval_point_square_bound hs hcF hcFs (hd t ht') hy
  have hline : ContinuousOn (fun t => F (boxPoint t y) ^ 2) (Icc tl tr) :=
    (hF.pow 2).comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy)
  have hIF := rectangle_vertical_integral_intervalIntegrable ht hs.le (hF.pow 2)
  have hIS := rectangle_vertical_integral_intervalIntegrable ht hs.le (hFs.pow 2)
  have hi := intervalIntegral.integral_mono_on ht
    (hline.intervalIntegrable_of_Icc ht)
    ((hIF.const_mul (1 + 1 / (st - sb))).add hIS) hv
  rw [intervalIntegral.integral_add (hIF.const_mul (1 + 1 / (st - sb))) hIS,
    intervalIntegral.integral_const_mul] at hi
  rw [← rectangleIntegral_swap ht hs.le (hF.pow 2),
    ← rectangleIntegral_swap ht hs.le (hFs.pow 2)] at hi
  exact hi

theorem rectangle_point_square_bound
    {f : Coord → ℝ} {U : Set Coord} (ht : tl < tr) (hs : sb < st)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    {x y : ℝ} (hx : x ∈ Icc tl tr) (hy : y ∈ Icc sb st) :
    f (boxPoint x y) ^ 2 ≤
      (1 + 1 / (tr - tl)) * (1 + 1 / (st - sb)) *
        rectangleIntegral tl tr sb st (fun p => f p ^ 2) +
      (1 + 1 / (st - sb)) *
        rectangleIntegral tl tr sb st (fun p => coordPartial 0 f p ^ 2) +
      (1 + 1 / (tr - tl)) *
        rectangleIntegral tl tr sb st (fun p => coordPartial 1 f p ^ 2) +
      rectangleIntegral tl tr sb st (fun p => coordPartial 1 (coordPartial 0 f) p ^ 2) := by
  have hfx := partial_contDiffOn hf hU 0
  have hfy := partial_contDiffOn hf hU 1
  have hfyx := partial_contDiffOn hfx hU 1
  have hfc : ContinuousOn f (closedRectangle tl tr sb st) := hf.continuousOn.mono hbox
  have hfxc : ContinuousOn (coordPartial 0 f) (closedRectangle tl tr sb st) :=
    hfx.continuousOn.mono hbox
  have hfyc : ContinuousOn (coordPartial 1 f) (closedRectangle tl tr sb st) :=
    hfy.continuousOn.mono hbox
  have hfyxc : ContinuousOn (coordPartial 1 (coordPartial 0 f))
      (closedRectangle tl tr sb st) := hfyx.continuousOn.mono hbox
  have hdt (t : ℝ) (ht' : t ∈ Icc tl tr) :
      HasDerivAt (fun r => f (boxPoint r y)) (coordPartial 0 f (boxPoint t y)) t := by
    have hp := hbox (boxPoint_mem ht' hy)
    exact ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt t (boxPoint_hasDerivAt_t t y)
  have hds (t : ℝ) (ht' : t ∈ Icc tl tr) (s : ℝ) (hs' : s ∈ Icc sb st) :
      HasDerivAt (fun r => f (boxPoint t r)) (coordPartial 1 f (boxPoint t s)) s := by
    have hp := hbox (boxPoint_mem ht' hs')
    exact ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
  have hdxs (t : ℝ) (ht' : t ∈ Icc tl tr) (s : ℝ) (hs' : s ∈ Icc sb st) :
      HasDerivAt (fun r => coordPartial 0 f (boxPoint t r))
        (coordPartial 1 (coordPartial 0 f) (boxPoint t s)) s := by
    have hp := hbox (boxPoint_mem ht' hs')
    exact ((hfx.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
  have hhor := interval_point_square_bound ht
    (hfc.comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy))
    (hfxc.comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy)) hdt hx
  have hvf := rectangle_vertical_trace_square_bound ht.le hs hfc hfyc hds hy
  have hvx := rectangle_vertical_trace_square_bound ht.le hs hfxc hfyxc hdxs hy
  have hL : 0 ≤ 1 + 1 / (tr - tl) :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (sub_nonneg.mpr ht.le))
  have hscale := mul_le_mul_of_nonneg_left hvf hL
  simp only [Function.comp_def] at hhor
  nlinarith only [hscale, hvx, hhor]

end SmoothLocal.Sobolev

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def coordinateDirections : (ds : List (Fin 2)) → Fin ds.length → Coord
  | [] => fun _ => 0
  | i :: ds => Fin.cons (Pi.single i 1) (coordinateDirections ds)

theorem coordinateDirections_norm (ds : List (Fin 2)) (k : Fin ds.length) :
    ‖coordinateDirections ds k‖ = 1 := by
  induction ds with
  | nil => exact Fin.elim0 k
  | cons i ds ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [coordinateDirections, Pi.norm_single]
    · simpa only [coordinateDirections, Fin.cons_succ] using ih j

theorem iteratedCoordPartial_eq_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2))
    {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds f p = iteratedFDeriv ℝ ds.length f p (coordinateDirections ds) := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds f =ᶠ[𝓝 p]
        (fun x => iteratedFDeriv ℝ ds.length f x (coordinateDirections ds)) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds f) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl ds.length)
    simp only [List.length_cons]
    rw [hd.iteratedFDeriv_succ_apply_left']
    rfl

theorem norm_iteratedCoordPartial_le_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2))
    {p : Coord} (hp : p ∈ U) :
    ‖iteratedCoordPartial ds f p‖ ≤ ‖iteratedFDeriv ℝ ds.length f p‖ := by
  rw [iteratedCoordPartial_eq_jet hf hU ds hp]
  simpa only [coordinateDirections_norm, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ ds.length f p).le_opNorm (coordinateDirections ds)

theorem coordinateBound_of_frechet_bounds {f : Coord → ℝ} {U S : Set Coord} {n : ℕ} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U)
    (hB : ∀ k ≤ n, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M) :
    CoordinateBound f S n M := by
  intro ds hds p hp
  exact (norm_iteratedCoordPartial_le_jet hf hU ds (hSU hp)).trans (hB ds.length hds p hp)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.ODE

def pairPrimitive (B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t in 0..p.1, B (t, p.2)

def pairPartialY (B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ B p (0, 1)

def pairCompactFamily (B : ℝ × ℝ → ℝ) (r : ℝ) (y : ℝ) : IntervalFunctions r :=
  ContinuousMap.mkD (fun x : Icc (-r) r => B (x, y)) 0

theorem pairRectangle_isOpen (R a b : ℝ) : IsOpen (pairRectangle R a b) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem exists_compact_time_interval {R x : ℝ} (hx : x ∈ Ioo (-R) R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ x ∈ Ioo (-r) r := by
  have hxa : |x| < R := abs_lt.mpr hx
  refine ⟨(|x| + R) / 2, ?_, ?_, ?_⟩
  · nlinarith [abs_nonneg x]
  · linarith
  · apply abs_lt.mp
    linarith

theorem pairCompactFamily_joint_continuous {B : ℝ × ℝ → ℝ} {R a b r : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R) :
    ContinuousOn (fun p : ℝ × Icc (-r) r => B (p.2, p.1))
      (Ioo a b ×ˢ (univ : Set (Icc (-r) r))) := by
  exact hB.comp (by fun_prop)
    (fun p hp => ⟨⟨(neg_lt_neg hrR).trans_le p.2.2.1,
      p.2.2.2.trans_lt hrR⟩, hp.1⟩)

theorem pairCompactFamily_continuousOn {B : ℝ × ℝ → ℝ} {R a b r : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R) :
    ContinuousOn (pairCompactFamily B r) (Ioo a b) :=
  ContinuousMap.continuousOn_mkD_of_uncurry _ 0 (pairCompactFamily_joint_continuous hB hrR)

theorem pairCompactFamily_apply {B : ℝ × ℝ → ℝ} {R a b r y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R)
    (hy : y ∈ Ioo a b) (x : Icc (-r) r) : pairCompactFamily B r y x = B (x, y) := by
  have hc : Continuous (fun t : Icc (-r) r => B (t, y)) :=
    (pairCompactFamily_joint_continuous hB hrR).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy, mem_univ _⟩)
  unfold pairCompactFamily
  rw [ContinuousMap.mkD_of_continuous hc]
  rfl

theorem pairPrimitive_eq_clamped {B : ℝ × ℝ → ℝ} {R a b r x y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hr : 0 < r) (hrR : r < R)
    (hx : x ∈ Ioo (-r) r) (hy : y ∈ Ioo a b) :
    pairPrimitive B (x, y) =
      intervalExtension r hr (primitiveCLM r hr (pairCompactFamily B r y)) x := by
  rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩, primitiveCLM_apply]
  unfold pairPrimitive
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (-r) r :=
    uIcc_subset_Icc ⟨by linarith, hr.le⟩ ⟨hx.1.le, hx.2.le⟩ ht
  rw [intervalExtension_apply_of_mem r hr _ ht', pairCompactFamily_apply hB hrR hy]

theorem pairPrimitive_continuousOn {B : ℝ × ℝ → ℝ} {R a b : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) :
    ContinuousOn (pairPrimitive B) (pairRectangle R a b) := by
  intro p hp
  obtain ⟨r, hr, hrR, hpr⟩ := exists_compact_time_interval hp.1
  have hF := (primitiveCLM r hr).continuous.comp_continuousOn
    (pairCompactFamily_continuousOn hB hrR)
  have hc := intervalExtension_family_continuousOn r hr hF
  have hn : (univ : Set ℝ) ×ˢ Ioo a b ∈ 𝓝 p :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp.2⟩
  have he : pairPrimitive B =ᶠ[𝓝 p]
      (fun q => intervalExtension r hr (primitiveCLM r hr (pairCompactFamily B r q.2)) q.1) := by
    filter_upwards [(pairRectangle_isOpen r a b).mem_nhds ⟨hpr, hp.2⟩] with q hq
    exact pairPrimitive_eq_clamped hB hr hrR hq.1 hq.2
  exact ((hc.continuousAt hn).congr_of_eventuallyEq he).continuousWithinAt

theorem pairPartialY_contDiffOn {B : ℝ × ℝ → ℝ} {R a b : ℝ} (n : ℕ)
    (hB : ContDiffOn ℝ (n + 1 : ℕ) B (pairRectangle R a b)) :
    ContDiffOn ℝ n (pairPartialY B) (pairRectangle R a b) := by
  have hd : ContDiffOn ℝ n (fderiv ℝ B) (pairRectangle R a b) :=
    hB.fderiv_of_isOpen (pairRectangle_isOpen R a b) (by simp)
  exact hd.clm_apply contDiffOn_const

theorem pairCompactFamily_hasDerivAt {B : ℝ × ℝ → ℝ} {R a b r y : ℝ}
    (hB : ContDiffOn ℝ 1 B (pairRectangle R a b)) (hrR : r < R) (hy : y ∈ Ioo a b) :
    HasDerivAt (pairCompactFamily B r) (pairCompactFamily (pairPartialY B) r y) y := by
  have hP : ContinuousOn (pairPartialY B) (pairRectangle R a b) :=
    (pairPartialY_contDiffOn 0 hB).continuousOn
  apply hasDerivAt_continuousMap_of_eval (pairCompactFamily_continuousOn hP hrR) _ hy
  intro u hu x
  have hx : (x : ℝ) ∈ Ioo (-R) R :=
    ⟨(neg_lt_neg hrR).trans_le x.2.1, x.2.2.trans_lt hrR⟩
  have hxu : ((x : ℝ), u) ∈ pairRectangle R a b := ⟨hx, hu⟩
  have hd := ((hB.contDiffAt ((pairRectangle_isOpen R a b).mem_nhds hxu)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hs : HasDerivAt (fun v : ℝ => ((x : ℝ), v)) (0, 1) u :=
    (hasDerivAt_const u (x : ℝ)).prodMk (hasDerivAt_id u)
  have hpoint : HasDerivAt (fun v => B (x, v)) (pairPartialY B (x, u)) u :=
    hd.comp_hasDerivAt u hs
  rw [pairCompactFamily_apply hP hrR hu x]
  apply hpoint.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact pairCompactFamily_apply hB.continuousOn hrR hv x

theorem pairPrimitive_hasDerivAt_y {B : ℝ × ℝ → ℝ} {R a b x y : ℝ}
    (hB : ContDiffOn ℝ 1 B (pairRectangle R a b))
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    HasDerivAt (fun v => pairPrimitive B (x, v)) (pairPrimitive (pairPartialY B) (x, y)) y := by
  obtain ⟨r, hr, hrR, hxr⟩ := exists_compact_time_interval hx
  have hP : ContinuousOn (pairPartialY B) (pairRectangle R a b) :=
    (pairPartialY_contDiffOn 0 hB).continuousOn
  have hFB := pairCompactFamily_hasDerivAt hB hrR hy
  have hPB := (primitiveCLM r hr).hasFDerivAt.comp_hasDerivAt y hFB
  have hd := intervalExtension_family_hasDerivAt r hr hPB x
  rw [← pairPrimitive_eq_clamped hP hr hrR hxr hy] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hy] with v hv
  exact pairPrimitive_eq_clamped hB.continuousOn hr hrR hxr hv

theorem pairPrimitive_hasDerivAt_x {B : ℝ × ℝ → ℝ} {R a b x y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b))
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    HasDerivAt (fun t => pairPrimitive B (t, y)) (B (x, y)) x := by
  obtain ⟨r, hr, hrR, hxr⟩ := exists_compact_time_interval hx
  have hd := intervalExtension_primitive_hasDerivAt r hr (pairCompactFamily B r y) hxr
  rw [intervalExtension_apply_of_mem r hr _ ⟨hxr.1.le, hxr.2.le⟩,
    pairCompactFamily_apply hB hrR hy] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxr] with t ht
  exact pairPrimitive_eq_clamped hB hr hrR ht hy

theorem pairPrimitive_contDiffOn_nat (n : ℕ) {B : ℝ × ℝ → ℝ} {R a b : ℝ}
    (hB : ContDiffOn ℝ n B (pairRectangle R a b)) :
    ContDiffOn ℝ n (pairPrimitive B) (pairRectangle R a b) := by
  induction n generalizing B with
  | zero =>
      simpa only [Nat.cast_zero, contDiffOn_zero] using pairPrimitive_continuousOn hB.continuousOn
  | succ n hn =>
      have hB1 : ContDiffOn ℝ 1 B (pairRectangle R a b) := hB.of_le (by simp)
      apply contDiffOn_succ_of_continuous_partials (pairRectangle_isOpen R a b) n
        (hB.of_le (by simp)) (hn (pairPartialY_contDiffOn n hB))
      · intro p hp
        exact pairPrimitive_hasDerivAt_x hB.continuousOn hp.1 hp.2
      · intro p hp
        exact pairPrimitive_hasDerivAt_y hB1 hp.1 hp.2

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

theorem coordinatePoint_mem_modelSquare {t y : ℝ}
    (ht : t ∈ Icc (-3 : ℝ) 3) (hy : y ∈ Icc (-3 : ℝ) 3) :
    coordinatePoint t y ∈ modelSquare := by
  simp only [mem_Icc] at ht hy
  constructor <;> intro i <;> fin_cases i <;> simp [coordinatePoint] <;> tauto

variable {q : Coord → ℝ} {U : Set Coord}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry SmoothLocal.Weighted

def halfOpenCoordinateRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioc tl tr ∧ p 1 ∈ Ioc sb st}

theorem boxPoint_eta (p : Coord) : boxPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [boxPoint]

theorem rectangleIntegral_eq_coordinate_area
    {tl tr sb st : ℝ} {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F = ∫ p in halfOpenCoordinateRectangle tl tr sb st, F p := by
  rw [rectangleIntegral_eq_area ht hs hF]
  have h := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding
    (fun p : ℝ × ℝ => F (boxPoint p.1 p.2)) (Ioc tl tr ×ˢ Ioc sb st)
  change (∫ p in halfOpenCoordinateRectangle tl tr sb st, F (boxPoint (p 0) (p 1))) =
    ∫ p in Ioc tl tr ×ˢ Ioc sb st, F (boxPoint p.1 p.2) at h
  simpa only [boxPoint_eta] using h.symm

theorem rectangle_square_integral_le_region
    {tl tr sb st : ℝ} {f : Coord → ℝ} {V : Set Coord}
    (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st))
    (hsub : closedRectangle tl tr sb st ⊆ V) (hLp : MemLp f 2 (volume.restrict V)) :
    rectangleIntegral tl tr sb st (fun p => f p ^ 2) ≤ ∫ p in V, f p ^ 2 := by
  have hfsq : ContinuousOn (fun p => f p^2) (closedRectangle tl tr sb st) := hf.pow 2
  rw [rectangleIntegral_eq_coordinate_area ht hs hfsq]
  have hhalf : halfOpenCoordinateRectangle tl tr sb st ⊆ V := by
    intro p hp
    exact hsub ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩
  exact setIntegral_mono_set hLp.integrable_sq
    (Filter.Eventually.of_forall (fun p => sq_nonneg (f p))) hhalf.eventuallyLE

def squareSobolevWeight (r : ℝ) : ℝ := 1 + 1 / (2 * r)

def regionSobolevEnergy (r : ℝ) (V : Set Coord) (f : Coord → ℝ) : ℝ :=
  squareSobolevWeight r * squareSobolevWeight r * (∫ p in V, f p ^ 2) +
  squareSobolevWeight r * (∫ p in V, coordPartial 0 f p ^ 2) +
  squareSobolevWeight r * (∫ p in V, coordPartial 1 f p ^ 2) +
  ∫ p in V, coordPartial 1 (coordPartial 0 f) p ^ 2

theorem point_square_bound_on_region
    {f : Coord → ℝ} {U V : Set Coord} {p : Coord} {r : ℝ} (hr : 0 < r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hVU : V ⊆ U)
    (hsquare : closedRectangle (p 0 - r) (p 0 + r) (p 1 - r) (p 1 + r) ⊆ V)
    (h0 : MemLp f 2 (volume.restrict V))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict V))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict V))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2 (volume.restrict V)) :
    f p ^ 2 ≤ regionSobolevEnergy r V f := by
  have ht : p 0 - r < p 0 + r := by linarith
  have hs : p 1 - r < p 1 + r := by linarith
  have hbox := hsquare.trans hVU
  have hfx := partial_contDiffOn hf hU 0
  have hfy := partial_contDiffOn hf hU 1
  have hfyx := partial_contDiffOn hfx hU 1
  have hSob := rectangle_point_square_bound ht hs hU hf hbox
    (x := p 0) (y := p 1) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have hw : 0 ≤ squareSobolevWeight r := by
    unfold squareSobolevWeight
    exact add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  have hE0 := rectangle_square_integral_le_region ht.le hs.le (hf.continuousOn.mono hbox) hsquare h0
  have hEx := rectangle_square_integral_le_region ht.le hs.le (hfx.continuousOn.mono hbox) hsquare hx
  have hEy := rectangle_square_integral_le_region ht.le hs.le (hfy.continuousOn.mono hbox) hsquare hy
  have hExy := rectangle_square_integral_le_region ht.le hs.le (hfyx.continuousOn.mono hbox) hsquare hxy
  have hwidth0 : (p 0 + r) - (p 0 - r) = 2 * r := by ring
  have hwidth1 : (p 1 + r) - (p 1 - r) = 2 * r := by ring
  rw [boxPoint_eta, hwidth0, hwidth1] at hSob
  change f p ^ 2 ≤ squareSobolevWeight r * squareSobolevWeight r * _ +
    squareSobolevWeight r * _ + squareSobolevWeight r * _ + _ at hSob
  exact hSob.trans (add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hE0 (mul_nonneg hw hw))
      (mul_le_mul_of_nonneg_left hEx hw))
    (mul_le_mul_of_nonneg_left hEy hw)) hExy)

theorem point_abs_bound_on_region
    {f : Coord → ℝ} {U V : Set Coord} {p : Coord} {r : ℝ} (hr : 0 < r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hVU : V ⊆ U)
    (hsquare : closedRectangle (p 0 - r) (p 0 + r) (p 1 - r) (p 1 + r) ⊆ V)
    (h0 : MemLp f 2 (volume.restrict V))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict V))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict V))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2 (volume.restrict V)) :
    |f p| ≤ Real.sqrt (regionSobolevEnergy r V f) := by
  have h := point_square_bound_on_region hr hU hf hVU hsquare h0 hx hy hxy
  have he : 0 ≤ regionSobolevEnergy r V f := (sq_nonneg _).trans h
  nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (regionSobolevEnergy r V f), sq_abs (f p), abs_nonneg (f p)]

end SmoothLocal.Sobolev

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem inverseShearCoordinates_contDiff (q0 : ℝ) : ContDiff ℝ ∞ (inverseShearCoordinates q0) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Coord => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Coord => x 1 - q0 * x 0)
    fun_prop

theorem inverse_shear (q0 : ℝ) (p : Coord) :
    inverseShearCoordinates q0 (shearCoordinates q0 p) = p := by
  ext i
  fin_cases i <;> simp [shearCoordinates, inverseShearCoordinates]

theorem inverseShearCoordinates_eq_affine (q0 : ℝ) :
    inverseShearCoordinates q0 = affineCoordinates 0 (inverseShearMatrix q0) := by
  ext p i
  fin_cases i <;> simp [inverseShearCoordinates, inverseShearMatrix,
    affineCoordinates, dotProduct, Fin.sum_univ_two]
  ring

def pulseLocalBox (a delta tau : ℝ) : Set Coord :=
  Icc (![-a, -(delta / (2 * tau))]) (![a, delta / (2 * tau)])

def pulseOriginalBox (q0 a delta tau : ℝ) : Set Coord :=
  inverseShearCoordinates q0 '' pulseLocalBox a delta tau

theorem pulseLocalBox_isCompact (a delta tau : ℝ) : IsCompact (pulseLocalBox a delta tau) :=
  isCompact_Icc

theorem pulseOriginalBox_isCompact (q0 a delta tau : ℝ) :
    IsCompact (pulseOriginalBox q0 a delta tau) :=
  (pulseLocalBox_isCompact a delta tau).image (inverseShearCoordinates_contDiff q0).continuous

theorem pulseScalar_support_bound {a delta tau : ℝ} (ha : 0 < a)
    (hd : 0 < delta) (ht : 0 < tau) (N : ℕ) {p : Coord}
    (hp : pulseScalar a N delta tau p ≠ 0) : p ∈ pulseLocalBox a delta tau := by
  have hχ : axisBump a (p 0) ≠ 0 := by
    intro h
    apply hp
    simp only [pulseScalar, h, mul_zero, zero_mul]
  have hφ : temporalCutoff (tau * p 1 / delta) ≠ 0 := by
    intro h
    apply hp
    simp only [pulseScalar, h, mul_zero, zero_mul]
  have hx := abs_lt.mp (axisBump_support_bound ha hχ)
  have hy := axisBump_support_bound (by norm_num : (0 : ℝ) < 1 / 2) hφ
  have hy' : |p 1| < delta / (2 * tau) := by
    rw [abs_div, abs_mul, abs_of_pos ht, abs_of_pos hd] at hy
    apply (lt_div_iff₀ (mul_pos (by norm_num) ht)).mpr
    have hh := (div_lt_iff₀ hd).mp hy
    nlinarith
  constructor <;> intro i <;> fin_cases i
  · exact hx.1.le
  · exact (abs_lt.mp hy').1.le
  · exact hx.2.le
  · exact (abs_lt.mp hy').2.le

theorem pulseTensor_tsupport_subset {q0 a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) (N : ℕ) :
    tsupport (pulseTensor q0 a N delta tau) ⊆ pulseOriginalBox q0 a delta tau := by
  apply closure_minimal _ (pulseOriginalBox_isCompact q0 a delta tau).isClosed
  intro p hp
  have hs : pulseScalar a N delta tau (shearCoordinates q0 p) ≠ 0 := by
    intro h
    apply hp
    ext i j
    simp only [pulseTensor, h, zero_mul, Matrix.zero_apply]
  exact ⟨shearCoordinates q0 p, pulseScalar_support_bound ha hd ht N hs, inverse_shear q0 p⟩

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def verticalAverageDerivative (q : Coord → ℝ) (t y0 y1 : ℝ) : ℝ :=
  ∫ u in 0..1, coordPartial 1 q (coordinatePoint t (y0 + u * (y1 - y0)))

theorem verticalSegment_mem_modelSquare {t y0 y1 u : ℝ}
    (ht : t ∈ Icc (-2 : ℝ) 2) (hy0 : y0 ∈ Icc (-3 : ℝ) 3)
    (hy1 : y1 ∈ Icc (-3 : ℝ) 3) (hu : u ∈ Icc (0 : ℝ) 1) :
    coordinatePoint t (y0 + u * (y1 - y0)) ∈ modelSquare := by
  apply coordinatePoint_mem_modelSquare
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc := (convex_Icc (-3 : ℝ) 3) hy0 hy1
    (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (show (1 - u) + u = 1 by ring)
  have he : y0 + u * (y1 - y0) = (1 - u) * y0 + u * y1 := by ring
  rw [he]
  exact hc

theorem vertical_secant_identity {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {t y0 y1 : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2)
    (hy0 : y0 ∈ Icc (-3 : ℝ) 3) (hy1 : y1 ∈ Icc (-3 : ℝ) 3) :
    q (coordinatePoint t y1) - q (coordinatePoint t y0) =
      (y1 - y0) * verticalAverageDerivative q t y0 y1 := by
  let z (u : ℝ) := y0 + u * (y1 - y0)
  have hm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : coordinatePoint t (z u) ∈ U :=
    hSU (verticalSegment_mem_modelSquare ht hy0 hy1 hu)
  have hc : ContinuousOn (fun u => coordPartial 1 q (coordinatePoint t (z u)))
      (Icc (0 : ℝ) 1) :=
    (partial_contDiffOn hq hU 1).continuousOn.comp
      (by unfold coordinatePoint z; fun_prop) hm
  have hd (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v => q (coordinatePoint t (z v)))
        (coordPartial 1 q (coordinatePoint t (z u)) * (y1 - y0)) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    have hqy := ((hq.contDiffAt (hU.mem_nhds (hm u hu'))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt (z u) (coordinatePoint_hasDerivAt_y t (z u))
    have hz : HasDerivAt z (y1 - y0) u := by
      convert ((hasDerivAt_id u).mul_const (y1 - y0)).const_add y0 using 1 <;>
        first | rfl | ring
    convert hqy.comp u hz using 1 <;> rfl
  have hi : IntervalIntegrable
      (fun u => coordPartial 1 q (coordinatePoint t (z u))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hint : IntervalIntegrable
      (fun u => coordPartial 1 q (coordinatePoint t (z u)) * (y1 - y0)) volume 0 1 :=
    hi.mul_const (y1 - y0)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_mul_const] at hFTC
  have h0 : z 0 = y0 := by dsimp [z]; ring
  have h1 : z 1 = y1 := by dsimp [z]; ring
  rw [h0, h1] at hFTC
  unfold verticalAverageDerivative
  simpa only [z, mul_comm] using hFTC.symm

theorem verticalAverageDerivative_diagonal (q : Coord → ℝ) (t y : ℝ) :
    verticalAverageDerivative q t y y = coordPartial 1 q (coordinatePoint t y) := by
  simp [verticalAverageDerivative]

theorem flow_difference_hasDerivWithinAt {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {y0 y1 : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2)
    (hy0 : y0 t ∈ Icc (-3 : ℝ) 3) (hy1 : y1 t ∈ Icc (-3 : ℝ) 3)
    (hdy0 : HasDerivWithinAt y0 (-q (coordinatePoint t (y0 t))) (Icc (-2 : ℝ) 2) t)
    (hdy1 : HasDerivWithinAt y1 (-q (coordinatePoint t (y1 t))) (Icc (-2 : ℝ) 2) t) :
    HasDerivWithinAt (fun v => y1 v - y0 v)
      (-verticalAverageDerivative q t (y0 t) (y1 t) * (y1 t - y0 t))
      (Icc (-2 : ℝ) 2) t := by
  have he := vertical_secant_identity hq hU hSU ht hy0 hy1
  convert hdy1.sub hdy0 using 1 <;> try with_reducible_and_instances rfl
  first | rfl | nlinarith only [he]

theorem scalar_linear_evolution_formula {a z : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (ha : ContinuousOn a (Ioo (-R) R))
    (hz : ∀ t ∈ Ioo (-R) R, HasDerivAt z (-a t * z t) t)
    {t : ℝ} (ht : t ∈ Ioo (-R) R) :
    z t = z 0 * Real.exp (-(∫ r in 0..t, a r)) := by
  let I (v : ℝ) := ∫ r in 0..v, a r
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hI (v : ℝ) (hv : v ∈ Ioo (-R) R) : HasDerivAt I (a v) v := by
    have hseg : uIcc 0 v ⊆ Ioo (-R) R := by
      intro w hw
      exact ⟨(lt_min hzero.1 hv.1).trans_le hw.1,
        hw.2.trans_lt (max_lt hzero.2 hv.2)⟩
    exact intervalIntegral.integral_hasDerivAt_right (ha.mono hseg).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo ha v hv)
      (ha.continuousAt (isOpen_Ioo.mem_nhds hv))
  have hprod (v : ℝ) (hv : v ∈ Ioo (-R) R) :
      HasDerivAt (fun w => z w * Real.exp (I w)) 0 v := by
    convert (hz v hv).mul ((hI v hv).exp) using 1 <;> try with_reducible_and_instances rfl
    first | rfl | ring
  have heq : z t * Real.exp (I t) = z 0 := by
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-R) R).isPreconnected
      (fun v hv => (hprod v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hprod v hv).deriv) ht hzero
    simpa [I] using hconst
  have he : Real.exp (I t) * Real.exp (-I t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    z t = (z t * Real.exp (I t)) * Real.exp (-I t) := by rw [mul_assoc, he, mul_one]
    _ = z 0 * Real.exp (-I t) := by rw [heq]
    _ = _ := rfl

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem continuous_intervalIntegral_of_joint
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {a b : ℝ} (hab : a ≤ b) {f : X → ℝ → ℝ}
    (hf : Continuous (fun p : X × Icc a b => f p.1 p.2)) :
    Continuous (fun x => ∫ u in a..b, f x u) := by
  let g : X → ℝ → ℝ := fun x u => f x (projIcc a b hab u)
  have hg : Continuous (uncurry g) :=
    hf.comp (continuous_fst.prodMk ((continuous_projIcc (h := hab)).comp continuous_snd))
  have hc : Continuous (fun x => ∫ u in Icc a b, g x u) :=
    continuous_parametric_integral_of_continuous hg isCompact_Icc
  apply hc.congr
  intro x
  calc
    (∫ u in Icc a b, g x u) = ∫ u in a..b, g x u := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    _ = ∫ u in a..b, f x u := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
      simp only [g, projIcc_of_mem hab hu']

abbrev CapInterval := Icc (-2 : ℝ) 2
abbrev VerticalInterval := Icc (-3 : ℝ) 3

theorem verticalAverageDerivative_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) :
    Continuous (fun p : CapInterval × (VerticalInterval × VerticalInterval) =>
      verticalAverageDerivative q p.1 p.2.1 p.2.2) := by
  apply continuous_intervalIntegral_of_joint (show (0 : ℝ) ≤ 1 by norm_num)
  have hmap : Continuous
      (fun p : (CapInterval × (VerticalInterval × VerticalInterval)) × Icc (0 : ℝ) 1 =>
        coordinatePoint p.1.1 ((p.1.2.1 : ℝ) + p.2 * ((p.1.2.2 : ℝ) - p.1.2.1))) := by
    unfold coordinatePoint
    fun_prop
  exact (partial_contDiffOn hq hU 1).continuousOn.comp_continuous hmap
    (fun p => hSU (verticalSegment_mem_modelSquare p.1.1.2 p.1.2.1.2 p.1.2.2.2 p.2.2))

def flowAverageCoefficient (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (s0 s1 t : ℝ) : ℝ :=
  verticalAverageDerivative q t (Y s0 t) (Y s1 t)

theorem flowAverageCoefficient_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {Y : ℝ → ℝ → ℝ}
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3) :
    Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      flowAverageCoefficient q Y p.1 p.2.1 p.2.2) := by
  have hy0 : Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      Y p.1 p.2.2) :=
    hY.comp_continuous
      (f := fun p : CapInterval × (CapInterval × CapInterval) => ((p.1 : ℝ), (p.2.2 : ℝ)))
      (by fun_prop) (fun p => ⟨p.1.2, p.2.2.2⟩)
  have hy1 : Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      Y p.2.1 p.2.2) :=
    hY.comp_continuous
      (f := fun p : CapInterval × (CapInterval × CapInterval) => ((p.2.1 : ℝ), (p.2.2 : ℝ)))
      (by fun_prop) (fun p => ⟨p.2.1.2, p.2.2.2⟩)
  have hmap : Continuous
      (fun p : CapInterval × (CapInterval × CapInterval) =>
        (p.2.2, ((⟨Y p.1 p.2.2, hrange _ p.1.2 _ p.2.2.2⟩,
          ⟨Y p.2.1 p.2.2, hrange _ p.2.1.2 _ p.2.2.2⟩) :
          VerticalInterval × VerticalInterval))) :=
    (continuous_snd.snd).prodMk
      ((hy0.subtype_mk _).prodMk (hy1.subtype_mk _))
  exact (verticalAverageDerivative_continuous hq hU hSU).comp hmap

theorem flowAverageIntegral_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {Y : ℝ → ℝ → ℝ}
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3) {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    Continuous (fun p : CapInterval × CapInterval =>
      ∫ u in 0..t, flowAverageCoefficient q Y p.1 p.2 u) := by
  have hcoeff := flowAverageCoefficient_continuous hq hU hSU hY hrange
  have haux (a b : ℝ) (hab : a ≤ b) (ha : -2 ≤ a) (hb : b ≤ 2) :
      Continuous (fun p : CapInterval × CapInterval =>
        ∫ u in a..b, flowAverageCoefficient q Y p.1 p.2 u) := by
    apply continuous_intervalIntegral_of_joint hab
    have hmap : Continuous
        (fun p : (CapInterval × CapInterval) × Icc a b =>
          (p.1.1, (p.1.2, (⟨p.2, ⟨ha.trans p.2.2.1, p.2.2.2.trans hb⟩⟩ : CapInterval)))) := by
      fun_prop
    exact hcoeff.comp hmap
  by_cases ht0 : 0 ≤ t
  · exact haux 0 t ht0 (by norm_num) ht.2
  · have hc := (haux t 0 (le_of_not_ge ht0) ht.1 (by norm_num)).neg
    apply hc.congr
    intro p
    exact (intervalIntegral.integral_symm _ _).symm

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem heightInShearCoordinates_contDiffOn {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (q0 : ℝ) :
    ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) (inverseShearCoordinates q0 ⁻¹' U) :=
  hz.comp (inverseShearCoordinates_contDiff q0).contDiffOn (fun _ hp => hp)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem hasDerivAt_of_exact_secant {f g : ℝ → ℝ} {s : ℝ}
    (hg : ContinuousAt g s)
    (he : ∀ᶠ u in 𝓝 s, f u - f s = (u - s) * g u) :
    HasDerivAt f (g s) s := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : slope f s =ᶠ[𝓝[≠] s] g := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hne
    have hne' : u ≠ s := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
    rw [slope_def_field, hu]
    exact mul_div_cancel_left₀ (g u) (sub_ne_zero.mpr hne')
  exact (hg.mono_left nhdsWithin_le_nhds).congr' hslope.symm

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem flow_difference_formula
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {s0 s1 t : ℝ} (hs0 : s0 ∈ Icc (-2 : ℝ) 2) (hs1 : s1 ∈ Icc (-2 : ℝ) 2)
    (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Y s1 t - Y s0 t = (s1 - s0) *
      Real.exp (-(∫ u in 0..t, flowAverageCoefficient q Y s0 s1 u)) := by
  have hcoeff := flowAverageCoefficient_continuous hq hU hSU hY hrange
  have ha : ContinuousOn (flowAverageCoefficient q Y s0 s1) (Icc (-2 : ℝ) 2) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcoeff.comp
      ((continuous_const (y := (⟨s0, hs0⟩ : CapInterval))).prodMk
        ((continuous_const (y := (⟨s1, hs1⟩ : CapInterval))).prodMk continuous_id))
  have hz (u : ℝ) (hu : u ∈ Ioo (-2 : ℝ) 2) :
      HasDerivAt (fun v => Y s1 v - Y s0 v)
        (-flowAverageCoefficient q Y s0 s1 u * (Y s1 u - Y s0 u)) u := by
    exact (flow_difference_hasDerivWithinAt hq hU hSU ⟨hu.1.le, hu.2.le⟩
      (hrange s0 hs0 u ⟨hu.1.le, hu.2.le⟩) (hrange s1 hs1 u ⟨hu.1.le, hu.2.le⟩)
      (hode s0 hs0 u ⟨hu.1.le, hu.2.le⟩) (hode s1 hs1 u ⟨hu.1.le, hu.2.le⟩)).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2)
  have he := scalar_linear_evolution_formula (show (0 : ℝ) < 2 by norm_num)
    (ha.mono Ioo_subset_Icc_self) hz ht
  simpa only [hstart s0 hs0, hstart s1 hs1] using he

theorem cap_flow_hasDerivAt_initial
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => Y u t)
      (Real.exp (-(∫ r in 0..t, coordPartial 1 q (coordinatePoint r (Y s r))))) s := by
  let G (u : ℝ) := Real.exp (-(∫ r in 0..t, flowAverageCoefficient q Y s u r))
  have hG : ContinuousOn G (Icc (-2 : ℝ) 2) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (((flowAverageIntegral_continuous hq hU hSU hY hrange
      ⟨ht.1.le, ht.2.le⟩).comp
        ((continuous_const (y := (⟨s, ⟨hs.1.le, hs.2.le⟩⟩ : CapInterval))).prodMk continuous_id)).neg).rexp
  have he : ∀ᶠ u in 𝓝 s, Y u t - Y s t = (u - s) * G u := by
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with u hu
    exact flow_difference_formula hq hU hSU hY hrange hstart hode ⟨hs.1.le, hs.2.le⟩ hu ht
  have hd := hasDerivAt_of_exact_secant (hG.continuousAt (Icc_mem_nhds hs.1 hs.2)) he
  have hdiag : G s = Real.exp (-(∫ r in 0..t,
      coordPartial 1 q (coordinatePoint r (Y s r)))) := by
    simp only [G, flowAverageCoefficient, verticalAverageDerivative_diagonal]
  rw [hdiag] at hd
  exact hd

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def flowCoordinateMap (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Coord :=
  coordinatePoint p.1 (Y p.2 p.1)

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem cap_flow_joint_contDiffOn
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) := by
  let D := pairRectangle 2 (-2) 2
  let F (p : ℝ × ℝ) := Y p.2 p.1
  let B (p : ℝ × ℝ) := coordPartial 1 q (flowCoordinateMap Y p)
  have hmem : MapsTo (flowCoordinateMap Y) D U := by
    intro p hp
    exact hSU (coordinatePoint_mem_modelSquare
      ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
      (hrange p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩))
  have hdx (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => F (x, p.2)) (-q (flowCoordinateMap Y p)) p.1 := by
    exact (hode p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩).hasDerivAt
      (Icc_mem_nhds hp.1.1 hp.1.2)
  have hdy (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => F (p.1, y)) (Real.exp (-pairPrimitive B p)) p.2 := by
    exact cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hnat : ∀ n : ℕ, ContDiffOn ℝ n F D := by
    intro n
    induction n with
    | zero =>
        have hc : ContinuousOn F D := hY.comp continuous_swap.continuousOn
          (fun p hp => ⟨⟨hp.2.1.le, hp.2.2.le⟩, ⟨hp.1.1.le, hp.1.2.le⟩⟩)
        simpa only [Nat.cast_zero, contDiffOn_zero] using hc
    | succ n hn =>
        have horder : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
        have hmap : ContDiffOn ℝ n (flowCoordinateMap Y) D := by
          exact (contDiffOn_fst.smul contDiffOn_const).add (hn.smul contDiffOn_const)
        have hfx : ContDiffOn ℝ n (fun p => -q (flowCoordinateMap Y p)) D :=
          ((hq.of_le horder).comp hmap hmem).neg
        have hB : ContDiffOn ℝ n B D :=
          ((partial_contDiffOn hq hU 1).of_le horder).comp hmap hmem
        have hfy : ContDiffOn ℝ n (fun p => Real.exp (-pairPrimitive B p)) D :=
          ((pairPrimitive_contDiffOn_nat n hB).neg).exp
        exact contDiffOn_succ_of_continuous_partials (pairRectangle_isOpen 2 (-2) 2) n
          hfx hfy hdx hdy
  exact contDiffOn_infty.mpr hnat

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem capChart_zero (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 0 = p 0 := by
  simp [capChart, coordinatePoint]

theorem capChart_one (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 1 = capFlowHeight Y p := by
  simp [capChart, coordinatePoint]

variable {Y : ℝ → ℝ → ℝ}

theorem capFlowHeight_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain := by
  exact hY.comp ((contDiffOn_apply ℝ ℝ 0 _).prodMk (contDiffOn_apply ℝ ℝ 1 _))
    (fun p hp => hp)

theorem capChart_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capChart Y) capChartDomain := by
  exact ((contDiffOn_apply ℝ ℝ 0 _).smul contDiffOn_const).add
    ((capFlowHeight_contDiffOn hY).smul contDiffOn_const)

variable {q : Coord → ℝ}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem flow_initial_integral_bound
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    {M : ℝ} (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Icc (-2 : ℝ) 2) (ht : t ∈ Icc (-2 : ℝ) 2) :
    IntervalIntegrable (fun r => coordPartial 1 q (coordinatePoint r (Y s r))) volume 0 t ∧
      |∫ r in 0..t, coordPartial 1 q (coordinatePoint r (Y s r))| ≤ 2 * M := by
  have hmem (u : ℝ) (hu : u ∈ Icc (-2 : ℝ) 2) :
      coordinatePoint u (Y s u) ∈ modelSquare :=
    coordinatePoint_mem_modelSquare ⟨by linarith [hu.1], by linarith [hu.2]⟩ (hrange s hs u hu)
  have hy : ContinuousOn (Y s) (Icc (-2 : ℝ) 2) :=
    hY.comp (f := fun u : ℝ => (s, u)) (by fun_prop) (fun u hu => ⟨hs, hu⟩)
  have hmap : ContinuousOn (fun u => coordinatePoint u (Y s u)) (Icc (-2 : ℝ) 2) :=
    (continuousOn_id.smul continuousOn_const).add (hy.smul continuousOn_const)
  have hc : ContinuousOn (fun u => coordPartial 1 q (coordinatePoint u (Y s u)))
      (Icc (-2 : ℝ) 2) :=
    (partial_contDiffOn hq hU 1).continuousOn.comp hmap (fun u hu => hSU (hmem u hu))
  have hseg : uIcc (0 : ℝ) t ⊆ Icc (-2 : ℝ) 2 :=
    uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ht
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := M)
    (f := fun u => coordPartial 1 q (coordinatePoint u (Y s u)))
    (fun u hu => by
      rw [Real.norm_eq_abs]
      exact hMq _ (hmem u (hseg (uIoc_subset_uIcc hu))))
  have ht2 : |t| ≤ 2 := abs_le.mpr ht
  calc
    _ ≤ M * |t| := by simpa only [Real.norm_eq_abs, sub_zero] using hh
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left ht2 hM
    _ = 2 * M := mul_comm _ _

theorem cap_flow_initial_deriv_bounds
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M : ℝ} (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Real.exp (-2 * M) ≤ deriv (fun u => Y u t) s ∧
      deriv (fun u => Y u t) s ≤ Real.exp (2 * M) := by
  have hI := (flow_initial_integral_bound hq hU hSU hY hrange hM hMq
    ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩).2
  rw [(cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).deriv]
  constructor
  · apply Real.exp_monotone
    linarith [(abs_le.mp hI).2]
  · apply Real.exp_monotone
    linarith [(abs_le.mp hI).1]

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flowCoordinateMap_mem_modelSquare {p : ℝ × ℝ}
    (hp : p ∈ pairRectangle 2 (-2) 2) : flowCoordinateMap Y p ∈ modelSquare := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hbound : Y p.2 p.1 ∈ Icc (-3 : ℝ) 3 := by
    apply isClosed_Icc.mem_of_tendsto
      (hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).continuousAt
    filter_upwards [(pairRectangle_isOpen 2 (-2) 2).mem_nhds hp] with point hpoint
    exact hrange point.2 ⟨hpoint.2.1.le, hpoint.2.2.le⟩
      point.1 ⟨hpoint.1.1.le, hpoint.1.2.le⟩
  exact coordinatePoint_mem_modelSquare ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    hbound

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def timeFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (Y p.2) p.1

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_time_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (Y s) (-q (coordinatePoint t (Y s t))) t := by
  have hsmooth := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have htime : DifferentiableAt ℝ (Y s) t :=
    ((hsmooth.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨ht, hs⟩)).differentiableAt
      (by simp)).comp t (differentiableAt_id.prodMk (differentiableAt_const s))
  have hderiv := (hode s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  simpa only [hderiv.deriv] using htime.hasDerivAt

theorem timeFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    timeFlowDerivative Y (t, s) = -q (coordinatePoint t (Y s t)) :=
  (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem modelOpenSquare_subset : modelOpenSquare ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> fin_cases i
  · exact hp.1.1.le
  · exact hp.2.1.le
  · exact hp.1.2.le
  · exact hp.2.2.le

theorem capChart_mem_modelOpenSquare {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hp : p ∈ capChartDomain) (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) :
    capChart Y p ∈ modelOpenSquare := by
  change (capChart Y p) 0 ∈ Ioo (-3 : ℝ) 3 ∧ (capChart Y p) 1 ∈ Ioo (-3 : ℝ) 3
  rw [capChart_zero, capChart_one]
  constructor
  · constructor <;> linarith [hp.1.1, hp.1.2]
  · constructor <;> linarith [hp.2.1, hp.2.2, (abs_le.mp hdisp).1, (abs_le.mp hdisp).2]

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_time_bound
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |timeFlowDerivative Y (t, s)| ≤ (1 : ℝ) / 100 := by
  rw [timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht, abs_neg]
  exact hq0 _ (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩)

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev

theorem capRectangle_isCompact (tl tr sb st : ℝ) : IsCompact (closedRectangle tl tr sb st) := by
  have he : closedRectangle tl tr sb st =
      (fun q : ℝ × ℝ => boxPoint q.1 q.2) '' (Icc tl tr ×ˢ Icc sb st) := by
    ext p
    constructor
    · intro hp
      exact ⟨(p 0,p 1),⟨hp.1,hp.2⟩,boxPoint_eta p⟩
    · rintro ⟨q,hq,rfl⟩
      exact boxPoint_mem hq.1 hq.2
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image (by unfold boxPoint; fun_prop)

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_seed_gap {M s0 s1 t : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hs0 : s0 ∈ Ioo (-2 : ℝ) 2) (hs1 : s1 ∈ Ioo (-2 : ℝ) 2)
    (ht : t ∈ Ioo (-2 : ℝ) 2) (hss : s0 ≤ s1) :
    Real.exp (-2 * M) * (s1 - s0) ≤ Y s1 t - Y s0 t := by
  have hd (s : ℝ) (hs : s ∈ Ioo (-2 : ℝ) 2) :
      DifferentiableAt ℝ (fun r => Y r t) s :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).differentiableAt
  have hc : ContinuousOn (fun r => Y r t) (Ioo (-2 : ℝ) 2) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hdi : DifferentiableOn ℝ (fun r => Y r t) (interior (Ioo (-2 : ℝ) 2)) := by
    intro s hs
    exact (hd s (interior_subset hs)).differentiableWithinAt
  have hbound : ∀ s ∈ interior (Ioo (-2 : ℝ) 2),
      Real.exp (-2 * M) ≤ deriv (fun r => Y r t) s := by
    intro s hs
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hq1
      (interior_subset hs) ht).1
  exact (convex_Ioo (-2 : ℝ) 2).mul_sub_le_image_sub_of_le_deriv hc hdi hbound
    s0 hs0 s1 hs1 hss

theorem cap_flow_time_lipschitz
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    {s t0 t1 : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2)
    (ht0 : t0 ∈ Ioo (-2 : ℝ) 2) (ht1 : t1 ∈ Ioo (-2 : ℝ) 2) :
    |Y s t1 - Y s t0| ≤ ((1 : ℝ) / 100) * |t1 - t0| := by
  have hd (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) : DifferentiableAt ℝ (Y s) t :=
    (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt
  have hb (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) : ‖deriv (Y s) t‖ ≤ (1 : ℝ) / 100 := by
    simpa only [Real.norm_eq_abs, timeFlowDerivative] using
      cap_flow_time_bound hq hU hSU hY hrange hstart hode hq0 hs ht
  simpa only [Real.norm_eq_abs] using
    (convex_Ioo (-2 : ℝ) 2).norm_image_sub_le_of_norm_deriv_le hd hb ht0 ht1

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def openCoordinateRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioo tl tr ∧ p 1 ∈ Ioo sb st}

def flowInteriorRadius (M dt ds : ℝ) : ℝ :=
  min (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)

theorem flowInteriorRadius_pos (M : ℝ) {dt ds : ℝ} (ht : 0 < dt) (hs : 0 < ds) :
    0 < flowInteriorRadius M dt ds := by
  apply lt_min
  · exact half_pos ht
  · exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hs

theorem flowInteriorRadius_lt_time (M : ℝ) {dt ds : ℝ} (ht : 0 < dt) :
    flowInteriorRadius M dt ds < dt := by
  have h := min_le_left (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)
  change flowInteriorRadius M dt ds ≤ dt / 2 at h
  linarith

theorem flowInteriorRadius_vertical_margin (M : ℝ) {dt ds : ℝ} (hs : 0 < ds) :
    ((101 : ℝ) / 100) * flowInteriorRadius M dt ds < Real.exp (-2 * M) * ds := by
  have h := min_le_right (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)
  change flowInteriorRadius M dt ds ≤ ((50 : ℝ) / 101) * Real.exp (-2 * M) * ds at h
  have hp := mul_pos (Real.exp_pos (-2 * M)) hs
  nlinarith

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem actual_flow_ordinary_rectangle_inclusion
    {M tl tr sb st dt ds t0 s0 : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds)
    (ht0 : t0 ∈ Icc (tl + dt) (tr - dt))
    (hs0 : s0 ∈ Icc (sb + ds) (st - ds)) :
    closedRectangle (t0 - flowInteriorRadius M dt ds) (t0 + flowInteriorRadius M dt ds)
      (Y s0 t0 - flowInteriorRadius M dt ds) (Y s0 t0 + flowInteriorRadius M dt ds) ⊆
      capChart Y '' openCoordinateRectangle tl tr sb st := by
  intro p hp
  let r := flowInteriorRadius M dt ds
  have hr : 0 < r := flowInteriorRadius_pos M hdt hds
  have hrt : r < dt := flowInteriorRadius_lt_time M hdt
  have hrs : ((101 : ℝ) / 100) * r < Real.exp (-2 * M) * ds :=
    flowInteriorRadius_vertical_margin M hds
  have hpx : p 0 ∈ Icc (t0 - r) (t0 + r) := hp.1
  have hpy : p 1 ∈ Icc (Y s0 t0 - r) (Y s0 t0 + r) := hp.2
  have htime : p 0 ∈ Ioo tl tr := by constructor <;> linarith [ht0.1, ht0.2, hpx.1, hpx.2]
  have htimeGlobal : p 0 ∈ Ioo (-2 : ℝ) 2 := ⟨htl.trans htime.1, htime.2.trans htr⟩
  have ht0Global : t0 ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [ht0.1, ht0.2]
  have hs0Global : s0 ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hsbGlobal : sb ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hstGlobal : st ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hsb0 : sb ≤ s0 := by linarith [hs0.1]
  have hs0t : s0 ≤ st := by linarith [hs0.2]
  have hlow := cap_flow_seed_gap hq hU hSU hY hrange hstart hode hM hq1
    hsbGlobal hs0Global htimeGlobal hsb0
  have hupp := cap_flow_seed_gap hq hU hSU hY hrange hstart hode hM hq1
    hs0Global hstGlobal htimeGlobal hs0t
  have hgap0 : Real.exp (-2 * M) * ds ≤ Real.exp (-2 * M) * (s0 - sb) :=
    mul_le_mul_of_nonneg_left (by linarith [hs0.1]) (Real.exp_pos _).le
  have hgap1 : Real.exp (-2 * M) * ds ≤ Real.exp (-2 * M) * (st - s0) :=
    mul_le_mul_of_nonneg_left (by linarith [hs0.2]) (Real.exp_pos _).le
  have hxdist : |p 0 - t0| ≤ r := abs_le.mpr ⟨by linarith [hpx.1], by linarith [hpx.2]⟩
  have hmove : |Y s0 (p 0) - Y s0 t0| ≤ ((1 : ℝ) / 100) * r :=
    (cap_flow_time_lipschitz hq hU hSU hY hrange hstart hode hq0
      hs0Global ht0Global htimeGlobal).trans
      (mul_le_mul_of_nonneg_left hxdist (by norm_num))
  have hlo : Y sb (p 0) < p 1 := by
    have hm := (abs_le.mp hmove).2
    nlinarith [hlow, hgap0, hpy.1, hrs]
  have hhi : p 1 < Y st (p 0) := by
    have hm := (abs_le.mp hmove).1
    nlinarith [hupp, hgap1, hpy.2, hrs]
  have hsb_st : sb ≤ st := hsb0.trans hs0t
  have hseedCont : ContinuousOn (fun s : ℝ => (s, p 0)) (Icc sb st) := by fun_prop
  have hseedMap : MapsTo (fun s : ℝ => (s, p 0)) (Icc sb st)
      (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) := by
    intro s hs
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨htimeGlobal.1.le, htimeGlobal.2.le⟩⟩
  have hcont : ContinuousOn (fun s => Y s (p 0)) (Icc sb st) := by
    convert hY.comp hseedCont hseedMap using 1; rfl
  obtain ⟨s, hs, hse⟩ := intermediate_value_Icc hsb_st hcont ⟨hlo.le, hhi.le⟩
  have hsStrict : s ∈ Ioo sb st := by
    constructor
    · by_contra hnot
      have he : s = sb := le_antisymm (le_of_not_gt hnot) hs.1
      subst s
      linarith
    · by_contra hnot
      have he : s = st := le_antisymm hs.2 (le_of_not_gt hnot)
      subst s
      linarith
  refine ⟨boxPoint (p 0) s, ?_, ?_⟩
  · simpa [openCoordinateRectangle, boxPoint] using And.intro htime hsStrict
  · ext i
    fin_cases i <;> simp [capChart, capFlowHeight, boxPoint, coordinatePoint, hse]

theorem actual_flow_uniform_image_margin
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) :
    0 < flowInteriorRadius M dt ds ∧
      ∀ p ∈ capChart Y '' closedRectangle (tl + dt) (tr - dt) (sb + ds) (st - ds),
        closedRectangle (p 0 - flowInteriorRadius M dt ds) (p 0 + flowInteriorRadius M dt ds)
          (p 1 - flowInteriorRadius M dt ds) (p 1 + flowInteriorRadius M dt ds) ⊆
          capChart Y '' openCoordinateRectangle tl tr sb st := by
  refine ⟨flowInteriorRadius_pos M hdt hds, ?_⟩
  rintro p ⟨a, ha, rfl⟩
  simpa [capChart, capFlowHeight, coordinatePoint] using
    actual_flow_ordinary_rectangle_inclusion hq hU hSU hY hrange hstart hode
      hM hq0 hq1 htl htr hsb hst hdt hds ha.1 ha.2

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem orderedPartial_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2)) :
    ContDiffOn ℝ ∞ (iteratedCoordPartial ds f) U := by
  induction ds with
  | nil => exact hf
  | cons i ds ih => exact normed_coordPartial_contDiffOn ih hU i

theorem fullJet_coordinate_inputs_eq_ordered
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (n : ℕ) (d : Fin n → Fin 2) {p : Coord} (hp : p ∈ U) :
    iteratedFDeriv ℝ n f p (fun i => Pi.single (d i) (1 : ℝ)) =
      iteratedCoordPartial (List.ofFn d) f p := by
  induction n generalizing p with
  | zero => simp [iteratedCoordPartial]
  | succ n ih =>
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
      rw [hd.iteratedFDeriv_succ_apply_left']
      have he : (fun q => iteratedFDeriv ℝ n f q
          (fun i => Pi.single (d i.succ) (1 : ℝ))) =ᶠ[𝓝 p]
          iteratedCoordPartial (List.ofFn (fun i => d i.succ)) f := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih (fun i => d i.succ) hq
      change fderiv ℝ (fun q => iteratedFDeriv ℝ n f q
        (fun i => Pi.single (d i.succ) (1 : ℝ))) p (Pi.single (d 0) 1) = _
      rw [he.fderiv_eq, List.ofFn_succ]
      rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev

theorem openCoordinateRectangle_subset_closed (tl tr sb st : ℝ) :
    openCoordinateRectangle tl tr sb st ⊆ closedRectangle tl tr sb st := by
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩

variable {q f : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)

include hSU hrange

theorem actual_closed_flow_rectangle_subset_domain
    {tl tr sb st : ℝ} (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2) :
    capChart Y '' closedRectangle tl tr sb st ⊆ U := by
  rintro p ⟨a, ha, rfl⟩
  apply hSU
  apply coordinatePoint_mem_modelSquare
  · exact ⟨by linarith [ha.1.1], by linarith [ha.1.2]⟩
  · exact hrange (a 1) ⟨by linarith [ha.2.1], by linarith [ha.2.2]⟩
      (a 0) ⟨by linarith [ha.1.1], by linarith [ha.1.2]⟩

include hq hU hY hstart hode

theorem actual_flow_interior_sobolev
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) (hf : ContDiffOn ℝ ∞ f U)
    (h0 : MemLp f 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2
      (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    {p : Coord}
    (hp : p ∈ capChart Y '' closedRectangle (tl + dt) (tr - dt) (sb + ds) (st - ds)) :
    |f p| ≤ Real.sqrt (regionSobolevEnergy (flowInteriorRadius M dt ds)
      (capChart Y '' closedRectangle tl tr sb st) f) := by
  obtain ⟨hr, hmargin⟩ := actual_flow_uniform_image_margin hq hU hSU hY hrange hstart hode
    hM hq0 hq1 htl htr hsb hst hdt hds
  have hsquare := (hmargin p hp).trans (Set.image_mono
    (openCoordinateRectangle_subset_closed tl tr sb st))
  exact point_abs_bound_on_region hr hU hf
    (actual_closed_flow_rectangle_subset_domain hSU hrange htl htr hsb hst)
    hsquare h0 hx hy hxy

end SmoothLocal.Flow

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry

theorem regionSobolevEnergy_nonneg {r : ℝ} (hr : 0 < r) (V : Set Coord) (f : Coord → ℝ) :
    0 ≤ regionSobolevEnergy r V f := by
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg hw hw) (integral_nonneg (fun p => sq_nonneg (f p))))
    (mul_nonneg hw (integral_nonneg (fun p => sq_nonneg (coordPartial 0 f p)))))
    (mul_nonneg hw (integral_nonneg (fun p => sq_nonneg (coordPartial 1 f p)))))
    (integral_nonneg (fun p => sq_nonneg (coordPartial 1 (coordPartial 0 f) p)))

theorem regionSobolevEnergy_le_common_bound
    {r B : ℝ} {V : Set Coord} {f : Coord → ℝ} (hr : 0 < r)
    (h0 : (∫ p in V, f p ^ 2) ≤ B ^ 2)
    (hx : (∫ p in V, coordPartial 0 f p ^ 2) ≤ B ^ 2)
    (hy : (∫ p in V, coordPartial 1 f p ^ 2) ≤ B ^ 2)
    (hxy : (∫ p in V, coordPartial 1 (coordPartial 0 f) p ^ 2) ≤ B ^ 2) :
    regionSobolevEnergy r V f ≤ ((squareSobolevWeight r + 1) * B)^2 := by
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  calc
    regionSobolevEnergy r V f ≤
        squareSobolevWeight r * squareSobolevWeight r * B^2 +
        squareSobolevWeight r * B^2 + squareSobolevWeight r * B^2 + B^2 :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h0 (mul_nonneg hw hw))
        (mul_le_mul_of_nonneg_left hx hw)) (mul_le_mul_of_nonneg_left hy hw)) hxy
    _ = _ := by ring

theorem abs_bound_of_regionSobolevEnergy
    {r B : ℝ} {V : Set Coord} {f : Coord → ℝ} {p : Coord}
    (hr : 0 < r) (hB : 0 ≤ B) (hp : |f p| ≤ Real.sqrt (regionSobolevEnergy r V f))
    (h0 : (∫ q in V, f q ^ 2) ≤ B ^ 2)
    (hx : (∫ q in V, coordPartial 0 f q ^ 2) ≤ B ^ 2)
    (hy : (∫ q in V, coordPartial 1 f q ^ 2) ≤ B ^ 2)
    (hxy : (∫ q in V, coordPartial 1 (coordPartial 0 f) q ^ 2) ≤ B ^ 2) :
    |f p| ≤ (squareSobolevWeight r + 1) * B := by
  have hE := regionSobolevEnergy_nonneg hr V f
  have henergy := regionSobolevEnergy_le_common_bound hr h0 hx hy hxy
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  have hbound : 0 ≤ (squareSobolevWeight r + 1) * B := mul_nonneg (by linarith) hB
  have hroot : Real.sqrt (regionSobolevEnergy r V f) ≤ (squareSobolevWeight r + 1) * B := by
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg (regionSobolevEnergy r V f)]
  exact hp.trans hroot

end SmoothLocal.Sobolev

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace SmoothLocal.Geometry
open SmoothLocal.HighEquation

theorem coordinate_basis_decomposition (v : Coord) :
    v = ∑ i : Fin 2, v i • (Pi.single i (1 : ℝ) : Coord) := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]

theorem multilinear_coordinate_components {n : ℕ}
    (L : Coord [×n]→L[ℝ] ℝ) (v : Fin n → Coord) :
    L v = ∑ r : Fin n → Fin 2,
      L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i) := by
  classical
  calc
    L v = L (fun i => ∑ j : Fin 2, v i j • (Pi.single j (1 : ℝ) : Coord)) := by
      congr 1
      funext i
      exact coordinate_basis_decomposition (v i)
    _ = ∑ r : Fin n → Fin 2, L (fun i => v i (r i) • Pi.single (r i) (1 : ℝ)) :=
      L.map_sum (fun i j => v i j • (Pi.single j (1 : ℝ) : Coord))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [L.map_smul_univ]
      simp only [smul_eq_mul, mul_comm]

theorem multilinear_norm_le_coordinate_bound {n : ℕ}
    (L : Coord [×n]→L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hL : ∀ r : Fin n → Fin 2, ‖L (fun i => Pi.single (r i) (1 : ℝ))‖ ≤ B) :
    ‖L‖ ≤ (2 : ℝ)^n * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hB)
  intro v
  rw [multilinear_coordinate_components]
  calc
    _ ≤ ∑ r : Fin n → Fin 2, ‖L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : Fin n → Fin 2, B * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, norm_prod]
      apply mul_le_mul (hL r) _ (by positivity) hB
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i _ => norm_le_pi_norm (v i) (r i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

theorem full_jet_norm_le_coordinate_words {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hword : ∀ ds : List (Fin 2), ds.length = n → |iteratedCoordPartial ds f p| ≤ B) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ (2 : ℝ)^n * B := by
  apply multilinear_norm_le_coordinate_bound _ hB
  intro r
  rw [fullJet_coordinate_inputs_eq_ordered hf hU n r hp, Real.norm_eq_abs]
  exact hword (List.ofFn r) (by simp)

theorem CoordinateBound.full_jet_norm_bound {f : Coord → ℝ} {U S : Set Coord}
    {N n : ℕ} {B : ℝ} (h : CoordinateBound f S N B)
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U) (hB : 0 ≤ B)
    (hn : n ≤ N) {p : Coord} (hp : p ∈ S) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ (2 : ℝ)^n * B := by
  apply full_jet_norm_le_coordinate_words hf hU (hSU hp) n hB
  intro ds hds
  exact h ds (by omega) p hp

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def inverseShearCLM (q0 : ℝ) : Coord →L[ℝ] Coord :=
  LinearMap.toContinuousLinearMap
    { toFun := inverseShearCoordinates q0
      map_add' := by
        intro left right
        ext index
        fin_cases index
        · rfl
        · dsimp [inverseShearCoordinates]
          ring
      map_smul' := by
        intro scalar point
        ext index
        fin_cases index
        · rfl
        · dsimp [inverseShearCoordinates]
          ring }

@[simp] theorem inverseShearCLM_apply (q0 : ℝ) (p : Coord) :
    inverseShearCLM q0 p = inverseShearCoordinates q0 p := rfl

theorem inverseShearCLM_norm_le (q0 : ℝ) : ‖inverseShearCLM q0‖ ≤ 1 + |q0| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (1 + |q0|) * ‖v‖)).mpr
  intro i
  fin_cases i
  · change ‖v 0‖ ≤ _
    exact (norm_le_pi_norm v 0).trans (by nlinarith [mul_nonneg (abs_nonneg q0) (norm_nonneg v)])
  · change ‖v 1 - q0 * v 0‖ ≤ _
    calc
      _ ≤ ‖v 1‖ + ‖q0 * v 0‖ := norm_sub_le _ _
      _ = ‖v 1‖ + |q0| * ‖v 0‖ := by rw [norm_mul, Real.norm_eq_abs q0]
      _ ≤ ‖v‖ + |q0| * ‖v‖ := add_le_add (norm_le_pi_norm v 1)
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (abs_nonneg q0))
      _ = _ := by ring

theorem local_linear_full_jet_norm_bound {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (L : Coord →L[ℝ] Coord)
    {p : Coord} (hp : L p ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ * ‖L‖^n := by
  have hpre := hU.preimage L.continuous
  have heq := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp,
    iteratedFDerivWithin_of_isOpen n hU hp] at heq
  rw [heq]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ n f (L p)) (fun _ : Fin n => L)

theorem sheared_full_jet_bound_of_coordinateBound {z : Coord → ℝ} {U S : Set Coord}
    {N n : ℕ} {B : ℝ} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hSU : S ⊆ U) (hbound : CoordinateBound z S N B) (hB : 0 ≤ B)
    (q0 : ℝ) (hn : n ≤ N) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ S) :
    ‖iteratedFDeriv ℝ n (heightInShearCoordinates z q0) p‖ ≤
      (2 * (1 + |q0|))^N * B := by
  have hlocal := local_linear_full_jet_norm_bound hz hU (inverseShearCLM q0) (hSU hp) n
  have hbase := hbound.full_jet_norm_bound hz hU hSU hB hn hp
  have hscale : 1 ≤ 2 * (1 + |q0|) := by nlinarith [abs_nonneg q0]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n z (inverseShearCoordinates q0 p)‖ * ‖inverseShearCLM q0‖^n := hlocal
    _ ≤ ((2 : ℝ)^n * B) * (1 + |q0|)^n := mul_le_mul hbase
      (pow_le_pow_left₀ (norm_nonneg _) (inverseShearCLM_norm_le q0) n)
      (pow_nonneg (norm_nonneg _) n) (mul_nonneg (by positivity) hB)
    _ = (2 * (1 + |q0|))^n * B := by rw [mul_pow]; ring
    _ ≤ (2 * (1 + |q0|))^N * B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hscale hn) hB

theorem CoordinateBound.inverse_shear {z : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {B : ℝ} (hbound : CoordinateBound z S N B)
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (hSU : S ⊆ U) (hB : 0 ≤ B) (q0 : ℝ) :
    CoordinateBound (heightInShearCoordinates z q0) (inverseShearCoordinates q0 ⁻¹' S)
      N ((2 * (1 + |q0|))^N * B) := by
  intro ds hds p hp
  apply (norm_iteratedCoordPartial_le_jet (heightInShearCoordinates_contDiffOn hz q0)
    (hU.preimage (inverseShearCoordinates_contDiff q0).continuous) ds (hSU hp)).trans
  exact sheared_full_jet_bound_of_coordinateBound hz hU hSU hbound hB q0 hds hp

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem compact_finite_fullJet_bound
    {f : Coord → ℝ} {U S : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (ell : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ ell, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M := by
  classical
  have hk : ∀ k : Fin (ell + 1), ∃ A : ℝ, ∀ p ∈ S, ‖iteratedFDeriv ℝ k.val f p‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val f) S := by
      intro p hp
      exact (((hf.contDiffAt (hU.mem_nhds (hSU hp))).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k.val)).continuousAt).continuousWithinAt
    exact hS.exists_bound_of_continuousOn hcont
  choose A hA using hk
  refine ⟨∑ k : Fin (ell + 1), |A k|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk p hp
  let j : Fin (ell + 1) := ⟨k, by omega⟩
  exact (hA j p hp).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def shearedMetricCoordinateBudget (G q0 : ℝ) (N : ℕ) : ℝ :=
  4 * (1 + |q0|)^2 * (2 * (1 + |q0|))^N * G

theorem shearedMetricCoordinateBudget_nonneg {G : ℝ} (q0 : ℝ) (N : ℕ) (hG : 0 ≤ G) :
    0 ≤ shearedMetricCoordinateBudget G q0 N := by
  unfold shearedMetricCoordinateBudget
  positivity

theorem coordinateBound_add_on {f h : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {A B : ℝ} (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hA : CoordinateBound f S N A) (hB : CoordinateBound h S N B) :
    CoordinateBound (fun p => f p + h p) S N (A + B) := by
  intro ds hds p hp
  rw [CoordinateBound.iterated_add hf hh hU ds (hSU hp)]
  exact (abs_add_le _ _).trans (add_le_add (hA ds hds p hp) (hB ds hds p hp))

theorem coordinateBound_const_mul_on {f : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {A : ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hA : CoordinateBound f S N A) (c : ℝ) :
    CoordinateBound (fun p => c * f p) S N (|c| * A) := by
  intro ds hds p hp
  rw [CoordinateBound.iterated_const_mul hf hU c ds (hSU hp), abs_mul]
  exact mul_le_mul_of_nonneg_left (hA ds hds p hp) (abs_nonneg _)

theorem inverseShearMatrix_entry_bound (q0 : ℝ) (i j : Fin 2) :
    |inverseShearMatrix q0 i j| ≤ 1 + |q0| := by
  fin_cases i <;> fin_cases j <;> simp [inverseShearMatrix]
  positivity

theorem metricInShearCoordinates_four_terms (g : MetricField) (q0 : ℝ) (i j : Fin 2) :
    (fun p => metricInShearCoordinates g q0 p i j) =
      (fun p =>
        ((inverseShearMatrix q0 0 i * inverseShearMatrix q0 0 j) *
            heightInShearCoordinates (fun r => g r 0 0) q0 p +
          (inverseShearMatrix q0 0 i * inverseShearMatrix q0 1 j) *
            heightInShearCoordinates (fun r => g r 0 1) q0 p) +
        ((inverseShearMatrix q0 1 i * inverseShearMatrix q0 0 j) *
            heightInShearCoordinates (fun r => g r 1 0) q0 p +
          (inverseShearMatrix q0 1 i * inverseShearMatrix q0 1 j) *
            heightInShearCoordinates (fun r => g r 1 1) q0 p)) := by
  funext p
  simp only [metricInShearCoordinates, affinePullbackMetric, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, heightInShearCoordinates,
    Function.comp_apply, ← inverseShearCoordinates_eq_affine]
  ring

theorem metric_coordinate_bound_inverse_shear
    {g : MetricField} {U S : Set Coord} {N : ℕ} {G : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : S ⊆ U) (hG : 0 ≤ G)
    (hgB : ∀ i j, CoordinateBound (fun p => g p i j) S N G) (q0 : ℝ) :
    ∀ i j, CoordinateBound (fun p => metricInShearCoordinates g q0 p i j)
      (inverseShearCoordinates q0 ⁻¹' S) N (shearedMetricCoordinateBudget G q0 N) := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  let T := inverseShearCoordinates q0 ⁻¹' S
  let A := (2 * (1 + |q0|))^N * G
  let B := (1 + |q0|)^2 * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hVU : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hTV : T ⊆ V := fun p hp => hSU hp
  have hs (a b : Fin 2) : ContDiffOn ℝ ∞ (heightInShearCoordinates (fun p => g p a b) q0) V :=
    heightInShearCoordinates_contDiffOn (hg.1 a b) q0
  have hb (a b : Fin 2) :
      CoordinateBound (heightInShearCoordinates (fun p => g p a b) q0) T N A :=
    SmoothLocal.Pulse.CoordinateBound.inverse_shear (hgB a b) (hg.1 a b) hU hSU hG q0
  intro i j
  let term (a b : Fin 2) : Coord → ℝ := fun p =>
    (inverseShearMatrix q0 a i * inverseShearMatrix q0 b j) *
      heightInShearCoordinates (fun r => g r a b) q0 p
  have htS (a b : Fin 2) : ContDiffOn ℝ ∞ (term a b) V := contDiffOn_const.mul (hs a b)
  have htB (a b : Fin 2) : CoordinateBound (term a b) T N B := by
    have hh := coordinateBound_const_mul_on (hs a b) hVU hTV (hb a b)
      (inverseShearMatrix q0 a i * inverseShearMatrix q0 b j)
    apply hh.mono le_rfl
    have hc : |inverseShearMatrix q0 a i * inverseShearMatrix q0 b j| ≤ (1 + |q0|)^2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (inverseShearMatrix_entry_bound q0 a i) (inverseShearMatrix_entry_bound q0 b j)
        (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hc hA
  have hrow0 := coordinateBound_add_on (htS 0 0) (htS 0 1) hVU hTV (htB 0 0) (htB 0 1)
  have hrow1 := coordinateBound_add_on (htS 1 0) (htS 1 1) hVU hTV (htB 1 0) (htB 1 1)
  have hsum := coordinateBound_add_on ((htS 0 0).add (htS 0 1))
    ((htS 1 0).add (htS 1 1)) hVU hTV hrow0 hrow1
  rw [metricInShearCoordinates_four_terms]
  have hbudget : B + B + (B + B) = shearedMetricCoordinateBudget G q0 N := by
    dsimp [B, A, shearedMetricCoordinateBudget]
    ring
  rw [hbudget] at hsum
  exact hsum

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.HighEquation

end SmoothLocal.Geometry

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

theorem boundedClassWidth_ge_hundred (kappa : ℝ) (M : ℕ) :
    100 ≤ boundedClassWidth kappa M := by
  have hv : 0 ≤ boundedClassSpeed kappa M :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg M) _)
  have hi := inv_nonneg.mpr hv
  dsimp only [boundedClassWidth]
  linarith

theorem boundedClassWidth_pos (kappa : ℝ) (M : ℕ) :
    0 < boundedClassWidth kappa M :=
  (by norm_num : (0 : ℝ) < 100).trans_le (boundedClassWidth_ge_hundred kappa M)

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.HighEquation

theorem fixed_metric_finite_coefficient_jet_bound
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U)
    (hU : IsOpen U) (hSU : modelSquare ⊆ U) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ B := by
  classical
  have hco : ∀ i j : Fin 2, ∃ A : ℝ, 0 ≤ A ∧
      ∀ k ≤ m, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ A :=
    fun i j => compact_finite_fullJet_bound (hg.1 i j) hU modelSquare_isCompact hSU m
  choose A hA0 hA using hco
  refine ⟨∑ i : Fin 2, ∑ j : Fin 2, A i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hA0 i j)),?_⟩
  intro i j k hk p hp
  exact (hA i j k hk p hp).trans
    ((Finset.single_le_sum (fun j _ => hA0 i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hA0 a b))
        (Finset.mem_univ i)))

theorem metricApproximationAccuracy_le_one {tau : ℕ} (htau : 1 ≤ tau) :
    metricApproximationAccuracy tau ≤ 1 := by
  have htauR : (1 : ℝ) ≤ (tau : ℝ) := by exact_mod_cast htau
  simpa only [metricApproximationAccuracy,div_one] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) (one_le_pow₀ htauR : 1 ≤ (tau : ℝ)^tau))

theorem metric_jet_norm_le_of_approximation_locality
    {gStar gTau test : MetricField} {U V : Set Coord}
    (hgStar : SmoothPositiveOn gStar U) (hgTau : SmoothPositiveOn gTau V)
    (hU : IsOpen U) (hV : IsOpen V) {p : Coord} (hpU : p ∈ U) (hpV : p ∈ V)
    (heq : test =ᶠ[𝓝 p] gStar) (i j : Fin 2) (k : ℕ) {B epsilon : ℝ}
    (hbase : ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ B)
    (happrox : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-test q i j) p‖ ≤ epsilon) :
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ B+epsilon := by
  have heqCoeff : (fun q => gTau q i j-test q i j) =ᶠ[𝓝 p]
      (fun q => gTau q i j-gStar q i j) := by
    filter_upwards [metric_coeff_eventuallyEq heq i j] with q hq
    rw [hq]
  have hdiff : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-gStar q i j) p‖ ≤ epsilon := by
    rw [←(heqCoeff.iteratedFDeriv ℝ k).self_of_nhds]
    exact happrox
  have hsplit := iteratedFDeriv_sub_apply (i := k)
    (((hgTau.1 i j).contDiffAt (hV.mem_nhds hpV)).of_le (WithTop.coe_le_coe.mpr le_top))
    (((hgStar.1 i j).contDiffAt (hU.mem_nhds hpU)).of_le (WithTop.coe_le_coe.mpr le_top))
  change ‖iteratedFDeriv ℝ k ((fun q => gTau q i j)-(fun q => gStar q i j)) p‖ ≤ epsilon at hdiff
  rw [hsplit] at hdiff
  calc
    _ = ‖(iteratedFDeriv ℝ k (fun q => gTau q i j) p-
        iteratedFDeriv ℝ k (fun q => gStar q i j) p)+
          iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ := by rw [sub_add_cancel]
    _ ≤ ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p-
        iteratedFDeriv ℝ k (fun q => gStar q i j) p‖+
          ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ := norm_add_le _ _
    _ ≤ epsilon+B := add_le_add hdiff hbase
    _ = B+epsilon := add_comm _ _

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

theorem integral_sq_eq_eLpNorm_toReal_sq {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) :
    (∫ p, f p ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  calc
    (∫ p, f p ^ 2 ∂μ) = ∫ p, ‖hf.toLp f p‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with p hp
      simp only [hp, Real.norm_eq_abs, sq_abs]
    _ = ∫ p, inner ℝ (hf.toLp f p) (hf.toLp f p) ∂μ := by
      simp only [real_inner_self_eq_norm_sq]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := rfl
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = (eLpNorm f 2 μ).toReal ^ 2 := by
      rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]

theorem integral_sq_le_of_eLpNorm_two_le {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) {H : ℝ≥0} (hH : eLpNorm f 2 μ ≤ (H : ℝ≥0∞)) :
    (∫ p, f p ^ 2 ∂μ) ≤ (H : ℝ)^2 := by
  rw [integral_sq_eq_eLpNorm_toReal_sq hf]
  have h := ENNReal.toReal_mono (by simp : (H : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) hH
  change (eLpNorm f 2 μ).toReal ≤ (H : ℝ) at h
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).mpr h

end SmoothLocal.Analytic

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem CoordinateL2Bound.mono {z : Coord → ℝ} {V : Set Coord} {N n : ℕ} {H H' : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hn : n ≤ N) (hH : H ≤ H') :
    CoordinateL2Bound z V n H' := by
  intro ds hds
  exact (h ds (hds.trans hn)).trans (by exact_mod_cast hH)

theorem CoordinateL2Bound.eLpNorm_le {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (hbound : CoordinateL2Bound z V N H) (word : List (Fin 2)) (hword : word.length ≤ N)
    (hmeas : AEStronglyMeasurable (iteratedCoordPartial word z) (volume.restrict V)) :
    eLpNorm (iteratedCoordPartial word z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact hbound word hword

theorem CoordinateL2Bound.memLp {z : Coord → ℝ} {U V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (ds : List (Fin 2)) (hds : ds.length ≤ N) :
    MemLp (iteratedCoordPartial ds z) 2 (volume.restrict V) := by
  have hmeas := ((orderedPartial_contDiffOn hz hU ds).continuousOn.mono
    hVU).aestronglyMeasurable (μ := volume) hV
  exact ⟨hmeas, (h.eLpNorm_le ds hds hmeas).trans_lt (by finiteness)⟩

theorem CoordinateL2Bound.integral_sq {z : Coord → ℝ} {U V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (ds : List (Fin 2)) (hds : ds.length ≤ N) :
    (∫ p in V, iteratedCoordPartial ds z p ^ 2) ≤ (H : ℝ)^2 := by
  have hmem := h.memLp hz hU hV hVU ds hds
  exact integral_sq_le_of_eLpNorm_two_le hmem (h.eLpNorm_le ds hds hmem.aestronglyMeasurable)

end SmoothLocal.HighEquation

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev
open SmoothLocal.HighEquation

theorem closedRectangle_subset_capChartDomain
    {tl tr sb st : ℝ} (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2) :
    closedRectangle tl tr sb st ⊆ capChartDomain := by
  intro p hp
  exact ⟨⟨htl.trans_le hp.1.1, hp.1.2.trans_lt htr⟩,
    ⟨hsb.trans_le hp.2.1, hp.2.2.trans_lt hst⟩⟩

theorem coordinateL2Bound_to_nested_flow_coordinateBound
    {q z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) (hz : ContDiffOn ℝ ∞ z U)
    {n : ℕ} {H : ℝ≥0}
    (hL : CoordinateL2Bound z (capChart Y '' closedRectangle tl tr sb st) (n + 2) H) :
    CoordinateBound z
      (capChart Y '' closedRectangle (tl+dt) (tr-dt) (sb+ds) (st-ds)) n
      ((squareSobolevWeight (flowInteriorRadius M dt ds)+1)*(H : ℝ)) := by
  let V := capChart Y '' closedRectangle tl tr sb st
  have hVU : V ⊆ U := actual_closed_flow_rectangle_subset_domain hSU hrange htl htr hsb hst
  have hYs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hcompact : IsCompact V := (capRectangle_isCompact tl tr sb st).image_of_continuousOn
    ((capChart_contDiffOn hYs).continuousOn.mono
      (closedRectangle_subset_capChartDomain htl htr hsb hst))
  have hV : MeasurableSet V := hcompact.isClosed.measurableSet
  intro word hword p hp
  have h0 := hL.memLp hz hU hV hVU word (by omega)
  have hx := hL.memLp hz hU hV hVU (0 :: word) (by simp only [List.length_cons]; omega)
  have hy := hL.memLp hz hU hV hVU (1 :: word) (by simp only [List.length_cons]; omega)
  have hxy := hL.memLp hz hU hV hVU (1 :: 0 :: word) (by simp only [List.length_cons]; omega)
  have hpoint := actual_flow_interior_sobolev hq hU hSU hY hrange hstart hode hM hq0 hq1
    htl htr hsb hst hdt hds (orderedPartial_contDiffOn hz hU word) h0 hx hy hxy hp
  exact abs_bound_of_regionSobolevEnergy (flowInteriorRadius_pos M hdt hds) H.2 hpoint
    (hL.integral_sq hz hU hV hVU word (by omega))
    (hL.integral_sq hz hU hV hVU (0 :: word) (by simp only [List.length_cons]; omega))
    (hL.integral_sq hz hU hV hVU (1 :: word) (by simp only [List.length_cons]; omega))
    (hL.integral_sq hz hU hV hVU (1 :: 0 :: word) (by simp only [List.length_cons]; omega))

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

namespace LowerCapRectangle

variable {bStar : ℝ}

theorem region_subset_domain (r : LowerCapRectangle bStar) : r.region ⊆ capChartDomain :=
  closedRectangle_subset_capChartDomain r.left_gt r.right_lt r.bottom_gt (by linarith [r.top_lt,r.ceiling_le])

theorem expand_shrink_region (r : LowerCapRectangle bStar) :
    closedRectangle (r.expand.left+r.margin) (r.expand.right-r.margin)
      (r.expand.bottom+r.margin) (r.expand.top-r.margin) = r.region := by
  dsimp only [expand, region]
  congr 1 <;> ring

end LowerCapRectangle

variable {bStar : ℝ}

theorem coordinateL2Bound_to_expanded_cap_coordinateBound
    {q z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hz : ContDiffOn ℝ ∞ z U) (r : LowerCapRectangle bStar) {n : ℕ} {H : ℝ≥0}
    (hL : SmoothLocal.HighEquation.CoordinateL2Bound z (r.expand.image Y) (n+2) H) :
    CoordinateBound z (r.image Y) n
      ((SmoothLocal.Sobolev.squareSobolevWeight (flowInteriorRadius M r.margin r.margin)+1)*(H : ℝ)) := by
  have h := coordinateL2Bound_to_nested_flow_coordinateBound hq hU hSU hY hrange hstart hode
    hM hq0 hq1 r.expand.left_gt r.expand.right_lt r.expand.bottom_gt
    (by linarith [r.expand.top_lt,r.expand.ceiling_le]) r.margin_pos r.margin_pos hz hL
  simpa only [LowerCapRectangle.expand_shrink_region, LowerCapRectangle.image] using h

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem cap_closed_image_properties {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    {tl tr sb st : ℝ} (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    IsCompact (capChart Y '' closedRectangle tl tr sb st) ∧
    MeasurableSet (capChart Y '' closedRectangle tl tr sb st) ∧
    volume (capChart Y '' closedRectangle tl tr sb st) < ⊤ ∧
    capChart Y '' closedRectangle tl tr sb st ⊆ modelOpenSquare := by
  have hc : IsCompact (capChart Y '' closedRectangle tl tr sb st) :=
    (capRectangle_isCompact _ _ _ _).image_of_continuousOn
      ((capChart_contDiffOn hYs).continuousOn.mono hbox)
  refine ⟨hc,hc.measurableSet,hc.measure_lt_top,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  exact capChart_mem_modelOpenSquare (hbox hp) (hdisp p (hbox hp))

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

variable {bStar : ℝ}

theorem CapInductionFlow.image_properties
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W) (r : LowerCapRectangle bStar) :
    IsCompact (r.image Y) ∧ MeasurableSet (r.image Y) ∧ volume (r.image Y) < ⊤ ∧
      r.image Y ⊆ modelOpenSquare :=
  cap_closed_image_properties hf.jointSmooth hf.displacement r.region_subset_domain

theorem CapInductionFlow.image_subset_square
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W) (r : LowerCapRectangle bStar) :
    r.image Y ⊆ modelSquare := (hf.image_properties r).2.2.2.trans modelOpenSquare_subset

theorem CapInductionFlow.pointwise_from_larger_L2
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (r : LowerCapRectangle bStar) {n : ℕ} {H : ℝ≥0}
    (hL : CoordinateL2Bound z (r.expand.image Y) (n+2) H) :
    CoordinateBound z (r.image Y) n
      ((squareSobolevWeight (flowInteriorRadius (heightQuotientJetBound G Z d c) r.margin r.margin)+1)*(H : ℝ)) := by
  apply coordinateL2Bound_to_expanded_cap_coordinateBound hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode (heightQuotientJetBound_nonneg hG hZ hd hc)
    hh.quotient (fun p hp => hf.quotientBound [1] (by norm_num) p hp)
    (hh.smooth.mono hf.domainSubset) r hL

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted

theorem scalar_fderiv_coordinate_bound {q : Coord → ℝ} {p v : Coord} {M : ℝ}
    (_hM : 0 ≤ M) (hpartial : ∀ i : Fin 2, |coordPartial i q p| ≤ M) :
    |fderiv ℝ q p v| ≤ M*(|v 0|+|v 1|) := by
  have he : v = (v 0) • Pi.single 0 (1 : ℝ) + (v 1) • Pi.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [he, map_add, map_smul, map_smul]
  change |v 0 * coordPartial 0 q p + v 1 * coordPartial 1 q p| ≤ _
  calc
    _ ≤ |v 0 * coordPartial 0 q p| + |v 1 * coordPartial 1 q p| := abs_add_le _ _
    _ = |v 0| * |coordPartial 0 q p|+|v 1| * |coordPartial 1 q p| := by rw [abs_mul,abs_mul]
    _ ≤ |v 0| * M+|v 1| * M := add_le_add
      (mul_le_mul_of_nonneg_left (hpartial 0) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hpartial 1) (abs_nonneg _))
    _ = _ := by ring

theorem quotient_change_from_origin
    {q : Coord → ℝ} {U : Set Coord} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (hM : 0 ≤ M)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    {p : Coord} (hp : p ∈ modelSquare) : |q p-q 0| ≤ M*(|p 0|+|p 1|) := by
  have hz : (0 : Coord) ∈ modelSquare := by constructor <;> intro i <;> norm_num
  have hconv : Convex ℝ modelSquare := convex_Icc _ _
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • p ∈ modelSquare := by
    have h := hconv hp hz ht.1 (sub_nonneg.mpr ht.2) (by ring)
    simpa only [smul_zero, add_zero] using h
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => q (s • p)) (fderiv ℝ q (t • p) p) t := by
    have hdq := ((hq.contDiffAt (hU.mem_nhds (hSU (hseg t ht)))).differentiableAt (by simp)).hasFDerivAt
    have hdp : HasDerivAt (fun s : ℝ => s • p) p t := by
      have ht := (hasDerivAt_id t).smul_const p
      change HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) t at ht
      rw [one_smul] at ht
      exact ht
    exact hdq.comp_hasDerivAt t hdp
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv (fun s : ℝ => q (s • p)) t‖ ≤ M*(|p 0|+|p 1|) := by
    rw [(hder t ht).deriv, Real.norm_eq_abs]
    exact scalar_fderiv_coordinate_bound hM (hpartial (t • p) (hseg t ht))
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hder t ht).differentiableAt) hb
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  simpa only [zero_smul, one_smul, sub_zero, norm_one, mul_one, Real.norm_eq_abs] using h

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flow_segment_coordinate_sum
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {q0 T r s t u : ℝ} (hq0 : |q0| ≤ 1/20) (_hT : 0 < T) (hT2 : T < 2)
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T) (hu : u ∈ Icc (-T) T)
    (htheta : |Y s t+q0*t| ≤ r) :
    |u|+|Y s u| ≤ r+107*T/100 := by
  have ht' : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hu' : u ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have habst : |t| ≤ T := abs_le.mpr ht
  have habsu : |u| ≤ T := abs_le.mpr hu
  have hdt : |u-t| ≤ 2*T := (abs_sub u t).trans (by linarith)
  have hmove := (cap_flow_time_lipschitz hq hU hSU hY hrange hstart hode hsmall hs ht' hu').trans
    (mul_le_mul_of_nonneg_left hdt (by norm_num : (0 : ℝ) ≤ 1/100))
  have hprod : |q0*t| ≤ (1/20)*T := by
    rw [abs_mul]
    exact mul_le_mul hq0 habst (abs_nonneg _) (by norm_num)
  have hyt : |Y s t| ≤ r+(1/20)*T := by
    calc
      |Y s t| = |(Y s t+q0*t)-q0*t| := by congr 1; ring
      _ ≤ |Y s t+q0*t|+|q0*t| := abs_sub _ _
      _ ≤ _ := add_le_add htheta hprod
  have hyu : |Y s u| ≤ |Y s u-Y s t|+|Y s t| := by
    calc
      |Y s u| = |(Y s u-Y s t)+Y s t| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

theorem flow_segment_quotient_near_center
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L T r s t : ℝ} (hM : 0 ≤ M) (hL : 0 < L)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : 0 < T) (hT2 : T < 2) (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T)
    (htheta : |Y s t+q0*t| ≤ r)
    (hrsmall : M*(r+107*T/100) ≤ 9/(100*L)) :
    ∀ u ∈ Icc (-T) T, |q (coordinatePoint u (Y s u))-q0| ≤ 1/(10*L) := by
  intro u hu
  have hu2 : u ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hp : coordinatePoint u (Y s u) ∈ modelSquare := coordinatePoint_mem_modelSquare
    ⟨by linarith [hu2.1],by linarith [hu2.2]⟩
    (hrange s ⟨hs.1.le,hs.2.le⟩ u hu2)
  have hnorm := flow_segment_coordinate_sum hq hU hSU hY hrange hstart hode
    hsmall hq0 hT hT2 hs ht hu htheta
  have hlocal : |q (coordinatePoint u (Y s u))-q 0| ≤ M*(|u|+|Y s u|) := by
    simpa [coordinatePoint] using quotient_change_from_origin hq hU hSU hM hpartial hp
  have hsum : |q (coordinatePoint u (Y s u))-q0| ≤
      |q (coordinatePoint u (Y s u))-q 0|+|q 0-q0| := by
    calc
      _ = |(q (coordinatePoint u (Y s u))-q 0)+(q 0-q0)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have ha := hsum.trans (add_le_add (hlocal.trans
    (mul_le_mul_of_nonneg_left hnorm hM)) hcenter)
  have heq : 9/(100*L)+1/(100*L) = 1/(10*L) := by field_simp [hL.ne']; ring
  exact ha.trans ((add_le_add hrsmall le_rfl).trans_eq heq)

theorem actual_shear_seed_distance
    {q0 epsilon T s t : ℝ} (hT : 0 < T) (hT2 : T < 2)
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Icc (-T) T)
    (hclose : ∀ u ∈ Icc (-T) T, |q (coordinatePoint u (Y s u))-q0| ≤ epsilon) :
    |Y s t+q0*t-s| ≤ epsilon*|t| := by
  have hd (u : ℝ) (hu : u ∈ Icc (-T) T) :
      HasDerivAt (fun a => Y s a+q0*a) (-q (coordinatePoint u (Y s u))+q0) u := by
    have hu2 : u ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hh := (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs hu2).add
      ((hasDerivAt_id u).const_mul q0)
    change HasDerivAt (fun a : ℝ => Y s a + q0 * a)
      (-q (coordinatePoint u (Y s u)) + q0 * 1) u at hh
    rw [mul_one] at hh
    exact hh
  have hb (u : ℝ) (hu : u ∈ Icc (-T) T) :
      ‖deriv (fun a => Y s a+q0*a) u‖ ≤ epsilon := by
    rw [(hd u hu).deriv, Real.norm_eq_abs]
    have heq : -q (coordinatePoint u (Y s u))+q0 = -(q (coordinatePoint u (Y s u))-q0) := by ring
    rw [heq,abs_neg]
    exact hclose u hu
  have h := (convex_Icc (-T) T).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hd u hu).differentiableAt) hb
    (show (0 : ℝ) ∈ Icc (-T) T by constructor <;> linarith) ht
  simpa only [hstart s ⟨hs.1.le,hs.2.le⟩, mul_zero, add_zero, sub_zero, Real.norm_eq_abs] using h

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

structure UpperCapRectangle (floor : ℝ) where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  left_gt : -2 < left
  right_lt : right < 2
  top_lt : top < 2
  horizontal : left ≤ right
  vertical : bottom ≤ top
  bottom_gt : floor < bottom
  floor_nonneg : 0 ≤ floor

namespace UpperCapRectangle
variable {floor : ℝ}

def region (r : UpperCapRectangle floor) : Set Coord :=
  closedRectangle r.left r.right r.bottom r.top

def image (r : UpperCapRectangle floor) (Y : ℝ → ℝ → ℝ) : Set Coord :=
  capChart Y '' r.region

def lower (r : UpperCapRectangle floor) : LowerCapRectangle (-floor) where
  left := r.left
  right := r.right
  bottom := -r.top
  top := -r.bottom
  left_gt := r.left_gt
  right_lt := r.right_lt
  bottom_gt := neg_lt_neg r.top_lt
  horizontal := r.horizontal
  vertical := neg_le_neg r.vertical
  top_lt := neg_lt_neg r.bottom_gt
  ceiling_le := neg_nonpos.mpr r.floor_nonneg

theorem region_subset_domain (r : UpperCapRectangle floor) : r.region ⊆ capChartDomain :=
  closedRectangle_subset_capChartDomain r.left_gt r.right_lt
    (by linarith [r.bottom_gt,r.floor_nonneg]) r.top_lt

theorem image_properties (r : UpperCapRectangle floor) {Y : ℝ → ℝ → ℝ}
    (hchart : ContDiffOn ℝ ∞ (capChart Y) capChartDomain)
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) :
    IsCompact (r.image Y) ∧ MeasurableSet (r.image Y) ∧ r.image Y ⊆ modelSquare := by
  have hcompact : IsCompact (r.image Y) :=
    (capRectangle_isCompact r.left r.right r.bottom r.top).image_of_continuousOn
      (hchart.continuousOn.mono r.region_subset_domain)
  refine ⟨hcompact,hcompact.measurableSet,?_⟩
  rintro p ⟨q,hq,rfl⟩
  exact modelOpenSquare_subset
    (capChart_mem_modelOpenSquare (r.region_subset_domain hq) (hdisp q (r.region_subset_domain hq)))

end UpperCapRectangle
end SmoothLocal.Flow.Reflection

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

theorem lowerCapMetricRequests_order_le {bStar : ℝ} (k : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapMetricRequests k r) : b.1 ≤ k+7 := by
  induction k generalizing r with
  | zero => simp [lowerCapMetricRequests] at hb
  | succ k ih =>
    simp only [lowerCapMetricRequests,List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · omega
    · omega
    · have h := ih r.energyOuter.expand hb
      omega

theorem lowerCapMetricRequests_full_order_le {bStar : ℝ} (k : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapMetricRequests k r) {n : ℕ} (hn : n ≤ b.1+2) : n ≤ k+9 := by
  have h := lowerCapMetricRequests_order_le k r b hb
  omega

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation

theorem exists_sectionFour_radius {M L : ℝ} (hM : 0 ≤ M) (hL : 0 < L) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      M*(r+107*(L*r)/100) ≤ 9/(100*L) := by
  let A := M*(1+107*L/100)
  let alpha := 9/(100*L)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have ha : 0 < alpha := by dsimp only [alpha]; positivity
  let r := min (1/40 : ℝ) (min (1/(20*L)) (alpha/(2*(A+1))))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1/40 := min_le_left _ _
  have hr2 : r ≤ 1/(20*L) := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ alpha/(2*(A+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hr2' := (le_div_iff₀ (by positivity : 0 < 20*L)).mp hr2
  have hr3' := (le_div_iff₀ (by positivity : 0 < 2*(A+1))).mp hr3
  refine ⟨r,hr,by linarith,by nlinarith,?_⟩
  have he : M*(r+107*(L*r)/100) = A*r := by dsimp only [A]; ring
  rw [he]
  change A*r ≤ alpha
  nlinarith

theorem pulse_width_eventually {r : ℝ} (hr : 0 < r) (delta : ℝ) :
    ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧ delta/(2*tau) ≤ r/4 := by
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0))
  have hw : Tendsto (fun tau : ℝ => delta/(2*tau)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm] using hi.const_mul (delta/2)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hw.eventually_lt tendsto_const_nhds (show (0 : ℝ) < r/4 by linarith)] with tau ht hwidth
  exact ⟨ht,hwidth.le⟩

theorem pulseOriginalBox_coordinate_bounds {q0 a delta tau : ℝ} {p : Coord}
    (hp : p ∈ pulseOriginalBox q0 a delta tau) :
    |p 0| ≤ a ∧ |p 1+q0*p 0| ≤ delta/(2*tau) := by
  obtain ⟨v,hv,rfl⟩ := hp
  have hx : |v 0| ≤ a := abs_le.mpr
    ⟨by simpa [pulseLocalBox] using hv.1 0,by simpa [pulseLocalBox] using hv.2 0⟩
  have hy : |v 1| ≤ delta/(2*tau) := abs_le.mpr
    ⟨by simpa [pulseLocalBox] using hv.1 1,by simpa [pulseLocalBox] using hv.2 1⟩
  constructor
  · simpa [inverseShearCoordinates] using hx
  · have he : (inverseShearCoordinates q0 v) 1+q0*(inverseShearCoordinates q0 v) 0 = v 1 := by
      simp [inverseShearCoordinates]
    simpa only [he] using hy

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem pulseBox_seed_abs_lt_half
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hwidth : delta/(2*tau) ≤ r/4)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpulse : capChart Y p ∈ pulseOriginalBox q0 a delta tau) :
    |p 1| < r/2 := by
  obtain ⟨hx,htheta⟩ := pulseOriginalBox_coordinate_bounds hpulse
  have htime : p 0 ∈ Icc (-(L*r)) (L*r) := by
    apply abs_le.mp
    exact (by simpa only [capChart_zero] using hx : |p 0| ≤ a).trans ha
  have htheta' : |Y (p 1) (p 0)+q0*p 0| ≤ delta/(2*tau) := by
    simpa only [capChart_one,capChart_zero,capFlowHeight] using htheta
  have hthetaR : |Y (p 1) (p 0)+q0*p 0| ≤ r := htheta'.trans (hwidth.trans (by linarith))
  have hclose := flow_segment_quotient_near_center hq hU hSU hY hrange hstart hode
    hsmall hM hL hpartial hq0 hcenter (mul_pos hL hr) hT hp.2 htime hthetaR hrsmall
  have hdist := actual_shear_seed_distance hq hU hSU hY hrange hstart hode
    (mul_pos hL hr) hT hp.2 htime hclose
  have htimeAbs : |p 0| ≤ L*r := abs_le.mpr htime
  have hdist' : |Y (p 1) (p 0)+q0*p 0-p 1| ≤ r/10 := by
    have he : (1/(10*L))*(L*r) = r/10 := by
      field_simp [hL.ne']
    exact hdist.trans ((mul_le_mul_of_nonneg_left htimeAbs (by positivity)).trans_eq he)
  have hsabs : |p 1| ≤ |Y (p 1) (p 0)+q0*p 0-p 1|+|Y (p 1) (p 0)+q0*p 0| := by
    calc
      |p 1| = |(Y (p 1) (p 0)+q0*p 0)-(Y (p 1) (p 0)+q0*p 0-p 1)| := by congr 1; ring
      _ ≤ |Y (p 1) (p 0)+q0*p 0|+|Y (p 1) (p 0)+q0*p 0-p 1| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith

theorem pulseTensor_not_tsupport_exterior_seed
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : 0 < a) (haL : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hd : 0 < delta) (ht : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (N : ℕ) {p : Coord} (hp : p ∈ capChartDomain) (hseed : r/2 ≤ |p 1|) :
    capChart Y p ∉ tsupport (pulseTensor q0 a N delta tau) := by
  intro hin
  have hbox := pulseTensor_tsupport_subset ha hd ht N hin
  exact (not_lt_of_ge hseed) (pulseBox_seed_abs_lt_half hq hU hSU hY hrange hstart hode
    hsmall hM hL hr hpartial hq0 hcenter hT haL hrsmall hwidth hp hbox)

theorem testMetric_eventuallyEq_on_lower_cap
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : 0 < a) (haL : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hd : 0 < delta) (ht : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (gStar : MetricField) (N : ℕ) (R : LowerCapRectangle (-r/2))
    {p : Coord} (hp : p ∈ R.image Y) :
    testMetric gStar q0 a N delta tau =ᶠ[𝓝 p] gStar := by
  obtain ⟨v,hv,rfl⟩ := hp
  have hseed : r/2 ≤ |v 1| := by
    have htop : v 1 ≤ R.top := hv.2.2
    have hceil := R.top_lt
    have habs := neg_le_abs (v 1)
    linarith
  exact metric_add_eventuallyEq_of_not_mem_tsupport gStar (pulseTensor q0 a N delta tau)
    (pulseTensor_not_tsupport_exterior_seed hq hU hSU hY hrange hstart hode hsmall hM hL hr
      hpartial hq0 hcenter hT ha haL hrsmall hd ht hwidth N (R.region_subset_domain hv) hseed)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

def lowerCapPointwiseRequests {bStar : ℝ} (n : ℕ) (r : LowerCapRectangle bStar) :
    List (ℕ × LowerCapRectangle bStar) := lowerCapMetricRequests (n-6) r.expand

theorem lowerCapPointwiseRequests_full_order_le {bStar : ℝ} (n : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapPointwiseRequests n r) {k : ℕ} (hk : k ≤ b.1+2) :
    k ≤ max 8 (n+3) := by
  by_cases hn : n ≤ 6
  · have hn0 : n-6=0 := Nat.sub_eq_zero_of_le hn
    simp [lowerCapPointwiseRequests,hn0,lowerCapMetricRequests] at hb
  · have h := lowerCapMetricRequests_full_order_le (n-6) r.expand b hb hk
    omega

theorem uniform_finite_varying_lowerCap_pointwise
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    {bStar : ℝ} (J : CapMetricJetBudget bStar) (n : ℕ) (r : LowerCapRectangle bStar)
    (hJ : ∀ b ∈ lowerCapPointwiseRequests n r, 0 ≤ J b.1 b.2) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        FiniteCapMetricJets g Y J (lowerCapPointwiseRequests n r) →
        CoordinateBound z (r.image Y) n B := by
  obtain ⟨H,hH⟩ := uniform_finite_varying_lowerCap_L2 G Z d c e0 kappa hG hZ hd hc
    J (n-6) r.expand hJ
  let M := heightQuotientJetBound G Z d c
  let B := (squareSobolevWeight (flowInteriorRadius M r.margin r.margin)+1)*(H : ℝ)
  have hr := flowInteriorRadius_pos M r.margin_pos r.margin_pos
  have hB : 0 ≤ B := by
    dsimp only [B,squareSobolevWeight]
    positivity
  refine ⟨B,hB,?_⟩
  intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
  exact CapInductionFlow.pointwise_from_larger_L2 hh hf hG hZ hd hc r
    ((hH g U z Y W hg hU hSU hgB hdet hh hf hlocal).mono
      (by omega : n+2 ≤ (n-6)+8) le_rfl)

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.Hyperbolic

def shearedModelSquare (q0 : ℝ) : Set Coord :=
  inverseShearCoordinates q0 ⁻¹' modelSquare

def sectionFourClosedSlab (L r : ℝ) : Set Coord :=
  {p | |p 0| ≤ L*r ∧ |p 1| ≤ r}

theorem sectionFourClosedSlab_mem_shearedModelSquare
    {q0 L r : ℝ} (_hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    {p : Coord} (hp : p ∈ sectionFourClosedSlab L r) :
    p ∈ shearedModelSquare q0 := by
  have hx : |p 0| ≤ (1/20 : ℝ) := hp.1.trans hLr
  have hmul : |q0 * p 0| ≤ (1/20 : ℝ) * (1/20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hx (abs_nonneg _) (by norm_num)
  have hy : |p 1 - q0 * p 0| ≤ r + (1/20 : ℝ)*(1/20) :=
    (abs_sub _ _).trans (add_le_add hp.2 hmul)
  have hx3 : |p 0| ≤ 3 := hx.trans (by norm_num)
  have hy3 : |p 1 - q0*p 0| ≤ 3 := hy.trans (by linarith)
  constructor <;> intro i <;> fin_cases i
  · exact (abs_le.mp hx3).1
  · exact (abs_le.mp hy3).1
  · exact (abs_le.mp hx3).2
  · exact (abs_le.mp hy3).2

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

abbrev UpperCapMetricJetBudget (floor : ℝ) := ℕ → UpperCapRectangle floor → ℝ

def reflectedUpperRectangle {floor : ℝ} (r : LowerCapRectangle (-floor)) :
    UpperCapRectangle floor where
  left := r.left
  right := r.right
  bottom := -r.top
  top := -r.bottom
  left_gt := r.left_gt
  right_lt := r.right_lt
  top_lt := by simpa only [neg_neg] using neg_lt_neg r.bottom_gt
  horizontal := r.horizontal
  vertical := neg_le_neg r.vertical
  bottom_gt := by simpa only [neg_neg] using neg_lt_neg r.top_lt
  floor_nonneg := neg_nonpos.mp r.ceiling_le

end SmoothLocal.Flow.Reflection

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem shrinking_class_slab_axis_bounds {kappa r b : ℝ} {M : ℕ} {p : Coord}
    (hr : 0 ≤ r) (hb : b ≤ 0)
    (hp : p ∈ shrinkingSlab (-(boundedClassWidth kappa M * r)) (boundedClassWidth kappa M * r)
      (-r) b (boundedClassWidth kappa M / 4)) :
    |p 0| ≤ boundedClassWidth kappa M * r ∧ |p 1| ≤ r := by
  have ht := hp.1
  have hx := hp.2
  have hspeed : 0 ≤ boundedClassWidth kappa M / 4 :=
    div_nonneg (boundedClassWidth_pos kappa M).le (by norm_num)
  have hmove : 0 ≤ (boundedClassWidth kappa M / 4) * (p 1 - (-r)) :=
    mul_nonneg hspeed (sub_nonneg.mpr ht.1)
  unfold inwardLeft inwardRight at hx
  exact ⟨abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    abs_le.mpr ⟨ht.1, by linarith [ht.2]⟩⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Hyperbolic

theorem testMetric_eventuallyEq_off_pulse
    (gStar : MetricField) (q0 a : ℝ) (N : ℕ) {delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) {p : Coord}
    (hfar : delta/tau ≤ |p 1+q0*p 0|) :
    testMetric gStar q0 a N delta tau =ᶠ[𝓝 p] gStar := by
  apply metric_add_eventuallyEq_of_not_mem_tsupport gStar (pulseTensor q0 a N delta tau)
  intro hp
  have hbox := pulseTensor_tsupport_subset ha hd ht N hp
  have hnear := (pulseOriginalBox_coordinate_bounds hbox).2
  have hpos : 0 < delta/tau := div_pos hd ht
  have he : delta/(2*tau) = (delta/tau)/2 := by ring
  rw [he] at hnear
  linarith

theorem testMetric_eventuallyEq_below_pulse
    (gStar : MetricField) (q0 a : ℝ) (N : ℕ) {delta tau x t : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (htau : 0 < tau) (ht : t ≤ -delta/tau) :
    testMetric gStar q0 a N delta tau =ᶠ[𝓝 (inverseShearCoordinates q0 ![x,t])] gStar := by
  apply testMetric_eventuallyEq_off_pulse gStar q0 a N ha hd htau
  have he : (inverseShearCoordinates q0 ![x,t]) 1+
      q0*(inverseShearCoordinates q0 ![x,t]) 0 = t := by
    simp [inverseShearCoordinates]
  rw [he]
  have hwidth : delta/tau ≤ -t := by
    simpa only [neg_div, neg_neg] using neg_le_neg ht
  exact hwidth.trans (neg_le_abs t)

theorem exists_uniform_off_pulse_metric_jets
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {q0 L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ tau : ℕ, 1 ≤ tau → m ≤ tau →
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
          testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
      ∀ x t : ℝ, |x| ≤ L*r → t ∈ Icc (-r) (-delta/(tau : ℝ)) →
      ∀ i j : Fin 2, ∀ k ≤ m,
        ‖iteratedFDeriv ℝ k (fun p => gTau p i j) (inverseShearCoordinates q0 ![x,t])‖ ≤ B := by
  obtain ⟨Bstar,hBstar,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  refine ⟨Bstar+1, by linarith, ?_⟩
  intro N delta hd tau htau hmtau gTau U hgTau hU hSU happrox x t hx ht i j k hk
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau)
  have hneg : -delta/(tau : ℝ) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hd) htr
  have hpS : inverseShearCoordinates q0 ![x,t] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨hx, abs_le.mpr ⟨ht.1, (ht.2.trans hneg.le).trans hr.le⟩⟩
  have heq := testMetric_eventuallyEq_below_pulse gStar q0 (L*r/16) N
    (x := x) (div_pos (mul_pos hL hr) (by norm_num)) hd htr ht.2
  have hb := metric_jet_norm_le_of_approximation_locality hgStar hgTau hV hU
    (hSV hpS) (hSU hpS) heq i j k (hbase i j k hk _ hpS)
    (happrox i j k (hk.trans hmtau) _ hpS)
  exact hb.trans (add_le_add le_rfl (metricApproximationAccuracy_le_one htau))

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation

theorem actual_flow_preimage_near_center
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ}
    {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    {t y : ℝ} (ht : |t| ≤ 1) (hy : |y| ≤ 3/4) :
    ∃ s ∈ Ioo (-1 : ℝ) 1, Y s t = y := by
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := by
    constructor <;> linarith [(abs_le.mp ht).1,(abs_le.mp ht).2]
  have hnegp : boxPoint t (-1) ∈ capChartDomain := by
    simpa [capChartDomain,coordinateRectangle,boxPoint] using And.intro ht2 (show (-1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  have hposp : boxPoint t 1 ∈ capChartDomain := by
    simpa [capChartDomain,coordinateRectangle,boxPoint] using And.intro ht2 (show (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  have hneg : |Y (-1) t+1| ≤ (1 : ℝ)/50 := by
    simpa [capFlowHeight,boxPoint] using hf.displacement (boxPoint t (-1)) hnegp
  have hpos : |Y 1 t-1| ≤ (1 : ℝ)/50 := by
    simpa [capFlowHeight,boxPoint] using hf.displacement (boxPoint t 1) hposp
  have hlo : Y (-1) t < y := by linarith [(abs_le.mp hneg).2,(abs_le.mp hy).1]
  have hhi : y < Y 1 t := by linarith [(abs_le.mp hpos).1,(abs_le.mp hy).2]
  have hmap : MapsTo (fun s : ℝ => (s,t)) (Icc (-1 : ℝ) 1)
      (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) := by
    intro s hs
    exact ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,⟨ht2.1.le,ht2.2.le⟩⟩
  have hcont : ContinuousOn (fun s : ℝ => Y s t) (Icc (-1 : ℝ) 1) :=
    hf.continuous.comp (by fun_prop : ContinuousOn (fun s : ℝ => (s,t)) (Icc (-1 : ℝ) 1)) hmap
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont ⟨hlo.le,hhi.le⟩
  refine ⟨s,⟨?_,?_⟩,hse⟩
  · by_contra hn
    have he : s = -1 := le_antisymm (le_of_not_gt hn) hs.1
    subst s
    linarith
  · by_contra hn
    have he : s = 1 := le_antisymm hs.2 (le_of_not_gt hn)
    subst s
    linarith

def lowerCutRectangle (L r : ℝ) (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) : LowerCapRectangle (-r/2) where
  left := -(2*L*r)
  right := 2*L*r
  bottom := -(3*r/2)
  top := -(3*r/4)
  left_gt := by nlinarith
  right_lt := by nlinarith
  bottom_gt := by linarith
  horizontal := by nlinarith [mul_pos hL hr]
  vertical := by linarith
  top_lt := by linarith
  ceiling_le := by linarith

theorem actual_lower_cut_in_cap_image
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa q0 L r : ℝ}
    {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2) (hLr : L*r ≤ 1/20)
    (hq0 : |q0| ≤ 1/20) (hcenter : |hessianQuotient g z 0-q0| ≤ 1/(100*L))
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    {t : ℝ} (ht : |t| ≤ L*r) :
    inverseShearCoordinates q0 (boxPoint t (-r)) ∈ (lowerCutRectangle L r hL hr hrhalf hLr).image Y := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hpartial (p : Coord) (hp : p ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) p| ≤ M := hf.quotientBound [i] (by norm_num) p hp
  have hTpos : 0 < L*r := mul_pos hL hr
  have ht1 : |t| ≤ 1 := ht.trans (by linarith)
  have hqt : |q0*t| ≤ (1/20)*(L*r) := by
    rw [abs_mul]
    exact mul_le_mul hq0 ht (abs_nonneg _) (by norm_num)
  have hy : |-r-q0*t| ≤ 3/4 := by
    have h := abs_sub (-r) (q0*t)
    rw [abs_neg,abs_of_pos hr] at h
    linarith
  obtain ⟨s,hs,hse⟩ := actual_flow_preimage_near_center hf ht1 hy
  have hs2 : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have htt : t ∈ Icc (-(L*r)) (L*r) := abs_le.mp ht
  have htheta : |Y s t+q0*t| ≤ r := by
    rw [hse]
    have he : -r-q0*t+q0*t = -r := by ring
    rw [he,abs_neg,abs_of_pos hr]
  have hclose := flow_segment_quotient_near_center hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hpartial hq0 hcenter
    hTpos (by linarith : L*r < 2) hs2 htt htheta hrsmall
  have hdist := actual_shear_seed_distance hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode hTpos (by linarith : L*r < 2) hs2 htt hclose
  have hdist' : |-r-s| ≤ r/10 := by
    have he : (1/(10*L))*(L*r) = r/10 := by
      rw [div_mul_eq_mul_div₀, one_mul, mul_comm (10 : ℝ) L, mul_div_mul_left _ _ hL.ne']
    have hbound := hdist.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq he)
    simpa only [hse,sub_add_cancel] using hbound
  refine ⟨boxPoint t s,?_,?_⟩
  · change (boxPoint t s) ∈ closedRectangle (-(2*L*r)) (2*L*r) (-(3*r/2)) (-(3*r/4))
    constructor
    · simpa [boxPoint] using (show t ∈ Icc (-(2*L*r)) (2*L*r) by
        constructor <;> nlinarith [(abs_le.mp ht).1,(abs_le.mp ht).2])
    · simpa [boxPoint] using (show s ∈ Icc (-(3*r/2)) (-(3*r/4)) by
        constructor <;> linarith [(abs_le.mp hdist').1,(abs_le.mp hdist').2])
  · ext i
    fin_cases i <;> simp [capChart,capFlowHeight,coordinatePoint,boxPoint,inverseShearCoordinates,hse]

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

def upperCapPointwiseRequests {floor : ℝ} (n : ℕ) (r : UpperCapRectangle floor) :
    List (ℕ × UpperCapRectangle floor) :=
  (lowerCapPointwiseRequests n r.lower).map (fun b => (b.1,reflectedUpperRectangle b.2))

def FiniteUpperCapMetricJets {floor : ℝ} (g : MetricField) (Y : ℝ → ℝ → ℝ)
    (J : UpperCapMetricJetBudget floor) (L : List (ℕ × UpperCapRectangle floor)) : Prop :=
  ∀ b ∈ L, ∀ (i j : Fin 2) (k : ℕ), k ≤ b.1+2 →
    ∀ p ∈ b.2.image Y, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ J b.1 b.2

theorem upperCapPointwiseRequests_full_order_le {floor : ℝ} (n : ℕ)
    (r : UpperCapRectangle floor) (b : ℕ × UpperCapRectangle floor)
    (hb : b ∈ upperCapPointwiseRequests n r) {k : ℕ} (hk : k ≤ b.1+2) :
    k ≤ max 8 (n+3) := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  exact lowerCapPointwiseRequests_full_order_le n r.lower a ha hk

end SmoothLocal.Flow.Reflection

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Hyperbolic

theorem exists_uniform_off_pulse_sheared_metric_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {q0 L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ tau : ℕ, 1 ≤ tau → m ≤ tau →
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
          testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
      ∀ i j : Fin 2, CoordinateBound (fun p => metricInShearCoordinates gTau q0 p i j)
        {p | |p 0| ≤ L*r ∧ p 1 ∈ Icc (-r) (-delta/(tau : ℝ))} m B := by
  obtain ⟨B,hB,hjets⟩ := exists_uniform_off_pulse_metric_jets hgStar hV hSV
    hL hr hrhalf hLr hq0 m
  refine ⟨shearedMetricCoordinateBudget B q0 m,
    shearedMetricCoordinateBudget_nonneg q0 m hB,?_⟩
  intro N delta hd tau htau hmtau gTau U hgTau hU hSU happrox
  let T : Set Coord := {p | |p 0| ≤ L*r ∧ p 1 ∈ Icc (-r) (-delta/(tau : ℝ))}
  let S : Set Coord := inverseShearCoordinates q0 '' T
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau)
  have ht0 : -delta/(tau : ℝ) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hd) htr
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨hp.1,abs_le.mpr ⟨hp.2.1,(hp.2.2.trans ht0.le).trans hr.le⟩⟩
  have hsub : S ⊆ U := by
    rintro y ⟨p,hp,rfl⟩
    exact hSU (hpS p hp)
  have hb (i j : Fin 2) : CoordinateBound (fun p => gTau p i j) S m B := by
    apply coordinateBound_of_frechet_bounds (hgTau.1 i j) hU hsub
    intro k hk y hy
    obtain ⟨p,hp,rfl⟩ := hy
    have he : ![p 0,p 1] = p := by ext a; fin_cases a <;> rfl
    simpa only [he] using hjets N delta hd tau htau hmtau gTau U hgTau hU hSU happrox
      (p 0) (p 1) hp.1 hp.2 i j k hk
  have hs := metric_coordinate_bound_inverse_shear hgTau hU hsub hB hb q0
  intro i j ds hds p hp
  exact hs i j ds hds p ⟨p,hp,rfl⟩

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

theorem actual_testMetric_eventuallyEq_on_upper_cap
    {G Z d c e0 kappa q0 L r delta tau : ℝ}
    {g : MetricField} {U W : Set Coord} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z)
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hr : 0 < r) (hLr : L*r ≤ 1/20)
    (hq0 : |q0| ≤ 1/20) (hcenter : |hessianQuotient g z 0-q0| ≤ 1/(100*L))
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hdelta : 0 < delta) (htau : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (gStar : MetricField) (N : ℕ) (R : UpperCapRectangle (r/2))
    {p : Coord} (hp : p ∈ R.image Y) :
    testMetric gStar q0 (L*r/16) N delta tau =ᶠ[𝓝 p] gStar := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hpartial (v : Coord) (hv : v ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) v| ≤ M := hf.quotientBound [i] (by norm_num) v hv
  obtain ⟨v,hv,rfl⟩ := hp
  have hseed : r/2 ≤ |v 1| := by
    have hbottom : R.bottom ≤ v 1 := hv.2.1
    have hfloor := R.bottom_gt
    have habs := le_abs_self (v 1)
    linarith
  exact metric_add_eventuallyEq_of_not_mem_tsupport gStar (pulseTensor q0 (L*r/16) N delta tau)
    (pulseTensor_not_tsupport_exterior_seed hf.quotientSmooth hf.domainOpen hf.squareSubset
      hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hr hpartial hq0 hcenter
      (by linarith : L*r < 2) (by positivity : 0 < L*r/16)
      (by nlinarith [mul_pos hL hr] : L*r/16 ≤ L*r) hrsmall hdelta htau hwidth N
      (R.region_subset_domain hv) hseed)

theorem exists_uniform_actual_two_sided_pulse_exclusion
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧
          ∀ (g gStar : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
            |hessianQuotient g z 0-q0| ≤ 1/(100*L) →
            (∀ R : LowerCapRectangle (-r/2), ∀ p ∈ R.image Y,
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) ∧
            (∀ R : UpperCapRectangle (r/2), ∀ p ∈ R.image Y,
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  obtain ⟨r,hr,hrhalf,hLr,hrsmall⟩ := exists_sectionFour_radius hM hL
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N delta hdelta
  have hevent : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hevent] with tau htau
  have htau0 : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htau.1
  refine ⟨by exact_mod_cast htau.1,?_⟩
  intro g gStar U W z Y hh hf hcenter
  have hpartial (v : Coord) (hv : v ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) v| ≤ M := hf.quotientBound [i] (by norm_num) v hv
  constructor
  · intro R p hp
    exact testMetric_eventuallyEq_on_lower_cap hf.quotientSmooth hf.domainOpen hf.squareSubset
      hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hr hpartial hq0 hcenter
      (by linarith : L*r < 2) (by positivity : 0 < L*r/16)
      (by nlinarith [mul_pos hL hr] : L*r/16 ≤ L*r) hrsmall hdelta htau0 htau.2 gStar N R hp
  · intro R p hp
    exact actual_testMetric_eventuallyEq_on_upper_cap hh hf hG hZ hd hc hL hr hLr
      hq0 hcenter hrsmall hdelta htau0 htau.2 gStar N R hp

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

def finiteCapRequiredMetricOrder (nLower nUpper : ℕ) : ℕ :=
  max (max 8 (nLower+3)) (max 8 (nUpper+3))

theorem exists_actual_finite_cap_metric_budgets
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ nLower nUpper : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
          ∀ᶠ tau : ℕ in atTop, finiteCapRequiredMetricOrder nLower nUpper ≤ tau ∧
            ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
              SmoothPositiveOn gTau U → IsOpen U →
              CapInductionHeight gTau U Z c e0 z →
              CapInductionFlow gTau U G Z d c e0 kappa z Y W →
              |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                  testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              (∀ R : LowerCapRectangle (-r/2),
                FiniteCapMetricJets gTau Y (fun _ _ => B) (lowerCapPointwiseRequests nLower R)) ∧
              (∀ R : UpperCapRectangle (r/2),
                FiniteUpperCapMetricJets gTau Y (fun _ _ => B) (upperCapPointwiseRequests nUpper R)) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hsep⟩ :=
    exists_uniform_actual_two_sided_pulse_exclusion (e0 := e0) (kappa := kappa)
      hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro nLower nUpper
  let m := finiteCapRequiredMetricOrder nLower nUpper
  obtain ⟨Bstar,hBstar,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  refine ⟨Bstar+1,add_nonneg hBstar zero_le_one,?_⟩
  intro N delta hdelta
  filter_upwards [hsep N delta hdelta,eventually_ge_atTop m] with tau htau hm
  refine ⟨hm,?_⟩
  intro gTau U W z Y hgTau hU hh hf hcenter happrox
  obtain ⟨hsepLower,hsepUpper⟩ := htau.2 gTau gStar U W z Y hh hf hcenter
  have herror := metricApproximationAccuracy_le_one htau.1
  have hbound (i j : Fin 2) (k : ℕ) (hk : k ≤ m) (p : Coord) (hpS : p ∈ modelSquare)
      (heq : testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) :
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ Bstar+1 := by
    have h := metric_jet_norm_le_of_approximation_locality hgStar hgTau hV hU
      (hSV hpS) (hf.domainSubset (hf.squareSubset hpS)) heq i j k
      (hbase i j k hk p hpS) (happrox i j k (hk.trans hm) p hpS)
    exact h.trans (add_le_add le_rfl herror)
  constructor
  · intro R b hb i j k hk p hp
    have hkM : k ≤ m :=
      (lowerCapPointwiseRequests_full_order_le nLower R b hb hk).trans (le_max_left _ _)
    exact hbound i j k hkM p (hf.image_subset_square b.2 hp) (hsepLower b.2 p hp)
  · intro R b hb i j k hk p hp
    have hkM : k ≤ m :=
      (upperCapPointwiseRequests_full_order_le nUpper R b hb hk).trans (le_max_right _ _)
    have hpS : p ∈ modelSquare :=
      (b.2.image_properties (capChart_contDiffOn hf.jointSmooth) hf.displacement).2.2 hp
    exact hbound i j k hkM p hpS (hsepUpper b.2 p hp)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem exists_actual_finite_lower_cut_height_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
          ∀ᶠ tau : ℕ in atTop,
            ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
              SmoothPositiveOn gTau U → IsOpen U →
              (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
              (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
              CapInductionHeight gTau U Z c e0 z →
              CapInductionFlow gTau U G Z d c e0 kappa z Y W →
              |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                  testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              ∀ ds : List (Fin 2), ds.length ≤ n → ∀ t : ℝ, |t| ≤ L*r →
                |iteratedCoordPartial ds z (inverseShearCoordinates q0 (boxPoint t (-r)))| ≤ C := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hmetric⟩ :=
    exists_actual_finite_cap_metric_budgets (e0 := e0) (kappa := kappa)
      hgStar hV hSV hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro n
  obtain ⟨Bmetric,hBmetric,hlocal⟩ := hmetric n 0
  let R := lowerCutRectangle L r hL hr hrhalf hLr
  let J : CapMetricJetBudget (-r/2) := fun _ _ => Bmetric
  obtain ⟨C,hC,hheight⟩ := uniform_finite_varying_lowerCap_pointwise
    G Z d c e0 kappa hG hZ hd hc J n R (fun _ _ => hBmetric)
  refine ⟨C,hC,?_⟩
  intro N delta hdelta
  filter_upwards [hlocal N delta hdelta] with tau htau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox ds hds t ht
  have hrequests : FiniteCapMetricJets gTau Y J (lowerCapPointwiseRequests n R) :=
    (htau.2 gTau U W z Y hgTau hU hh hf hcenter happrox).1 R
  have hbound := hheight gTau U z Y W hgTau hU (hf.squareSubset.trans hf.domainSubset)
    hg4 hdet hh hf hrequests
  have hp : inverseShearCoordinates q0 (boxPoint t (-r)) ∈ R.image Y :=
    actual_lower_cut_in_cap_image hh hf hG hZ hd hc hL hr hrhalf hLr hq0 hcenter hrsmall ht
  exact hbound ds hds _ hp

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem inverseShear_lower_cut_mem_modelSquare
    {q0 L r x : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (hx : |x| ≤ L*r) :
    inverseShearCoordinates q0 (boxPoint x (-r)) ∈ modelSquare := by
  have hx20 : |x| ≤ 1/20 := hx.trans hLr
  have hmul : |q0*x| ≤ (1/20 : ℝ)*(1/20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hx20 (abs_nonneg x) (by norm_num)
  have hy : |-r-q0*x| ≤ r+(1/20 : ℝ)*(1/20) := by
    calc
      _ ≤ |-r| + |q0*x| := abs_sub _ _
      _ = r + |q0*x| := by rw [abs_neg, abs_of_pos hr]
      _ ≤ _ := add_le_add le_rfl hmul
  have hx3 : |x| ≤ 3 := hx20.trans (by norm_num)
  have hy3 : |-r-q0*x| ≤ 3 := hy.trans (by linarith)
  obtain ⟨hxl,hxr⟩ := abs_le.mp hx3
  obtain ⟨hyl,hyr⟩ := abs_le.mp hy3
  constructor
  · intro i
    fin_cases i
    · simpa [inverseShearCoordinates,boxPoint] using hxl
    · simpa [inverseShearCoordinates,boxPoint] using hyl
  · intro i
    fin_cases i
    · simpa [inverseShearCoordinates,boxPoint] using hxr
    · simpa [inverseShearCoordinates,boxPoint] using hyr

theorem exists_actual_finite_sheared_lower_cut_height_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
          ∀ᶠ tau : ℕ in atTop,
            ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
              SmoothPositiveOn gTau U → IsOpen U →
              (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
              (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
              CapInductionHeight gTau U Z c e0 z →
              CapInductionFlow gTau U G Z d c e0 kappa z Y W →
              |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                  testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              ∀ ds : List (Fin 2), ds.length ≤ n → ∀ x : ℝ, |x| ≤ L*r →
                |iteratedCoordPartial ds (heightInShearCoordinates z q0)
                  (coordinatePoint x (-r))| ≤ B := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hcut⟩ := exists_actual_finite_lower_cut_height_bounds
    (e0 := e0) (kappa := kappa) hgStar hV hSV hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro n
  obtain ⟨C,hC,hCn⟩ := hcut n
  refine ⟨(2*(1+|q0|))^n*C, by positivity, ?_⟩
  intro N delta hdelta
  filter_upwards [hCn N delta hdelta] with tau htau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox ds hds x hx
  let S : Set Coord := {p | ∃ t : ℝ, |t| ≤ L*r ∧ p = inverseShearCoordinates q0 (boxPoint t (-r))}
  have hSU : S ⊆ U := by
    rintro _ ⟨t,ht,rfl⟩
    exact hf.domainSubset (hf.squareSubset (inverseShear_lower_cut_mem_modelSquare hr hrhalf hLr hq0 ht))
  have hbound : CoordinateBound z S n C := by
    intro es hes _ hp
    obtain ⟨t,ht,rfl⟩ := hp
    exact htau gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox es hes t ht
  have hshear := SmoothLocal.Pulse.CoordinateBound.inverse_shear hbound hh.smooth hU hSU hC q0
  exact hshear ds hds (coordinatePoint x (-r)) ⟨x,hx,rfl⟩

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix NNReal

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_off_pulse_cauchy_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B := by
  let L := boundedClassWidth kappa M
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hcut⟩ := exists_actual_finite_sheared_lower_cut_height_bounds
    (G := G) (Z := (M : ℝ)) (d := d) (c := 1/(M : ℝ)) (e0 := 1/(M : ℝ))
    (kappa := kappa) (q0 := q0) (L := L) hgStar hV hSV hG (Nat.cast_nonneg M) hd
      (one_div_pos.mpr hMR) hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro K
  obtain ⟨A0,hA0,hcutK⟩ := hcut (max 8 (K+2))
  let A : ℝ≥0 := ⟨A0,hA0⟩
  obtain ⟨Cmetric,hCmetric,hmetricK⟩ := exists_uniform_off_pulse_sheared_metric_bounds
    hgStar hV hSV hL hr hrhalf hLr hq0 (max 9 (K+3))
  obtain ⟨B,hB,hcauchy⟩ := exists_bounded_patch_cauchy_bound G d kappa q0 r Cmetric M A
    hG hd hkappa hM hr hrhalf hCmetric hq0 hLr hrsmall K
  refine ⟨B,hB,?_⟩
  intro N delta hdelt
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hcutK N delta hdelt,hwidth,
    eventually_ge_atTop (max 1 (max 9 (K+3)))] with tau hcutTau hwidthTau htau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ x hx n hn
  have htau1 : 1 ≤ tau := (le_max_left _ _).trans htau
  have htauk : max 9 (K+3) ≤ tau := (le_max_right _ _).trans htau
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau1)
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have hb0 : -delta/(tau : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdelt.le) htr.le
  have hab : -r ≤ -delta/(tau : ℝ) := by simpa only [neg_div] using neg_le_neg hdw
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hfullMetric := hmetricK N delta hdelt tau htau1 htauk
    (perturbedMetric g0 eta.val) U hg hU hSU happ
  have hmetric : ∀ i j, CoordinateBound
      (fun p => metricInShearCoordinates (perturbedMetric g0 eta.val) q0 p i j)
      (shrinkingSlab (-(L*r)) (L*r) (-r) (-delta/(tau : ℝ)) (L/4)) (max 9 (K+3)) Cmetric := by
    intro i j ds hds p hp
    have haxes := shrinking_class_slab_axis_bounds hr.le hb0 hp
    exact hfullMetric i j ds hds p ⟨haxes.1,hp.1⟩
  have hactualCut : ∀ ds : List (Fin 2), ds.length ≤ max 8 (K+2) →
      ∀ x : ℝ, |x| ≤ L*r →
        |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ (A : ℝ) :=
    hcutTau (perturbedMetric g0 eta.val) U W z Y hg hU hgB hdet hh hf hcenter happ
  exact hcauchy g0 eta z (-delta/(tau : ℝ)) hclass hab hb0 hgB hdet hcenter hmetric hactualCut x hx n hn

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.exists_actual_off_pulse_cauchy_bounds := @OAI.SmoothLocal.Perturbation.exists_actual_off_pulse_cauchy_bounds
