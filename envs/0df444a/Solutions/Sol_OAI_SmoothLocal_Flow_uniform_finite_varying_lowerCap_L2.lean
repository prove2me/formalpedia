-- Prove2me | solution 1 for OAI.SmoothLocal.Flow.uniform_finite_varying_lowerCap_L2
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:03:54.230204+00:00
-- url     : https://prove2.me/submissions/0b4b12c8-c6d2-4d02-8104-21eb2a40a364

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_HighEquation_exists_localized_actualHighRemainder_bound
import Theorems.Thm_OAI_SmoothLocal_HighEquation_coordinateL2Bound_order_step

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
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord}

theorem metricDet_ne_zero (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) :
    (g p).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit).ne_zero

theorem metricDet_contDiffOn (hg : SmoothPositiveOn g U) :
    ContDiffOn ℝ ∞ (fun p => (g p).det) U := by
  simpa only [Matrix.det_fin_two] using
    ((hg.1 0 0).mul (hg.1 1 1)).sub ((hg.1 0 1).mul (hg.1 1 0))

theorem metricAdjugate_contDiffOn (hg : SmoothPositiveOn g U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => (g p).adjugate i j) U := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hg.1 1 1
  · simpa [Matrix.adjugate_fin_two] using (hg.1 0 1).neg
  · simpa [Matrix.adjugate_fin_two] using (hg.1 1 0).neg
  · simpa [Matrix.adjugate_fin_two] using hg.1 0 0

theorem inverseMetric_contDiffOn (hg : SmoothPositiveOn g U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => inverseMetric g p i j) U := by
  have hi : ContDiffOn ℝ ∞ (fun p => ((g p).det)⁻¹) U :=
    (metricDet_contDiffOn hg).inv (fun p hp => metricDet_ne_zero hg hp)
  have ha := metricAdjugate_contDiffOn hg i j
  simpa [inverseMetric, Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hi.mul ha

theorem christoffel_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (k i j : Fin 2) :
    ContDiffOn ℝ ∞ (christoffel g k i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ l, inverseMetric g p k l *
      (coordPartial i (fun q => g q j l) p +
        coordPartial j (fun q => g q i l) p -
        coordPartial l (fun q => g q i j) p)) U := by
    apply ContDiffOn.sum
    intro l hl
    exact (inverseMetric_contDiffOn hg k l).mul
      (((partial_contDiffOn (hg.1 j l) hU i).add
        (partial_contDiffOn (hg.1 i l) hU j)).sub
        (partial_contDiffOn (hg.1 i j) hU l))
  exact contDiffOn_const.mul hs

end SmoothLocal.Geometry

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

theorem coordPartial_sub_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q - h q) p = coordPartial i f p - coordPartial i h p := by
  simp [coordPartial, fderiv_fun_sub hf hh]

theorem coordPartial_mul_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

theorem coordPartial_sum_two (f : Fin 2 → Coord → ℝ)
    (hf : ∀ a, DifferentiableAt ℝ (f a) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, f a q) p = ∑ a, coordPartial i (f a) p := by
  simp only [Fin.sum_univ_two]
  exact coordPartial_add_at (hf 0) (hf 1) i

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

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

namespace DarbouxJetCalculus

end DarbouxJetCalculus

theorem jetYY_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetYY g p (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 1 1 := rfl

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace MetricJetCalculus

theorem coordPartial_const_mul_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => c * f q) p = c * coordPartial i f p := by
  simp [coordPartial, fderiv_const_mul hf]

end MetricJetCalculus

theorem metric_inverse_derivative_identity {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d i j : Fin 2) :
    (∑ a, (coordPartial d (fun q => g q i a) p * inverseMetric g p a j +
      g p i a * coordPartial d (fun q => inverseMetric g q a j) p)) = 0 := by
  have hproduct : (fun q => ∑ a, g q i a * inverseMetric g q a j) =ᶠ[𝓝 p]
      (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact congrFun (congrFun
      (Matrix.mul_nonsing_inv (g q) ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 q hq).isUnit)) i) j
  have hdg (a : Fin 2) : DifferentiableAt ℝ (fun q => g q i a) p :=
    (((hg.1 i a) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdi (a : Fin 2) : DifferentiableAt ℝ (fun q => inverseMetric g q a j) p :=
    (((inverseMetric_contDiffOn hg a j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hzero : coordPartial d (fun q => ∑ a, g q i a * inverseMetric g q a j) p = 0 := by
    unfold coordPartial
    rw [hproduct.fderiv_eq]
    simp
  have hmul (a : Fin 2) : DifferentiableAt ℝ
      (fun q => g q i a * inverseMetric g q a j) p := (hdg a).mul (hdi a)
  rw [HessianCalculus.coordPartial_sum_two _ hmul d] at hzero
  simpa only [HessianCalculus.coordPartial_mul_at (hdg _) (hdi _) d] using hzero

theorem christoffel_coordPartial_formula {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d k i j : Fin 2) :
    coordPartial d (christoffel g k i j) p = (1 / 2 : ℝ) * ∑ l,
      (coordPartial d (fun q => inverseMetric g q k l) p *
        (coordPartial i (fun q => g q j l) p + coordPartial j (fun q => g q i l) p -
          coordPartial l (fun q => g q i j) p) +
        inverseMetric g p k l *
          (coordPartial d (coordPartial i (fun q => g q j l)) p +
            coordPartial d (coordPartial j (fun q => g q i l)) p -
            coordPartial d (coordPartial l (fun q => g q i j)) p)) := by
  have hdg (a b c : Fin 2) : DifferentiableAt ℝ (coordPartial a (fun q => g q b c)) p :=
    (((partial_contDiffOn (hg.1 b c) hU a) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdi (l : Fin 2) : DifferentiableAt ℝ (fun q => inverseMetric g q k l) p :=
    (((inverseMetric_contDiffOn hg k l) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  let B : Fin 2 → Coord → ℝ := fun l q =>
    coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q -
      coordPartial l (fun q => g q i j) q
  have hB (l : Fin 2) : DifferentiableAt ℝ (B l) p :=
    ((hdg i j l).add (hdg j i l)).sub (hdg l i j)
  have hDB (l : Fin 2) : coordPartial d (B l) p =
      coordPartial d (coordPartial i (fun q => g q j l)) p +
        coordPartial d (coordPartial j (fun q => g q i l)) p -
        coordPartial d (coordPartial l (fun q => g q i j)) p := by
    change coordPartial d (fun q =>
      (coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q) -
        coordPartial l (fun q => g q i j) q) p = _
    have hadd : DifferentiableAt ℝ
        (fun q => coordPartial i (fun q => g q j l) q + coordPartial j (fun q => g q i l) q) p :=
      (hdg i j l).add (hdg j i l)
    rw [HessianCalculus.coordPartial_sub_at hadd (hdg l i j) d,
      HessianCalculus.coordPartial_add_at (hdg i j l) (hdg j i l) d]
  have hsum : DifferentiableAt ℝ (fun q => ∑ l, inverseMetric g q k l * B l q) p :=
    DifferentiableAt.fun_sum fun l _ => (hdi l).mul (hB l)
  change coordPartial d (fun q => (1 / 2 : ℝ) * ∑ l, inverseMetric g q k l * B l q) p = _
  have hterm (l : Fin 2) : DifferentiableAt ℝ
      (fun q => inverseMetric g q k l * B l q) p := (hdi l).mul (hB l)
  rw [MetricJetCalculus.coordPartial_const_mul_at hsum _ d,
    HessianCalculus.coordPartial_sum_two _ hterm d]
  simp only [HessianCalculus.coordPartial_mul_at (hdi _) (hB _) d, hDB, B]

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.LowQuotient

variable {U : Set Coord} {a b : Coord → ℝ} {M c : ℝ}

theorem denominator_ne_zero (hc : 0 < c) (hden : ∀ p ∈ U, c ≤ |b p|) :
    ∀ p ∈ U, b p ≠ 0 := by
  intro p hp hzero
  have hh := hden p hp
  rw [hzero, abs_zero] at hh
  linarith

section SmoothQuotient
variable (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hU : IsOpen U)
variable (hM : 0 ≤ M) (hc : 0 < c)
variable (haB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds a p| ≤ M)
variable (hbB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds b p| ≤ M)
variable (hden : ∀ p ∈ U, c ≤ |b p|)
include ha hb hU hM hc haB hbB hden

end SmoothQuotient
end SmoothLocal.Geometry.LowQuotient

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def inverseDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (d i j : Fin 2) : ℝ :=
  -(∑ a, ∑ b, G⁻¹ i a * D d a b * G⁻¹ b j)

def christoffelJet (G : MetricMatrix) (D : MetricFirstJet) (k i j : Fin 2) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, G⁻¹ k l * (D i j l + D j i l - D l i j)

def christoffelDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (d k i j : Fin 2) : ℝ :=
  (1 / 2 : ℝ) * ∑ l,
    (inverseDerivativeJet G D d k l * (D i j l + D j i l - D l i j) +
      G⁻¹ k l * (DD d i j l + DD d j i l - DD d l i j))

def riemannJet (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (l k i j : Fin 2) : ℝ :=
  christoffelDerivativeJet G D DD i l j k -
    christoffelDerivativeJet G D DD j l i k +
    ∑ m, (christoffelJet G D m j k * christoffelJet G D l i m -
      christoffelJet G D m i k * christoffelJet G D l j m)

def curvatureJet (G : MetricMatrix) (D : MetricFirstJet) (DD : MetricSecondJet) : ℝ :=
  (∑ l, G 0 l * riemannJet G D DD l 1 0 1) / G.det

theorem inverseMetric_coordPartial_eq_jet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d i j : Fin 2) :
    coordPartial d (fun q => inverseMetric g q i j) p =
      inverseDerivativeJet (g p) (fun e a b => coordPartial e (fun q => g q a b) p)
        d i j := by
  let D : MetricMatrix := fun a b => coordPartial d (fun q => g q a b) p
  let I' : MetricMatrix := fun a b => coordPartial d (fun q => inverseMetric g q a b) p
  have hprod : D * (g p)⁻¹ + g p * I' = 0 := by
    ext a b
    change (∑ l, D a l * (g p)⁻¹ l b) + (∑ l, g p a l * I' l b) = 0
    simpa only [← Finset.sum_add_distrib, D, I', inverseMetric] using
      metric_inverse_derivative_identity hg hU hp d a b
  have hinv : (g p)⁻¹ * g p = 1 :=
    Matrix.nonsing_inv_mul (g p)
      ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit)
  have hz : ((g p)⁻¹ * D) * (g p)⁻¹ + I' = 0 := by
    calc
      _ = (g p)⁻¹ * (D * (g p)⁻¹ + g p * I') := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, hinv, one_mul]
      _ = 0 := by rw [hprod, mul_zero]
  have hentry : (((g p)⁻¹ * D) * (g p)⁻¹) i j =
      ∑ a, ∑ b, (g p)⁻¹ i a * D a b * (g p)⁻¹ b j := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have heq := congrFun (congrFun hz i) j
  simp only [Matrix.add_apply, Matrix.zero_apply, hentry] at heq
  change I' i j = -(∑ a, ∑ b, (g p)⁻¹ i a * D a b * (g p)⁻¹ b j)
  linarith only [heq]

theorem gaussianCurvature_eq_curvatureJet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature g p = curvatureJet (g p)
      (fun d i j => coordPartial d (fun q => g q i j) p)
      (fun d e i j => coordPartial d (coordPartial e (fun q => g q i j)) p) := by
  have hΓ (k i j : Fin 2) : christoffel g k i j p =
      christoffelJet (g p) (fun d i j => coordPartial d (fun q => g q i j) p) k i j := rfl
  have hDΓ (d k i j : Fin 2) : coordPartial d (christoffel g k i j) p =
      christoffelDerivativeJet (g p)
        (fun d i j => coordPartial d (fun q => g q i j) p)
        (fun d e i j => coordPartial d (coordPartial e (fun q => g q i j)) p) d k i j := by
    rw [christoffel_coordPartial_formula hg hU hp]
    have hi := inverseMetric_coordPartial_eq_jet hg hU hp
    simp only [inverseMetric] at hi
    simp only [christoffelDerivativeJet, inverseMetric, hi]
  simp only [gaussianCurvature, curvatureJet, riemann, riemannJet, hΓ, hDΓ]

section Continuity
variable {T : Type*} [TopologicalSpace T] {t : T}
variable {G : T → MetricMatrix} {D : T → MetricFirstJet} {DD : T → MetricSecondJet}

end Continuity
end SmoothLocal.Geometry

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

def stateBaseDomain (U : Set Coord) : Set DarbouxState := statePoint ⁻¹' U

def stateConnection (g : MetricField) (i j : Fin 2) (w : DarbouxState) : ℝ :=
  jetConnection g (statePoint w) i j (stateGradient w)

def stateDenominator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetYY g (statePoint w) (w 5) (stateGradient w)

def darbouxStateDomain (g : MetricField) (U : Set Coord) : Set DarbouxState :=
  {w | statePoint w ∈ U ∧ stateDenominator g w ≠ 0}

theorem statePoint_contDiff : ContDiff ℝ ∞ statePoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (0 : Fin 6)
  · exact contDiff_apply ℝ ℝ (1 : Fin 6)

theorem stateGradient_contDiff : ContDiff ℝ ∞ stateGradient := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (2 : Fin 6)
  · exact contDiff_apply ℝ ℝ (3 : Fin 6)

theorem stateBaseDomain_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (stateBaseDomain U) := hU.preimage statePoint_contDiff.continuous

variable {g : MetricField} {U : Set Coord}

theorem stateConnection_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (stateConnection g i j) (stateBaseDomain U) := by
  unfold stateConnection jetConnection
  apply ContDiffOn.sum
  intro r hr
  exact ((christoffel_contDiffOn hg hU r i j).comp statePoint_contDiff.contDiffOn
    (fun w hw => hw)).mul (((contDiff_apply ℝ ℝ r).comp stateGradient_contDiff).contDiffOn)

theorem stateDenominator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 1 1)

theorem darbouxStateDomain_isOpen (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    IsOpen (darbouxStateDomain g U) := by
  exact (stateDenominator_contDiffOn hg hU).continuousOn.isOpen_inter_preimage
    (stateBaseDomain_isOpen hU) isClosed_singleton.isOpen_compl

theorem statePoint_solutionJet (z : Coord → ℝ) (p : Coord) :
    statePoint (solutionJet z p) = p := by
  ext i
  fin_cases i <;> rfl

theorem stateGradient_solutionJet (z : Coord → ℝ) (p : Coord) :
    stateGradient (solutionJet z p) = fun i => coordPartial i z p := by
  ext i
  fin_cases i <;> rfl

theorem stateDenominator_solutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    stateDenominator g (solutionJet z p) = covHessian g z p 1 1 := by
  unfold stateDenominator
  rw [statePoint_solutionJet, stateGradient_solutionJet]
  exact jetYY_at_height g p z

end SmoothLocal.HighEquation

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

end CoordinateBound
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry SmoothLocal.ODE

theorem coordinateRectangle_isOpen (R a b : ℝ) : IsOpen (coordinateRectangle R a b) := by
  change IsOpen (((fun p : Coord => p 0) ⁻¹' Ioo (-R) R) ∩
    ((fun p : Coord => p 1) ⁻¹' Ioo a b))
  exact (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (isOpen_Ioo.preimage (continuous_apply 1))

variable {B : Coord → ℝ} {R a b : ℝ}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

section Smoothness
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] {t : T}
variable {G : T → MetricMatrix} {D : T → MetricFirstJet} {DD : T → MetricSecondJet}

theorem metricMatrix_inverse_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t) (hdet : (G t).det ≠ 0)
    (i j : Fin 2) : ContDiffAt ℝ ∞ (fun s => (G s)⁻¹ i j) t := by
  have hdetc : ContDiffAt ℝ ∞ (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hi := hdetc.inv hdet
  have ha : ContDiffAt ℝ ∞ (fun s => (G s).adjugate i j) t := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · convert (hG 0 1).neg using 1
      funext s
      simp [Matrix.adjugate_fin_two]
    · convert (hG 1 0).neg using 1
      funext s
      simp [Matrix.adjugate_fin_two]
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  have hh : ContDiffAt ℝ ∞ (fun s => (G s).det⁻¹ * (G s).adjugate i j) t := hi.mul ha
  simpa [Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hh

theorem inverseDerivativeJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (d i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => inverseDerivativeJet (G s) (D s) d i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have ht (a b : Fin 2) :
      ContDiffAt ℝ ∞ (fun s => (G s)⁻¹ i a * D s d a b * (G s)⁻¹ b j) t :=
    ((hi i a).mul (hD d a b)).mul (hi b j)
  simpa only [inverseDerivativeJet, Fin.sum_univ_two] using
    (((ht 0 0).add (ht 0 1)).add ((ht 1 0).add (ht 1 1))).neg

theorem christoffelJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => christoffelJet (G s) (D s) k i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have ht (l : Fin 2) : ContDiffAt ℝ ∞
      (fun s => (G s)⁻¹ k l * (D s i j l + D s j i l - D s l i j)) t :=
    (hi k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [christoffelJet, Fin.sum_univ_two] using
    (contDiffAt_const (c := (1 / 2 : ℝ))).mul ((ht 0).add (ht 1))

theorem christoffelDerivativeJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (d k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => christoffelDerivativeJet (G s) (D s) (DD s) d k i j) t := by
  have hi := metricMatrix_inverse_contDiffAt hG hdet
  have hdi := inverseDerivativeJet_contDiffAt hG hD hdet
  have ht (l : Fin 2) : ContDiffAt ℝ ∞ (fun s =>
      inverseDerivativeJet (G s) (D s) d k l * (D s i j l + D s j i l - D s l i j) +
        (G s)⁻¹ k l * (DD s d i j l + DD s d j i l - DD s d l i j)) t :=
    ((hdi d k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))).add
      ((hi k l).mul (((hDD d i j l).add (hDD d j i l)).sub (hDD d l i j)))
  simpa only [christoffelDerivativeJet, Fin.sum_univ_two] using
    (contDiffAt_const (c := (1 / 2 : ℝ))).mul ((ht 0).add (ht 1))

theorem riemannJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (l k i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun s => riemannJet (G s) (D s) (DD s) l k i j) t := by
  have hΓ := christoffelJet_contDiffAt hG hD hdet
  have hDΓ := christoffelDerivativeJet_contDiffAt hG hD hDD hdet
  have ht (m : Fin 2) : ContDiffAt ℝ ∞ (fun s =>
      christoffelJet (G s) (D s) m j k * christoffelJet (G s) (D s) l i m -
        christoffelJet (G s) (D s) m i k * christoffelJet (G s) (D s) l j m) t :=
    ((hΓ m j k).mul (hΓ l i m)).sub ((hΓ m i k).mul (hΓ l j m))
  simpa only [riemannJet, Fin.sum_univ_two] using
    ((hDΓ i l j k).sub (hDΓ j l i k)).add ((ht 0).add (ht 1))

theorem curvatureJet_contDiffAt
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hD : ∀ d i j, ContDiffAt ℝ ∞ (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContDiffAt ℝ ∞ (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun s => curvatureJet (G s) (D s) (DD s)) t := by
  have hR := riemannJet_contDiffAt hG hD hDD hdet
  have hn : ContDiffAt ℝ ∞ (fun s => ∑ l, G s 0 l * riemannJet (G s) (D s) (DD s) l 1 0 1) t := by
    simpa only [Fin.sum_univ_two] using
      ((hG 0 0).mul (hR 0 1 0 1)).add ((hG 0 1).mul (hR 1 1 0 1))
  have hd : ContDiffAt ℝ ∞ (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  exact hn.div hd hdet

end Smoothness
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

theorem coordinateBound_five_of_frechet_eight {f : Coord → ℝ} {U S : Set Coord} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U)
    (hB : ∀ k ≤ 8, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M) :
    CoordinateBound f S 5 M :=
  (coordinateBound_of_frechet_bounds hf hU hSU hB).mono (by norm_num) le_rfl

end SmoothLocal.Geometry

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

theorem verticalJet_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ n, ContDiffOn ℝ ∞ (verticalJet f n) U := by
  intro n
  induction n with
  | zero => exact hf
  | succ n hn => exact normed_coordPartial_contDiffOn hn hU 1

end SmoothLocal.HighEquation

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
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

abbrev MetricPInput := MetricMatrix × (MetricFirstJet × (MetricSecondJet × DarbouxState))

def universalConnection (a : MetricPInput) (i j : Fin 2) : ℝ :=
  ∑ k, christoffelJet a.1 a.2.1 k i j * stateGradient a.2.2.2 k

def universalDenominator (a : MetricPInput) : ℝ :=
  a.2.2.2 5 - universalConnection a 1 1

def universalEnergy (a : MetricPInput) : ℝ :=
  a.1.det - (a.1 1 1 * (stateGradient a.2.2.2 0)^2 -
    (a.1 0 1 + a.1 1 0) * stateGradient a.2.2.2 0 * stateGradient a.2.2.2 1 +
    a.1 0 0 * (stateGradient a.2.2.2 1)^2)

def universalMetricP (a : MetricPInput) : ℝ :=
  universalConnection a 0 0 +
    ((a.2.2.2 4 - universalConnection a 0 1)^2 +
      curvatureJet a.1 a.2.1 a.2.2.1 * universalEnergy a) / universalDenominator a

def universalMetricBase : Set MetricPInput := {a | a.1.det ≠ 0}
def universalMetricDomain : Set MetricPInput :=
  {a | a.1.det ≠ 0 ∧ universalDenominator a ≠ 0}

def metricPBundle (g : MetricField) (w : DarbouxState) : MetricPInput :=
  (g (statePoint w),
    ((fun d i j => coordPartial d (fun p => g p i j) (statePoint w)),
      ((fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w)), w)))

theorem universalConnection_metricPBundle (g : MetricField) (w : DarbouxState)
    (i j : Fin 2) :
    universalConnection (metricPBundle g w) i j = stateConnection g i j w := rfl

theorem universalDenominator_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalDenominator (metricPBundle g w) = stateDenominator g w := rfl

theorem universalEnergy_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalEnergy (metricPBundle g w) = stateEnergy g w := rfl

theorem sixVariableP_eq_universalMetricP {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableP g w = universalMetricP (metricPBundle g w) := by
  have hK := gaussianCurvature_eq_curvatureJet hg hU hw
  unfold sixVariableP solvedDarboux jetNumerator jetMixed jetYY
  unfold universalMetricP
  rw [universalConnection_metricPBundle, universalConnection_metricPBundle,
    universalDenominator_metricPBundle, universalEnergy_metricPBundle]
  simp only [stateConnection, stateDenominator, stateEnergy, jetYY, metricPBundle, hK]

theorem universalMetricDet_contDiff :
    ContDiff ℝ ∞ (fun a : MetricPInput => a.1.det) := by
  simp only [Matrix.det_fin_two]
  fun_prop

theorem universalMetricBase_isOpen : IsOpen universalMetricBase :=
  isOpen_ne_fun universalMetricDet_contDiff.continuous continuous_const

theorem universalConnection_contDiffAt {a : MetricPInput}
    (ha : a ∈ universalMetricBase) (i j : Fin 2) :
    ContDiffAt ℝ ∞ (fun b => universalConnection b i j) a := by
  have hΓ (k : Fin 2) :
      ContDiffAt ℝ ∞ (fun b : MetricPInput => christoffelJet b.1 b.2.1 k i j) a :=
    christoffelJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) ha k i j
  have hv (k : Fin 2) :
      ContDiffAt ℝ ∞ (fun b : MetricPInput => stateGradient b.2.2.2 k) a :=
    ((contDiff_apply ℝ ℝ k).comp
      (stateGradient_contDiff.comp (by fun_prop))).contDiffAt
  simp only [universalConnection, Fin.sum_univ_two]
  exact ((hΓ 0).mul (hv 0)).add ((hΓ 1).mul (hv 1))

theorem universalDenominator_contDiffOn :
    ContDiffOn ℝ ∞ universalDenominator universalMetricBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 5) a by fun_prop).sub
    (universalConnection_contDiffAt ha 1 1)).contDiffWithinAt

theorem universalMetricDomain_isOpen : IsOpen universalMetricDomain := by
  exact universalDenominator_contDiffOn.continuousOn.isOpen_inter_preimage
    universalMetricBase_isOpen isClosed_singleton.isOpen_compl

theorem universalEnergy_contDiff : ContDiff ℝ ∞ universalEnergy := by
  unfold universalEnergy stateGradient
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Matrix.det_fin_two]
  fun_prop

theorem universalMetricP_contDiffOn :
    ContDiffOn ℝ ∞ universalMetricP universalMetricDomain := by
  intro a ha
  have hΓ := universalConnection_contDiffAt ha.1
  have hK : ContDiffAt ℝ ∞
      (fun b : MetricPInput => curvatureJet b.1 b.2.1 b.2.2.1) a :=
    curvatureJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha.1
  have hm : ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 0 0).add (((hm.pow 2).add (hK.mul universalEnergy_contDiff.contDiffAt)).div
    (universalDenominator_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha.1))
    ha.2)).contDiffWithinAt

def universalMetricBaseTube (M d : ℝ) : Set MetricPInput :=
  Metric.closedBall 0 M ∩ (fun a : MetricPInput => |a.1.det|) ⁻¹' Ici d

def universalMetricTube (M d c : ℝ) : Set MetricPInput :=
  universalMetricBaseTube M d ∩ universalDenominator ⁻¹' {x : ℝ | c ≤ |x|}

theorem universalMetricBaseTube_isCompact (M d : ℝ) :
    IsCompact (universalMetricBaseTube M d) :=
  (isCompact_closedBall (0 : MetricPInput) M).inter_right
    (isClosed_Ici.preimage universalMetricDet_contDiff.continuous.abs)

theorem universalMetricBaseTube_subset_base (M : ℝ) {d : ℝ} (hd : 0 < d) :
    universalMetricBaseTube M d ⊆ universalMetricBase := by
  intro a ha hz
  have hh : d ≤ |a.1.det| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (universalMetricTube M d c) := by
  have hbase := universalMetricBaseTube_isCompact M d
  have hc : ContinuousOn universalDenominator (universalMetricBaseTube M d) :=
    universalDenominator_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd)
  have hclosed : IsClosed (universalMetricTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem universalMetricTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    universalMetricTube M d c ⊆ universalMetricDomain := by
  intro a ha
  refine ⟨universalMetricBaseTube_subset_base M hd ha.1, ?_⟩
  intro hz
  have hh : c ≤ |universalDenominator a| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricTube_finite_P_bounds (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ N, ∀ a ∈ universalMetricTube M d c,
      ‖iteratedFDeriv ℝ k universalMetricP a‖ ≤ C := by
  classical
  have hk : ∀ k : Fin (N + 1), ∃ A : ℝ,
      ∀ a ∈ universalMetricTube M d c, ‖iteratedFDeriv ℝ k.val universalMetricP a‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val universalMetricP) universalMetricDomain := by
      apply (universalMetricP_contDiffOn.continuousOn_iteratedFDerivWithin
        (WithTop.coe_le_coe.mpr le_top) universalMetricDomain_isOpen.uniqueDiffOn).congr
      intro a ha
      exact (iteratedFDerivWithin_eq_iteratedFDeriv universalMetricDomain_isOpen.uniqueDiffOn
        ((universalMetricP_contDiffOn.contDiffAt
          (universalMetricDomain_isOpen.mem_nhds ha)).of_le (WithTop.coe_le_coe.mpr le_top)) ha).symm
    exact (universalMetricTube_isCompact M hd c).exists_bound_of_continuousOn
      (hcont.mono (universalMetricTube_subset_domain M hd hc))
  choose A hA using hk
  refine ⟨∑ k : Fin (N + 1), |A k|, Finset.sum_nonneg (fun k hk => abs_nonneg _), ?_⟩
  intro k hk a ha
  let j : Fin (N + 1) := ⟨k, by omega⟩
  exact (hA j a ha).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun i hi => abs_nonneg (A i)) (Finset.mem_univ j)))

end SmoothLocal.HighEquation

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
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

section FiniteProducts
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_pi_le {ι : Type*} [Fintype ι]
    {f : E → ι → F} {p : E} (hf : ContDiffAt ℝ ∞ f p)
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i, ‖iteratedFDeriv ℝ n (fun x => f x i) p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n f p‖ ≤ M := by
  have heq : iteratedFDeriv ℝ n f p =
      ContinuousMultilinearMap.pi (fun i => iteratedFDeriv ℝ n (fun x => f x i) p) := by
    ext v i
    have hh := congrArg (fun L => L v)
      ((ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).iteratedFDeriv_comp_left
        hf (WithTop.coe_le_coe.mpr le_top) (i := n))
    exact hh.symm
  rw [heq, ContinuousMultilinearMap.opNorm_pi]
  exact (pi_norm_le_iff_of_nonneg hM).mpr hb

theorem norm_iteratedFDeriv_prod_le {f : E → F} {g : E → G} {p : E}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (n : ℕ) {M : ℝ}
    (hfB : ‖iteratedFDeriv ℝ n f p‖ ≤ M)
    (hgB : ‖iteratedFDeriv ℝ n g p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun x => (f x, g x)) p‖ ≤ M := by
  rw [iteratedFDeriv_prodMk hf hg (WithTop.coe_le_coe.mpr le_top),
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le hfB hgB

theorem norm_iteratedFDeriv_comp_contraction
    (L : E →L[ℝ] F) {f : F → G} {U : Set F}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hL : ‖L‖ ≤ 1)
    {p : E} (hp : L p ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ := by
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  rw [← iteratedFDerivWithin_of_isOpen n hpre hp,
    L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hp
      (WithTop.coe_le_coe.mpr le_top),
    iteratedFDerivWithin_of_isOpen n hU hp]
  exact ((iteratedFDeriv ℝ n f (L p)).norm_compContinuousLinearMap_le
    (fun _ => L)).trans (by
      calc
        _ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ * ∏ _ : Fin n, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg L)
            (fun _ _ => hL)) (norm_nonneg _)
        _ = _ := by simp)

theorem norm_iteratedFDeriv_id_pos (p : E) {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun x : E => x) p‖ ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun x : E => x) = (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext x
      exact fderiv_fun_id
    rw [he]
    cases n with
    | zero => simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    | succ n => simp only [iteratedFDeriv_succ_const]; norm_num
end FiniteProducts

theorem norm_iteratedFDeriv_coordPartial_le {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (i : Fin 2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (coordPartial i f) p‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f p‖ := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) p :=
    (hf.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hp)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := Pi.single i (1 : ℝ))
    hd (n := n) (WithTop.coe_le_coe.mpr le_top)
  have he : (fun y : Coord => fderiv ℝ f y (Pi.single i (1 : ℝ))) = coordPartial i f := by
    funext y
    rfl
  rw [he, Pi.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] at hh
  exact hh

def statePointCLM : DarbouxState →L[ℝ] Coord :=
  ContinuousLinearMap.pi (fun i =>
    if i = 0 then ContinuousLinearMap.proj 0 else ContinuousLinearMap.proj 1)

theorem statePointCLM_eq (w : DarbouxState) : statePointCLM w = statePoint w := by
  ext i
  fin_cases i <;> simp [statePointCLM, statePoint]

theorem statePointCLM_norm_le : ‖statePointCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  rw [one_mul, statePointCLM_eq]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm w 0
  · exact norm_le_pi_norm w 1

theorem norm_iteratedFDeriv_comp_statePoint {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v => f (statePoint v)) w‖ ≤
      ‖iteratedFDeriv ℝ n f (statePoint w)‖ := by
  have hp : statePointCLM w ∈ U := by
    rw [statePointCLM_eq]
    exact hw
  have hnumerical : ‖iteratedFDeriv ℝ n (f ∘ statePointCLM) w‖ ≤
      ‖iteratedFDeriv ℝ n f (statePointCLM w)‖ :=
    norm_iteratedFDeriv_comp_contraction statePointCLM hf hU statePointCLM_norm_le hp n
  have he : (fun v => f (statePoint v)) = f ∘ statePointCLM := by
    funext v
    change f (statePoint v) = f (statePointCLM v)
    rw [statePointCLM_eq]
  rw [he, ← statePointCLM_eq w]
  exact hnumerical

theorem metricPBundle_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (metricPBundle g) (stateBaseDomain U) := by
  have h0 : ContDiffOn ℝ ∞ (fun w => g (statePoint w)) (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (hg.1 i j).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have h1 : ContDiffOn ℝ ∞
      (fun w d i j => coordPartial d (fun p => g p i j) (statePoint w)) (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro d
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (partial_contDiffOn (hg.1 i j) hU d).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have h2 : ContDiffOn ℝ ∞
      (fun w d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))
      (stateBaseDomain U) := by
    apply contDiffOn_pi.mpr
    intro d
    apply contDiffOn_pi.mpr
    intro e
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d).comp
      statePoint_contDiff.contDiffOn (fun w hw => hw)
  exact h0.prodMk (h1.prodMk (h2.prodMk contDiffOn_id))

theorem metricPBundle_positive_jet_bound {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {N : ℕ} {G : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (metricPBundle g) w‖ ≤ max 1 G := by
  have hB := (metricPBundle_contDiffOn hg hU).contDiffAt
    ((stateBaseDomain_isOpen hU).mem_nhds hw)
  have h0 := hB.fst
  have h1 := hB.snd.fst
  have h2 := hB.snd.snd.fst
  have hId := hB.snd.snd.snd
  have hcon {f : Coord → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
      ‖iteratedFDeriv ℝ n (fun v => f (statePoint v)) w‖ ≤
        ‖iteratedFDeriv ℝ n f (statePoint w)‖ := by
    exact norm_iteratedFDeriv_comp_statePoint hf hU hw n
  have hb0 : ‖iteratedFDeriv ℝ n (fun v => g (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h0 n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h0) i) n hG
    intro j
    exact (hcon (hg.1 i j)).trans (hgB i j n (by omega))
  have hb1 : ‖iteratedFDeriv ℝ n
      (fun v d i j => coordPartial d (fun p => g p i j) (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h1 n hG
    intro d
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h1) d) n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp ((contDiffAt_pi.mp h1) d)) i) n hG
    intro j
    exact ((hcon (partial_contDiffOn (hg.1 i j) hU d)).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw d n)).trans
        (hgB i j (n + 1) (by omega))
  have hb2 : ‖iteratedFDeriv ℝ n
      (fun v d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint v)) w‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h2 n hG
    intro d
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h2) d) n hG
    intro e
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp ((contDiffAt_pi.mp h2) d)) e) n hG
    intro i
    apply norm_iteratedFDeriv_pi_le
      ((contDiffAt_pi.mp ((contDiffAt_pi.mp ((contDiffAt_pi.mp h2) d)) e)) i) n hG
    intro j
    exact (((hcon (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d)).trans
      (norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn (hg.1 i j) hU e) hU hw d n)).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw e (n + 1))).trans
        (hgB i j (n + 1 + 1) (by omega))
  exact norm_iteratedFDeriv_prod_le h0 hB.snd n (hb0.trans (le_max_right _ _))
    (norm_iteratedFDeriv_prod_le h1 hB.snd.snd n (hb1.trans (le_max_right _ _))
      (norm_iteratedFDeriv_prod_le h2 hId n (hb2.trans (le_max_right _ _))
        ((norm_iteratedFDeriv_id_pos w hn).trans (le_max_left _ _))))

end SmoothLocal.HighEquation

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

theorem CoordinateBound.restrict_domain {f : Coord → ℝ} {S T : Set Coord} {n : ℕ} {M : ℝ}
    (hf : CoordinateBound f S n M) (hTS : T ⊆ S) : CoordinateBound f T n M :=
  fun ds hds p hp => hf ds hds p (hTS hp)

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

end SmoothLocal.Geometry

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

theorem modelOpenSquare_isOpen : IsOpen modelOpenSquare := coordinateRectangle_isOpen _ _ _

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
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem heightStateFactor_contDiffOn (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (n : ℕ) (j : Fin 4) : ContDiffOn ℝ ∞ (heightStateFactor z n j) U := by
  have hv := verticalJet_contDiffOn hU hz n
  fin_cases j
  · exact partial_contDiffOn hv hU 0
  · exact partial_contDiffOn hv hU 1
  · exact partial_contDiffOn (partial_contDiffOn hv hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hv hU 1) hU 1

end SmoothLocal.HighEquation

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

theorem orderedPartial_append
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ds es : List (Fin 2)) (f : Coord → E) :
    iteratedCoordPartial (ds ++ es) f = iteratedCoordPartial ds (iteratedCoordPartial es f) := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [List.cons_append, iteratedCoordPartial, ih]

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
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem chainProductL2Budget_lt_top (B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) : chainProductL2Budget B H V ell < (⊤ : ℝ≥0∞) := by
  unfold chainProductL2Budget
  exact ENNReal.mul_lt_top (by finiteness)
    (ENNReal.add_lt_top.mpr ⟨by finiteness,
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hVfinite.ne⟩)

theorem chainWordL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) (w : ChainWord) :
    chainWordL2Budget C B H V ell w < (⊤ : ℝ≥0∞) := by
  unfold chainWordL2Budget
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.mul_lt_top (by finiteness)
    (chainProductL2Budget_lt_top B H hVfinite ell))

theorem chainSumL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (ell : ℕ) (ws : List ChainWord) :
    chainSumL2Budget C B H V ell ws < (⊤ : ℝ≥0∞) := by
  induction ws with
  | nil => simp [chainSumL2Budget]
  | cons w ws ih =>
      exact ENNReal.add_lt_top.mpr ⟨chainWordL2Budget_lt_top C B H hVfinite ell w, ih⟩

theorem actualHighRemainderL2Budget_lt_top (C Cfirst B : ℝ) (H : ℝ≥0)
    {V : Set Coord} (hVfinite : volume V < (⊤ : ℝ≥0∞)) (m : ℕ) :
    actualHighRemainderL2Budget C Cfirst B H V m < (⊤ : ℝ≥0∞) := by
  unfold actualHighRemainderL2Budget firstJetPairL2Budget
  exact ENNReal.add_lt_top.mpr
    ⟨chainSumL2Budget_lt_top C B H hVfinite (m + 3) (topResidualWords m), by finiteness⟩

theorem bounded_real_eLpNorm_two {V : Set Coord} (hV : MeasurableSet V)
    {f : Coord → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ p ∈ V, ‖f p‖ ≤ B) :
    eLpNorm' f (2 : ℝ) (volume.restrict V) ≤ ‖B‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
  have hdom : ∀ᵐ p ∂(volume.restrict V), ‖f p‖ ≤ ‖B‖ := by
    filter_upwards [ae_restrict_mem hV] with p hp
    simpa only [Real.norm_of_nonneg hB] using hf p hp
  calc
    _ ≤ eLpNorm' (fun _ : Coord => B) (2 : ℝ) (volume.restrict V) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := by
      rw [eLpNorm'_const B (by norm_num), Measure.restrict_apply_univ]

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

end SmoothLocal.HighEquation

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

def heightStateSuffix : Fin 4 → List (Fin 2) := ![[0], [1], [0, 1], [1, 1]]

theorem heightStateSuffix_length (i : Fin 4) :
    (heightStateSuffix i).length = heightStateBaseOrder i := by
  fin_cases i <;> rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem metricPBundle_norm_bound {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) : ‖metricPBundle g w‖ ≤ max G W := by
  have hb0 (i j : Fin 2) : |g (statePoint w) i j| ≤ G := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hgB i j 0 (by omega)
  have hb1 (d i j : Fin 2) : |coordPartial d (fun p => g p i j) (statePoint w)| ≤ G := by
    have hh := (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw d 0).trans
      (hgB i j 1 (by omega))
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh
  have hb2 (d e i j : Fin 2) :
      |coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w)| ≤ G := by
    have hh := ((norm_iteratedFDeriv_coordPartial_le
      (partial_contDiffOn (hg.1 i j) hU e) hU hw d 0).trans
      (norm_iteratedFDeriv_coordPartial_le (hg.1 i j) hU hw e 1)).trans (hgB i j 2 (by omega))
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hh
  have h0 : ‖g (statePoint w)‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb0 i j))
  have h1 : ‖(fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb1 d i j)))
  have h2 : ‖(fun d e i j =>
      coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun e =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
          (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hb2 d e i j))))
  change max ‖g (statePoint w)‖
    (max ‖(fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖
      (max ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖
        ‖w‖)) ≤ max G W
  exact max_le (h0.trans (le_max_left _ _))
    (max_le (h1.trans (le_max_left _ _))
      (max_le (h2.trans (le_max_left _ _)) (hwB.trans (le_max_right _ _))))

theorem metricPBundle_mapsTo_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    MapsTo (metricPBundle g) (darbouxStateDomain g U) universalMetricDomain := by
  intro w hw
  exact ⟨metricDet_ne_zero hg hw.1,
    by simpa only [universalDenominator_metricPBundle] using hw.2⟩

theorem metricPBundle_mem_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d c : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateDenominator g w|) :
    metricPBundle g w ∈ universalMetricTube (max G W) d c := by
  refine ⟨⟨?_, hdet⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      metricPBundle_norm_bound hg hU hw hG hgB hwB
  · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, universalDenominator_metricPBundle] using hden

theorem actualP_jet_bound_from_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxStateDomain g U) {N : ℕ} {G W d c C : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateDenominator g w|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricP a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (sixVariableP g) w‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := darbouxStateDomain_isOpen hg hU
  have hsub : darbouxStateDomain g U ⊆ stateBaseDomain U := fun _ hv => hv.1
  have hf := (metricPBundle_contDiffOn hg hU).mono hsub
  have hmap := metricPBundle_mapsTo_domain hg
  have hmem := metricPBundle_mem_universalTube hg hU hw.1 hG
    (fun i j k hk => hgB i j k (by omega)) hwB hdet hden
  have hdomain := universalMetricTube_subset_domain (max G W) hd hc hmem
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricP universalMetricDomain (metricPBundle g w)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricDomain_isOpen hdomain]
    exact hC i (hi.trans hn) (metricPBundle g w) hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricPBundle g) (darbouxStateDomain g U) w‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hw]
    exact (metricPBundle_positive_jet_bound hg hU hw.1 hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricP_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hw ho hi
  have heq : iteratedFDerivWithin ℝ n (sixVariableP g) (darbouxStateDomain g U) w =
      iteratedFDerivWithin ℝ n (universalMetricP ∘ metricPBundle g) (darbouxStateDomain g U) w :=
    iteratedFDerivWithin_congr (fun _ hv => sixVariableP_eq_universalMetricP hg hU hv.1) hw n
  rw [iteratedFDerivWithin_of_isOpen n hD hw] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_metric_P_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ w : DarbouxState,
      statePoint w ∈ U →
      (∀ i j k, k ≤ N + 2 →
        ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → d ≤ |(g (statePoint w)).det| → c ≤ |stateDenominator g w| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (sixVariableP g) w‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCP⟩ := universalMetricTube_finite_P_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun index _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU w hw hgB hwB hdet hden n hn
  have hne : stateDenominator g w ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hb := actualP_jet_bound_from_universalTube hg hU ⟨hw, hne⟩ hG hd hc hgB hwB hdet hden hCP hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun index _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

theorem exists_same_region_solution_P_jet_bound (G Z : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U → S ⊆ modelSquare →
      (∀ i j k, k ≤ N + 2 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 1 1|) →
      ∀ n ≤ N, ∀ p ∈ S, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C := by
  obtain ⟨C, hC, hP⟩ := exists_local_metric_P_jet_bound G (max 3 Z) hG hd hc N
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hSS hgB hzB hdet hden n hn p hp
  have hwB : ‖solutionJet z p‖ ≤ max 3 Z := by
    apply (pi_norm_le_iff_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 3) (le_max_left _ _))).mpr
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · exact (abs_le.mpr ⟨(hSS hp).1 0, (hSS hp).2 0⟩).trans (le_max_left 3 Z)
    · exact (abs_le.mpr ⟨(hSS hp).1 1, (hSS hp).2 1⟩).trans (le_max_left 3 Z)
    · exact (hzB [0] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [1] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right 3 Z)
    · exact (hzB [1, 1] (by norm_num) p hp).trans (le_max_right 3 Z)
  exact hP g U hg hU (solutionJet z p)
    (by simpa only [statePoint_solutionJet] using hSU hp)
    (fun i j k hk => by simpa only [statePoint_solutionJet] using hgB i j k hk p hp)
    hwB (by simpa only [statePoint_solutionJet] using hdet p hp)
    (by simpa only [stateDenominator_solutionJet] using hden p hp) n hn

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem orderedPartial_replicate_y (z : Coord → ℝ) (n : ℕ) :
    iteratedCoordPartial (List.replicate n 1) z = verticalJet z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, iteratedCoordPartial, verticalJet, ih]

end SmoothLocal.HighEquation

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

theorem eLpNorm_two_le_of_integral_sq_le {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) {H : ℝ≥0} (hH : (∫ p, f p ^ 2 ∂μ) ≤ (H : ℝ)^2) :
    eLpNorm f 2 μ ≤ (H : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top (by simp)).mp
  rw [integral_sq_eq_eLpNorm_toReal_sq hf] at hH
  change (eLpNorm f 2 μ).toReal ≤ (H : ℝ)
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).mp hH

end SmoothLocal.Analytic

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem CoordinateL2Bound.restrict {z : Coord → ℝ} {V W : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hWV : W ⊆ V) : CoordinateL2Bound z W N H := by
  intro ds hds
  exact (eLpNorm'_mono_measure _ (Measure.restrict_mono_set volume hWV)
    (by norm_num)).trans (h ds hds)

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

theorem heightStateFactor_eq_ordered (z : Coord → ℝ) (n : ℕ) (j : Fin 4) :
    heightStateFactor z n j =
      iteratedCoordPartial (heightStateSuffix j ++ List.replicate n 1) z := by
  rw [orderedPartial_append, orderedPartial_replicate_y]
  fin_cases j <;> rfl

theorem CoordinateL2Bound.heightFactors {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (n : ℕ) (j : Fin 4)
    (hn : n + heightStateBaseOrder j ≤ N) :
    eLpNorm' (heightStateFactor z n j) (2 : ℝ) (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [heightStateFactor_eq_ordered]
  apply h
  simpa only [List.length_append, List.length_replicate, heightStateSuffix_length, Nat.add_comm] using hn

theorem CoordinateL2Bound.heightFactors_of_aestronglyMeasurable
    {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (hbound : CoordinateL2Bound z V N H) (order : ℕ) (component : Fin 4)
    (horder : order + heightStateBaseOrder component ≤ N)
    (hmeas : AEStronglyMeasurable (heightStateFactor z order component) (volume.restrict V)) :
    eLpNorm (heightStateFactor z order component) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact hbound.heightFactors order component horder

theorem coordinateBound_heightFactors {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {B : ℝ}
    (h : CoordinateBound z V N B) (n : ℕ) (j : Fin 4)
    (hn : n + heightStateBaseOrder j ≤ N) :
    ∀ p ∈ V, |heightStateFactor z n j p| ≤ B := by
  rw [heightStateFactor_eq_ordered]
  apply h
  simpa only [List.length_append, List.length_replicate, heightStateSuffix_length, Nat.add_comm] using hn

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
open Set MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Analytic

theorem chainProductL2Budget_mono_area (B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) :
    chainProductL2Budget B H V ell ≤ chainProductL2Budget B H W ell :=
  mul_le_mul' le_rfl (add_le_add le_rfl
    (ENNReal.rpow_le_rpow hVW (by norm_num : 0 ≤ (1 / (2 : ℝ)))))

theorem chainWordL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) (w : ChainWord) :
    chainWordL2Budget C B H V ell w ≤ chainWordL2Budget C B H W ell w := by
  apply Finset.sum_le_sum
  intro _ _
  exact mul_le_mul' le_rfl (chainProductL2Budget_mono_area B H hVW ell)

theorem chainSumL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (ell : ℕ) (ws : List ChainWord) :
    chainSumL2Budget C B H V ell ws ≤ chainSumL2Budget C B H W ell ws := by
  induction ws with
  | nil => exact le_rfl
  | cons word _ ih => exact add_le_add (chainWordL2Budget_mono_area C B H hVW ell word) ih

theorem actualHighRemainderL2Budget_mono_area (C Cfirst B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (m : ℕ) :
    actualHighRemainderL2Budget C Cfirst B H V m ≤ actualHighRemainderL2Budget C Cfirst B H W m :=
  add_le_add (chainSumL2Budget_mono_area C B H hVW (m+3) (topResidualWords m)) le_rfl

end SmoothLocal.HighEquation

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

theorem region_subset_energyOuter (r : LowerCapRectangle bStar) : r.region ⊆ r.energyOuter.region := by
  obtain ⟨_,_,_,_,_,_,_,hB0,hB1,hL,hR⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
  intro p hp
  exact ⟨⟨by change capOuterLeft r.left ≤ p 0; linarith [hp.1.1],
    by change p 0 ≤ capOuterRight r.right; linarith [hp.1.2]⟩,
    ⟨by change capOuterBottom r.bottom ≤ p 1; linarith [hp.2.1],
      by change p 1 ≤ (r.top+bStar)/2; linarith [hp.2.2,r.top_lt]⟩⟩

theorem region_subset_expand (r : LowerCapRectangle bStar) : r.region ⊆ r.expand.region := by
  intro p hp
  exact ⟨⟨by change r.left-r.margin ≤ p 0; linarith [hp.1.1,r.margin_pos],
    by change p 0 ≤ r.right+r.margin; linarith [hp.1.2,r.margin_pos]⟩,
    ⟨by change r.bottom-r.margin ≤ p 1; linarith [hp.2.1,r.margin_pos],
      by change p 1 ≤ r.top+r.margin; linarith [hp.2.2,r.margin_pos]⟩⟩

theorem expand_shrink_region (r : LowerCapRectangle bStar) :
    closedRectangle (r.expand.left+r.margin) (r.expand.right-r.margin)
      (r.expand.bottom+r.margin) (r.expand.top-r.margin) = r.region := by
  dsimp only [expand, region]
  congr 1 <;> ring

theorem image_subset_energyOuter (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) :
    r.image Y ⊆ r.energyOuter.image Y := Set.image_mono r.region_subset_energyOuter

theorem image_subset_expand (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) :
    r.image Y ⊆ r.expand.image Y := Set.image_mono r.region_subset_expand

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
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem heightPhysicalCapConstant_pos (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : 0 < heightPhysicalCapConstant G Z d c e0 kappa ell L R bottom top b := by
  unfold heightPhysicalCapConstant
  positivity

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

theorem lowerCapConstant_pos (G Z d c e0 kappa : ℝ) (ell : ℕ) (r : LowerCapRectangle bStar) :
    0 < lowerCapConstant G Z d c e0 kappa ell r :=
  heightPhysicalCapConstant_pos G Z d c e0 kappa ell r.left r.right r.bottom r.top ((r.top+bStar)/2)

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

def originalC8L2Budget (Z : ℝ) : ℝ≥0 :=
  (‖Z‖ₑ * (volume modelSquare) ^ (1/(2 : ℝ))).toNNReal

theorem originalC8L2Budget_coe (Z : ℝ) :
    (originalC8L2Budget Z : ℝ≥0∞) = ‖Z‖ₑ * (volume modelSquare) ^ (1/(2 : ℝ)) := by
  apply ENNReal.coe_toNNReal
  exact (ENNReal.mul_lt_top (by finiteness)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) modelSquare_isCompact.measure_lt_top.ne)).ne

theorem CapInductionHeight.original_L2
    {g : MetricField} {U : Set Coord} {Z c e0 : ℝ} {z : Coord → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hZ : 0 ≤ Z) {V : Set Coord} (hV : MeasurableSet V) (hVS : V ⊆ modelSquare) :
    CoordinateL2Bound z V 8 (originalC8L2Budget Z) := by
  have hC := coordinateBound_of_frechet_bounds hh.smooth hU hSU hh.lowJet
  intro ds hds
  rw [originalC8L2Budget_coe]
  exact (bounded_real_eLpNorm_two hV hZ (fun p hp => by
    rw [Real.norm_eq_abs]
    exact hC ds hds p (hVS hp))).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (z := 1/(2 : ℝ)) (measure_mono hVS) (by norm_num)))

theorem compact_continuous_memLp_two {f : Coord → ℝ} {V : Set Coord}
    (hV : IsCompact V) (hf : ContinuousOn f V) : MemLp f 2 (volume.restrict V) :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable hV.isClosed.measurableSet)).mpr
    ((hf.pow 2).integrableOn_compact hV)

theorem integral_each_sq_le_sum {f h : Coord → ℝ} {V : Set Coord}
    (hV : IsCompact V) (hf : ContinuousOn f V) (hh : ContinuousOn h V) :
    (∫ p in V, (f p)^2) ≤ ∫ p in V, (f p)^2+(h p)^2 ∧
      (∫ p in V, (h p)^2) ≤ ∫ p in V, (f p)^2+(h p)^2 := by
  have hfI : IntegrableOn (fun p => (f p)^2) V volume := (hf.pow 2).integrableOn_compact hV
  have hhI : IntegrableOn (fun p => (h p)^2) V volume := (hh.pow 2).integrableOn_compact hV
  exact ⟨setIntegral_mono_on hfI (hfI.add hhI) hV.isClosed.measurableSet
      (fun p hp => le_add_of_nonneg_right (sq_nonneg _)),
    setIntegral_mono_on hhI (hfI.add hhI) hV.isClosed.measurableSet
      (fun p hp => le_add_of_nonneg_left (sq_nonneg _))⟩

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

theorem uniform_finite_varying_lowerCap_L2
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    {bStar : ℝ} (J : CapMetricJetBudget bStar) :
    ∀ k : ℕ, ∀ r : LowerCapRectangle bStar,
      (∀ b ∈ lowerCapMetricRequests k r, 0 ≤ J b.1 b.2) → ∃ H : ℝ≥0,
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        FiniteCapMetricJets g Y J (lowerCapMetricRequests k r) → CoordinateL2Bound z (r.image Y) (k+8) H := by
  intro k
  induction k with
  | zero =>
    intro r hJ
    refine ⟨originalC8L2Budget Z, ?_⟩
    intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
    exact hh.original_L2 hU hSU hZ (hf.image_properties r).2.1 (hf.image_subset_square r)
  | succ k ih =>
    intro r hJ
    let T := r.energyOuter
    have hsourceRequest : (k+8,T) ∈ lowerCapMetricRequests (k+1) r := by
      simp [lowerCapMetricRequests,T]
    have hmixedRequest : (k+7,r) ∈ lowerCapMetricRequests (k+1) r := by
      simp [lowerCapMetricRequests]
    have htail : ∀ b, b ∈ lowerCapMetricRequests k T.expand →
        b ∈ lowerCapMetricRequests (k+1) r := by
      intro b hb
      change b ∈ (k+8,T)::(k+7,r)::lowerCapMetricRequests k T.expand
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb)
    obtain ⟨H, hH⟩ := ih T.expand (fun b hb => hJ b (htail b hb))
    obtain ⟨CR, hCR0, hCR⟩ := exists_localized_actualHighRemainder_bound
      G Z (J (k+8) T) hG hZ (hJ (k+8,T) hsourceRequest) hd hc (k+5) (by omega)
    obtain ⟨CP, hCP0, hCP⟩ := exists_same_region_solution_P_jet_bound
      (J (k+7) r) Z (hJ (k+7,r) hmixedRequest) hd hc (k+7)
    let M := heightQuotientJetBound G Z d c
    let B := max 1 ((squareSobolevWeight (flowInteriorRadius M T.margin T.margin)+1)*(H : ℝ))
    have hB : 1 ≤ B := le_max_left _ _
    let Rraw := actualHighRemainderL2Budget CR (heightPFirstBound G Z d c) B H modelSquare (k+5)
    have hRfinite : Rraw < (⊤ : ℝ≥0∞) := actualHighRemainderL2Budget_lt_top CR
      (heightPFirstBound G Z d c) B H modelSquare_isCompact.measure_lt_top (k+5)
    let RB : ℝ≥0 := Rraw.toNNReal
    have hRB : (RB : ℝ≥0∞) = Rraw := ENNReal.coe_toNNReal hRfinite.ne
    let Ccap := lowerCapConstant G Z d c e0 kappa (k+8) r
    have hCcap : 0 < Ccap := lowerCapConstant_pos G Z d c e0 kappa (k+8) r
    let Htop : ℝ≥0 := ⟨Real.sqrt (Ccap*((RB : ℝ)^2+(H : ℝ)^2)), Real.sqrt_nonneg _⟩
    have hTopSq : (Htop : ℝ)^2 = Ccap*((RB : ℝ)^2+(H : ℝ)^2) :=
      Real.sq_sqrt (mul_nonneg hCcap.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    refine ⟨uniformMixedOrderBudget CP B H Htop (k+9), ?_⟩
    intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
    have hlocalTail : FiniteCapMetricJets g Y J (lowerCapMetricRequests k T.expand) :=
      fun b hb => hlocal b (htail b hb)
    have hLarge : CoordinateL2Bound z (T.expand.image Y) (k+8) H := hH g U z Y W hg hU hSU hgB hdet hh hf hlocalTail
    have hT : CoordinateL2Bound z (T.image Y) (k+8) H :=
      hLarge.restrict (T.image_subset_expand Y)
    have hR : CoordinateL2Bound z (r.image Y) (k+8) H :=
      hT.restrict (r.image_subset_energyOuter Y)
    have hlowT0 : CoordinateBound z (T.image Y) (k+6)
        ((squareSobolevWeight (flowInteriorRadius M T.margin T.margin)+1)*(H : ℝ)) := by
      apply CapInductionFlow.pointwise_from_larger_L2 hh hf hG hZ hd hc T
      convert hLarge using 1 <;> try with_reducible_and_instances rfl
    have hlowT : CoordinateBound z (T.image Y) (k+6) B :=
      hlowT0.mono le_rfl (le_max_right _ _)
    obtain ⟨hTcompact, hTmeas, hTfinite, hTO⟩ := hf.image_properties T
    obtain ⟨hRcompact, hRmeas, hRfiniteImage, hRO⟩ := hf.image_properties r
    have hTS : T.image Y ⊆ modelSquare := hTO.trans modelOpenSquare_subset
    have hRS : r.image Y ⊆ modelSquare := hRO.trans modelOpenSquare_subset
    have hTU : T.image Y ⊆ U := hTS.trans hSU
    have hRU : r.image Y ⊆ U := hRS.trans hSU
    have hlowFactors : ∀ n j, n + heightStateBaseOrder j ≤ (k+5)+1 →
        ∀ p ∈ T.image Y, |heightStateFactor z n j p| ≤ B := by
      intro n j hn
      exact coordinateBound_heightFactors hlowT n j (by omega)
    have hL2Factors : ∀ n j, n + heightStateBaseOrder j ≤ (k+5)+3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict (T.image Y)) ≤ (H : ℝ≥0∞) := by
      intro n j hn
      exact hT.heightFactors_of_aestronglyMeasurable n j (by omega)
        (((heightStateFactor_contDiffOn hU hh.smooth n j).continuousOn.mono
          hTU).aestronglyMeasurable hTmeas)
    have hgHighT : ∀ i j n, n ≤ (k+5)+5 → ∀ p ∈ T.image Y,
        ‖iteratedFDeriv ℝ n (fun q => g q i j) p‖ ≤ J (k+8) T := by
      intro i j n hn p hp
      exact hlocal (k+8,T) hsourceRequest i j n (by omega) p hp
    obtain ⟨hsource, _, hsourceMem⟩ := hCR g z U (T.image Y) hg hU hSU hgB hdet
      hh.smooth hh.lowJet hh.denominator hTmeas hTS hTfinite hgHighT B hB H hlowFactors hL2Factors
    have hsourceRB : eLpNorm (actualHighRemainder g z (k+5)) 2
        (volume.restrict (T.image Y)) ≤ (RB : ℝ≥0∞) := by
      rw [hRB]
      exact hsource.trans (actualHighRemainderL2Budget_mono_area CR
        (heightPFirstBound G Z d c) B H (measure_mono hTS) (k+5))
    have hsourceIntegral : (∫ p in T.image Y, (actualHighRemainder g z (k+5) p)^2) ≤ (RB : ℝ)^2 :=
      integral_sq_le_of_eLpNorm_two_le hsourceMem hsourceRB
    have huIntegral : (∫ p in T.image Y, (verticalJet z (k+8) p)^2) ≤ (H : ℝ)^2 := by
      have hu := hT.integral_sq hh.smooth hU hTmeas hTU (List.replicate (k+8) 1) (by simp)
      simpa only [orderedPartial_replicate_y] using hu
    have hcap : (∫ p in r.image Y,
        (coordPartial 0 (verticalJet z (k+8)) p)^2+(verticalJet z (k+9) p)^2) ≤
        Ccap*((∫ p in T.image Y, (actualHighRemainder g z (k+5) p)^2)+
          (∫ p in T.image Y, (verticalJet z (k+8) p)^2)) := by
      simpa only [Nat.add_assoc, show 5+3=8 by omega, show 5+4=9 by omega] using hf.physicalEstimate (k+5) r
    have hgradient : (∫ p in r.image Y,
        (coordPartial 0 (verticalJet z (k+8)) p)^2+(verticalJet z (k+9) p)^2) ≤ (Htop : ℝ)^2 := by
      rw [hTopSq]
      exact hcap.trans (mul_le_mul_of_nonneg_left (add_le_add hsourceIntegral huIntegral) hCcap.le)
    have hxcont : ContinuousOn (coordPartial 0 (verticalJet z (k+8))) (r.image Y) :=
      ((partial_contDiffOn (verticalJet_contDiffOn hU hh.smooth (k+8)) hU 0).continuousOn).mono hRU
    have hycont : ContinuousOn (verticalJet z (k+9)) (r.image Y) :=
      (verticalJet_contDiffOn hU hh.smooth (k+9)).continuousOn.mono hRU
    have hparts := integral_each_sq_le_sum hRcompact hxcont hycont
    have hxTop : eLpNorm (coordPartial 0 (verticalJet z (k+8))) 2
        (volume.restrict (r.image Y)) ≤ (Htop : ℝ≥0∞) :=
      eLpNorm_two_le_of_integral_sq_le (compact_continuous_memLp_two hRcompact hxcont)
        (hparts.1.trans hgradient)
    have hyTop : eLpNorm (verticalJet z (k+9)) 2
        (volume.restrict (r.image Y)) ≤ (Htop : ℝ≥0∞) :=
      eLpNorm_two_le_of_integral_sq_le (compact_continuous_memLp_two hRcompact hycont)
        (hparts.2.trans hgradient)
    have hz2 : CoordinateBound z modelSquare 2 Z :=
      (coordinateBound_five_of_frechet_eight hh.smooth hU hSU hh.lowJet).mono (by norm_num) le_rfl
    have hP : ∀ n ≤ (k+9)-2, ∀ p ∈ r.image Y,
        ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ CP := by
      intro n hn p hp
      exact hCP g z U (r.image Y) hg hU hRU hRS
        (fun i j n hn p hp => hlocal (k+7,r) hmixedRequest i j n hn p hp)
        (hz2.restrict_domain hRS) (fun p hp => hdet p (hRS hp))
        (fun p hp => hh.denominator p (hRS hp)) n (by omega) p hp
    have hlowR : CoordinateBound z (r.image Y) ((k+9)-3) B := by
      intro word hword p hp
      exact hlowT word (by omega) p (r.image_subset_energyOuter Y hp)
    have hPrev : CoordinateL2Bound z (r.image Y) ((k+9)-1) H := by
      convert hR using 1 <;> try with_reducible_and_instances rfl
      omega
    have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
    have hgO : SmoothPositiveOn g modelOpenSquare :=
      ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
    have hDo : ∀ p ∈ modelOpenSquare,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p :=
      fun p hp => hh.darboux p (modelOpenSquare_subset hp)
    have hyyO : ∀ p ∈ modelOpenSquare, covHessian g z p 1 1 ≠ 0 :=
      fun p hp => LowQuotient.denominator_ne_zero hc hh.denominator p (modelOpenSquare_subset hp)
    have hfinal := coordinateL2Bound_order_step hgO modelOpenSquare_isOpen (hh.smooth.mono hOU)
      hDo hyyO hRmeas hRO hRS (by omega : 7 ≤ k+9) hCP0 hB hP hlowR hPrev hyTop
      (by simpa only [show (k+9)-1=k+8 by omega] using hxTop)
    convert hfinal using 1 <;> try with_reducible_and_instances rfl

end SmoothLocal.Flow

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Flow.uniform_finite_varying_lowerCap_L2 := @OAI.SmoothLocal.Flow.uniform_finite_varying_lowerCap_L2
