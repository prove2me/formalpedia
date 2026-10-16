-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.four_weight_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:33:21.088667+00:00
-- url     : https://prove2.me/submissions/36c27482-abf4-4cc4-86a0-d1b021433534

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean:L634-L668
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.four_weight_interpolation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Theorems.Thm_OAI_DiagonalForms_System_comparison_dualLogMean
import Theorems.Thm_OAI_DiagonalForms_System_comparison_fiveQuadratic
import Theorems.Thm_OAI_DiagonalForms_System_comparison_logMean
import Theorems.Thm_OAI_DiagonalForms_System_comparison_resolvent_average
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compactDen_ne_zero
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compactIntegral_ne_zero
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compactIntegral_real_pos
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compact_stieltjes_representation
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_continuousAt_compactIntegral
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_differentiableAt_compactIntegral
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_pick_divided_difference_of_continuous
import Theorems.Thm_OAI_EntropyPhotonNumber_continuousAt_boundaryB
import Theorems.Thm_OAI_EntropyPhotonNumber_genericAdditionalE_pos
import Theorems.Thm_OAI_EntropyPhotonNumber_inv_sqrt_mem_closedSineQuadrant
import Theorems.Thm_OAI_EntropyPhotonNumber_inv_sqrt_mem_sineQuadrant
import Theorems.Thm_OAI_EntropyPhotonNumber_logarithmicMean_exp_pair
import Theorems.Thm_OAI_EntropyPhotonNumber_scalar_minimum

-- ---- from OAI.InformationTheory.PhotonNumber.Functions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber

open Set Filter Topology

theorem b_pos (x : ℝ) : 0 < b x := mul_pos (f_pos x) (Real.cosh_pos x)

theorem f_mul_sinh (x : ℝ) : f x * Real.sinh x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [f_of_ne_zero hx, div_mul_cancel₀ _ (Real.sinh_ne_zero.mpr hx)]

theorem f_mul_exp (x : ℝ) : f x * Real.exp x = b x + x := by
  have h : Real.exp x = Real.cosh x + Real.sinh x := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  rw [h, mul_add, f_mul_sinh]
  rfl

theorem f_mul_exp_neg (x : ℝ) : f x * Real.exp (-x) = b x - x := by
  simpa [sub_eq_add_neg] using f_mul_exp (-x)

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric

namespace EntropyPhotonNumber

open Set Filter Topology
theorem f_lt_one {x : ℝ} (hx : x ≠ 0) : f x < 1 := by
  have h (y : ℝ) (hy : 0 < y) : f y < 1 := by
    rw [f_of_ne_zero hy.ne', div_lt_one (Real.sinh_pos_iff.mpr hy)]
    exact Real.self_lt_sinh_iff.mpr hy
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · simpa using h (-x) (neg_pos.mpr hneg)
  · exact h x hpos

theorem one_lt_b {x : ℝ} (hx : x ≠ 0) : 1 < b x := by
  have h (y : ℝ) (hy : 0 < y) : 1 < b y := by
    rw [b, f_of_ne_zero hy.ne', div_mul_eq_mul_div,
      lt_div_iff₀ (Real.sinh_pos_iff.mpr hy)]
    simpa using sinh_lt_mul_cosh hy
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · simpa using h (-x) (neg_pos.mpr hneg)
  · exact h x hpos

theorem hasDerivAt_b {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt b ((b x - f x ^ 2) / x) x := by
  have hd := (hasDerivAt_f hx).mul (Real.hasDerivAt_cosh x)
  change HasDerivAt b _ x at hd
  convert! hd using 1
  dsimp [b]
  rw [f_of_ne_zero hx]
  have hs := Real.sinh_ne_zero.mpr hx
  have hi := Real.cosh_sq_sub_sinh_sq x
  field_simp
  nlinarith [congrArg (fun z : ℝ => x * z) hi]

theorem hasDerivAt_f_sq {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u => f u ^ 2) (2 * f x ^ 2 * (1 - b x) / x) x := by
  convert! (hasDerivAt_f hx).pow 2 using 1
  dsimp [b]
  rw [f_of_ne_zero hx]
  have hs := Real.sinh_ne_zero.mpr hx
  field_simp

theorem B_f_sq {x : ℝ} (hx : 0 ≤ x) : B (f x ^ 2) = b x := by
  rw [B, bParameter_f_sq hx]

theorem bParameter_pos {s : ℝ} (hs : s ∈ Ioo 0 1) : 0 < bParameter s := by
  have hn := bParameter_nonneg ⟨hs.1, hs.2.le⟩
  have he := f_sq_bParameter ⟨hs.1, hs.2.le⟩
  by_contra h
  have : bParameter s = 0 := le_antisymm (not_lt.mp h) hn
  simp [this] at he
  linarith [hs.2]

theorem strictAntiOn_bParameter : StrictAntiOn bParameter (Ioc 0 1) := by
  intro s hs t ht hst
  by_contra h
  have hle := strictAntiOn_f_sq.antitoneOn (bParameter_nonneg hs)
    (bParameter_nonneg ht) (not_lt.mp h)
  rw [f_sq_bParameter hs, f_sq_bParameter ht] at hle
  exact (not_le_of_gt hst) hle

theorem range_bParameter : bParameter '' Ioo 0 1 = Ioi (0 : ℝ) := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact bParameter_pos hs
  · intro x hx
    refine ⟨f x ^ 2, ?_, bParameter_f_sq hx.le⟩
    refine ⟨sq_pos_of_pos (f_pos x), ?_⟩
    have hf := f_lt_one hx.ne'
    nlinarith [f_pos x]

theorem continuousAt_bParameter {s : ℝ} (hs : s ∈ Ioo 0 1) :
    ContinuousAt bParameter s := by
  have hm : StrictAntiOn bParameter (Ioo 0 1) :=
    strictAntiOn_bParameter.mono Ioo_subset_Ioc_self
  apply hm.dual_right.continuousAt_of_image_mem_nhds (Ioo_mem_nhds hs.1 hs.2)
  change bParameter '' Ioo 0 1 ∈ 𝓝 (bParameter s)
  rw [range_bParameter]
  exact Ioi_mem_nhds (bParameter_pos hs)

theorem hasDerivAt_bParameter {s : ℝ} (hs : s ∈ Ioo 0 1) :
    HasDerivAt bParameter
      (2 * s * (1 - B s) / bParameter s)⁻¹ s := by
  have hp := bParameter_pos hs
  have hd := hasDerivAt_f_sq hp.ne'
  rw [f_sq_bParameter ⟨hs.1, hs.2.le⟩] at hd
  apply HasDerivAt.of_local_left_inverse (continuousAt_bParameter hs) hd
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs.1.ne')
      (sub_ne_zero.mpr (one_lt_b hp.ne').ne)) hp.ne'
  · filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact f_sq_bParameter ⟨ht.1, ht.2.le⟩

theorem hasDerivAt_B {s : ℝ} (hs : s ∈ Ioo 0 1) :
    HasDerivAt B ((B s - s) / (2 * s * (1 - B s))) s := by
  have hp := bParameter_pos hs
  have hd := (hasDerivAt_b hp.ne').comp s (hasDerivAt_bParameter hs)
  rw [f_sq_bParameter ⟨hs.1, hs.2.le⟩] at hd
  convert! hd using 1
  change (B s - s) / (2 * s * (1 - B s)) =
    ((B s - s) / bParameter s) * (2 * s * (1 - B s) / bParameter s)⁻¹
  field_simp [hp.ne']

theorem sineInverse_mem {w : ℂ} (hw : w ∈ sineQuadrant) :
    sineInverse w ∈ sineDomain := by
  simpa only [sineInverse, dite_eq_left hw] using
    ((Equiv.ofBijective sineMap bijective_sineMap).symm ⟨w, hw⟩).property

theorem csinc_sineInverse {w : ℂ} (hw : w ∈ sineQuadrant) :
    csinc (sineInverse w) = w := by
  have he := congrArg Subtype.val
    ((Equiv.ofBijective sineMap bijective_sineMap).apply_symm_apply ⟨w, hw⟩)
  simpa only [sineInverse, dite_eq_left hw, Equiv.ofBijective_apply, sineMap] using he

theorem sineInverse_csinc {z : ℂ} (hz : z ∈ sineDomain) :
    sineInverse (csinc z) = z := by
  have he := congrArg Subtype.val
    ((Equiv.ofBijective sineMap bijective_sineMap).symm_apply_apply ⟨z, hz⟩)
  simpa only [sineInverse, dite_eq_left (csinc_mapsTo hz), Equiv.ofBijective_apply,
    sineMap] using he

theorem analyticAt_sineInverse {w : ℂ} (hw : w ∈ sineQuadrant) :
    AnalyticAt ℂ sineInverse w := by
  let z := sineInverse w
  have hz : z ∈ sineDomain := sineInverse_mem hw
  have he : sineInverse ∘ csinc =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_sineDomain.mem_nhds hz] with u hu
    exact sineInverse_csinc hu
  have ha : AnalyticAt ℂ (sineInverse ∘ csinc) z := analyticAt_id.congr he.symm
  have := (analyticAt_comp_iff_of_deriv_ne_zero (analyticAt_csinc z)
    (deriv_csinc_ne_zero hz)).mp ha
  simpa only [z, csinc_sineInverse hw] using this

theorem analyticAt_upperB {s : ℂ} (hs : 0 < s.im) : AnalyticAt ℂ upperB s := by
  have hm := sineInverse_mem (inv_sqrt_mem_sineQuadrant hs)
  have hsqrt : AnalyticAt ℂ Complex.sqrt s :=
    Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane s (Or.inr hs.ne')
  have hn : Complex.sqrt s ≠ 0 := by
    have hi := (inv_sqrt_mem_sineQuadrant hs).1
    intro he
    simp [he] at hi
  have ha := (analyticAt_sineInverse (inv_sqrt_mem_sineQuadrant hs)).comp
    (f := fun w : ℂ => (Complex.sqrt w)⁻¹) (hsqrt.inv hn)
  have hsin : Complex.sin (sineInverse (Complex.sqrt s)⁻¹) ≠ 0 := by
    intro he
    have he' := Complex.normSq_eq_zero.mpr he
    rw [normSq_sin] at he'
    have hsh := Real.sinh_pos_iff.mpr hm.2.2.1
    nlinarith [sq_nonneg (Real.sin (sineInverse (Complex.sqrt s)⁻¹).re)]
  exact (ha.mul (Complex.analyticAt_cos.comp ha)).div (Complex.analyticAt_sin.comp ha) hsin

theorem upperB_im_neg {s : ℂ} (hs : 0 < s.im) : (upperB s).im < 0 := by
  have hm := sineInverse_mem (inv_sqrt_mem_sineQuadrant hs)
  exact cotParameter_im_neg hm.1 hm.2.2.1

theorem closedSineInverse_eq_sineInverse {w : ℂ} (hw : w ∈ sineQuadrant) :
    closedSineInverse w = sineInverse w := by
  have hw' : w ∈ closedSineQuadrant := ⟨hw.1, hw.2.le⟩
  have hz := sineInverse_mem hw
  apply csinc_injOn_closedSineDomain (closedSineInverse_mem hw')
    ⟨⟨hz.1.le, hz.2.1.le, hz.2.2.1.le⟩, hz.2.2.2, (csinc_mapsTo hz).2.le⟩
  exact (csinc_closedSineInverse hw').trans (csinc_sineInverse hw).symm

theorem ccot_eq_cotParameter {z : ℂ} (hz : z ≠ 0) : ccot z = cotParameter z := by
  rw [ccot, csinc_of_ne hz, sineParameter, cotParameter]
  rw [div_div_eq_mul_div, mul_comm]

theorem ccot_boundary_im {w : ℂ} (hw : w ∈ closedSineQuadrant) (hi : w.im = 0) :
    (ccot (closedSineInverse w)).im = 0 := by
  let z := closedSineInverse w
  have hz : z ∈ closedSineDomain := closedSineInverse_mem hw
  have he : csinc z = w := csinc_closedSineInverse hw
  rcases csinc_boundary_axes hz (by rw [he, hi]) with hr | hi'
  · have hcos : Complex.cos z = (Real.cosh z.im : ℂ) := by
      calc
        Complex.cos z = Complex.cos ((z.im : ℂ) * I) := congrArg _ (eq_mul_I_of_re_zero hr)
        _ = (Real.cosh z.im : ℂ) := by rw [Complex.cos_mul_I, Complex.ofReal_cosh]
    change (ccot z).im = 0
    rw [ccot, hcos, csinc_eq_sinhc_of_re_zero hr, ← Complex.ofReal_div]
    exact Complex.ofReal_im _
  · have hcos : Complex.cos z = (Real.cos z.re : ℂ) := by
      calc
        Complex.cos z = Complex.cos (z.re : ℂ) := congrArg _ (eq_of_im_zero hi')
        _ = (Real.cos z.re : ℂ) := (Complex.ofReal_cos _).symm
    change (ccot z).im = 0
    rw [ccot, hcos, csinc_eq_sinc_of_im_zero hi', ← Complex.ofReal_div]
    exact Complex.ofReal_im _

theorem boundaryB_eq_upperB {s : ℂ} (hs : 0 < s.im) : boundaryB s = upperB s := by
  rw [boundaryB, upperReflect_eq hs.le,
    closedSineInverse_eq_sineInverse (inv_sqrt_mem_sineQuadrant hs)]
  have hz := sineInverse_mem (inv_sqrt_mem_sineQuadrant hs)
  exact ccot_eq_cotParameter (by intro he; have hr := hz.1; simp [he] at hr)

theorem analyticAt_boundaryB {s : ℂ} (hs : 0 < s.im) : AnalyticAt ℂ boundaryB s := by
  apply (analyticAt_upperB hs).congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hs] with z hz
  exact (boundaryB_eq_upperB hz).symm

theorem boundaryB_im_neg {s : ℂ} (hs : 0 < s.im) : (boundaryB s).im < 0 := by
  rw [boundaryB_eq_upperB hs]
  exact upperB_im_neg hs

theorem boundaryB_real {x : ℝ} (hx : 0 < x) : (boundaryB (x : ℂ)).im = 0 := by
  have hr : (Complex.sqrt (x : ℂ))⁻¹ ∈ closedSineQuadrant :=
    inv_sqrt_mem_closedSineQuadrant hx (by simp)
  have hi : ((Complex.sqrt (x : ℂ))⁻¹).im = 0 := by
    have hs : Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
      exact Complex.sqrt_of_nonneg (by exact_mod_cast hx.le)
    rw [hs, ← Complex.ofReal_inv]
    exact Complex.ofReal_im _
  rw [boundaryB, upperReflect_eq (by simp : (0 : ℝ) ≤ (x : ℂ).im)]
  exact ccot_boundary_im hr hi

end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.Analysis.DiagonalForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace DiagonalForms.System
end DiagonalForms.System

namespace QuantumCalculus
end QuantumCalculus

namespace DiagonalForms.System
end DiagonalForms.System

namespace DiagonalForms.System
open EntropyPhotonNumber

end DiagonalForms.System

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace DiagonalForms

namespace System

variable {P I J : Type*} (D : System P I J)

theorem comparison_smul {w : P → ℝ} (hw : D.Comparison w) {a : ℝ} (ha : 0 ≤ a) :
    D.Comparison (fun p => a * w p) := by
  intro z s
  simp only [mul_assoc, ← Finset.mul_sum]
  simp only [sourceForm, mul_assoc, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hw z s) ha

end System

end DiagonalForms

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

section CompactIntegral
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
theorem affine_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (t : UnitInterval) :
    0 < (1 - t.val) * X + t.val * Y := by
  rcases t.property.1.eq_or_lt with ht | ht
  · simp [← ht, hX]
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) hX.le) (mul_pos ht hY)
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

theorem resolvent_kernel_pos {q r : ℝ} (hq : 0 < q) (hr : r ∈ Icc 0 1) :
    0 < 1+(q-1)*r := by
  have h := affine_pos (X := 1) (Y := q) (by norm_num) hq ⟨r, hr⟩
  dsimp at h
  nlinarith

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure μ] in
theorem resolventWeight_pos {c : ℝ} (hc : 0 ≤ c) {r : K → ℝ}
    (hr : ∀ k, r k ∈ Icc 0 1) {q : ℝ} (hq : 0 < q) :
    0 < resolventWeight μ c r q := by
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (inv_pos.mpr hq) hc)
    (integral_nonneg (fun k => inv_nonneg.mpr (resolvent_kernel_pos hq (hr k)).le))

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

theorem continuous_resolvent_comp {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    {c : ℝ} {r : K → ℝ} (hrc : Continuous r) (hr : ∀ k, r k ∈ Icc 0 1)
    {q : X → ℝ} (hqc : Continuous q) (hqp : ∀ x, 0 < q x) :
    Continuous (fun x => resolventWeight μ c r (q x)) := by
  have hk : Continuous (fun z : X × K => (1+(q z.1-1)*r z.2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro z
      exact (resolvent_kernel_pos (hqp z.1) (hr z.2)).ne'
  have hi : Continuous (fun x => ∫ k, (1+(q x-1)*r k)⁻¹ ∂μ) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := μ) hk isCompact_univ)
  exact ((hqc.inv₀ (fun x => (hqp x).ne')).add continuous_const).add hi

theorem continuousOn_resolventWeight {c : ℝ} {r : K → ℝ} (hrc : Continuous r)
    (hr : ∀ k, r k ∈ Icc 0 1) : ContinuousOn (resolventWeight μ c r) (Ioi 0) := by
  let : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_resolvent_comp μ hrc hr continuous_subtype_val (fun x => x.property)

end DiagonalForms.System

namespace DiagonalForms.System
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

end

end

end OAI

-- ---- from OAI.Analysis.Herglotz ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber.Herglotz

section Density
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

end Density

section WeakIntegral
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X]

end WeakIntegral

attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle
theorem approachRadius_tendsto : Tendsto approachRadius atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun _ => by linarith) tendsto_natCast_atTop_atTop
  change Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1)
  simpa only [Function.comp_apply, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hn)

theorem boundaryWeight_pos (θ : Angle) : 0 < boundaryWeight θ := by
  dsimp [boundaryWeight]
  positivity

theorem compactKernel_integrable (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) :
    Integrable (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s)
      (μ : Measure Angle) := by
  have hc : Continuous (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s) := by
    exact (Complex.continuous_ofReal.comp continuous_boundaryWeight).div
      (continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp continuous_boundaryParameter)))
      (fun θ => compactDen_ne_zero (boundaryParameter_mem θ) hs)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mul_compactKernel_im (t w : ℝ) (s : ℂ) :
    (s * compactKernel t w s).im = w * (1 - t) * s.im / Complex.normSq (1 + (s - 1) * t) := by
  rw [compactKernel, ← mul_div_assoc, Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_im, Complex.one_re, sub_zero, mul_zero, zero_add]
  ring

theorem complex_im_integral {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → ℂ} (hf : Integrable f ν) : (∫ x, f x ∂ν).im = ∫ x, (f x).im ∂ν :=
  (Complex.imCLM.integral_comp_comm hf).symm

theorem mul_compactIntegral_im_nonneg (μ : FiniteMeasure Angle) {s : ℂ} (hs : 0 < s.im) :
    0 ≤ (s * compactIntegral μ s).im := by
  rw [compactIntegral, ← integral_const_mul,
    complex_im_integral ((compactKernel_integrable μ (Or.inl hs)).const_mul s)]
  apply integral_nonneg
  intro θ
  change 0 ≤ (s * compactKernel _ _ _).im
  rw [mul_compactKernel_im]
  exact div_nonneg (mul_nonneg (mul_nonneg (boundaryWeight_pos θ).le
    (sub_nonneg.mpr (boundaryParameter_mem θ).2)) hs.le) (Complex.normSq_nonneg _)

theorem upper_boundary_eq {F G : ℂ → ℂ} {x : ℝ}
    (hF : ContinuousAt F (x : ℂ)) (hG : ContinuousAt G (x : ℂ))
    (he : ∀ s : ℂ, 0 < s.im → F s = G s) : F (x : ℂ) = G (x : ℂ) := by
  let z : ℕ → ℂ := fun n => (x : ℂ) + ((1 - approachRadius n : ℝ) : ℂ) * I
  have hz : Tendsto z atTop (𝓝 (x : ℂ)) := by
    simpa [z] using (tendsto_const_nhds (x := (x : ℂ))).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := (1 : ℝ))).sub approachRadius_tendsto)).mul_const I)
  have hi (n : ℕ) : 0 < (z n).im := by
    simpa [z] using sub_pos.mpr (approachRadius_mem n).2
  exact tendsto_nhds_unique (hF.tendsto.comp hz)
    ((hG.tendsto.comp hz).congr (fun n => (he _ (hi n)).symm))

theorem compactIntegral_real (μ : FiniteMeasure Angle) (x : ℝ) :
    compactIntegral μ (x : ℂ) =
      ((∫ θ : Angle, boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) ∂(μ : Measure Angle) : ℝ) : ℂ) := by
  rw [compactIntegral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with θ
  simp only [compactKernel, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem analyticAt_compactIntegral (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : AnalyticAt ℂ (compactIntegral μ) s := by
  have hopen : IsOpen {s : ℂ | 0 < s.im ∨ 0 < s.re} :=
    (isOpen_lt continuous_const Complex.continuous_im).union
      (isOpen_lt continuous_const Complex.continuous_re)
  exact (DifferentiableOn.analyticOnNhd
    (fun z hz => (differentiableAt_compactIntegral μ hz).differentiableWithinAt) hopen) s hs

end EntropyPhotonNumber.Herglotz

end

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber
open Herglotz MeasureTheory

theorem boundaryB_f_sq {x : ℝ} (hx : 0 ≤ x) :
    boundaryB ((f x ^ 2 : ℝ) : ℂ) = (b x : ℂ) := by
  have hf := f_pos x
  have hroot : Complex.sqrt ((f x ^ 2 : ℝ) : ℂ) = (f x : ℂ) := by
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast (sq_nonneg (f x))), Complex.ofReal_re,
      Real.sqrt_sq hf.le]
  have hsin : sinhc x = (f x)⁻¹ := by
    rw [f_eq_inv_dslope, inv_inv]
    rfl
  have hz : (x : ℂ) * I ∈ closedSineDomain := by
    constructor
    · exact ⟨by simp, by simpa using Real.pi_pos.le, by simpa using hx⟩
    · change 0 < (csinc ((x : ℂ) * I)).re ∧ (csinc ((x : ℂ) * I)).im ≤ 0
      rw [csinc_mul_I, hsin]
      exact ⟨inv_pos.mpr hf, by simp⟩
  have hw : (f x : ℂ)⁻¹ ∈ closedSineQuadrant := by
    rw [← Complex.ofReal_inv]
    exact ⟨inv_pos.mpr hf, by simp⟩
  have hi : closedSineInverse ((f x : ℂ)⁻¹) = (x : ℂ) * I := by
    apply csinc_injOn_closedSineDomain (closedSineInverse_mem hw) hz
    rw [csinc_closedSineInverse hw, csinc_mul_I, hsin, Complex.ofReal_inv]
  rw [boundaryB, upperReflect_eq (by simp [-Complex.ofReal_pow]), hroot, hi, ccot, Complex.cos_mul_I,
    ← Complex.ofReal_cosh, csinc_mul_I, ← Complex.ofReal_div, hsin, div_inv_eq_mul]
  simp only [b, Complex.ofReal_mul, mul_comm]

theorem boundaryB_eq_B {s : ℝ} (hs : s ∈ Ioc 0 1) : boundaryB (s : ℂ) = (B s : ℂ) := by
  have he := boundaryB_f_sq (bParameter_nonneg hs)
  rw [f_sq_bParameter hs] at he
  exact he

theorem exists_B_resolvent : ∃ μ : FiniteMeasure Angle,
    (μ : Measure Angle) ≠ 0 ∧
    ∀ s : ℂ, 0 < s.im ∨ (s.im = 0 ∧ 0 < s.re) →
      boundaryB s = 1 - (s - 1) * compactIntegral μ s := by
  obtain ⟨μ, hμ⟩ := pick_divided_difference_of_continuous (P := fun s => -boundaryB s)
    (fun s hs => (analyticAt_boundaryB hs).neg)
    (fun s hs => by simpa using (boundaryB_im_neg hs).le)
    (fun x hx => ⟨(continuousAt_boundaryB hx).neg, by simp [boundaryB_real hx]⟩)
  have he (s : ℂ) (hs : 0 < s.im) : boundaryB s = 1 - (s - 1) * compactIntegral μ s := by
    have h := hμ s hs
    rw [boundaryB_one] at h
    linear_combination -h
  have hn : (μ : Measure Angle) ≠ 0 := by
    intro hz
    have h := he I (by simp)
    simp only [compactIntegral, hz, integral_zero_measure, mul_zero, sub_zero] at h
    have hi := boundaryB_im_neg (s := I) (by simp)
    simp [h] at hi
  refine ⟨μ, hn, ?_⟩
  intro s hs
  rcases hs with hs | ⟨hi, hr⟩
  · exact he s hs
  · have hb := upper_boundary_eq (continuousAt_boundaryB hr)
      (continuousAt_const.sub ((continuousAt_id.sub continuousAt_const).mul
        (continuousAt_compactIntegral μ hr))) he
    have hs : (s.re : ℂ) = s := (eq_of_im_zero hi).symm
    simpa only [Pi.sub_apply, Pi.mul_apply, id_eq, hs] using hb

end EntropyPhotonNumber

namespace EntropyPhotonNumber.Herglotz

theorem compactIntegral_re_pos (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {s : ℂ} (hs : 0 < s.re) : 0 < (compactIntegral μ s).re := by
  have hi := compactKernel_integrable μ (Or.inr hs)
  have hre : (compactIntegral μ s).re = ∫ θ : Angle,
      (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).re ∂(μ : Measure Angle) :=
    (Complex.reCLM.integral_comp_comm hi).symm
  have hp (θ : Angle) : 0 < (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).re := by
    have ht := boundaryParameter_mem θ
    have hd : 0 < (1 + (s - 1) * (boundaryParameter θ : ℂ)).re := by
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.sub_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      by_cases ha : boundaryParameter θ = 0
      · simp [ha]
      · nlinarith [mul_pos hs (lt_of_le_of_ne ht.1 (Ne.symm ha)), ht.2]
    simp only [compactKernel, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos (boundaryWeight_pos θ) hd)
      (Complex.normSq_pos.mpr (compactDen_ne_zero ht (Or.inr hs)))
  rw [hre, integral_pos_iff_support_of_nonneg (fun θ => (hp θ).le) (Complex.reCLM.integrable_comp hi)]
  have he : Function.support (fun θ : Angle =>
      (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).re) = univ := by
    ext θ
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp θ).ne'
  rw [he]
  exact Measure.measure_univ_pos.mpr hμ

end EntropyPhotonNumber.Herglotz

namespace EntropyPhotonNumber
open MeasureTheory Herglotz

theorem analyticAt_resolventB (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : AnalyticAt ℂ (resolventB μ) s :=
  analyticAt_const.sub ((analyticAt_id.sub analyticAt_const).mul (analyticAt_compactIntegral μ hs))

theorem analyticAt_resolventR (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {s : ℂ} (hs : 0 < s.im ∨ 0 < s.re) : AnalyticAt ℂ (resolventR μ) s := by
  apply ((analyticAt_id.mul (analyticAt_compactIntegral μ hs))).inv
  apply mul_ne_zero
  · intro h
    change s = 0 at h
    rcases hs with hs | hs <;> simp [h] at hs
  · rcases hs with hs | hs
    · exact compactIntegral_ne_zero μ hμ hs
    · intro h
      have hp := compactIntegral_re_pos μ hμ hs
      simp [h] at hp

theorem resolventR_im_nonpos (μ : FiniteMeasure Angle) {s : ℂ} (hs : 0 < s.im) :
    (resolventR μ s).im ≤ 0 := by
  rw [resolventR, Complex.inv_im]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_compactIntegral_im_nonneg μ hs))
    (Complex.normSq_nonneg _)

theorem resolventR_real (μ : FiniteMeasure Angle) (x : ℝ) : (resolventR μ (x : ℂ)).im = 0 := by
  rw [resolventR, compactIntegral_real, ← Complex.ofReal_mul, ← Complex.ofReal_inv]
  exact Complex.ofReal_im _

theorem resolventR_real_pos (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {x : ℝ} (hx : 0 < x) : 0 < (resolventR μ (x : ℂ)).re := by
  have hp := compactIntegral_real_pos μ hμ hx
  rw [resolventR, compactIntegral_real, ← Complex.ofReal_mul, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [compactIntegral_real, Complex.ofReal_re] at hp
  exact inv_pos.mpr (mul_pos hx hp)

theorem resolventR_stieltjes (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ν : FiniteMeasure Angle,
      ∀ x : ℝ, 0 < x → (resolventR μ (x : ℂ)).re = c +
        ∫ θ : Angle, (1 + (x - 1) * boundaryParameter θ)⁻¹ ∂(ν : Measure Angle) := by
  apply compact_stieltjes_representation
  · intro s hs
    exact analyticAt_resolventR μ hμ (Or.inl hs)
  · exact fun s hs => resolventR_im_nonpos μ hs
  · intro x hx
    exact ⟨analyticAt_resolventR μ hμ (Or.inr hx), resolventR_real μ x,
      (resolventR_real_pos μ hμ hx).le⟩

theorem analytic_eqOn_rightHalfPlane_of_real_interval {F K : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.re})
    (hK : AnalyticOnNhd ℂ K {z : ℂ | 0 < z.re})
    (he : ∀ x : ℝ, x ∈ Ioo 0 1 → F (x : ℂ) = K (x : ℂ)) :
    EqOn F K {z : ℂ | 0 < z.re} := by
  apply hF.eqOn_of_preconnected_of_mem_closure hK (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := (1 / 2 : ℂ)) (by norm_num)
  let xs : ℕ → ℝ := fun n => 1 / 2 + 1 / ((n : ℝ) + 3)
  have hxs (n : ℕ) : xs n ∈ Ioo 0 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 0 < 1 / ((n : ℝ) + 3) := by positivity
    have hlt : 1 / ((n : ℝ) + 3) < 1 / 2 := by
      exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)
    dsimp [xs]
    constructor <;> linarith
  have ht : Tendsto xs atTop (𝓝 (1 / 2)) := by
    have hd : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 3)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 3)
    simpa [xs] using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add hd
  have htc : Tendsto (fun n => (xs n : ℂ)) atTop (𝓝 (1 / 2 : ℂ)) := by
    convert! Complex.continuous_ofReal.continuousAt.tendsto.comp ht using 1
    norm_num
  apply mem_closure_of_tendsto htc
  filter_upwards with n
  refine ⟨he (xs n) (hxs n), ?_⟩
  simp only [mem_singleton_iff]
  intro h
  have hreal := congrArg Complex.re h
  norm_num at hreal
  have hp : 0 < 1 / ((n : ℝ) + 3) := by positivity
  dsimp [xs] at hreal
  norm_num at hreal
  linarith

theorem deriv_resolventB_on_original (μ : FiniteMeasure Angle)
    (he : ∀ x : ℝ, x ∈ Ioc 0 1 → resolventB μ (x : ℂ) = (B x : ℂ))
    {x : ℝ} (hx : x ∈ Ioo 0 1) :
    deriv (resolventB μ) (x : ℂ) = ((B x - x) / (2 * x * (1 - B x)) : ℝ) := by
  have hd := ((analyticAt_resolventB μ (s := (x : ℂ)) (Or.inr hx.1)).differentiableAt.hasDerivAt).comp_ofReal
  have hr := (hasDerivAt_B hx).ofReal_comp
  apply hd.unique
  apply hr.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact he y ⟨hy.1, hy.2.le⟩

theorem deriv_resolventB_ode (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    (he : ∀ x : ℝ, x ∈ Ioc 0 1 → resolventB μ (x : ℂ) = (B x : ℂ))
    {s : ℂ} (hs : 0 < s.re) :
    deriv (resolventB μ) s = -(s⁻¹ + resolventR μ s) / 2 := by
  have ha : AnalyticOnNhd ℂ (resolventB μ) {z : ℂ | 0 < z.re} :=
    fun z hz => analyticAt_resolventB μ (Or.inr hz)
  apply analytic_eqOn_rightHalfPlane_of_real_interval ha.deriv
    (fun z hz => ((analyticAt_id.inv (by intro h; change z = 0 at h; simp [h] at hz)).add
      (analyticAt_resolventR μ hμ (Or.inr hz))).neg.div_const) ?_ hs
  intro x hx
  change deriv (resolventB μ) (x : ℂ) = -((x : ℂ)⁻¹ + resolventR μ (x : ℂ)) / 2
  rw [deriv_resolventB_on_original μ he hx]
  have hz : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  have hz1 : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hx.2.ne
  have hg : compactIntegral μ (x : ℂ) ≠ 0 := by
    intro h
    have hp := compactIntegral_real_pos μ hμ hx.1
    simp [h] at hp
  have hB := he x ⟨hx.1, hx.2.le⟩
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [← hB, resolventB, resolventR]
  have heq : (1 : ℂ) - (1 - ((x : ℂ) - 1) * compactIntegral μ (x : ℂ)) =
      ((x : ℂ) - 1) * compactIntegral μ (x : ℂ) := by ring
  rw [heq]
  field_simp [hz, hz1, hg]
  ring

theorem hasDerivAt_real_resolventB (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    (he : ∀ x : ℝ, x ∈ Ioc 0 1 → resolventB μ (x : ℂ) = (B x : ℂ))
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (resolventB μ (t : ℂ)).re)
      (-(x⁻¹ + (resolventR μ (x : ℂ)).re) / 2) x := by
  have hd := (analyticAt_resolventB μ (s := (x : ℂ)) (Or.inr hx)).differentiableAt.hasDerivAt
  rw [deriv_resolventB_ode μ hμ he hx] at hd
  convert! hd.real_of_complex using 1
  simp

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EntropyPhotonNumber

section
open DiagonalForms.System MeasureTheory Set Filter Topology

theorem dualLogarithmicMean_exp_pair {m : ℝ} (hm : 0 < m) (x : ℝ) :
    (m*f x*Real.exp x)*(m*f x*Real.exp (-x)) /
      logMean (m*f x*Real.exp x) (m*f x*Real.exp (-x)) = m * f x ^ 2 := by
  rw [logarithmicMean_exp_pair hm]
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  field_simp
  nlinarith [he]

theorem comparison_basic_weights {P I J : Type*} (D : DiagonalForms.System P I J)
    (m x y : P → ℝ) (hm : ∀ p, 0 < m p)
    (hxP : D.Comparison (fun p => m p*f (x p)*Real.exp (x p)))
    (hxM : D.Comparison (fun p => m p*f (x p)*Real.exp (-x p)))
    (hyP : D.Comparison (fun p => m p*f (y p)*Real.exp (y p)))
    (hyM : D.Comparison (fun p => m p*f (y p)*Real.exp (-y p))) :
    D.Comparison m ∧ D.Comparison (fun p => m p*f (x p)^2) ∧
      D.Comparison (fun p => m p*f (y p)^2) := by
  have hpos (t : P → ℝ) (p : P) : 0 < m p*f (t p)*Real.exp (t p) :=
    mul_pos (mul_pos (hm p) (f_pos _)) (Real.exp_pos _)
  have hneg (t : P → ℝ) (p : P) : 0 < m p*f (t p)*Real.exp (-t p) :=
    mul_pos (mul_pos (hm p) (f_pos _)) (Real.exp_pos _)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [logarithmicMean_exp_pair (hm _)] using
      D.comparison_logMean hxP hxM (hpos x) (hneg x)
  · simpa only [dualLogarithmicMean_exp_pair (hm _)] using
      D.comparison_dualLogMean hxP hxM (hpos x) (hneg x)
  · simpa only [dualLogarithmicMean_exp_pair (hm _)] using
      D.comparison_dualLogMean hyP hyM (hpos y) (hneg y)

theorem B_f_sq_all (x : ℝ) : B (f x ^ 2) = b x := by
  rcases le_total 0 x with hx | hx
  · exact B_f_sq hx
  · rw [← f_neg x, B_f_sq (neg_nonneg.mpr hx), b_neg]

theorem interpolationQuadratic_expand (m x y e : ℝ) (ξ φ : ℂ) :
    interpolationQuadratic m x y e ξ φ =
      m*(b x+b y)/2*Complex.normSq ξ +
      m*((b x+b y)/2+e)*Complex.normSq φ -
      m*(x-y)*(ξ.re*φ.re+ξ.im*φ.im) := by
  unfold interpolationQuadratic
  have hp (z : ℝ) : m*f z*Real.exp z = m*(b z+z) := by
    rw [mul_assoc, f_mul_exp]
  have hn (z : ℝ) : m*f z*Real.exp (-z) = m*(b z-z) := by
    rw [mul_assoc, f_mul_exp_neg]
  rw [hp, hp, hn, hn]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring

theorem interpolationQuadratic_complete {m x y e : ℝ} (he : 0 < e)
    (ξ φ : ℂ) :
    interpolationQuadratic m x y e ξ φ =
      m*((b x+b y-(x-y)^2/(b x+b y+2*e))/2)*Complex.normSq ξ +
      m*(b x+b y+2*e)/2 *
        Complex.normSq (φ-(((x-y)/(b x+b y+2*e) : ℝ) : ℂ)*ξ) := by
  have hA : b x+b y+2*e ≠ 0 := ne_of_gt (by positivity [b_pos x, b_pos y])
  rw [interpolationQuadratic_expand]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp
  ring

theorem interpolationQuadratic_lower {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) {m : ℝ} (hm : 0 < m) (x y : ℝ) (ξ φ : ℂ) :
    fourWeightTarget m x y * Complex.normSq ξ ≤
      interpolationQuadratic m x y (genericAdditionalE D (f x^2) (f y^2)) ξ φ := by
  have he := genericAdditionalE_pos hc hp (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))
  rw [interpolationQuadratic_complete he, scalar_minimum hc hp hd hb]
  have hnon : 0 ≤ m*(b x+b y+2*genericAdditionalE D (f x^2) (f y^2))/2 *
      Complex.normSq (φ-(((x-y)/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)) : ℝ) : ℂ)*ξ) := by
    exact mul_nonneg (div_nonneg (mul_nonneg hm.le (by positivity [b_pos x, b_pos y])) (by norm_num))
      (Complex.normSq_nonneg _)
  dsimp [fourWeightTarget]
  convert le_add_of_nonneg_right hnon using 1
  ring

theorem interpolationQuadratic_minimum {B₀ D : ℝ → ℝ}
    (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q)
    (hb : ∀ x, B₀ (f x^2) = b x) {m : ℝ} (x y : ℝ) (ξ : ℂ) :
    interpolationQuadratic m x y (genericAdditionalE D (f x^2) (f y^2)) ξ
      ((((x-y)/(b x+b y+2*genericAdditionalE D (f x^2) (f y^2)) : ℝ) : ℂ)*ξ) =
      fourWeightTarget m x y * Complex.normSq ξ := by
  have he := genericAdditionalE_pos hc hp (sq_pos_of_pos (f_pos x)) (sq_pos_of_pos (f_pos y))
  rw [interpolationQuadratic_complete he, scalar_minimum hc hp hd hb]
  simp only [sub_self, map_zero, mul_zero, add_zero]
  dsimp [fourWeightTarget]
  ring

theorem comparison_interpolation_of_stieltjes {P I J : Type*} (S : DiagonalForms.System P I J)
    {B₀ D : ℝ → ℝ} (hc : ContinuousOn D (Ioi 0)) (hp : ∀ q, 0 < q → 0 < D q)
    (hd : ∀ q, 0 < q → HasDerivAt B₀ (-D q/2) q) (hb : ∀ x, B₀ (f x^2) = b x)
    (m x y : P → ℝ) (hm : ∀ p, 0 < m p)
    (hxP : S.Comparison (fun p => m p*f (x p)*Real.exp (x p)))
    (hxM : S.Comparison (fun p => m p*f (x p)*Real.exp (-x p)))
    (hyP : S.Comparison (fun p => m p*f (y p)*Real.exp (y p)))
    (hyM : S.Comparison (fun p => m p*f (y p)*Real.exp (-y p)))
    (hE : S.Comparison (fun p => m p*genericAdditionalE D (f (x p)^2) (f (y p)^2))) :
    S.Comparison (fun p => fourWeightTarget (m p) (x p) (y p)) := by
  apply S.comparison_fiveQuadratic
    (δ := fun p => (x p-y p)/(b (x p)+b (y p)+2*genericAdditionalE D (f (x p)^2) (f (y p)^2)))
    (S.comparison_smul hxP (by norm_num : (0 : ℝ) ≤ 1/4))
    (S.comparison_smul hxM (by norm_num : (0 : ℝ) ≤ 1/4))
    (S.comparison_smul hyP (by norm_num : (0 : ℝ) ≤ 1/4))
    (S.comparison_smul hyM (by norm_num : (0 : ℝ) ≤ 1/4)) hE
  · intro p ξ
    convert interpolationQuadratic_minimum hc hp hd hb (x p) (y p) ξ using 1
    dsimp [fiveQuadratic, interpolationQuadratic]
    ring
  · intro p ξ φ
    convert interpolationQuadratic_lower hc hp hd hb (hm p) (x p) (y p) ξ φ using 1
    dsimp [fiveQuadratic, interpolationQuadratic]
    ring

end

open DiagonalForms.System MeasureTheory Set Filter Topology Herglotz

theorem four_weight_interpolation {P I J : Type*} (S : DiagonalForms.System P I J)
    (m x y : P → ℝ) (hm : ∀ p, 0 < m p)
    (hxP : S.Comparison (fun p => m p*f (x p)*Real.exp (x p)))
    (hxM : S.Comparison (fun p => m p*f (x p)*Real.exp (-x p)))
    (hyP : S.Comparison (fun p => m p*f (y p)*Real.exp (y p)))
    (hyM : S.Comparison (fun p => m p*f (y p)*Real.exp (-y p))) :
    S.Comparison (fun p => fourWeightTarget (m p) (x p) (y p)) := by
  obtain ⟨μ, hμ, hμB⟩ := exists_B_resolvent
  have he (q : ℝ) (hq : q ∈ Ioc 0 1) : resolventB μ (q : ℂ) = (B q : ℂ) :=
    (hμB (q : ℂ) (Or.inr ⟨Complex.ofReal_im q, hq.1⟩)).symm.trans (boundaryB_eq_B hq)
  obtain ⟨c, hc, ν, hν⟩ := resolventR_stieltjes μ hμ
  let D := resolventWeight (ν : Measure Angle) c boundaryParameter
  let B₀ := fun q : ℝ => (resolventB μ (q : ℂ)).re
  have hcont : ContinuousOn D (Ioi 0) :=
    continuousOn_resolventWeight (ν : Measure Angle) continuous_boundaryParameter boundaryParameter_mem
  have hpos (q : ℝ) (hq : 0 < q) : 0 < D q :=
    resolventWeight_pos (ν : Measure Angle) hc boundaryParameter_mem hq
  have hd (q : ℝ) (hq : 0 < q) : HasDerivAt B₀ (-D q/2) q := by
    have h := hasDerivAt_real_resolventB μ hμ he hq
    rw [hν q hq] at h
    convert h using 1
    dsimp [D, B₀, resolventWeight]
    ring
  have hb (z : ℝ) : B₀ (f z^2) = b z := by
    have hq : f z^2 ∈ Ioc (0 : ℝ) 1 :=
      ⟨sq_pos_of_pos (f_pos z), by nlinarith [f_pos z, f_le_one z]⟩
    dsimp [B₀]
    rw [he _ hq, Complex.ofReal_re, B_f_sq_all]
  obtain ⟨hmc, hsc, htc⟩ := comparison_basic_weights S m x y hm hxP hxM hyP hyM
  have hE : S.Comparison (fun p => m p*genericAdditionalE D (f (x p)^2) (f (y p)^2)) := by
    have h := S.comparison_resolvent_average (ν : Measure Angle) ⟨0, ⟨le_rfl, by positivity⟩⟩ hc
      continuous_boundaryParameter boundaryParameter_mem hm
      (fun p => sq_pos_of_pos (f_pos (x p))) (fun p => sq_pos_of_pos (f_pos (y p))) hmc hsc htc
    simpa only [D, genericAdditionalE, div_eq_mul_inv] using h
  exact comparison_interpolation_of_stieltjes S hcont hpos hd hb m x y hm hxP hxM hyP hyM hE

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open DiagonalForms.System MeasureTheory Set Filter Topology Herglotz


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.four_weight_interpolation := @_root_.OAI.EntropyPhotonNumber.four_weight_interpolation
