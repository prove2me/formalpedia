-- Prove2me | solution 1 for OAI.SmoothLocal.HighEquation.exists_same_slice_actual_Q_source_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:45:20.640739+00:00
-- url     : https://prove2.me/submissions/75ad96ae-98b9-43c7-ab01-5b7d43fdbe6d

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport

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
open MeasureTheory
open scoped ENNReal

namespace SmoothLocal.Hyperbolic

theorem integral_square_eq_L2_norm_square
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂μ) = ∫ x, inner ℝ (hf.toLp f x) (hf.toLp f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := rfl
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _

theorem sqrt_integral_square_eq_L2_norm
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖hf.toLp f‖ := by
  rw [integral_square_eq_L2_norm_square hf, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

end SmoothLocal.Hyperbolic

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
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SmoothLocal.Analytic

variable {ι α : Type*} [DecidableEq ι]

theorem finite_product_one_factor_bound (s : Finset ι) (f : ι → α → ℝ)
    {j : ι} (hj : j ∈ s) {B : ℝ} (hB : 0 ≤ B) (x : α)
    (hb : ∀ i ∈ s.erase j, ‖f i x‖ ≤ B) :
    ‖∏ i ∈ s, f i x‖ ≤ B ^ (s.erase j).card * ‖f j x‖ := by
  have hprod : ‖∏ i ∈ s.erase j, f i x‖ ≤ B ^ (s.erase j).card := by
    calc
      _ ≤ ∏ i ∈ s.erase j, ‖f i x‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _i ∈ s.erase j, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hb
      _ = _ := Finset.prod_const B
  rw [← Finset.prod_erase_mul s (fun i => f i x) hj, norm_mul]
  exact mul_le_mul hprod le_rfl (norm_nonneg _) (pow_nonneg hB _)

variable [MeasurableSpace α] {μ : Measure α} {U : Set α}

theorem finite_product_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    {j : ι} (hj : j ∈ s) {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s.erase j, ∀ x ∈ U, ‖f i x‖ ≤ B) :
    eLpNorm' (fun x => ∏ i ∈ s, f i x) (2 : ℝ) (μ.restrict U) ≤
      ‖B ^ (s.erase j).card‖ₑ * eLpNorm' (f j) (2 : ℝ) (μ.restrict U) := by
  have hdom : ∀ᵐ x ∂(μ.restrict U),
      ‖∏ i ∈ s, f i x‖ ≤ ‖B ^ (s.erase j).card * f j x‖ := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hB (s.erase j).card)]
    exact finite_product_one_factor_bound s f hj hB x (fun i hi => hb i hi x hx)
  calc
    _ ≤ eLpNorm' (fun x => B ^ (s.erase j).card * f j x) (2 : ℝ) (μ.restrict U) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f j)
      (B ^ (s.erase j).card) (by norm_num)

theorem finite_product_eLpNorm_two_of_aestronglyMeasurable
    (indices : Finset ι) (factors : ι → α → ℝ) {chosen : ι} (hchosen : chosen ∈ indices)
    {bound : ℝ} (hbound : 0 ≤ bound) (hU : MeasurableSet U)
    (hb : ∀ index ∈ indices.erase chosen, ∀ point ∈ U, ‖factors index point‖ ≤ bound)
    (hmeas : AEStronglyMeasurable
      (fun point => ∏ index ∈ indices, factors index point) (μ.restrict U)) :
    eLpNorm (fun point => ∏ index ∈ indices, factors index point) 2 (μ.restrict U) ≤
      ‖bound ^ (indices.erase chosen).card‖ₑ * eLpNorm (factors chosen) 2 (μ.restrict U) := by
  have hfactor : eLpNorm' (factors chosen) (2 : ℝ) (μ.restrict U) ≤
      eLpNorm (factors chosen) 2 (μ.restrict U) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
    norm_num
  calc
    _ = eLpNorm' (fun point => ∏ index ∈ indices, factors index point)
        (2 : ℝ) (μ.restrict U) := by
      simpa only [ENNReal.toReal_ofNat] using
        (eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num))
    _ ≤ ‖bound ^ (indices.erase chosen).card‖ₑ *
        eLpNorm' (factors chosen) (2 : ℝ) (μ.restrict U) :=
      finite_product_eLpNorm_two indices factors hchosen hbound hU hb
    _ ≤ _ := mul_le_mul_right hfactor _

end SmoothLocal.Analytic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SmoothLocal.Analytic
variable {ι α : Type*} [MeasurableSpace α] {μ : Measure α} {U : Set α}

theorem finite_product_bounded_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s, ∀ x ∈ U, ‖f i x‖ ≤ B) :
    eLpNorm' (fun x => ∏ i ∈ s, f i x) (2 : ℝ) (μ.restrict U) ≤
      ‖B ^ s.card‖ₑ * (μ U) ^ (1 / (2 : ℝ)) := by
  have hdom : ∀ᵐ x ∂(μ.restrict U), ‖∏ i ∈ s, f i x‖ ≤ ‖B ^ s.card‖ := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [Real.norm_of_nonneg (pow_nonneg hB s.card)]
    calc
      _ ≤ ∏ i ∈ s, ‖f i x‖ := Finset.norm_prod_le s _
      _ ≤ ∏ _i ∈ s, B :=
        Finset.prod_le_prod (fun index _ => norm_nonneg (f index x))
          (fun index hindex => hb index hindex x hx)
      _ = _ := Finset.prod_const B
  calc
    _ ≤ eLpNorm' (fun _ : α => B ^ s.card) (2 : ℝ) (μ.restrict U) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := by
      rw [eLpNorm'_const (B ^ s.card) (by norm_num), Measure.restrict_apply_univ]

theorem finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable
    (s : Finset ι) (f : ι → α → ℝ) {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s, ∀ x ∈ U, ‖f i x‖ ≤ B)
    (hm : AEStronglyMeasurable (fun x => ∏ i ∈ s, f i x) (μ.restrict U)) :
    eLpNorm (fun x => ∏ i ∈ s, f i x) 2 (μ.restrict U) ≤
      ‖B ^ s.card‖ₑ * (μ U) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact finite_product_bounded_eLpNorm_two s f hB hU hb

theorem finite_sum_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    (C : ι → ℝ≥0∞)
    (_hm : ∀ i ∈ s, AEStronglyMeasurable (f i) (μ.restrict U))
    (hb : ∀ i ∈ s, eLpNorm (f i) 2 (μ.restrict U) ≤ C i) :
    eLpNorm (fun x => ∑ i ∈ s, f i x) 2 (μ.restrict U) ≤ ∑ i ∈ s, C i := by
  have hsum := eLpNorm_sum_le (f := f) (s := s) (μ := μ.restrict U)
    _hm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact hsum.trans (Finset.sum_le_sum hb)

end SmoothLocal.Analytic

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter
namespace SmoothLocal.Geometry

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Coord → V} {U : Set Coord} {p : Coord}

theorem second_coordPartial_eq_fderiv (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p =
      fderiv ℝ (fderiv ℝ F) p (Pi.single i 1) (Pi.single j 1) := by
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hs p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const (c := Pi.single j (1 : ℝ)))]
  simp

theorem coordPartial_comm (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p = coordPartial j (coordPartial i F) p := by
  rw [second_coordPartial_eq_fderiv hF hU hp, second_coordPartial_eq_fderiv hF hU hp]
  exact (((hF p hp).contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt
    (by
      simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
      exact WithTop.coe_le_coe.mpr le_top)) _ _

end Calculus

end SmoothLocal.Geometry

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

theorem riemann_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (l k i j : Fin 2) :
    ContDiffOn ℝ ∞ (riemann g l k i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ m,
      (christoffel g m j k p * christoffel g l i m p -
        christoffel g m i k p * christoffel g l j m p)) U := by
    apply ContDiffOn.sum
    intro m hm
    exact ((christoffel_contDiffOn hg hU m j k).mul
      (christoffel_contDiffOn hg hU l i m)).sub
        ((christoffel_contDiffOn hg hU m i k).mul
          (christoffel_contDiffOn hg hU l j m))
  exact ((partial_contDiffOn (christoffel_contDiffOn hg hU l j k) hU i).sub
    (partial_contDiffOn (christoffel_contDiffOn hg hU l i k) hU j)).add hs

theorem gaussianCurvature_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (gaussianCurvature g) U := by
  have hn : ContDiffOn ℝ ∞ (fun p => ∑ l, g p 0 l * riemann g l 1 0 1 p) U := by
    apply ContDiffOn.sum
    intro l hl
    exact (hg.1 0 l).mul (riemann_contDiffOn hg hU l 1 0 1)
  exact hn.div (metricDet_contDiffOn hg) (fun p hp => metricDet_ne_zero hg hp)

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

def christoffelFirstKind (g : MetricField) (i j : Fin 2) (p : Coord) : Coord :=
  fun l => (coordPartial i (fun q => g q j l) p +
    coordPartial j (fun q => g q i l) p - coordPartial l (fun q => g q i j) p) / 2

theorem christoffel_eq_inverse_mulVec (g : MetricField) (i j : Fin 2) (p : Coord) :
    (fun k => christoffel g k i j p) = (g p)⁻¹ *ᵥ christoffelFirstKind g i j p := by
  ext k
  simp only [christoffel, inverseMetric, Matrix.mulVec, dotProduct, christoffelFirstKind]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem metric_mul_christoffel {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    g p *ᵥ (fun k => christoffel g k i j p) = christoffelFirstKind g i j p := by
  rw [christoffel_eq_inverse_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit),
    Matrix.one_mulVec]

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem affineCoordinates_contDiff (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affineCoordinates b R) :=
  contDiff_const.add (matrixContinuousLinear R).contDiff

theorem affineCoordinates_hasFDerivAt (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Coord) : HasFDerivAt (affineCoordinates b R) (matrixContinuousLinear R) q := by
  change HasFDerivAt (fun x => b + matrixContinuousLinear R x)
    (matrixContinuousLinear R) q
  exact (matrixContinuousLinear R).hasFDerivAt.const_add b

theorem affineCoordinates_fderiv (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Coord) : fderiv ℝ (affineCoordinates b R) q = matrixContinuousLinear R :=
  (affineCoordinates_hasFDerivAt b R q).fderiv

@[simp] theorem affineCoordinates_zero (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    affineCoordinates b R 0 = b := by simp [affineCoordinates]

theorem isOpen_affine_preimage {U : Set Coord} (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    IsOpen (affineCoordinates b R ⁻¹' U) :=
  hU.preimage (affineCoordinates_contDiff b R).continuous

theorem affine_comp_contDiffOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiffOn ℝ ∞ (f ∘ affineCoordinates b R) (affineCoordinates b R ⁻¹' U) :=
  hf.comp (affineCoordinates_contDiff b R).contDiffOn (fun _ hq => hq)

theorem fderiv_affine_comp_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q v : Coord)
    (hf : DifferentiableAt ℝ f (affineCoordinates b R q)) :
    fderiv ℝ (f ∘ affineCoordinates b R) q v =
      fderiv ℝ f (affineCoordinates b R q) (R *ᵥ v) := by
  rw [fderiv_comp q hf (affineCoordinates_hasFDerivAt b R q).differentiableAt,
    affineCoordinates_fderiv, ContinuousLinearMap.comp_apply, matrixContinuousLinear_apply]

theorem affinePullbackMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : Function.Injective R.mulVec) :
    SmoothPositiveOn (affinePullbackMetric g b R) (affineCoordinates b R ⁻¹' U) := by
  constructor
  · intro i j
    have hc (a k : Fin 2) : ContDiffOn ℝ ∞
        (fun q => g (affineCoordinates b R q) a k) (affineCoordinates b R ⁻¹' U) :=
      affine_comp_contDiffOn (hg.1 a k) b R
    simp only [affinePullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
    apply ContDiffOn.sum
    intro k _
    apply ContDiffOn.mul _ contDiffOn_const
    apply ContDiffOn.sum
    intro a _
    exact contDiffOn_const.mul (hc a k)
  · intro q hq
    simpa only [affinePullbackMetric, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hg.2 (affineCoordinates b R q) hq).conjTranspose_mul_mul_same hR

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

theorem metric_coeff_symm (hg : SmoothPositiveOn g U) (hp : p ∈ U) (i j : Fin 2) :
    g p i j = g p j i := by
  simpa using (hg.2 p hp).1.apply j i

theorem metric_coeff_partial_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    coordPartial k (fun q => g q i j) p = coordPartial k (fun q => g q j i) p := by
  have heq : (fun q => g q i j) =ᶠ[𝓝 p] (fun q => g q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_coeff_symm hg hq i j
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem christoffel_lower_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    christoffel g k i j p = christoffel g k j i p := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [metric_coeff_partial_symm hg hU hp l i j]
  ring

end SmoothLocal.Geometry

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
open Filter

namespace SmoothLocal.Geometry

theorem matrix_column_basis_expansion (R : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    R *ᵥ Pi.single i (1 : ℝ) =
      R 0 i • Pi.single 0 (1 : ℝ) + R 1 i • Pi.single 1 (1 : ℝ) := by
  rw [Matrix.mulVec_single_one]
  funext k
  fin_cases k <;> simp

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

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem metric_compatibility (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    coordPartial k (fun q => g q i j) p =
      (∑ r, christoffel g r k i p * g p r j) +
        (∑ r, christoffel g r k j p * g p i r) := by
  have hlower (a b c : Fin 2) :
      (∑ r, christoffel g r a b p * g p c r) = christoffelFirstKind g a b p c := by
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using
      congrFun (metric_mul_christoffel hg hp a b) c
  have hsym : (∑ r, christoffel g r k i p * g p r j) =
      ∑ r, christoffel g r k i p * g p j r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [metric_coeff_symm hg hp r j]
  rw [hsym, hlower k i j, hlower k j i]
  simp only [christoffelFirstKind]
  rw [metric_coeff_partial_symm hg hU hp k j i]
  ring

namespace CompatibilityCalculus

end CompatibilityCalculus

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

variable {g : MetricField} {U : Set Coord} {p : Coord}

theorem metric_second_compatibility (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (d k i j : Fin 2) :
    coordPartial d (coordPartial k (fun q => g q i j)) p =
      (∑ r, (coordPartial d (christoffel g r k i) p * g p r j +
        christoffel g r k i p * coordPartial d (fun q => g q r j) p)) +
      (∑ r, (coordPartial d (christoffel g r k j) p * g p i r +
        christoffel g r k j p * coordPartial d (fun q => g q i r) p)) := by
  have heq : coordPartial k (fun q => g q i j) =ᶠ[𝓝 p]
      (fun q => (∑ r, christoffel g r k i q * g q r j) +
        (∑ r, christoffel g r k j q * g q i r)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_compatibility hg hU hq k i j
  have hdg (a b : Fin 2) : DifferentiableAt ℝ (fun q => g q a b) p :=
    (((hg.1 a b) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdΓ (a b c : Fin 2) : DifferentiableAt ℝ (christoffel g a b c) p :=
    (((christoffel_contDiffOn hg hU a b c) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hA (r : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g r k i q * g q r j) p := (hdΓ r k i).mul (hdg r j)
  have hB (r : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g r k j q * g q i r) p := (hdΓ r k j).mul (hdg i r)
  change fderiv ℝ (coordPartial k (fun q => g q i j)) p (Pi.single d 1) = _
  rw [heq.fderiv_eq]
  change coordPartial d (fun q => (∑ r, christoffel g r k i q * g q r j) +
    (∑ r, christoffel g r k j q * g q i r)) p = _
  rw [HessianCalculus.coordPartial_add_at
      (DifferentiableAt.fun_sum fun r _ => hA r)
      (DifferentiableAt.fun_sum fun r _ => hB r) d,
    HessianCalculus.coordPartial_sum_two _ hA d,
    HessianCalculus.coordPartial_sum_two _ hB d]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _
    exact HessianCalculus.coordPartial_mul_at (hdΓ r k i) (hdg r j) d
  · apply Finset.sum_congr rfl
    intro r _
    exact HessianCalculus.coordPartial_mul_at (hdΓ r k j) (hdg i r) d

def loweredRiemann (g : MetricField) (l k i j : Fin 2) (p : Coord) : ℝ :=
  ∑ r, g p l r * riemann g r k i j p

theorem loweredRiemann_skew_last (g : MetricField) (l k i j : Fin 2) (p : Coord) :
    loweredRiemann g l k i j p = -loweredRiemann g l k j i p := by
  simp only [loweredRiemann, riemann, Fin.sum_univ_two]
  ring

theorem loweredRiemann_skew_first_add (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p + loweredRiemann g k l i j p = 0 := by
  have hc := coordPartial_comm (hg.1 k l) hU hp i j
  rw [metric_second_compatibility hg hU hp i j k l,
    metric_second_compatibility hg hU hp j i k l] at hc
  simp only [metric_compatibility hg hU hp, Fin.sum_univ_two] at hc
  simp only [loweredRiemann, riemann, Fin.sum_univ_two]
  simp only [metric_coeff_symm hg hp] at hc ⊢
  linear_combination hc

theorem loweredRiemann_skew_first (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p = -loweredRiemann g k l i j p := by
  have h := loweredRiemann_skew_first_add hg hU hp l k i j
  linarith

theorem loweredRiemann_self_first (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l i j : Fin 2) : loweredRiemann g l l i j p = 0 := by
  have h := loweredRiemann_skew_first_add hg hU hp l l i j
  linarith

theorem loweredRiemann_self_last (g : MetricField) (l k i : Fin 2) (p : Coord) :
    loweredRiemann g l k i i p = 0 := by
  have h := loweredRiemann_skew_last g l k i i p
  linarith

theorem loweredRiemann_0101 (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    loweredRiemann g 0 1 0 1 p = gaussianCurvature g p * (g p).det := by
  unfold loweredRiemann gaussianCurvature
  rw [div_mul_cancel₀ _ (metricDet_ne_zero hg hp)]

theorem loweredRiemann_factorization (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p = gaussianCurvature g p *
      (g p l i * g p j k - g p l j * g p i k) := by
  have h10 (a b : Fin 2) : loweredRiemann g 1 0 a b p = -loweredRiemann g 0 1 a b p :=
    loweredRiemann_skew_first hg hU hp 1 0 a b
  have hrev : loweredRiemann g 0 1 1 0 p = -loweredRiemann g 0 1 0 1 p :=
    loweredRiemann_skew_last g 0 1 1 0 p
  have hsym : g p 1 0 = g p 0 1 := metric_coeff_symm hg hp 1 0
  fin_cases l <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, loweredRiemann_self_first hg hU hp, loweredRiemann_self_last,
      h10, hrev, loweredRiemann_0101 hg hp, Matrix.det_fin_two, hsym] <;> ring

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
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace AffineCalculus

theorem coordPartial_const_mul_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => c * f q) p = c * coordPartial i f p := by
  simp [coordPartial, fderiv_const_mul hf]

theorem coordPartial_mul_const_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => f q * c) p = coordPartial i f p * c := by
  simpa only [mul_comm] using coordPartial_const_mul_at hf c i

end AffineCalculus

theorem coordPartial_affine_comp {f : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hf : DifferentiableAt ℝ f (affineCoordinates b R q)) (i : Fin 2) :
    coordPartial i (f ∘ affineCoordinates b R) q =
      ∑ a, R a i * coordPartial a f (affineCoordinates b R q) := by
  change fderiv ℝ (f ∘ affineCoordinates b R) q (Pi.single i 1) = _
  rw [fderiv_affine_comp_apply b R q (Pi.single i 1) hf,
    matrix_column_basis_expansion R i]
  simp only [map_add, map_smul, smul_eq_mul, Fin.sum_univ_two, coordPartial]

theorem coordPartial_affinePullbackMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (k i j : Fin 2) :
    coordPartial k (fun p => affinePullbackMetric g b R p i j) q =
      ∑ a, ∑ c, ∑ d, R a i * R c j * R d k *
        coordPartial d (fun p => g p a c) (affineCoordinates b R q) := by
  have hd (a c : Fin 2) : DifferentiableAt ℝ (fun p => g p a c)
      (affineCoordinates b R q) :=
    (((hg.1 a c) _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  have hdc (a c : Fin 2) : DifferentiableAt ℝ
      (fun p => g (affineCoordinates b R p) a c) q :=
    (hd a c).comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have hs (c : Fin 2) : DifferentiableAt ℝ
      (fun p => ∑ a, R a i * g (affineCoordinates b R p) a c) q :=
    DifferentiableAt.fun_sum fun a _ => (hdc a c).const_mul (R a i)
  have hchain (a c : Fin 2) :
      coordPartial k (fun p => g (affineCoordinates b R p) a c) q =
        ∑ d, R d k * coordPartial d (fun p => g p a c) (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q (hd a c) k
  simp only [affinePullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
  rw [HessianCalculus.coordPartial_sum_two _
    (fun c => (hs c).mul_const (R c j)) k]
  simp_rw [AffineCalculus.coordPartial_mul_const_at (hs _) _ k,
    HessianCalculus.coordPartial_sum_two _
      (fun a => (hdc a _).const_mul (R a i)) k,
    AffineCalculus.coordPartial_const_mul_at (hdc _ _) _ k,
    hchain]
  simp only [Fin.sum_univ_two]
  ring

theorem christoffelFirstKind_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (i j l : Fin 2) :
    christoffelFirstKind (affinePullbackMetric g b R) i j q l =
      ∑ a, ∑ c, ∑ d, R a l * R c i * R d j *
        christoffelFirstKind g c d (affineCoordinates b R q) a := by
  simp only [christoffelFirstKind, coordPartial_affinePullbackMetric hg hU b R q hq,
    Fin.sum_univ_two]
  ring

theorem christoffel_affinePullback_push {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a i j : Fin 2) :
    (∑ l, R a l * christoffel (affinePullbackMetric g b R) l i j q) =
      ∑ c, ∑ d, R c i * R d j * christoffel g a c d (affineCoordinates b R q) := by
  have hRinj : Function.Injective R.mulVec := Matrix.mulVec_injective_of_isUnit hR
  have hgR := affinePullbackMetric_smoothPositive hg b R hRinj
  have hRt : IsUnit Rᵀ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hR
  have hlower (l c d : Fin 2) :
      christoffelFirstKind g c d (affineCoordinates b R q) l =
        ∑ r, g (affineCoordinates b R q) l r *
          christoffel g r c d (affineCoordinates b R q) :=
    (congrFun (metric_mul_christoffel hg hq c d) l).symm
  have heq :
      (Rᵀ * g (affineCoordinates b R q)) *ᵥ
        (R *ᵥ (fun l => christoffel (affinePullbackMetric g b R) l i j q)) =
      (Rᵀ * g (affineCoordinates b R q)) *ᵥ
        (fun r => ∑ c, ∑ d, R c i * R d j *
          christoffel g r c d (affineCoordinates b R q)) := by
    rw [Matrix.mulVec_mulVec]
    change affinePullbackMetric g b R q *ᵥ
      (fun l => christoffel (affinePullbackMetric g b R) l i j q) = _
    rw [metric_mul_christoffel hgR hq i j]
    ext l
    rw [christoffelFirstKind_affinePullback hg hU b R q hq]
    simp only [hlower, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, Fin.sum_univ_two]
    ring
  have hv := Matrix.mulVec_injective_of_isUnit
    (hRt.mul (hg.2 (affineCoordinates b R q) hq).isUnit) heq
  exact congrFun hv a

end SmoothLocal.Geometry

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

def stateMixed (g : MetricField) (w : DarbouxState) : ℝ :=
  jetMixed g (statePoint w) (w 4) (stateGradient w)

def stateDenominator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetYY g (statePoint w) (w 5) (stateGradient w)

def stateNumerator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetNumerator g (statePoint w) (w 4) (stateGradient w)

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

theorem stateMixed_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateMixed g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 4 _).sub (stateConnection_contDiffOn hg hU 0 1)

theorem stateDenominator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 1 1)

theorem stateEnergy_contDiffOn (hg : SmoothPositiveOn g U) :
    ContDiffOn ℝ ∞ (stateEnergy g) (stateBaseDomain U) := by
  have hcoef (i j : Fin 2) : ContDiffOn ℝ ∞ (fun w => g (statePoint w) i j) (stateBaseDomain U) :=
    (hg.1 i j).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have hdet : ContDiffOn ℝ ∞ (fun w => (g (statePoint w)).det) (stateBaseDomain U) :=
    (metricDet_contDiffOn hg).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have hv (i : Fin 2) : ContDiffOn ℝ ∞ (fun w => stateGradient w i) (stateBaseDomain U) :=
    ((contDiff_apply ℝ ℝ i).comp stateGradient_contDiff).contDiffOn
  exact hdet.sub ((((hcoef 1 1).mul ((hv 0).pow 2)).sub
    ((((hcoef 0 1).add (hcoef 1 0)).mul (hv 0)).mul (hv 1))).add
      ((hcoef 0 0).mul ((hv 1).pow 2)))

theorem stateNumerator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateNumerator g) (stateBaseDomain U) :=
  ((stateMixed_contDiffOn hg hU).pow 2).add
    (((gaussianCurvature_contDiffOn hg hU).comp statePoint_contDiff.contDiffOn
      (fun _ hw => hw)).mul (stateEnergy_contDiffOn hg))

theorem darbouxStateDomain_isOpen (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    IsOpen (darbouxStateDomain g U) := by
  exact (stateDenominator_contDiffOn hg hU).continuousOn.isOpen_inter_preimage
    (stateBaseDomain_isOpen hU) isClosed_singleton.isOpen_compl

theorem sixVariableP_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sixVariableP g) (darbouxStateDomain g U) := by
  have hsub : darbouxStateDomain g U ⊆ stateBaseDomain U := fun w hw => hw.1
  exact ((stateConnection_contDiffOn hg hU 0 0).mono hsub).add
    (((stateNumerator_contDiffOn hg hU).mono hsub).div
      ((stateDenominator_contDiffOn hg hU).mono hsub) (fun w hw => hw.2))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace AffineCalculus

theorem coordPartial_sum_const_mul (f : Fin 2 → Coord → ℝ) (c : Fin 2 → ℝ)
    {p : Coord} (hf : ∀ a, DifferentiableAt ℝ (f a) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, c a * f a q) p =
      ∑ a, c a * coordPartial i (f a) p := by
  rw [HessianCalculus.coordPartial_sum_two _ (fun a => (hf a).const_mul (c a)) i]
  apply Finset.sum_congr rfl
  intro a _
  exact coordPartial_const_mul_at (hf a) (c a) i

theorem coordPartial_double_sum_const_mul
    (f : Fin 2 → Fin 2 → Coord → ℝ) (c : Fin 2 → Fin 2 → ℝ)
    {p : Coord} (hf : ∀ a b, DifferentiableAt ℝ (f a b) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, ∑ b, c a b * f a b q) p =
      ∑ a, ∑ b, c a b * coordPartial i (f a b) p := by
  rw [HessianCalculus.coordPartial_sum_two _
    (fun a => DifferentiableAt.fun_sum fun b _ => (hf a b).const_mul (c a b)) i]
  apply Finset.sum_congr rfl
  intro a _
  exact coordPartial_sum_const_mul (f a) (c a) (hf a) i

theorem pushed_connection_product
    (R : Matrix (Fin 2) (Fin 2) ℝ)
    (C D : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (h : ∀ a i j, (∑ l, R a l * C l i j) = ∑ c, ∑ d, R c i * R d j * D a c d)
    (a i j k : Fin 2) :
    (∑ l, R a l * ∑ m, C m j k * C l i m) =
      ∑ c, ∑ d, ∑ e, ∑ f, R c i * R e j * R f k * D d e f * D a c d := by
  calc
    _ = ∑ m, C m j k * (∑ l, R a l * C l i m) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ m, C m j k * (∑ c, ∑ d, R c i * R d m * D a c d) := by
      simp only [h]
    _ = ∑ c, ∑ d, R c i * D a c d * (∑ m, R d m * C m j k) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ c, ∑ d, R c i * D a c d *
        (∑ e, ∑ f, R e j * R f k * D d e f) := by simp only [h]
    _ = _ := by simp only [Fin.sum_univ_two]; ring

end AffineCalculus

theorem coordPartial_christoffel_affinePullback_push
    {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a i j k : Fin 2) :
    (∑ l, R a l * coordPartial i (christoffel (affinePullbackMetric g b R) l j k) q) =
      ∑ c, ∑ d, ∑ e, R c j * R d k * R e i *
        coordPartial e (christoffel g a c d) (affineCoordinates b R q) := by
  have hV := isOpen_affine_preimage hU b R
  have hgR := affinePullbackMetric_smoothPositive hg b R
    (Matrix.mulVec_injective_of_isUnit hR)
  have hL (l : Fin 2) : DifferentiableAt ℝ
      (christoffel (affinePullbackMetric g b R) l j k) q :=
    (((christoffel_contDiffOn hgR hV l j k) q hq).contDiffAt
      (hV.mem_nhds hq)).differentiableAt (by simp)
  have hG (c d : Fin 2) : DifferentiableAt ℝ (christoffel g a c d)
      (affineCoordinates b R q) :=
    (((christoffel_contDiffOn hg hU a c d) _ hq).contDiffAt
      (hU.mem_nhds hq)).differentiableAt (by simp)
  have hGc (c d : Fin 2) : DifferentiableAt ℝ
      (fun p => christoffel g a c d (affineCoordinates b R p)) q :=
    (hG c d).comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have hchain (c d : Fin 2) :
      coordPartial i (fun p => christoffel g a c d (affineCoordinates b R p)) q =
        ∑ e, R e i * coordPartial e (christoffel g a c d) (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q (hG c d) i
  have heq : (fun p => ∑ l, R a l *
      christoffel (affinePullbackMetric g b R) l j k p) =ᶠ[𝓝 q]
      (fun p => ∑ c, ∑ d, R c j * R d k *
        christoffel g a c d (affineCoordinates b R p)) := by
    filter_upwards [hV.mem_nhds hq] with p hp
    exact christoffel_affinePullback_push hg hU b R hR p hp a j k
  calc
    _ = coordPartial i (fun p => ∑ l, R a l *
        christoffel (affinePullbackMetric g b R) l j k p) q :=
      (AffineCalculus.coordPartial_sum_const_mul _ _ hL i).symm
    _ = coordPartial i (fun p => ∑ c, ∑ d, R c j * R d k *
        christoffel g a c d (affineCoordinates b R p)) q := by
      unfold coordPartial
      rw [heq.fderiv_eq]
    _ = ∑ c, ∑ d, (R c j * R d k) * coordPartial i
        (fun p => christoffel g a c d (affineCoordinates b R p)) q :=
      AffineCalculus.coordPartial_double_sum_const_mul _ _ hGc i
    _ = _ := by
      simp_rw [hchain]
      simp only [Fin.sum_univ_two]
      ring

theorem riemann_affinePullback_push {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a k i j : Fin 2) :
    (∑ l, R a l * riemann (affinePullbackMetric g b R) l k i j q) =
      ∑ c, ∑ d, ∑ e, R c k * R d i * R e j *
        riemann g a c d e (affineCoordinates b R q) := by
  let C := fun a i j => christoffel (affinePullbackMetric g b R) a i j q
  let D := fun a i j => christoffel g a i j (affineCoordinates b R q)
  have hp (a i j : Fin 2) : (∑ l, R a l * C l i j) =
      ∑ c, ∑ d, R c i * R d j * D a c d :=
    christoffel_affinePullback_push hg hU b R hR q hq a i j
  calc
    _ = (∑ l, R a l * coordPartial i
          (christoffel (affinePullbackMetric g b R) l j k) q) -
        (∑ l, R a l * coordPartial j
          (christoffel (affinePullbackMetric g b R) l i k) q) +
        (∑ l, R a l * ∑ m, C m j k * C l i m) -
        (∑ l, R a l * ∑ m, C m i k * C l j m) := by
      simp only [riemann, C, Fin.sum_univ_two]
      ring
    _ = (∑ c, ∑ d, ∑ e, R c j * R d k * R e i *
          coordPartial e (christoffel g a c d) (affineCoordinates b R q)) -
        (∑ c, ∑ d, ∑ e, R c i * R d k * R e j *
          coordPartial e (christoffel g a c d) (affineCoordinates b R q)) +
        (∑ c, ∑ d, ∑ e, ∑ f, R c i * R e j * R f k * D d e f * D a c d) -
        (∑ c, ∑ d, ∑ e, ∑ f, R c j * R e i * R f k * D d e f * D a c d) := by
      rw [coordPartial_christoffel_affinePullback_push hg hU b R hR q hq a i j k,
        coordPartial_christoffel_affinePullback_push hg hU b R hR q hq a j i k,
        AffineCalculus.pushed_connection_product R C D hp a i j k,
        AffineCalculus.pushed_connection_product R C D hp a j i k]
    _ = _ := by
      simp only [riemann, D, Fin.sum_univ_two]
      ring

theorem loweredRiemann_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (l k i j : Fin 2) :
    loweredRiemann (affinePullbackMetric g b R) l k i j q =
      ∑ a, ∑ c, ∑ d, ∑ e, R a l * R c k * R d i * R e j *
        loweredRiemann g a c d e (affineCoordinates b R q) := by
  calc
    _ = ∑ a, ∑ c, R a l * g (affineCoordinates b R q) a c *
        (∑ r, R c r * riemann (affinePullbackMetric g b R) r k i j q) := by
      simp only [loweredRiemann, affinePullbackMetric, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_two]
      ring
    _ = ∑ a, ∑ c, R a l * g (affineCoordinates b R q) a c *
        (∑ d, ∑ e, ∑ f, R d k * R e i * R f j *
          riemann g c d e f (affineCoordinates b R q)) := by
      simp_rw [riemann_affinePullback_push hg hU b R hR q hq]
    _ = _ := by simp only [loweredRiemann, Fin.sum_univ_two]; ring

theorem gaussianCurvature_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    gaussianCurvature (affinePullbackMetric g b R) q =
      gaussianCurvature g (affineCoordinates b R q) := by
  have hgR := affinePullbackMetric_smoothPositive hg b R
    (Matrix.mulVec_injective_of_isUnit hR)
  have hsym : g (affineCoordinates b R q) 1 0 = g (affineCoordinates b R q) 0 1 :=
    metric_coeff_symm hg hq 1 0
  have hlow : loweredRiemann (affinePullbackMetric g b R) 0 1 0 1 q =
      gaussianCurvature g (affineCoordinates b R q) * (affinePullbackMetric g b R q).det := by
    rw [loweredRiemann_affinePullback hg hU b R hR q hq]
    simp only [loweredRiemann_factorization hg hU hq,
      affinePullbackMetric, Matrix.det_fin_two, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two, hsym]
    ring
  change loweredRiemann (affinePullbackMetric g b R) 0 1 0 1 q /
    (affinePullbackMetric g b R q).det = _
  rw [hlow, mul_div_cancel_right₀ _ (metricDet_ne_zero hgR hq)]

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

theorem point_eta (p : Coord) : coordinatePoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem point_hasDerivAt_t (x y : ℝ) :
    HasDerivAt (fun t => coordinatePoint t y) (Pi.single 0 (1 : ℝ) : Coord) x := by
  simpa [coordinatePoint] using
    ((hasDerivAt_id x).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (y • (Pi.single 1 (1 : ℝ) : Coord))

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
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def swapCoordinateIndex (i : Fin 2) : Fin 2 := ![1, 0] i

def coordinateSwap : Coord → Coord := affineCoordinates 0 coordinateSwapMatrix

@[simp] theorem swapCoordinateIndex_zero : swapCoordinateIndex 0 = 1 := rfl
@[simp] theorem swapCoordinateIndex_one : swapCoordinateIndex 1 = 0 := rfl

@[simp] theorem swapCoordinateIndex_involutive (i : Fin 2) :
    swapCoordinateIndex (swapCoordinateIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem coordinateSwap_apply (p : Coord) (i : Fin 2) :
    coordinateSwap p i = p (swapCoordinateIndex i) := by
  fin_cases i <;>
    simp [coordinateSwap, affineCoordinates, coordinateSwapMatrix,
      dotProduct, Fin.sum_univ_two, swapCoordinateIndex]

@[simp] theorem coordinateSwap_involutive (p : Coord) :
    coordinateSwap (coordinateSwap p) = p := by
  ext i
  simp

@[simp] theorem coordinateSwapMatrix_det : coordinateSwapMatrix.det = -1 := by
  norm_num [coordinateSwapMatrix, Matrix.det_fin_two]

theorem coordinateSwapMatrix_isUnit : IsUnit coordinateSwapMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, coordinateSwapMatrix_det]
  exact isUnit_neg_one

theorem coordinateSwap_contDiff : ContDiff ℝ ∞ coordinateSwap :=
  affineCoordinates_contDiff 0 coordinateSwapMatrix

theorem coordinateSwap_preimage_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (coordinateSwap ⁻¹' U) :=
  hU.preimage coordinateSwap_contDiff.continuous

theorem swappedMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    SmoothPositiveOn (swappedMetric g) (coordinateSwap ⁻¹' U) :=
  affinePullbackMetric_smoothPositive hg 0 coordinateSwapMatrix
    (Matrix.mulVec_injective_of_isUnit coordinateSwapMatrix_isUnit)

@[simp] theorem swappedMetric_apply (g : MetricField) (p : Coord) (i j : Fin 2) :
    swappedMetric g p i j =
      g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) := by
  fin_cases i <;> fin_cases j <;>
    simp [swappedMetric, affinePullbackMetric, coordinateSwapMatrix,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      coordinateSwap, swapCoordinateIndex]

@[simp] theorem swappedMetric_det (g : MetricField) (p : Coord) :
    (swappedMetric g p).det = (g (coordinateSwap p)).det := by
  simp only [Matrix.det_fin_two, swappedMetric_apply,
    swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem gaussianCurvature_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) :
    gaussianCurvature (swappedMetric g) p = gaussianCurvature g (coordinateSwap p) :=
  gaussianCurvature_affinePullback hg hU 0 coordinateSwapMatrix
    coordinateSwapMatrix_isUnit p hp

theorem christoffel_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (k i j : Fin 2) :
    christoffel (swappedMetric g) k i j p =
      christoffel g (swapCoordinateIndex k) (swapCoordinateIndex i)
        (swapCoordinateIndex j) (coordinateSwap p) := by
  have h := christoffel_affinePullback_push hg hU 0 coordinateSwapMatrix
    coordinateSwapMatrix_isUnit p hp (swapCoordinateIndex k) i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simpa [coordinateSwapMatrix, swapCoordinateIndex, Fin.sum_univ_two,
      swappedMetric, coordinateSwap] using h

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

theorem iteratedDeriv_state_eval {f : ℝ → DarbouxState} {y : ℝ}
    (hf : ContDiffAt ℝ ∞ f y) (n : ℕ) (i : Fin 6) :
    (iteratedDeriv n f y) i = iteratedDeriv n (fun t => f t i) y := by
  let L : DarbouxState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  symm
  change iteratedFDeriv ℝ n (L ∘ f) y (fun _ => 1) = L (iteratedDeriv n f y)
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation

def ChainWord.total (w : ChainWord) : ℕ := ∑ i, w.order i

def ChainWord.Positive (w : ChainWord) : Prop := ∀ i, 0 < w.order i

def ChainWord.Bounded (w : ChainWord) (n : ℕ) : Prop := ∀ i, w.order i ≤ n

theorem ChainWord.prepend_positive {w : ChainWord} (hw : w.Positive) :
    w.prepend.Positive := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Nat.zero_lt_one
  · exact hw j

theorem ChainWord.bump_positive {w : ChainWord} (hw : w.Positive) (i : Fin w.arity) :
    (w.bump i).Positive := by
  change ∀ j : Fin w.arity, 0 < Function.update w.order i (w.order i + 1) j
  intro j
  by_cases hj : j = i
  · subst j; simp
  · rw [Function.update_of_ne hj]
    exact hw j

theorem ChainWord.prepend_total (w : ChainWord) : w.prepend.total = w.total + 1 := by
  change (∑ j : Fin (w.arity + 1), Fin.cons 1 w.order j) = (∑ j : Fin w.arity, w.order j) + 1
  simp [Fin.sum_univ_succ, Nat.add_comm]

theorem ChainWord.bump_total (w : ChainWord) (i : Fin w.arity) :
    (w.bump i).total = w.total + 1 := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin w.arity)) := Finset.mem_univ i
  have hsum := Finset.sum_update_of_mem hi w.order (w.order i + 1)
  simp only [Finset.sdiff_singleton_eq_erase] at hsum
  change (∑ j : Fin w.arity, Function.update w.order i (w.order i + 1) j) =
    (∑ j : Fin w.arity, w.order j) + 1
  rw [hsum]
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin w.arity)) w.order hi
  omega

theorem ChainWord.prepend_bounded {w : ChainWord} {n : ℕ}
    (hn : 1 ≤ n) (hw : w.Bounded n) : w.prepend.Bounded n := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hn
  · exact hw j

theorem ChainWord.bump_bounded {w : ChainWord} {n : ℕ}
    (hw : w.Bounded n) (i : Fin w.arity) : (w.bump i).Bounded (n + 1) := by
  change ∀ j : Fin w.arity, Function.update w.order i (w.order i + 1) j ≤ n + 1
  intro j
  by_cases hj : j = i
  · subst j
    simpa [ChainWord.bump] using Nat.add_le_add_right (hw i) 1
  · rw [Function.update_of_ne hj]
    exact Nat.le_succ_of_le (hw j)

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
open SmoothLocal.Geometry

abbrev MetricPInput := MetricMatrix × (MetricFirstJet × (MetricSecondJet × DarbouxState))

def universalConnection (a : MetricPInput) (i j : Fin 2) : ℝ :=
  ∑ k, christoffelJet a.1 a.2.1 k i j * stateGradient a.2.2.2 k

def universalEnergy (a : MetricPInput) : ℝ :=
  a.1.det - (a.1 1 1 * (stateGradient a.2.2.2 0)^2 -
    (a.1 0 1 + a.1 1 0) * stateGradient a.2.2.2 0 * stateGradient a.2.2.2 1 +
    a.1 0 0 * (stateGradient a.2.2.2 1)^2)

def universalMetricBase : Set MetricPInput := {a | a.1.det ≠ 0}

def metricPBundle (g : MetricField) (w : DarbouxState) : MetricPInput :=
  (g (statePoint w),
    ((fun d i j => coordPartial d (fun p => g p i j) (statePoint w)),
      ((fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w)), w)))

theorem universalConnection_metricPBundle (g : MetricField) (w : DarbouxState)
    (i j : Fin 2) :
    universalConnection (metricPBundle g w) i j = stateConnection g i j w := rfl

theorem universalEnergy_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalEnergy (metricPBundle g w) = stateEnergy g w := rfl

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

theorem universalEnergy_contDiff : ContDiff ℝ ∞ universalEnergy := by
  unfold universalEnergy stateGradient
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Matrix.det_fin_two]
  fun_prop

def universalMetricBaseTube (M d : ℝ) : Set MetricPInput :=
  Metric.closedBall 0 M ∩ (fun a : MetricPInput => |a.1.det|) ⁻¹' Ici d

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

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def solvedDarbouxQ (g : MetricField) (p : Coord) (b c : ℝ) (u : Coord) : ℝ :=
  jetConnection g p 1 1 u + jetNumerator g p b u / jetXX g p c u

theorem jetConnection_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (i j : Fin 2) (u : Coord) :
    jetConnection (swappedMetric g) p i j (coordinateSwap u) =
      jetConnection g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) u := by
  simp only [jetConnection, christoffel_swappedMetric hg hU hp,
    coordinateSwap_apply, Fin.sum_univ_two, swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem jetMixed_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b : ℝ) (u : Coord) :
    jetMixed (swappedMetric g) p b (coordinateSwap u) =
      jetMixed g (coordinateSwap p) b u := by
  have hs (k : Fin 2) : christoffel g k 1 0 (coordinateSwap p) =
      christoffel g k 0 1 (coordinateSwap p) := christoffel_lower_symm hg hU hp k 1 0
  rw [jetMixed, jetConnection_swappedMetric hg hU hp]
  simp only [swapCoordinateIndex_zero, swapCoordinateIndex_one]
  simp only [jetConnection, hs, jetMixed]

theorem jetYY_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (c : ℝ) (u : Coord) :
    jetYY (swappedMetric g) p c (coordinateSwap u) =
      jetXX g (coordinateSwap p) c u := by
  rw [jetYY, jetConnection_swappedMetric hg hU hp]
  rfl

theorem jetEnergy_swappedMetric (g : MetricField) (p u : Coord) :
    jetEnergy (swappedMetric g) p (coordinateSwap u) =
      jetEnergy g (coordinateSwap p) u := by
  simp only [jetEnergy, swappedMetric_det, swappedMetric_apply, coordinateSwap_apply,
    swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem jetNumerator_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b : ℝ) (u : Coord) :
    jetNumerator (swappedMetric g) p b (coordinateSwap u) =
      jetNumerator g (coordinateSwap p) b u := by
  rw [jetNumerator, jetMixed_swappedMetric hg hU hp,
    gaussianCurvature_swappedMetric hg hU hp, jetEnergy_swappedMetric]
  rfl

theorem solvedDarboux_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (b c : ℝ) (u : Coord) :
    solvedDarboux (swappedMetric g) p b c (coordinateSwap u) =
      solvedDarbouxQ g (coordinateSwap p) b c u := by
  rw [solvedDarboux, jetConnection_swappedMetric hg hU hp,
    jetNumerator_swappedMetric hg hU hp, jetYY_swappedMetric hg hU hp]
  rfl

theorem solvedDarbouxQ_eq_swappedP {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ U) (b c : ℝ) (u : Coord) :
    solvedDarbouxQ g p b c u =
      solvedDarboux (swappedMetric g) (coordinateSwap p) b c (coordinateSwap u) := by
  simpa only [coordinateSwap_involutive] using
    (solvedDarboux_swappedMetric hg hU (p := coordinateSwap p) (by simpa using hp) b c u).symm

theorem jetXX_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetXX g p (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 0 := rfl

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

theorem ChainWord.children_properties {w v : ChainWord} {n : ℕ}
    (hn : 1 ≤ n) (hp : w.Positive) (hb : w.Bounded n) (hv : v ∈ w.children) :
    v.Positive ∧ v.total = w.total + 1 ∧ v.Bounded (n + 1) := by
  simp only [ChainWord.children, List.mem_cons, List.mem_ofFn] at hv
  rcases hv with rfl | ⟨i, rfl⟩
  · refine ⟨ChainWord.prepend_positive hp, w.prepend_total, ?_⟩
    exact ChainWord.prepend_bounded (by omega) (fun j => Nat.le_succ_of_le (hb j))
  · exact ⟨ChainWord.bump_positive hp i, w.bump_total i,
      ChainWord.bump_bounded hb i⟩

theorem topResidualWords_properties : ∀ m w, w ∈ topResidualWords m →
    w.Positive ∧ w.total = m + 3 ∧ w.Bounded (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro w hw
    simp only [topResidualWords, List.mem_singleton] at hw
    subst w
    refine ⟨?_, ?_, ?_⟩
    · change ∀ i : Fin 3, 0 < (![1, 1, 1] : Fin 3 → ℕ) i
      intro i; fin_cases i <;> norm_num
    · change (∑ i : Fin 3, (![1, 1, 1] : Fin 3 → ℕ) i) = 0 + 3
      norm_num [Fin.sum_univ_succ]
    · change ∀ i : Fin 3, (![1, 1, 1] : Fin 3 → ℕ) i ≤ 0 + 1
      intro i; fin_cases i <;> norm_num
  | succ m ih =>
    intro w hw
    change w ∈ ((topResidualWords m).flatMap ChainWord.children ++
      List.replicate (m + 3) (ChainWord.triple 1 1 (m + 2))) ++
      List.replicate (m + 3) (ChainWord.pair 2 (m + 2)) at hw
    rw [List.mem_append, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · obtain ⟨v, hv, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨hp, ht, hb⟩ := ih v hv
      obtain ⟨hwp, hwt, hwb⟩ := ChainWord.children_properties (by omega) hp hb hw
      refine ⟨hwp, ?_, ?_⟩
      · omega
      · simpa [Nat.add_assoc] using hwb
    · have he := List.eq_of_mem_replicate hw
      subst w
      refine ⟨?_, ?_, ?_⟩
      · change ∀ i : Fin 3, 0 < (![1, 1, m + 2] : Fin 3 → ℕ) i
        intro i; fin_cases i <;> simp
      · change (∑ i : Fin 3, (![1, 1, m + 2] : Fin 3 → ℕ) i) = m + 1 + 3
        simp [Fin.sum_univ_succ]; omega
      · change ∀ i : Fin 3, (![1, 1, m + 2] : Fin 3 → ℕ) i ≤ m + 1 + 1
        intro i; fin_cases i <;> simp
    · have he := List.eq_of_mem_replicate hw
      subst w
      refine ⟨?_, ?_, ?_⟩
      · change ∀ i : Fin 2, 0 < (![2, m + 2] : Fin 2 → ℕ) i
        intro i; fin_cases i <;> simp
      · change (∑ i : Fin 2, (![2, m + 2] : Fin 2 → ℕ) i) = m + 1 + 3
        simp [Fin.sum_univ_succ]; omega
      · change ∀ i : Fin 2, (![2, m + 2] : Fin 2 → ℕ) i ≤ m + 1 + 1
        intro i; fin_cases i <;> simp

theorem topResidual_high_unique {m : ℕ} (hm : 8 ≤ m + 3)
    {w : ChainWord} (hw : w ∈ topResidualWords m) (base : Fin w.arity → ℕ)
    (hb : ∀ i, base i ≤ 2) {i j : Fin w.arity}
    (hi : m + 2 ≤ w.order i + base i) (hj : m + 2 ≤ w.order j + base j) : i = j := by
  classical
  by_contra hij
  have hsum := (topResidualWords_properties m w hw).2.1
  have hpair : w.order i + w.order j ≤ w.total := by
    have hh : ∑ k ∈ ({i, j} : Finset (Fin w.arity)), w.order k ≤ ∑ k, w.order k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    simpa [ChainWord.total, Finset.sum_pair hij] using hh
  have hbi := hb i
  have hbj := hb j
  omega

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

end FiniteProducts

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

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qToPStateLinear : DarbouxState →ₗ[ℝ] DarbouxState where
  toFun := qToPState
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def qToPStateCLM : DarbouxState →L[ℝ] DarbouxState :=
  LinearMap.toContinuousLinearMap qToPStateLinear

@[simp] theorem qToPStateCLM_apply (w : DarbouxState) : qToPStateCLM w = qToPState w := rfl

@[simp] theorem qToPStateIndex_involutive (i : Fin 6) :
    qToPStateIndex (qToPStateIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem qToPState_involutive (w : DarbouxState) : qToPState (qToPState w) = w := by
  ext i
  exact congrArg w (qToPStateIndex_involutive i)

theorem qToPState_contDiff : ContDiff ℝ ∞ qToPState := qToPStateCLM.contDiff

@[simp] theorem statePoint_qToPState (w : DarbouxState) :
    statePoint (qToPState w) = coordinateSwap (statePoint w) := by
  ext i
  fin_cases i <;> simp [statePoint, qToPState, qToPStateIndex]

@[simp] theorem stateGradient_qToPState (w : DarbouxState) :
    stateGradient (qToPState w) = coordinateSwap (stateGradient w) := by
  ext i
  fin_cases i <;> simp [stateGradient, qToPState, qToPStateIndex]

@[simp] theorem qToPState_four (w : DarbouxState) : qToPState w 4 = w 4 := rfl
@[simp] theorem qToPState_five (w : DarbouxState) : qToPState w 5 = w 5 := rfl

def darbouxQStateDomain (g : MetricField) (U : Set Coord) : Set DarbouxState :=
  {w | statePoint w ∈ U ∧ stateQDenominator g w ≠ 0}

theorem stateDenominator_qToPState {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    stateDenominator (swappedMetric g) (qToPState w) = stateQDenominator g w := by
  unfold stateDenominator
  rw [statePoint_qToPState, stateGradient_qToPState, qToPState_five]
  simpa only [stateQDenominator, coordinateSwap_involutive] using
    (jetYY_swappedMetric hg hU (p := coordinateSwap (statePoint w))
      (by simpa using hw) (w 5) (stateGradient w))

theorem sixVariableQ_explicit {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableQ g w =
      solvedDarbouxQ g (statePoint w) (w 4) (w 5) (stateGradient w) := by
  unfold sixVariableQ sixVariableP
  simp only [Function.comp_apply, statePoint_qToPState, stateGradient_qToPState,
    qToPState_four, qToPState_five]
  exact (solvedDarbouxQ_eq_swappedP hg hU hw (w 4) (w 5) (stateGradient w)).symm

theorem darbouxQStateDomain_eq_preimage {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    darbouxQStateDomain g U =
      qToPState ⁻¹' darbouxStateDomain (swappedMetric g) (coordinateSwap ⁻¹' U) := by
  ext w
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · simpa only [Set.mem_preimage, statePoint_qToPState, coordinateSwap_involutive] using hw.1
    · simpa only [stateDenominator_qToPState hg hU hw.1] using hw.2
  · intro hw
    have hp : statePoint w ∈ U := by
      simpa only [Set.mem_preimage, statePoint_qToPState, coordinateSwap_involutive] using hw.1
    exact ⟨hp, by simpa only [stateDenominator_qToPState hg hU hp] using hw.2⟩

theorem qToPState_mem_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    qToPState w ∈ darbouxStateDomain (swappedMetric g) (coordinateSwap ⁻¹' U) := by
  simpa only [darbouxQStateDomain_eq_preimage hg hU, Set.mem_preimage] using hw

theorem darbouxQStateDomain_isOpen {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) : IsOpen (darbouxQStateDomain g U) := by
  rw [darbouxQStateDomain_eq_preimage hg hU]
  exact (darbouxStateDomain_isOpen (swappedMetric_smoothPositive hg)
    (coordinateSwap_preimage_isOpen hU)).preimage qToPState_contDiff.continuous

theorem sixVariableQ_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sixVariableQ g) (darbouxQStateDomain g U) :=
  (sixVariableP_contDiffOn (swappedMetric_smoothPositive hg)
    (coordinateSwap_preimage_isOpen hU)).comp qToPState_contDiff.contDiffOn
      (fun _ hw => qToPState_mem_domain hg hU hw)

theorem statePoint_qSolutionJet (z : Coord → ℝ) (p : Coord) :
    statePoint (qSolutionJet z p) = p := by
  ext i
  fin_cases i <;> rfl

theorem stateGradient_qSolutionJet (z : Coord → ℝ) (p : Coord) :
    stateGradient (qSolutionJet z p) = fun i => coordPartial i z p := by
  ext i
  fin_cases i <;> rfl

theorem stateQDenominator_qSolutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    stateQDenominator g (qSolutionJet z p) = covHessian g z p 0 0 := by
  unfold stateQDenominator
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  exact jetXX_at_height g p z

theorem qSolutionJet_mem_domain {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    qSolutionJet z p ∈ darbouxQStateDomain g U := by
  constructor
  · simpa only [statePoint_qSolutionJet] using hp
  · simpa only [stateQDenominator_qSolutionJet] using hxx

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qFirstCoefficient_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (qFirstCoefficient g i) (darbouxQStateDomain g U) :=
  ((sixVariableQ_contDiffOn hg hU).fderiv_of_isOpen
    (darbouxQStateDomain_isOpen hg hU) (by simp)).clm_apply contDiffOn_const

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Sobolev

theorem spatialJet_contDiffOn {f : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ContDiffOn ℝ ∞ (spatialJet f n) U := by
  induction n with
  | zero => exact hf
  | succ n hn => exact partial_contDiffOn hn hU 0

theorem spatialJet_slice_hasDerivAt
    {f : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) {x theta : ℝ} (hp : coordinatePoint x theta ∈ U) :
    HasDerivAt (fun xi => spatialJet f n (coordinatePoint xi theta))
      (spatialJet f (n + 1) (coordinatePoint x theta)) x := by
  have hd := ((spatialJet_contDiffOn hU hf n).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt x (point_hasDerivAt_t x theta)

theorem smooth_slice_memLp_two
    {f : Coord → ℝ} {U : Set Coord} {left right theta : ℝ}
    (hf : ContinuousOn f U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) :
    MemLp (fun x => f (coordinatePoint x theta)) 2 (volume.restrict (Icc left right)) := by
  have hc : ContinuousOn (fun x => f (coordinatePoint x theta)) (Icc left right) :=
    hf.comp (by unfold coordinatePoint; fun_prop) hseg
  exact (memLp_two_iff_integrable_sq (hc.aestronglyMeasurable measurableSet_Icc)).2
    ((hc.pow 2).integrableOn_compact isCompact_Icc)

theorem interval_square_integral_le_of_eLpNorm
    {f : ℝ → ℝ} {left right : ℝ} {H : ℝ≥0} (hlr : left ≤ right)
    (hf : MemLp f 2 (volume.restrict (Icc left right)))
    (hH : eLpNorm f 2 (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞)) :
    (∫ x in left..right, f x ^ 2) ≤ (H : ℝ) ^ 2 := by
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    integral_square_eq_L2_norm_square hf, Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  have hh := ENNReal.toReal_mono (by simp : (H : ℝ≥0∞) ≠ ⊤) hH
  change (eLpNorm f 2 (volume.restrict (Icc left right))).toReal ≤ (H : ℝ) at hh
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).2 hh

theorem spatialJet_point_bound_from_same_interval_L2
    {f : Coord → ℝ} {U : Set Coord} {left right theta lengthFloor : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (n : ℕ) {H : ℝ≥0}
    (h0 : eLpNorm (fun x => spatialJet f n (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞))
    (h1 : eLpNorm (fun x => spatialJet f (n + 1) (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞))
    {x : ℝ} (hx : x ∈ Icc left right) :
    |spatialJet f n (coordinatePoint x theta)| ≤
      Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ) := by
  have hlr : left < right := by linarith
  have hc0 : ContinuousOn (fun x => spatialJet f n (coordinatePoint x theta)) (Icc left right) :=
    (spatialJet_contDiffOn hU hf n).continuousOn.comp
      (by unfold coordinatePoint; fun_prop) hseg
  have hc1 : ContinuousOn (fun x => spatialJet f (n + 1) (coordinatePoint x theta))
      (Icc left right) :=
    (spatialJet_contDiffOn hU hf (n + 1)).continuousOn.comp
      (by unfold coordinatePoint; fun_prop) hseg
  have hp := interval_point_square_bound hlr hc0 hc1
    (fun x hx => spatialJet_slice_hasDerivAt hU hf n (hseg x hx)) hx
  have h0I := interval_square_integral_le_of_eLpNorm hlr.le
    (smooth_slice_memLp_two (spatialJet_contDiffOn hU hf n).continuousOn hseg) h0
  have h1I := interval_square_integral_le_of_eLpNorm hlr.le
    (smooth_slice_memLp_two (spatialJet_contDiffOn hU hf (n + 1)).continuousOn hseg) h1
  have hinv : 1 / (right - left) ≤ 1 / lengthFloor := by
    exact one_div_le_one_div_of_le hlength hwidth
  have hc : 0 ≤ 1 + 1 / (right - left) := by positivity
  have h0scale := mul_le_mul_of_nonneg_left h0I hc
  have hInvScale := mul_le_mul_of_nonneg_right hinv (sq_nonneg (H : ℝ))
  have hpoint : spatialJet f n (coordinatePoint x theta) ^ 2 ≤
      (2 + 1 / lengthFloor) * (H : ℝ) ^ 2 := by nlinarith
  have hpos : 0 ≤ 2 + 1 / lengthFloor := by positivity
  have hroot := Real.sq_sqrt hpos
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) H.2)).1
  rw [sq_abs, mul_pow, hroot]
  exact hpoint

theorem SpatialSliceL2Bound.pointwise_below_top
    {ι : Type*} {F : ι → Coord → ℝ} {U : Set Coord}
    {theta left right lengthFloor : ℝ} {N : ℕ} {H : ℝ≥0}
    (hL2 : SpatialSliceL2Bound F theta left right N H)
    (hU : IsOpen U) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (i : ι) (n : ℕ) (hn : n + 1 ≤ N) {x : ℝ} (hx : x ∈ Icc left right) :
    |spatialJet (F i) n (coordinatePoint x theta)| ≤
      Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ) :=
  spatialJet_point_bound_from_same_interval_L2 hU (hF i) hseg hlength hwidth n
    (hL2 i n (by omega)) (hL2 i (n + 1) hn) hx

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Analytic

def spatialLowFactorBound (lengthFloor : ℝ) (H : ℝ≥0) : ℝ :=
  max 1 (Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ))

def spatialProductL2Budget (lengthFloor left right : ℝ) (H : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ‖spatialLowFactorBound lengthFloor H ^ n‖ₑ *
    ((H : ℝ≥0∞) + (volume (Icc left right)) ^ (1 / (2 : ℝ)))

theorem spatialProductL2Budget_lt_top (lengthFloor left right : ℝ) (H : ℝ≥0) (n : ℕ) :
    spatialProductL2Budget lengthFloor left right H n < (⊤ : ℝ≥0∞) := by
  unfold spatialProductL2Budget
  rw [Real.volume_Icc]
  finiteness

theorem real_interval_coefficient_eLpNorm_two
    {a f : ℝ → ℝ} {left right C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ x ∈ Icc left right, |a x| ≤ C) :
    eLpNorm' (fun x => a x * f x) (2 : ℝ) (volume.restrict (Icc left right)) ≤
      ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict (Icc left right)) := by
  have hdom : ∀ᵐ x ∂volume.restrict (Icc left right), ‖a x * f x‖ ≤ ‖C * f x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (ha x hx) (abs_nonneg _)
  calc
    _ ≤ eLpNorm' (fun x => C * f x) (2 : ℝ) (volume.restrict (Icc left right)) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f) C (by norm_num)

theorem real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    {coefficient factor : ℝ → ℝ} {left right bound : ℝ} (hbound : 0 ≤ bound)
    (hcoefficient : ∀ point ∈ Icc left right, |coefficient point| ≤ bound)
    (hmeas : AEStronglyMeasurable (fun point => coefficient point * factor point)
      (volume.restrict (Icc left right))) :
    eLpNorm (fun point => coefficient point * factor point) 2
      (volume.restrict (Icc left right)) ≤
      ‖bound‖ₑ * eLpNorm factor 2 (volume.restrict (Icc left right)) := by
  have hfactor : eLpNorm' factor (2 : ℝ) (volume.restrict (Icc left right)) ≤
      eLpNorm factor 2 (volume.restrict (Icc left right)) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
    norm_num
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact (real_interval_coefficient_eLpNorm_two hbound hcoefficient).trans
    (mul_le_mul_right hfactor _)

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem horizontalJet_eq_spatialJet (f : Coord → ℝ) (n : ℕ) :
    horizontalJet f n = spatialJet f n := by
  induction n with
  | zero => rfl
  | succ n hn => simp only [horizontalJet, spatialJet, hn]

theorem horizontalJet_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ n, ContDiffOn ℝ ∞ (horizontalJet f n) U := by
  intro n
  induction n with
  | zero => exact hf
  | succ _ hn => exact normed_coordPartial_contDiffOn hn hU 0

theorem horizontalPoint_contDiff (y : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ => coordinatePoint x y) := by
  unfold coordinatePoint
  fun_prop

theorem horizontalJet_slice_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ)
    (hp : coordinatePoint x y ∈ U) :
    HasDerivAt (fun t => horizontalJet f n (coordinatePoint t y))
      (horizontalJet f (n + 1) (coordinatePoint x y)) x := by
  have hd : DifferentiableAt ℝ (horizontalJet f n) (coordinatePoint x y) :=
    ((horizontalJet_contDiffOn hU hf n).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt x (point_hasDerivAt_t x y)

theorem horizontalJet_slice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (y : ℝ) : ∀ n x, coordinatePoint x y ∈ U →
      iteratedDeriv n (fun t => f (coordinatePoint t y)) x =
        horizontalJet f n (coordinatePoint x y) := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n hn =>
    intro x hx
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t => f (coordinatePoint t y)) =ᶠ[𝓝 x]
        (fun t => horizontalJet f n (coordinatePoint t y)) := by
      filter_upwards [(hU.preimage (horizontalPoint_contDiff y).continuous).mem_nhds hx] with t ht
      exact hn t ht
    rw [heq.deriv_eq]
    exact (horizontalJet_slice_hasDerivAt hU hf n hx).deriv

theorem horizontalJet_coordPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin 2) : ∀ n p, p ∈ U →
      horizontalJet (coordPartial i f) n p = coordPartial i (horizontalJet f n) p := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n hn =>
    intro p hp
    have heq : horizontalJet (coordPartial i f) n =ᶠ[𝓝 p] coordPartial i (horizontalJet f n) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hn q hq
    have hd : coordPartial 0 (horizontalJet (coordPartial i f) n) p =
        coordPartial 0 (coordPartial i (horizontalJet f n)) p :=
      congrArg (fun L : Coord →L[ℝ] V => L (Pi.single 0 1)) heq.fderiv_eq
    change coordPartial 0 (horizontalJet (coordPartial i f) n) p =
      coordPartial i (coordPartial 0 (horizontalJet f n)) p
    rw [hd]
    exact coordPartial_comm (horizontalJet_contDiffOn hU hf n) hU hp 0 i

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def qSolutionJetCurve (z : Coord → ℝ) (y : ℝ) : ℝ → DarbouxState :=
  fun x => qSolutionJet z (coordinatePoint x y)

theorem qSolutionJet_contDiffOn {z : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (qSolutionJet z) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_apply ℝ ℝ 0 U
  · exact contDiffOn_apply ℝ ℝ 1 U
  · exact partial_contDiffOn hz hU 0
  · exact partial_contDiffOn hz hU 1
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0

theorem qSolutionJetCurve_contDiffAt {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U) :
    ContDiffAt ℝ ∞ (qSolutionJetCurve z y) x :=
  ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).comp x
    (horizontalPoint_contDiff y).contDiffAt

theorem sixVariableQ_contDiffAt_solutionJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sixVariableQ g) (qSolutionJet z p) :=
  (sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds (qSolutionJet_mem_domain hp hxx))

theorem qSolutionJetCurve_iteratedDeriv_positive
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (qSolutionJetCurve z y) x =
      ![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n (coordinatePoint x y),
        spatialJet (spatialFirstJet z 1) n (coordinatePoint x y),
        spatialJet (spatialFirstJet z 1) (n + 1) (coordinatePoint x y),
        spatialJet (spatialFirstJet z 0) (n + 1) (coordinatePoint x y)] := by
  have hc := qSolutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · simpa [qSolutionJetCurve, qSolutionJet, coordinatePoint, hn.ne'] using
      (iteratedDeriv_fun_id (n := n) (x := x))
  · simp [qSolutionJetCurve, qSolutionJet, coordinatePoint, iteratedDeriv_const, hn.ne']
  · change iteratedDeriv n (fun t => coordPartial 0 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 0) y n x hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 1) y n x hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0) y n x hp,
      horizontalJet_coordPartial hU (partial_contDiffOn hz hU 1) 0 n _ hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 0 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0) y n x hp,
      horizontalJet_coordPartial hU (partial_contDiffOn hz hU 0) 0 n _ hp,
      horizontalJet_eq_spatialJet]
    rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem finite_state_basis_decomposition (v : DarbouxState) :
    v = ∑ i : Fin 6, v i • (Pi.single i (1 : ℝ) : DarbouxState) := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply, smul_eq_mul]

theorem multilinear_state_components {k : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => DarbouxState) ℝ)
    (v : Fin k → DarbouxState) :
    L v = ∑ r : Fin k → Fin 6,
      L (fun i => Pi.single (r i) (1 : ℝ)) * ∏ i, v i (r i) := by
  classical
  calc
    L v = L (fun i => ∑ j : Fin 6, v i j • (Pi.single j (1 : ℝ) : DarbouxState)) := by
      congr 1
      funext i
      exact finite_state_basis_decomposition (v i)
    _ = ∑ r : Fin k → Fin 6, L (fun i => v i (r i) • Pi.single (r i) (1 : ℝ)) :=
      L.map_sum (fun i j => v i j • (Pi.single j (1 : ℝ) : DarbouxState))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [L.map_smul_univ]
      simp only [smul_eq_mul, mul_comm]

theorem ChainWord.arity_le_total {w : ChainWord} (hw : w.Positive) : w.arity ≤ w.total := by
  have hsum : ∑ _i : Fin w.arity, (1 : ℕ) ≤ ∑ i : Fin w.arity, w.order i :=
    Finset.sum_le_sum (fun index _ => hw index)
  simpa [ChainWord.total] using hsum

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem heightQCoefficient_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (i : Fin 6) :
    ContDiffOn ℝ ∞ (heightQCoefficient g z i) U :=
  (qFirstCoefficient_contDiffOn hg hU i).comp (qSolutionJet_contDiffOn hU hz)
    (fun p hp => qSolutionJet_mem_domain hp (hxx p hp))

theorem second_fderiv_comp_constant_direction_xi
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial 0 J p, v] =
      coordPartial 0 (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) :=
    fderiv_comp p hdF hJ
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def qCoordinateChainCoefficient (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p)
    (fun i => Pi.single (r i) (1 : ℝ))

def qCoordinateChainFactor (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (i : Fin w.arity) (p : Coord) : ℝ :=
  horizontalJet (qSolutionJet z) (w.order i) p (r i)

def qFirstJetOffset : Fin 6 → ℕ := ![0, 0, 0, 0, 1, 1]

def qChainFactorOrder (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) : ℕ :=
  w.order i + qFirstJetOffset (r i)

theorem qFirstJetOffset_le_one (i : Fin 6) : qFirstJetOffset i ≤ 1 := by
  fin_cases i <;> norm_num [qFirstJetOffset]

theorem qCoordinateChainTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    (w : ChainWord) (p : Coord) :
    qCoordinateChainTerm g z w p = ∑ r : Fin w.arity → Fin 6,
      qCoordinateChainCoefficient g z w r p * ∏ i, qCoordinateChainFactor z w r i p :=
  multilinear_state_components _ _

theorem coordinate_qSolutionJet_horizontal_positive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (n : ℕ) (hn : 0 < n) :
    horizontalJet (qSolutionJet z) n p =
      ![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n p, spatialJet (spatialFirstJet z 1) n p,
        spatialJet (spatialFirstJet z 1) (n + 1) p,
        spatialJet (spatialFirstJet z 0) (n + 1) p] := by
  have h := qSolutionJetCurve_iteratedDeriv_positive hU hz
    (x := p 0) (y := p 1) (by simpa only [point_eta] using hp) n hn
  have hs := horizontalJet_slice hU (qSolutionJet_contDiffOn hU hz) (p 1) n (p 0)
    (by simpa only [point_eta] using hp)
  change iteratedDeriv n (qSolutionJetCurve z (p 1)) (p 0) = _ at hs
  rw [hs] at h
  simpa only [point_eta] using h

theorem q_residual_factor_orders {m : ℕ} {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    (∀ i, qChainFactorOrder w r i ≤ m + 2) ∧ w.arity ≤ m + 3 := by
  obtain ⟨hpos, htotal, hbound⟩ := topResidualWords_properties m w hw
  constructor
  · intro i
    have ho := hbound i
    have hb := qFirstJetOffset_le_one (r i)
    unfold qChainFactorOrder
    omega
  · exact htotal ▸ ChainWord.arity_le_total hpos

theorem q_residual_high_unique {m : ℕ} (hm : 8 ≤ m + 3) {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) {i j : Fin w.arity}
    (hi : m + 2 ≤ qChainFactorOrder w r i) (hj : m + 2 ≤ qChainFactorOrder w r j) : i = j :=
  topResidual_high_unique hm hw (fun k => qFirstJetOffset (r k))
    (fun k => (qFirstJetOffset_le_one (r k)).trans (by norm_num)) hi hj

theorem qCoordinateChainFactor_continuousOn
    {z : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) :
    ContinuousOn (qCoordinateChainFactor z w r i) U :=
  (ContinuousLinearMap.proj (r i) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (horizontalJet_contDiffOn hU (qSolutionJet_contDiffOn hU hz) (w.order i)).continuousOn

theorem qCoordinateChainCoefficient_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (qCoordinateChainCoefficient g z w r) U := by
  intro p hp
  have hQ := sixVariableQ_contDiffAt_solutionJet hg hU hp (hxx p hp)
  have houter := (hQ.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).continuousAt
  have hjet := ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).continuousAt
  have heval := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.arity => DarbouxState) ℝ
    (fun i => Pi.single (r i) (1 : ℝ))).continuous.continuousAt
      (x := iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p))
  exact ((heval.comp houter).comp hjet).continuousWithinAt

theorem q_state_factor_low_bound
    {z : Coord → ℝ} {U : Set Coord} {theta left right lengthFloor : ℝ}
    {N : ℕ} {H : ℝ≥0}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (horder : n + qFirstJetOffset k + 1 ≤ N)
    {x : ℝ} (hx : x ∈ Icc left right) :
    ‖horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k‖ ≤
      spatialLowFactorBound lengthFloor H := by
  rw [coordinate_qSolutionJet_horizontal_positive hU hz (hseg x hx) n hn]
  have hB : 1 ≤ spatialLowFactorBound lengthFloor H := le_max_left _ _
  have hf (i : Fin 2) := partial_contDiffOn hz hU i
  have hlow (i : Fin 2) (j : ℕ) (hj : j + 1 ≤ N) :
      ‖spatialJet (spatialFirstJet z i) j (coordinatePoint x theta)‖ ≤
        spatialLowFactorBound lengthFloor H := by
    rw [Real.norm_eq_abs]
    exact (hL2.pointwise_below_top hU hf hseg hlength hwidth i j hj hx).trans (le_max_right _ _)
  fin_cases k
  · by_cases he : n = 1
    · simpa [he] using hB
    · simpa [he] using (zero_le_one.trans hB)
  · simpa using (zero_le_one.trans hB)
  · exact hlow 0 n (by simpa [qFirstJetOffset] using horder)
  · exact hlow 1 n (by simpa [qFirstJetOffset] using horder)
  · exact hlow 1 (n + 1) (by simpa [qFirstJetOffset] using horder)
  · exact hlow 0 (n + 1) (by simpa [qFirstJetOffset] using horder)

theorem q_state_factor_high_eLpNorm
    {z : Coord → ℝ} {U : Set Coord} {theta left right : ℝ} {N : ℕ} {H : ℝ≥0}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (n : ℕ) (hn : 0 < n) (hnlow : n < N) (k : Fin 6)
    (hhigh : N ≤ n + qFirstJetOffset k) (htop : n + qFirstJetOffset k ≤ N) :
    eLpNorm (fun x => horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) := by
  have he : (fun x => horizontalJet (qSolutionJet z) n (coordinatePoint x theta) k) =ᵐ[
      volume.restrict (Icc left right)] (fun x =>
      (![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 1) n (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 1) (n + 1) (coordinatePoint x theta),
        spatialJet (spatialFirstJet z 0) (n + 1) (coordinatePoint x theta)] : DarbouxState) k) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact congrArg (fun w : DarbouxState => w k)
      (coordinate_qSolutionJet_horizontal_positive hU hz (hseg x hx) n hn)
  rw [eLpNorm_congr_ae he]
  fin_cases k
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · norm_num [qFirstJetOffset] at hhigh
    omega
  · exact hL2 1 (n + 1) (by simpa [qFirstJetOffset] using htop)
  · exact hL2 0 (n + 1) (by simpa [qFirstJetOffset] using htop)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Analytic

def qWordSliceBudget (C lengthFloor left right : ℝ) (H : ℝ≥0) (w : ChainWord) : ℝ≥0∞ :=
  ∑ _r : Fin w.arity → Fin 6,
    ‖C‖ₑ * spatialProductL2Budget lengthFloor left right H w.arity

def qChainSliceBudget (C lengthFloor left right : ℝ) (H : ℝ≥0)
    (ws : List ChainWord) : ℝ≥0∞ :=
  (ws.map (qWordSliceBudget C lengthFloor left right H)).sum

def qPairSliceBudget (Cfirst : ℝ) (H : ℝ≥0) : ℝ≥0∞ :=
  ‖Cfirst‖ₑ * (H : ℝ≥0∞) + ‖Cfirst‖ₑ * (H : ℝ≥0∞)

def qRemainderSliceBudget (C Cfirst lengthFloor left right : ℝ) (H : ℝ≥0)
    (m : ℕ) : ℝ≥0∞ :=
  qChainSliceBudget C lengthFloor left right H (topResidualWords m) +
    ‖(m + 3 : ℝ)‖ₑ * qPairSliceBudget Cfirst H

theorem qWordSliceBudget_lt_top (C lengthFloor left right : ℝ) (H : ℝ≥0) (w : ChainWord) :
    qWordSliceBudget C lengthFloor left right H w < (⊤ : ℝ≥0∞) := by
  unfold qWordSliceBudget
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.mul_lt_top (by finiteness)
    (spatialProductL2Budget_lt_top lengthFloor left right H w.arity))

theorem qChainSliceBudget_lt_top (C lengthFloor left right : ℝ) (H : ℝ≥0)
    (ws : List ChainWord) : qChainSliceBudget C lengthFloor left right H ws < (⊤ : ℝ≥0∞) := by
  induction ws with
  | nil => simp [qChainSliceBudget]
  | cons w ws ih =>
      exact ENNReal.add_lt_top.mpr ⟨qWordSliceBudget_lt_top C lengthFloor left right H w, ih⟩

theorem qRemainderSliceBudget_lt_top (C Cfirst lengthFloor left right : ℝ)
    (H : ℝ≥0) (m : ℕ) : qRemainderSliceBudget C Cfirst lengthFloor left right H m < (⊤ : ℝ≥0∞) := by
  unfold qRemainderSliceBudget qPairSliceBudget
  exact ENNReal.add_lt_top.mpr
    ⟨qChainSliceBudget_lt_top C lengthFloor left right H (topResidualWords m), by finiteness⟩

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem qCoordinateScalarTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (fun p => qCoordinateChainCoefficient g z w r p *
      ∏ i, qCoordinateChainFactor z w r i p) U :=
  (qCoordinateChainCoefficient_continuousOn hg hU hz hxx w r).mul
    (continuousOn_finsetProd Finset.univ (fun i _ =>
      qCoordinateChainFactor_continuousOn hU hz w r i))

theorem qCoordinateChainTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (w : ChainWord) :
    ContinuousOn (qCoordinateChainTerm g z w) U := by
  have he : qCoordinateChainTerm g z w = fun p => ∑ r : Fin w.arity → Fin 6,
      qCoordinateChainCoefficient g z w r p * ∏ i, qCoordinateChainFactor z w r i p :=
    funext (qCoordinateChainTerm_scalar_expansion g z w)
  rw [he]
  exact continuousOn_finsetSum Finset.univ
    (fun r _ => qCoordinateScalarTerm_continuousOn hg hU hz hxx w r)

theorem qCoordinateChainSum_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (ws : List ChainWord) :
    ContinuousOn (qCoordinateChainSum g z ws) U := by
  induction ws with
  | nil => exact continuousOn_const
  | cons w ws ih => exact (qCoordinateChainTerm_continuousOn hg hU hz hxx w).add ih

theorem q_residual_product_eLpNorm_two
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {theta left right lengthFloor : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    {w : ChainWord} (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    eLpNorm (fun x => ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤
        spatialProductL2Budget lengthFloor left right H w.arity := by
  classical
  let B := spatialLowFactorBound lengthFloor H
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  obtain ⟨hpos, _, horders⟩ := topResidualWords_properties m w hw
  have hproductMeas := (smooth_slice_memLp_two
    (continuousOn_finsetProd Finset.univ (fun index _ =>
      qCoordinateChainFactor_continuousOn hU hz w r index)) hseg).aestronglyMeasurable
  have hfactorOrders := (q_residual_factor_orders hw r).1
  have hlow (i : Fin w.arity) (hi : qChainFactorOrder w r i + 1 ≤ m + 2)
      (x : ℝ) (hx : x ∈ Icc left right) :
      ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B :=
    q_state_factor_low_bound hU hz hseg hlength hwidth hL2
      (w.order i) (hpos i) (r i) hi hx
  by_cases hh : ∃ j, m + 2 ≤ qChainFactorOrder w r j
  · obtain ⟨j, hj⟩ := hh
    have hb (i : Fin w.arity) (hi : i ∈ (Finset.univ : Finset (Fin w.arity)).erase j)
        (x : ℝ) (hx : x ∈ Icc left right) :
        ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B := by
      apply hlow i _ x hx
      have hnot : ¬ m + 2 ≤ qChainFactorOrder w r i := fun hie =>
        (Finset.mem_erase.mp hi).1 (q_residual_high_unique hm hw r hie hj)
      omega
    have hjL2 : eLpNorm (fun x => qCoordinateChainFactor z w r j (coordinatePoint x theta)) 2
        (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) :=
      q_state_factor_high_eLpNorm hU hz hseg hL2 (w.order j) (hpos j)
        (by have ho := horders j; omega) (r j) hj (hfactorOrders j)
    have hprod := finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (fun i x => qCoordinateChainFactor z w r i (coordinatePoint x theta))
      (Finset.mem_univ j) hB0 measurableSet_Icc hb hproductMeas
    have hcard : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ w.arity := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin w.arity)))
    have hpow : ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ ≤ ‖B ^ w.arity‖ₑ := by
      rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (pow_nonneg hB0 _),
        Real.norm_of_nonneg (pow_nonneg hB0 _)]
      exact pow_le_pow_right₀ hB1 hcard
    calc
      _ ≤ ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ *
          eLpNorm (fun x => qCoordinateChainFactor z w r j (coordinatePoint x theta)) 2
            (volume.restrict (Icc left right)) := hprod
      _ ≤ ‖B ^ w.arity‖ₑ * (H : ℝ≥0∞) := mul_le_mul' hpow hjL2
      _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_right (by positivity))
  · have hb (i : Fin w.arity) (_ : i ∈ (Finset.univ : Finset (Fin w.arity)))
        (x : ℝ) (hx : x ∈ Icc left right) :
        ‖qCoordinateChainFactor z w r i (coordinatePoint x theta)‖ ≤ B := by
      apply hlow i _ x hx
      have hnot : ¬ m + 2 ≤ qChainFactorOrder w r i := fun hie => hh ⟨i, hie⟩
      omega
    have hprod := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (fun i x => qCoordinateChainFactor z w r i (coordinatePoint x theta))
      hB0 measurableSet_Icc hb hproductMeas
    calc
      _ ≤ ‖B ^ w.arity‖ₑ * (volume (Icc left right)) ^ (1 / (2 : ℝ)) := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hprod
      _ ≤ _ := mul_le_mul' le_rfl (le_add_of_nonneg_left (by positivity))

theorem qFirstJetPairRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (n : ℕ) :
    ContinuousOn (qFirstJetPairRemainder g z n) U := by
  have hc (i : Fin 6) := (partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx i) hU 0).continuousOn
  have hf (i : Fin 2) := (partial_contDiffOn (horizontalJet_contDiffOn hU hz n) hU i).continuousOn
  exact ((hc 2).mul (hf 0)).add ((hc 3).mul (hf 1))

theorem qFirstJetPairRemainder_slice_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right Cfirst : ℝ} {N : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) (hCfirst : 0 ≤ Cfirst)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (hfirst2 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x theta)| ≤ Cfirst)
    (hfirst3 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x theta)| ≤ Cfirst) :
    eLpNorm (fun x => qFirstJetPairRemainder g z N (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qPairSliceBudget Cfirst H := by
  have hf (i : Fin 2) : eLpNorm (fun x => coordPartial i (horizontalJet z N) (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) := by
    have he : (fun x => coordPartial i (horizontalJet z N) (coordinatePoint x theta)) =ᵐ[
        volume.restrict (Icc left right)] (fun x => spatialJet (spatialFirstJet z i) N (coordinatePoint x theta)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [← horizontalJet_coordPartial hU hz i N _ (hseg x hx), horizontalJet_eq_spatialJet]
      rfl
    rw [eLpNorm_congr_ae he]
    exact hL2 i N le_rfl
  have hm (i : Fin 6) (j : Fin 2) : AEStronglyMeasurable
      (fun x => coordPartial 0 (heightQCoefficient g z i) (coordinatePoint x theta) *
        coordPartial j (horizontalJet z N) (coordinatePoint x theta))
      (volume.restrict (Icc left right)) :=
    (smooth_slice_memLp_two
      ((partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx i) hU 0).continuousOn.mul
        (partial_contDiffOn (horizontalJet_contDiffOn hU hz N) hU j).continuousOn) hseg).aestronglyMeasurable
  have h0 := (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    hCfirst hfirst2 (hm 2 0)).trans (mul_le_mul' le_rfl (hf 0))
  have h1 := (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    hCfirst hfirst3 (hm 3 1)).trans (mul_le_mul' le_rfl (hf 1))
  exact (eLpNorm_add_le (hm 2 0) (hm 3 1) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add h0 h1)

theorem actualQHighRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (m : ℕ) :
    ContinuousOn (actualQHighRemainder g z m) U :=
  (qCoordinateChainSum_continuousOn hg hU hz hxx (topResidualWords m)).add
    (continuousOn_const.mul (qFirstJetPairRemainder_continuousOn hg hU hz hxx (m + 2)))

theorem actualQHighRemainder_slice_memLp_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (m : ℕ)
    {theta left right : ℝ} (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) :
    MemLp (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) :=
  smooth_slice_memLp_two (actualQHighRemainder_continuousOn hg hU hz hxx m) hseg

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Analytic

def QActiveComponents (w : ChainWord) (r : Fin w.arity → Fin 6) : Prop :=
  ∀ i, r i ≠ 1 ∧ (r i = 0 → w.order i = 1)

theorem q_state_factor_eq_zero_of_spatial_inactive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (hk : k = 1 ∨ (k = 0 ∧ n ≠ 1)) :
    horizontalJet (qSolutionJet z) n p k = 0 := by
  rw [coordinate_qSolutionJet_horizontal_positive hU hz hp n hn]
  rcases hk with hk | ⟨hk, hn1⟩
  · subst k
    rfl
  · subst k
    simp [hn1]

theorem qCoordinateChainProduct_eq_zero_of_inactive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (w : ChainWord) (hpos : w.Positive) (r : Fin w.arity → Fin 6)
    (hinactive : ¬ QActiveComponents w r) :
    (∏ i, qCoordinateChainFactor z w r i p) = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hinactive
  have hbad : r i = 1 ∨ (r i = 0 ∧ w.order i ≠ 1) := by
    by_cases h1 : r i = 1
    · exact Or.inl h1
    · right
      have hh : ¬ (r i = 0 → w.order i = 1) := fun himp => hi ⟨h1, himp⟩
      by_cases hzero : r i = 0
      · exact ⟨hzero, fun horder => hh (fun _ => horder)⟩
      · exact (hh (fun heq => (hzero heq).elim)).elim
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (q_state_factor_eq_zero_of_spatial_inactive hU hz hp (w.order i) (hpos i) (r i) hbad)

theorem qCoordinateChainTerm_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    {w : ChainWord} (hw : w ∈ topResidualWords m)
    (hcoeff : ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C) :
    eLpNorm (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qWordSliceBudget C lengthFloor left right H w := by
  classical
  have he : (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta)) = fun x =>
      ∑ r : Fin w.arity → Fin 6, qCoordinateChainCoefficient g z w r (coordinatePoint x theta) *
        ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta) :=
    funext (fun x => qCoordinateChainTerm_scalar_expansion g z w (coordinatePoint x theta))
  rw [he]
  apply finite_sum_eLpNorm_two (μ := volume) (U := Icc left right) Finset.univ _
    (fun _ => ‖C‖ₑ * spatialProductL2Budget lengthFloor left right H w.arity)
  · intro r _
    exact (smooth_slice_memLp_two
      (qCoordinateScalarTerm_continuousOn hg hU hz hxx w r) hseg).aestronglyMeasurable
  · intro r _
    by_cases hactive : QActiveComponents w r
    · exact (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable hC (hcoeff r hactive)
        (smooth_slice_memLp_two
          (qCoordinateScalarTerm_continuousOn hg hU hz hxx w r) hseg).aestronglyMeasurable).trans
        (mul_le_mul' le_rfl (q_residual_product_eLpNorm_two hU hz hseg hlength hwidth hm hL2 hw r))
    · have hzero : (fun x => qCoordinateChainCoefficient g z w r (coordinatePoint x theta) *
          ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta)) =ᵐ[
          volume.restrict (Icc left right)] (0 : ℝ → ℝ) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        rw [qCoordinateChainProduct_eq_zero_of_inactive hU hz (hseg x hx) w
          (topResidualWords_properties m w hw).1 r hactive, mul_zero]
        rfl
      rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
      positivity

theorem qCoordinateChainSum_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C)
    (ws : List ChainWord) (hws : ∀ w ∈ ws, w ∈ topResidualWords m) :
    eLpNorm (fun x => qCoordinateChainSum g z ws (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qChainSliceBudget C lengthFloor left right H ws := by
  induction ws with
  | nil =>
      change eLpNorm (0 : ℝ → ℝ) 2 (volume.restrict (Icc left right)) ≤ 0
      simp
  | cons w ws ih =>
      have hw := hws w List.mem_cons_self
      have ht := qCoordinateChainTerm_slice_eLpNorm_two_active hg hU hz hxx hseg hlength hwidth hm hC
        hL2 hw (hcoeff w hw)
      have hs := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
      change eLpNorm (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta) +
        qCoordinateChainSum g z ws (coordinatePoint x theta)) 2 (volume.restrict (Icc left right)) ≤
          qWordSliceBudget C lengthFloor left right H w + qChainSliceBudget C lengthFloor left right H ws
      exact (eLpNorm_add_le
        (smooth_slice_memLp_two (qCoordinateChainTerm_continuousOn hg hU hz hxx w) hseg).aestronglyMeasurable
        (smooth_slice_memLp_two (qCoordinateChainSum_continuousOn hg hU hz hxx ws) hseg).aestronglyMeasurable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add ht hs)

theorem actualQHighRemainder_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C Cfirst : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C)
    (hfirst2 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x theta)| ≤ Cfirst)
    (hfirst3 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x theta)| ≤ Cfirst) :
    eLpNorm (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qRemainderSliceBudget C Cfirst lengthFloor left right H m := by
  have hs := qCoordinateChainSum_slice_eLpNorm_two_active hg hU hz hxx hseg hlength hwidth hm hC
    hL2 hcoeff (topResidualWords m) (fun _ wordMem => wordMem)
  have hp := qFirstJetPairRemainder_slice_eLpNorm_two hg hU hz hxx hseg hCfirst hL2 hfirst2 hfirst3
  have hscaled : eLpNorm (fun x => (m + 3 : ℝ) * qFirstJetPairRemainder g z (m + 2) (coordinatePoint x theta))
      2 (volume.restrict (Icc left right)) ≤ ‖(m + 3 : ℝ)‖ₑ * qPairSliceBudget Cfirst H := by
    change eLpNorm ((m + 3 : ℝ) • (fun x => qFirstJetPairRemainder g z (m + 2) (coordinatePoint x theta)))
      2 (volume.restrict (Icc left right)) ≤ _
    rw [eLpNorm_const_smul (𝕜 := ℝ) (F := ℝ)]
    exact mul_le_mul' le_rfl hp
  exact (eLpNorm_add_le
    (smooth_slice_memLp_two (qCoordinateChainSum_continuousOn hg hU hz hxx (topResidualWords m)) hseg).aestronglyMeasurable
    (smooth_slice_memLp_two (continuousOn_const.mul (qFirstJetPairRemainder_continuousOn hg hU hz hxx (m + 2))) hseg).aestronglyMeasurable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hs hscaled)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem spatialProductL2Budget_mono_width
    {lengthFloor left right width : ℝ} (H : ℝ≥0) (n : ℕ)
    (hwidth : right - left ≤ width) :
    spatialProductL2Budget lengthFloor left right H n ≤
      spatialProductL2Budget lengthFloor 0 width H n := by
  have hvol : volume (Icc left right) ≤ volume (Icc (0 : ℝ) width) := by
    rw [Real.volume_Icc, Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_le_ofReal hwidth
  exact mul_le_mul' le_rfl (add_le_add le_rfl
    (ENNReal.rpow_le_rpow hvol (by norm_num : 0 ≤ 1 / (2 : ℝ))))

theorem qRemainderSliceBudget_mono_width
    {C Cfirst lengthFloor left right width : ℝ} (H : ℝ≥0) (m : ℕ)
    (hwidth : right - left ≤ width) :
    qRemainderSliceBudget C Cfirst lengthFloor left right H m ≤
      qRemainderSliceBudget C Cfirst lengthFloor 0 width H m := by
  have hword (w : ChainWord) : qWordSliceBudget C lengthFloor left right H w ≤
      qWordSliceBudget C lengthFloor 0 width H w := by
    apply Finset.sum_le_sum
    intro _ _
    exact mul_le_mul' le_rfl (spatialProductL2Budget_mono_width H w.arity hwidth)
  have hsum (ws : List ChainWord) : qChainSliceBudget C lengthFloor left right H ws ≤
      qChainSliceBudget C lengthFloor 0 width H ws := by
    induction ws with
    | nil => exact le_rfl
    | cons w ws ih => exact add_le_add (hword w) ih
  exact add_le_add (hsum (topResidualWords m)) le_rfl

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
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

abbrev QSpatialState := Fin 5 → ℝ

def qSpatialAxis : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]
def qSpatialIndex : Fin 6 → Fin 5 := ![0, 0, 1, 2, 3, 4]

def qSpatialLinear : QSpatialState →ₗ[ℝ] DarbouxState where
  toFun v := ![v 0, 0, v 1, v 2, v 3, v 4]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

def qSpatialCLM : QSpatialState →L[ℝ] DarbouxState :=
  LinearMap.toContinuousLinearMap qSpatialLinear

def qFixedTimeState (theta : ℝ) (v : QSpatialState) : DarbouxState :=
  qSpatialCLM v + Pi.single 1 theta

def qSpatialProjection (w : DarbouxState) : QSpatialState := ![w 0, w 2, w 3, w 4, w 5]

def qFixedTimeQ (g : MetricField) (theta : ℝ) : QSpatialState → ℝ :=
  sixVariableQ g ∘ qFixedTimeState theta

def qFixedTimeDomain (g : MetricField) (U : Set Coord) (theta : ℝ) : Set QSpatialState :=
  qFixedTimeState theta ⁻¹' darbouxQStateDomain g U

theorem qSpatialAxis_index {i : Fin 6} (hi : i ≠ 1) : qSpatialAxis (qSpatialIndex i) = i := by
  fin_cases i <;> first | rfl | exact (hi rfl).elim

theorem qSpatialCLM_single (i : Fin 5) :
    qSpatialCLM (Pi.single i 1) = Pi.single (qSpatialAxis i) 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [qSpatialCLM, qSpatialLinear, qSpatialAxis]

theorem qFixedTimeState_projection (w : DarbouxState) :
    qFixedTimeState (w 1) (qSpatialProjection w) = w := by
  ext i
  fin_cases i <;> simp [qFixedTimeState, qSpatialProjection, qSpatialCLM,
    qSpatialLinear]

theorem qFixedTimeState_contDiff (theta : ℝ) : ContDiff ℝ ∞ (qFixedTimeState theta) :=
  qSpatialCLM.contDiff.add contDiff_const

theorem qFixedTimeDomain_isOpen {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (theta : ℝ) :
    IsOpen (qFixedTimeDomain g U theta) :=
  (darbouxQStateDomain_isOpen hg hU).preimage (qFixedTimeState_contDiff theta).continuous

theorem qFixedTimeQ_iteratedFDeriv
    {g : MetricField} {U : Set Coord} {theta : ℝ} {v : QSpatialState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hv : v ∈ qFixedTimeDomain g U theta) (n : ℕ) :
    iteratedFDeriv ℝ n (qFixedTimeQ g theta) v =
      (iteratedFDeriv ℝ n (sixVariableQ g) (qFixedTimeState theta v)).compContinuousLinearMap
        (fun _ => qSpatialCLM) := by
  let c : DarbouxState := Pi.single 1 theta
  let O : Set DarbouxState := (fun w : DarbouxState => w + c) ⁻¹' darbouxQStateDomain g U
  have hO : IsOpen O := (darbouxQStateDomain_isOpen hg hU).preimage (by fun_prop)
  have hF : ContDiffOn ℝ ∞ (fun w : DarbouxState => sixVariableQ g (w + c)) O :=
    (sixVariableQ_contDiffOn hg hU).comp (by fun_prop) (fun _ hw => hw)
  have hpre : IsOpen (qSpatialCLM ⁻¹' O) := hO.preimage qSpatialCLM.continuous
  have hp : qSpatialCLM v ∈ O := hv
  have he := qSpatialCLM.iteratedFDerivWithin_comp_right hF hO.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp,
    iteratedFDerivWithin_of_isOpen n hO hp,
    iteratedFDeriv_comp_add_right n c (qSpatialCLM v)] at he
  exact he

theorem qCoordinateChainCoefficient_eq_fixedTime
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) (w : ChainWord) (r : Fin w.arity → Fin 6)
    (hactive : QActiveComponents w r) :
    qCoordinateChainCoefficient g z w r p =
      iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))
        (fun i => Pi.single (qSpatialIndex (r i)) 1) := by
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hv : qSpatialProjection (qSolutionJet z p) ∈ qFixedTimeDomain g U (p 1) := by
    change qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) ∈ darbouxQStateDomain g U
    rw [he]
    exact qSolutionJet_mem_domain hp hxx
  rw [qFixedTimeQ_iteratedFDeriv hg hU hv w.arity,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, he]
  unfold qCoordinateChainCoefficient
  congr 1
  funext i
  rw [qSpatialCLM_single, qSpatialAxis_index (hactive i).1]

theorem qCoordinateChainCoefficient_abs_le_fixedTime_derivative
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) (w : ChainWord) (r : Fin w.arity → Fin 6)
    (hactive : QActiveComponents w r) :
    |qCoordinateChainCoefficient g z w r p| ≤
      ‖iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))‖ := by
  rw [qCoordinateChainCoefficient_eq_fixedTime hg hU hp hxx w r hactive, ← Real.norm_eq_abs]
  have hb := (iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1))
    (qSpatialProjection (qSolutionJet z p))).le_opNorm
      (fun i => Pi.single (qSpatialIndex (r i)) (1 : ℝ))
  simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using hb

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
open SmoothLocal.Geometry

def universalQDenominator (a : MetricPInput) : ℝ :=
  a.2.2.2 5 - universalConnection a 0 0

def universalMetricQ (a : MetricPInput) : ℝ :=
  universalConnection a 1 1 +
    ((a.2.2.2 4 - universalConnection a 0 1)^2 +
      curvatureJet a.1 a.2.1 a.2.2.1 * universalEnergy a) / universalQDenominator a

def universalMetricQDomain : Set MetricPInput :=
  {a | a.1.det ≠ 0 ∧ universalQDenominator a ≠ 0}

def universalMetricQTube (M d c : ℝ) : Set MetricPInput :=
  universalMetricBaseTube M d ∩ universalQDenominator ⁻¹' {x : ℝ | c ≤ |x|}

theorem universalQDenominator_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalQDenominator (metricPBundle g w) = stateQDenominator g w := rfl

theorem sixVariableQ_eq_universalMetricQ {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableQ g w = universalMetricQ (metricPBundle g w) := by
  rw [sixVariableQ_explicit hg hU hw]
  have hK := gaussianCurvature_eq_curvatureJet hg hU hw
  unfold solvedDarbouxQ jetNumerator jetMixed jetXX universalMetricQ
  rw [universalConnection_metricPBundle, universalConnection_metricPBundle,
    universalQDenominator_metricPBundle, universalEnergy_metricPBundle]
  simp only [stateConnection, stateQDenominator, stateEnergy, jetXX, metricPBundle, hK]

theorem universalQDenominator_contDiffOn :
    ContDiffOn ℝ ∞ universalQDenominator universalMetricBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 5) a by fun_prop).sub
    (universalConnection_contDiffAt ha 0 0)).contDiffWithinAt

theorem universalMetricQDomain_isOpen : IsOpen universalMetricQDomain :=
  universalQDenominator_contDiffOn.continuousOn.isOpen_inter_preimage
    universalMetricBase_isOpen isClosed_singleton.isOpen_compl

theorem universalMetricQ_contDiffOn :
    ContDiffOn ℝ ∞ universalMetricQ universalMetricQDomain := by
  intro a ha
  have hΓ := universalConnection_contDiffAt ha.1
  have hK : ContDiffAt ℝ ∞
      (fun b : MetricPInput => curvatureJet b.1 b.2.1 b.2.2.1) a :=
    curvatureJet_contDiffAt (fun i j => by fun_prop)
      (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha.1
  have hm : ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 1 1).add (((hm.pow 2).add (hK.mul universalEnergy_contDiff.contDiffAt)).div
    (universalQDenominator_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha.1))
    ha.2)).contDiffWithinAt

theorem universalMetricQTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (universalMetricQTube M d c) := by
  have hbase := universalMetricBaseTube_isCompact M d
  have hc : ContinuousOn universalQDenominator (universalMetricBaseTube M d) :=
    universalQDenominator_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd)
  have hclosed : IsClosed (universalMetricQTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem universalMetricQTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    universalMetricQTube M d c ⊆ universalMetricQDomain := by
  intro a ha
  refine ⟨universalMetricBaseTube_subset_base M hd ha.1, ?_⟩
  intro hz
  have hh : c ≤ |universalQDenominator a| := ha.2
  rw [hz, abs_zero] at hh
  linarith

theorem universalMetricQTube_finite_bounds (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ N, ∀ a ∈ universalMetricQTube M d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C := by
  classical
  have hk : ∀ k : Fin (N + 1), ∃ A : ℝ,
      ∀ a ∈ universalMetricQTube M d c, ‖iteratedFDeriv ℝ k.val universalMetricQ a‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val universalMetricQ) universalMetricQDomain := by
      apply (universalMetricQ_contDiffOn.continuousOn_iteratedFDerivWithin
        (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn).congr
      intro a ha
      exact (iteratedFDerivWithin_eq_iteratedFDeriv universalMetricQDomain_isOpen.uniqueDiffOn
        ((universalMetricQ_contDiffOn.contDiffAt
          (universalMetricQDomain_isOpen.mem_nhds ha)).of_le (WithTop.coe_le_coe.mpr le_top)) ha).symm
    exact (universalMetricQTube_isCompact M hd c).exists_bound_of_continuousOn
      (hcont.mono (universalMetricQTube_subset_domain M hd hc))
  choose A hA using hk
  refine ⟨∑ k : Fin (N + 1), |A k|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk a ha
  let j : Fin (N + 1) := ⟨k, by omega⟩
  exact (hA j a ha).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

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
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def qFixedTimeBaseDomain (U : Set Coord) (theta : ℝ) : Set QSpatialState :=
  {v | coordinatePoint (v 0) theta ∈ U}

def metricQSpatialBundle (g : MetricField) (theta : ℝ) : QSpatialState → MetricPInput :=
  metricPBundle g ∘ qFixedTimeState theta

theorem statePoint_qFixedTimeState (theta : ℝ) (v : QSpatialState) :
    statePoint (qFixedTimeState theta v) = coordinatePoint (v 0) theta := by
  ext i
  fin_cases i <;> simp [statePoint, qFixedTimeState, qSpatialCLM, qSpatialLinear,
    coordinatePoint]

theorem qFixedTimeBaseDomain_isOpen {U : Set Coord} (hU : IsOpen U) (theta : ℝ) :
    IsOpen (qFixedTimeBaseDomain U theta) :=
  hU.preimage (by unfold coordinatePoint; fun_prop)

theorem metricQSpatialBundle_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (theta : ℝ) :
    ContDiffOn ℝ ∞ (metricQSpatialBundle g theta) (qFixedTimeBaseDomain U theta) := by
  apply (metricPBundle_contDiffOn hg hU).comp (qFixedTimeState_contDiff theta).contDiffOn
  intro v hv
  change statePoint (qFixedTimeState theta v) ∈ U
  simpa only [statePoint_qFixedTimeState, qFixedTimeBaseDomain, Set.mem_ofPred_eq] using hv

theorem norm_iteratedFDeriv_fixedTime_coordinate
    {f : Coord → ℝ} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {theta : ℝ} {v : QSpatialState} (hp : coordinatePoint (v 0) theta ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun w : QSpatialState => f (coordinatePoint (w 0) theta)) v‖ ≤
      |horizontalJet f n (coordinatePoint (v 0) theta)| := by
  let I : Set ℝ := {x | coordinatePoint x theta ∈ U}
  let L : QSpatialState →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hI : IsOpen I := hU.preimage (horizontalPoint_contDiff theta).continuous
  have hs : ContDiffOn ℝ ∞ (fun x : ℝ => f (coordinatePoint x theta)) I :=
    hf.comp (horizontalPoint_contDiff theta).contDiffOn (fun x hx => hx)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [one_mul, L, ContinuousLinearMap.proj_apply] using norm_le_pi_norm w 0
  have h := norm_iteratedFDeriv_comp_contraction L hs hI hL hp n
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  change ‖iteratedFDeriv ℝ n (fun w : QSpatialState => f (coordinatePoint (w 0) theta)) v‖ ≤
    ‖iteratedDeriv n (fun x => f (coordinatePoint x theta)) (v 0)‖ at h
  rw [horizontalJet_slice hU hf theta n (v 0) hp, Real.norm_eq_abs] at h
  exact h

theorem qSpatialCLM_norm_le : ‖qSpatialCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm v 0
  · simp [qSpatialCLM, qSpatialLinear]
  · exact norm_le_pi_norm v 1
  · exact norm_le_pi_norm v 2
  · exact norm_le_pi_norm v 3
  · exact norm_le_pi_norm v 4

theorem qFixedTimeState_positive_jet_bound (theta : ℝ) (v : QSpatialState)
    {n : ℕ} (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n (qFixedTimeState theta) v‖ ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
      rw [← norm_iteratedFDeriv_fderiv]
      have he : fderiv ℝ (qFixedTimeState theta) = (fun _ : QSpatialState => qSpatialCLM) := by
        funext w
        exact (qSpatialCLM.hasFDerivAt.add_const (Pi.single 1 theta)).fderiv
      rw [he]
      cases n with
      | zero => simpa only [norm_iteratedFDeriv_zero] using qSpatialCLM_norm_le
      | succ _ => simp only [iteratedFDeriv_succ_const]; norm_num

theorem metricQSpatialBundle_norm_bound
    {g : MetricField} {theta G W : ℝ} {v : QSpatialState} {N : ℕ}
    (hG : 0 ≤ G) (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    (hwB : ‖qFixedTimeState theta v‖ ≤ W) :
    ‖metricQSpatialBundle g theta v‖ ≤ max G W := by
  have h0 : ‖g (coordinatePoint (v 0) theta)‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.1 i j 0 (by omega)))
  have h1 : ‖(fun d i j => coordPartial d (fun p => g p i j) (coordinatePoint (v 0) theta))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.2.1 d i j 0 (by omega))))
  have h2 : ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g p i j))
      (coordinatePoint (v 0) theta))‖ ≤ G :=
    (pi_norm_le_iff_of_nonneg hG).mpr (fun d =>
      (pi_norm_le_iff_of_nonneg hG).mpr (fun e =>
        (pi_norm_le_iff_of_nonneg hG).mpr (fun i =>
          (pi_norm_le_iff_of_nonneg hG).mpr (fun j => hgB.2.2 d e i j 0 (by omega)))))
  unfold metricQSpatialBundle metricPBundle
  simp only [Function.comp_apply, statePoint_qFixedTimeState, Prod.norm_def]
  exact max_le (h0.trans (le_max_left _ _))
    (max_le (h1.trans (le_max_left _ _))
      (max_le (h2.trans (le_max_left _ _)) (hwB.trans (le_max_right _ _))))

theorem metricQSpatialBundle_positive_jet_bound
    {g : MetricField} {U : Set Coord} {theta G : ℝ} {v : QSpatialState} {N : ℕ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : coordinatePoint (v 0) theta ∈ U)
    (hG : 0 ≤ G) (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (metricQSpatialBundle g theta) v‖ ≤ max 1 G := by
  have hB := (metricQSpatialBundle_contDiffOn hg hU theta).contDiffAt
    ((qFixedTimeBaseDomain_isOpen hU theta).mem_nhds hp)
  have h0 := hB.fst
  have h1 := hB.snd.fst
  have h2 := hB.snd.snd.fst
  have hId := hB.snd.snd.snd
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).1) v at h0
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.1) v at h1
  change ContDiffAt ℝ ∞ (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.2.1) v at h2
  have he0 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).1) =
      (fun w => g (coordinatePoint (w 0) theta)) := by
    funext w
    exact congrArg g (statePoint_qFixedTimeState theta w)
  have he1 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.1) =
      (fun w d i j => coordPartial d (fun p => g p i j) (coordinatePoint (w 0) theta)) := by
    funext w d i j
    exact congrArg (coordPartial d (fun p => g p i j)) (statePoint_qFixedTimeState theta w)
  have he2 : (fun w : QSpatialState => (metricQSpatialBundle g theta w).2.2.1) =
      (fun w d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (coordinatePoint (w 0) theta)) := by
    funext w d e i j
    exact congrArg (coordPartial d (coordPartial e (fun p => g p i j))) (statePoint_qFixedTimeState theta w)
  rw [he0] at h0
  rw [he1] at h1
  rw [he2] at h2
  have hb0 : ‖iteratedFDeriv ℝ n (fun w : QSpatialState => g (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le h0 n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h0) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate (hg.1 i j) hU hp n).trans (hgB.1 i j n hnN)
  have hb1 : ‖iteratedFDeriv ℝ n
      (fun w : QSpatialState => fun d i j => coordPartial d (fun p => g p i j) (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le (F := Matrix (Fin 2) (Fin 2) ℝ) h1 n hG
    intro d
    have h1d := (contDiffAt_pi (F' := fun _ : Fin 2 => Matrix (Fin 2) (Fin 2) ℝ)).mp h1 d
    apply norm_iteratedFDeriv_pi_le h1d n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h1d) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate (partial_contDiffOn (hg.1 i j) hU d) hU hp n).trans
      (hgB.2.1 d i j n hnN)
  have hb2 : ‖iteratedFDeriv ℝ n
      (fun w : QSpatialState => fun d e i j => coordPartial d (coordPartial e (fun p => g p i j))
        (coordinatePoint (w 0) theta)) v‖ ≤ G := by
    apply norm_iteratedFDeriv_pi_le (F := Fin 2 → Matrix (Fin 2) (Fin 2) ℝ) h2 n hG
    intro d
    have h2d := (contDiffAt_pi (F' := fun _ : Fin 2 => Fin 2 → Matrix (Fin 2) (Fin 2) ℝ)).mp h2 d
    apply norm_iteratedFDeriv_pi_le (F := Matrix (Fin 2) (Fin 2) ℝ) h2d n hG
    intro e
    have h2de := (contDiffAt_pi (F' := fun _ : Fin 2 => Matrix (Fin 2) (Fin 2) ℝ)).mp h2d e
    apply norm_iteratedFDeriv_pi_le h2de n hG
    intro i
    apply norm_iteratedFDeriv_pi_le ((contDiffAt_pi.mp h2de) i) n hG
    intro j
    exact (norm_iteratedFDeriv_fixedTime_coordinate
      (partial_contDiffOn (partial_contDiffOn (hg.1 i j) hU e) hU d) hU hp n).trans
        (hgB.2.2 d e i j n hnN)
  have hb0' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).1) v‖ ≤ G := by
    rw [he0]
    exact hb0
  have hb1' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).2.1) v‖ ≤ G := by
    rw [he1]
    exact hb1
  have hb2' : ‖iteratedFDeriv ℝ n (fun w => (metricQSpatialBundle g theta w).2.2.1) v‖ ≤ G := by
    rw [he2]
    exact hb2
  exact norm_iteratedFDeriv_prod_le hB.fst hB.snd n (hb0'.trans (le_max_right _ _))
    (norm_iteratedFDeriv_prod_le hB.snd.fst hB.snd.snd n (hb1'.trans (le_max_right _ _))
      (norm_iteratedFDeriv_prod_le hB.snd.snd.fst hId n (hb2'.trans (le_max_right _ _))
        ((qFixedTimeState_positive_jet_bound theta v hn).trans (le_max_left _ _))))

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
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem metricQSpatialBundle_mapsTo_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (theta : ℝ) :
    MapsTo (metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) universalMetricQDomain := by
  intro v hv
  exact ⟨metricDet_ne_zero hg hv.1,
    by simpa only [metricQSpatialBundle, Function.comp_apply, universalQDenominator_metricPBundle] using hv.2⟩

theorem actual_fixedTime_Q_jet_bound_from_universalTube
    {g : MetricField} {U : Set Coord} {theta : ℝ} {v : QSpatialState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hv : v ∈ qFixedTimeDomain g U theta)
    {N : ℕ} {G W d c C : ℝ} (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    (hwB : ‖qFixedTimeState theta v‖ ≤ W)
    (hdet : d ≤ |(g (coordinatePoint (v 0) theta)).det|)
    (hden : c ≤ |stateQDenominator g (qFixedTimeState theta v)|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricQTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (qFixedTimeQ g theta) v‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := qFixedTimeDomain_isOpen hg hU theta
  have hsub : qFixedTimeDomain g U theta ⊆ qFixedTimeBaseDomain U theta := by
    intro w hw
    simpa only [statePoint_qFixedTimeState, qFixedTimeBaseDomain, Set.mem_ofPred_eq] using hw.1
  have hf := (metricQSpatialBundle_contDiffOn hg hU theta).mono hsub
  have hmap := metricQSpatialBundle_mapsTo_domain hg theta
  have hmem : metricQSpatialBundle g theta v ∈ universalMetricQTube (max G W) d c := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using metricQSpatialBundle_norm_bound hG hgB hwB
    · simpa only [metricQSpatialBundle, Function.comp_apply, metricPBundle, statePoint_qFixedTimeState,
        Set.mem_preimage, Set.mem_Ici] using hdet
    · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, metricQSpatialBundle,
        Function.comp_apply, universalQDenominator_metricPBundle] using hden
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricQ universalMetricQDomain (metricQSpatialBundle g theta v)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricQDomain_isOpen
      (universalMetricQTube_subset_domain (max G W) hd hc hmem)]
    exact hC i (hi.trans hn) _ hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) v‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hv]
    exact (metricQSpatialBundle_positive_jet_bound hg hU (hsub hv) hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricQ_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hv ho hi
  have heq : iteratedFDerivWithin ℝ n (qFixedTimeQ g theta) (qFixedTimeDomain g U theta) v =
      iteratedFDerivWithin ℝ n (universalMetricQ ∘ metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) v :=
    iteratedFDerivWithin_congr
      (fun w hw => sixVariableQ_eq_universalMetricQ hg hU hw.1) hv n
  rw [iteratedFDerivWithin_of_isOpen n hD hv] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_fixedTime_Q_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ (theta : ℝ) (v : QSpatialState),
      coordinatePoint (v 0) theta ∈ U →
      HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G →
      ‖qFixedTimeState theta v‖ ≤ W →
      d ≤ |(g (coordinatePoint (v 0) theta)).det| →
      c ≤ |stateQDenominator g (qFixedTimeState theta v)| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (qFixedTimeQ g theta) v‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCQ⟩ := universalMetricQTube_finite_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU theta v hp hgB hwB hdet hden n hn
  have hne : stateQDenominator g (qFixedTimeState theta v) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hv : v ∈ qFixedTimeDomain g U theta :=
    ⟨by simpa only [statePoint_qFixedTimeState] using hp, hne⟩
  have hb := actual_fixedTime_Q_jet_bound_from_universalTube hg hU hv hG hd hc hgB hwB hdet hden hCQ hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun i _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

theorem qSolutionJet_norm_bound_of_coordinateBound
    {z : Coord → ℝ} {S : Set Coord} {R Z : ℝ} (hR : 0 ≤ R)
    (hzB : CoordinateBound z S 2 Z)
    (hcoords : ∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) {p : Coord} (hp : p ∈ S) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (hcoords p hp).1.trans (le_max_left _ _)
  · exact (hcoords p hp).2.trans (le_max_left _ _)
  · exact (hzB [0] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0] (by norm_num) p hp).trans (le_max_right _ _)

theorem exists_same_region_active_Q_coefficient_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ p ∈ S,
        |qCoordinateChainCoefficient g z w r p| ≤ C := by
  obtain ⟨C, hC, hQ⟩ := exists_local_fixedTime_Q_jet_bound G (max R Z) hG hd hc (m + 3)
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hcoords hgB hzB hdet hden w hw r hactive p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hpoint : coordinatePoint (qSpatialProjection (qSolutionJet z p) 0) (p 1) = p := point_eta p
  have hbound := hQ g U hg hU (p 1) (qSpatialProjection (qSolutionJet z p))
    (by simpa only [hpoint] using hSU hp)
    (by simpa only [hpoint] using hgB p hp)
    (by rw [he]; exact qSolutionJet_norm_bound_of_coordinateBound hR hzB hcoords hp)
    (by simpa only [hpoint] using hdet p hp)
    (by rw [he, stateQDenominator_qSolutionJet]; exact hden p hp)
    w.arity (q_residual_factor_orders hw r).2
  exact (qCoordinateChainCoefficient_abs_le_fixedTime_derivative hg hU (hSU hp) hxx w r hactive).trans hbound

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
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qSpatialProjection_norm_le (w : DarbouxState) : ‖qSpatialProjection w‖ ≤ ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  fin_cases i
  · exact norm_le_pi_norm w 0
  · exact norm_le_pi_norm w 2
  · exact norm_le_pi_norm w 3
  · exact norm_le_pi_norm w 4
  · exact norm_le_pi_norm w 5

theorem qSpatialCLM_projection_of_time_zero {w : DarbouxState} (hw : w 1 = 0) :
    qSpatialCLM (qSpatialProjection w) = w := by
  have he := qFixedTimeState_projection w
  simpa only [qFixedTimeState, hw, Pi.single_zero, add_zero] using he

theorem coordPartial_qSolutionJet_xi_norm_bound
    {z : Coord → ℝ} {U S : Set Coord} {Z : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hSU : S ⊆ U)
    (hzB : CoordinateBound z S 3 Z) {p : Coord} (hp : p ∈ S) :
    ‖coordPartial 0 (qSolutionJet z) p‖ ≤ max 1 Z := by
  have he := coordinate_qSolutionJet_horizontal_positive hU hz (hSU hp) 1 (by norm_num)
  change coordPartial 0 (qSolutionJet z) p = _ at he
  rw [he]
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · simp
  · simp
  · exact (hzB [0, 0] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · exact (hzB [0, 0, 0] (by norm_num) p hp).trans (le_max_right _ _)

theorem heightQCoefficient_xi_eq_fixedTime_second
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) (i : Fin 6) (hi : i ≠ 1) :
    coordPartial 0 (heightQCoefficient g z i) p =
      iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))
        ![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) 1] := by
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hv : qSpatialProjection (qSolutionJet z p) ∈ qFixedTimeDomain g U (p 1) := by
    change qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) ∈ darbouxQStateDomain g U
    rw [he]
    exact qSolutionJet_mem_domain hp hxx
  have htime : coordPartial 0 (qSolutionJet z) p 1 = 0 := by
    have hh := congrArg (fun v : DarbouxState => v 1)
      (coordinate_qSolutionJet_horizontal_positive hU hz hp 1 (by norm_num))
    exact hh
  rw [qFixedTimeQ_iteratedFDeriv hg hU hv 2,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, he]
  have hvec : (fun j : Fin 2 => qSpatialCLM
      (![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) 1] j)) =
      ![coordPartial 0 (qSolutionJet z) p, Pi.single i 1] := by
    funext j
    fin_cases j
    · exact qSpatialCLM_projection_of_time_zero htime
    · change qSpatialCLM (Pi.single (qSpatialIndex i) 1) = Pi.single i 1
      rw [qSpatialCLM_single, qSpatialAxis_index hi]
  rw [hvec]
  exact (second_fderiv_comp_constant_direction_xi
    (sixVariableQ_contDiffAt_solutionJet hg hU hp hxx)
    (((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    (Pi.single i 1)).symm

theorem heightQCoefficient_xi_bound_of_fixedTime_second
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord} {Z C : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : S ⊆ U) (hzB : CoordinateBound z S 3 Z) (hC : 0 ≤ C)
    {p : Coord} (hp : p ∈ S) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : ‖iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))‖ ≤ C)
    (i : Fin 6) (hi : i ≠ 1) :
    |coordPartial 0 (heightQCoefficient g z i) p| ≤ C * max 1 Z := by
  rw [heightQCoefficient_xi_eq_fixedTime_second hg hU hz (hSU hp) hxx i hi, ← Real.norm_eq_abs]
  have hd := (qSpatialProjection_norm_le (coordPartial 0 (qSolutionJet z) p)).trans
    (coordPartial_qSolutionJet_xi_norm_bound hU hz hSU hzB hp)
  have hb := (iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1))
    (qSpatialProjection (qSolutionJet z p))).le_opNorm
      ![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) (1 : ℝ)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (mul_le_mul hQ hd (norm_nonneg _) hC)

theorem exists_same_region_Q_first_xi_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ Cfirst : ℝ, 0 ≤ Cfirst ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p 2 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, i ≠ 1 → ∀ p ∈ S, |coordPartial 0 (heightQCoefficient g z i) p| ≤ Cfirst := by
  obtain ⟨C, hC, hQ⟩ := exists_local_fixedTime_Q_jet_bound G (max R Z) hG hd hc 2
  refine ⟨C * max 1 Z, mul_nonneg hC (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden i hi p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hpoint : coordinatePoint (qSpatialProjection (qSolutionJet z p) 0) (p 1) = p := point_eta p
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have hbound := hQ g U hg hU (p 1) (qSpatialProjection (qSolutionJet z p))
    (by simpa only [hpoint] using hSU hp)
    (by simpa only [hpoint] using hgB p hp)
    (by rw [he]; exact qSolutionJet_norm_bound_of_coordinateBound hR hz2 hcoords hp)
    (by simpa only [hpoint] using hdet p hp)
    (by rw [he, stateQDenominator_qSolutionJet]; exact hden p hp) 2 le_rfl
  exact heightQCoefficient_xi_bound_of_fixedTime_second hg hU hz hSU hzB hC hp hxx hbound i hi

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem HorizontalMetricTwoJetBound.mono_order
    {g : MetricField} {p : Coord} {N M : ℕ} {G : ℝ}
    (h : HorizontalMetricTwoJetBound g p N G) (hMN : M ≤ N) :
    HorizontalMetricTwoJetBound g p M G :=
  ⟨fun i j n hn => h.1 i j n (hn.trans hMN),
    fun d i j n hn => h.2.1 d i j n (hn.trans hMN),
    fun d e i j n hn => h.2.2 d e i j n (hn.trans hMN)⟩

theorem exists_same_slice_actual_Q_source_bound
    (G R Z lengthFloor width : ℝ) (H : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hlen : 0 < lengthFloor)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ B : ℝ≥0, ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ U, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ theta left right : ℝ,
      (∀ x ∈ Icc left right, coordinatePoint x theta ∈ S) →
      lengthFloor ≤ right - left → right - left ≤ width →
      SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H →
      eLpNorm (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
        (volume.restrict (Icc left right)) ≤ (B : ℝ≥0∞) := by
  obtain ⟨C, hC, hOuter⟩ := exists_same_region_active_Q_coefficient_bound G R Z hG hR hd hc m
  obtain ⟨Cfirst, hCfirst, hFirst⟩ := exists_same_region_Q_first_xi_bound G R Z hG hR hd hc
  let budget := qRemainderSliceBudget C Cfirst lengthFloor 0 width H m
  have hbudget : budget < (⊤ : ℝ≥0∞) := qRemainderSliceBudget_lt_top C Cfirst lengthFloor 0 width H m
  refine ⟨budget.toNNReal, ?_⟩
  intro g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have houter := hOuter g z U S hg hU hSU hcoords hgB hz2 hdet hden
  have hfirst := hFirst g z U S hg hU hz hSU hcoords
    (fun p hp => (hgB p hp).mono_order (by omega)) hzB hdet hden
  rw [ENNReal.coe_toNNReal hbudget.ne]
  exact (actualQHighRemainder_slice_eLpNorm_two_active hg hU hz hxx
    (fun x hx => hSU (hseg x hx)) hlen hwidth hm hC hCfirst hL2
    (fun w hw r hr x hx => houter w hw r hr _ (hseg x hx))
    (fun x hx => hfirst 2 (by decide) _ (hseg x hx))
    (fun x hx => hfirst 3 (by decide) _ (hseg x hx))).trans
      (qRemainderSliceBudget_mono_width H m hupper)

theorem exists_same_slice_actual_Q_source_norm_bound
    (G R Z lengthFloor width : ℝ) (H : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hlen : 0 < lengthFloor)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ B : ℝ≥0, ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ U, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ p ∈ S, HorizontalMetricTwoJetBound g p (m + 3) G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ theta left right : ℝ,
      (∀ x ∈ Icc left right, coordinatePoint x theta ∈ S) →
      lengthFloor ≤ right - left → right - left ≤ width →
      SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H →
      Real.sqrt (∫ x in left..right, actualQHighRemainder g z m (coordinatePoint x theta)^2) ≤ (B : ℝ) := by
  obtain ⟨B, hB⟩ := exists_same_slice_actual_Q_source_bound G R Z lengthFloor width H hG hR hlen hd hc m hm
  refine ⟨B, ?_⟩
  intro g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hn := hB g z U S hg hU hz hSU hxx hcoords hgB hzB hdet hden theta left right hseg hwidth hupper hL2
  have hmem := actualQHighRemainder_slice_memLp_two hg hU hz hxx m (fun x hx => hSU (hseg x hx))
  have hlr : left ≤ right := by linarith
  rw [intervalIntegral.integral_of_le hlr, restrict_Ioc_eq_restrict_Icc,
    sqrt_integral_square_eq_L2_norm hmem, Lp.norm_def, eLpNorm_congr_ae hmem.coeFn_toLp]
  exact ENNReal.toReal_mono (by simp : (B : ℝ≥0∞) ≠ ⊤) hn

end SmoothLocal.HighEquation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.HighEquation.exists_same_slice_actual_Q_source_norm_bound := @OAI.SmoothLocal.HighEquation.exists_same_slice_actual_Q_source_norm_bound
