-- Prove2me | solution 1 for OAI.SmoothLocal.HighEquation.exists_localized_actualHighRemainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:41:40.574625+00:00
-- url     : https://prove2.me/submissions/9743978a-9979-419d-b146-be83b50bd930

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
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem coordPartial_div
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => f x / h x) p =
      (coordPartial i f p * h p - f p * coordPartial i h p) / (h p) ^ 2 := by
  have hinv : HasFDerivAt (fun x : Coord => (h x)⁻¹)
      (-(h p ^ 2)⁻¹ • fderiv ℝ h p) p := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv hne).comp_hasFDerivAt p hh.hasFDerivAt
  have hquot : HasFDerivAt (fun x : Coord => f x / h x)
      (f p • (-(h p ^ 2)⁻¹ • fderiv ℝ h p) +
        (h p)⁻¹ • fderiv ℝ f p) p := by
    simpa only [div_eq_mul_inv] using hf.hasFDerivAt.fun_mul hinv
  unfold coordPartial
  rw [hquot.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp [hne]
  ring

theorem quotient_contDiffOn
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (hne : ∀ p ∈ U, h p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => f p / h p) U := by
  exact hf.div hh hne

end SmoothLocal.Geometry

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

theorem covHessian_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    {z : Coord → ℝ} (hz : ContDiffOn ℝ ∞ z U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => covHessian g z p i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ k,
      christoffel g k i j p * coordPartial k z p) U := by
    apply ContDiffOn.sum
    intro k hk
    exact (christoffel_contDiffOn hg hU k i j).mul (partial_contDiffOn hz hU k)
  exact (partial_contDiffOn (partial_contDiffOn hz hU j) hU i).sub hs

theorem covectorNormSq_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    {z : Coord → ℝ} (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (covectorNormSq g z) U := by
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact ((inverseMetric_contDiffOn hg i j).mul (partial_contDiffOn hz hU i)).mul
    (partial_contDiffOn hz hU j)

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
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

theorem heightEnergy_contDiffOn {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (heightEnergy g z) U :=
  (metricDet_contDiffOn hg).mul (contDiffOn_const.sub (covectorNormSq_contDiffOn hg hU hz))

theorem heightEnergy_polynomial {g : MetricField} (z : Coord → ℝ) {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) :
    heightEnergy g z p = (g p).det -
      (g p 1 1 * (coordPartial 0 z p) ^ 2 -
        (g p 0 1 + g p 1 0) * coordPartial 0 z p * coordPartial 1 z p +
        g p 0 0 * (coordPartial 1 z p) ^ 2) := by
  have hdet := metricDet_ne_zero hg hp
  simp only [heightEnergy, covectorNormSq, inverseMetric, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.adjugate_fin_two, Fin.sum_univ_two]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hdet]
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
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

theorem coordPartial_eq_of_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f p = coordPartial i h p := by
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem coordPartial_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f =ᶠ[𝓝 p] coordPartial i h := by
  filter_upwards [heq.eventuallyEq_nhds] with q hq
  exact coordPartial_eq_of_eventuallyEq hq i

theorem iteratedCoordPartial_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (dirs : List (Fin 2)) :
    iteratedCoordPartial dirs f =ᶠ[𝓝 p] iteratedCoordPartial dirs h := by
  induction dirs with
  | nil => exact heq
  | cons i is ih => exact coordPartial_eventuallyEq ih i

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def jetDriftVector (q : ℝ) : Coord := ![1, -q]

def christoffelAlongD (g : MetricField) (p : Coord) (q : ℝ) (i : Fin 2) : ℝ :=
  ∑ a, ∑ b, christoffel g i a b p * jetDriftVector q a * jetDriftVector q b

namespace DarbouxJetCalculus

theorem coordPartial_const (c : ℝ) (i : Fin 2) (u : Coord) :
    coordPartial i (fun _ : Coord => c) u = 0 := by
  simp [coordPartial]

theorem coordPartial_eval (i j : Fin 2) (u : Coord) :
    coordPartial i (fun v : Coord => v j) u = if j = i then 1 else 0 := by
  simp [coordPartial, (hasFDerivAt_apply j u).fderiv, Pi.single_apply]

theorem coordPartial_sq {f : Coord → ℝ} {u : Coord}
    (hf : DifferentiableAt ℝ f u) (i : Fin 2) :
    coordPartial i (fun v => (f v) ^ 2) u = 2 * f u * coordPartial i f u := by
  simp only [pow_two]
  rw [HessianCalculus.coordPartial_mul_at hf hf i]
  ring

end DarbouxJetCalculus

theorem jetConnection_differentiableAt (g : MetricField) (p u : Coord) (a b : Fin 2) :
    DifferentiableAt ℝ (jetConnection g p a b) u := by
  have h0 : DifferentiableAt ℝ (fun v : Coord => christoffel g 0 a b p * v 0) u :=
    (differentiableAt_apply (𝕜 := ℝ) 0 u).const_mul (christoffel g 0 a b p)
  have h1 : DifferentiableAt ℝ (fun v : Coord => christoffel g 1 a b p * v 1) u :=
    (differentiableAt_apply (𝕜 := ℝ) 1 u).const_mul (christoffel g 1 a b p)
  change DifferentiableAt ℝ (fun v => ∑ r, christoffel g r a b p * v r) u
  simpa only [Fin.sum_univ_two, Pi.add_def] using h0.add h1

theorem coordPartial_jetConnection (g : MetricField) (p u : Coord) (a b i : Fin 2) :
    coordPartial i (jetConnection g p a b) u = christoffel g i a b p := by
  have h0 : DifferentiableAt ℝ (fun v : Coord => christoffel g 0 a b p * v 0) u :=
    (differentiableAt_apply (𝕜 := ℝ) 0 u).const_mul (christoffel g 0 a b p)
  have h1 : DifferentiableAt ℝ (fun v : Coord => christoffel g 1 a b p * v 1) u :=
    (differentiableAt_apply (𝕜 := ℝ) 1 u).const_mul (christoffel g 1 a b p)
  change coordPartial i (fun v => ∑ r, christoffel g r a b p * v r) u = _
  simp only [Fin.sum_univ_two]
  rw [HessianCalculus.coordPartial_add_at h0 h1 i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (christoffel g 0 a b p))
      (differentiableAt_apply (𝕜 := ℝ) 0 u) i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (christoffel g 1 a b p))
      (differentiableAt_apply (𝕜 := ℝ) 1 u) i]
  fin_cases i <;>
    simp [DarbouxJetCalculus.coordPartial_const, DarbouxJetCalculus.coordPartial_eval]

theorem jetMixed_differentiableAt (g : MetricField) (p u : Coord) (b : ℝ) :
    DifferentiableAt ℝ (jetMixed g p b) u := by
  change DifferentiableAt ℝ (fun v => b - jetConnection g p 0 1 v) u
  simpa only [Pi.sub_def] using
    (differentiableAt_const (𝕜 := ℝ) b).sub (jetConnection_differentiableAt g p u 0 1)

theorem jetYY_differentiableAt (g : MetricField) (p u : Coord) (c : ℝ) :
    DifferentiableAt ℝ (jetYY g p c) u := by
  change DifferentiableAt ℝ (fun v => c - jetConnection g p 1 1 v) u
  simpa only [Pi.sub_def] using
    (differentiableAt_const (𝕜 := ℝ) c).sub (jetConnection_differentiableAt g p u 1 1)

theorem coordPartial_jetMixed (g : MetricField) (p u : Coord) (b : ℝ) (i : Fin 2) :
    coordPartial i (jetMixed g p b) u = -christoffel g i 0 1 p := by
  change coordPartial i (fun v => b - jetConnection g p 0 1 v) u = _
  rw [HessianCalculus.coordPartial_sub_at (differentiableAt_const b)
    (jetConnection_differentiableAt g p u 0 1) i]
  simp [DarbouxJetCalculus.coordPartial_const, coordPartial_jetConnection]

theorem coordPartial_jetYY (g : MetricField) (p u : Coord) (c : ℝ) (i : Fin 2) :
    coordPartial i (jetYY g p c) u = -christoffel g i 1 1 p := by
  change coordPartial i (fun v => c - jetConnection g p 1 1 v) u = _
  rw [HessianCalculus.coordPartial_sub_at (differentiableAt_const c)
    (jetConnection_differentiableAt g p u 1 1) i]
  simp [DarbouxJetCalculus.coordPartial_const, coordPartial_jetConnection]

theorem jetEnergy_differentiableAt (g : MetricField) (p u : Coord) :
    DifferentiableAt ℝ (jetEnergy g p) u := by
  have h0 := differentiableAt_apply (𝕜 := ℝ) 0 u
  have h1 := differentiableAt_apply (𝕜 := ℝ) 1 u
  change DifferentiableAt ℝ (fun v : Coord => (g p).det -
    (g p 1 1 * (v 0) ^ 2 - (g p 0 1 + g p 1 0) * v 0 * v 1 +
      g p 0 0 * (v 1) ^ 2)) u
  simpa only [Pi.pow_apply, Pi.add_def, Pi.sub_def, Pi.mul_apply] using
    (differentiableAt_const (𝕜 := ℝ) (g p).det).sub
    ((((h0.pow 2).const_mul (g p 1 1)).sub
      ((h0.const_mul (g p 0 1 + g p 1 0)).mul h1)).add
        ((h1.pow 2).const_mul (g p 0 0)))

theorem coordPartial_jetEnergy (g : MetricField) (p u : Coord) (i : Fin 2) :
    coordPartial i (jetEnergy g p) u =
      if i = 0 then -2 * g p 1 1 * u 0 + (g p 0 1 + g p 1 0) * u 1
      else (g p 0 1 + g p 1 0) * u 0 - 2 * g p 0 0 * u 1 := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) 0 u
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) 1 u
  have hQ := (((h0.fun_mul h0).const_mul (g p 1 1)).sub
    ((h0.const_mul (g p 0 1 + g p 1 0)).fun_mul h1)).add
      ((h1.fun_mul h1).const_mul (g p 0 0))
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (g p).det u).sub hQ
  simp only [Pi.add_def, Pi.sub_def] at hd
  change fderiv ℝ (fun v : Coord => (g p).det -
    (g p 1 1 * (v 0) ^ 2 - (g p 0 1 + g p 1 0) * v 0 * v 1 +
      g p 0 0 * (v 1) ^ 2)) u (Pi.single i 1) = _
  simp only [pow_two]
  rw [hd.fderiv]
  fin_cases i <;> simp <;> ring

theorem jetNumerator_differentiableAt (g : MetricField) (p u : Coord) (b : ℝ) :
    DifferentiableAt ℝ (jetNumerator g p b) u := by
  have hsq : DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2) u := by
    simpa only [pow_two] using
      ((jetMixed_differentiableAt g p u b).hasFDerivAt.fun_mul
        (jetMixed_differentiableAt g p u b).hasFDerivAt).differentiableAt
  have hKE : DifferentiableAt ℝ
      (fun v => gaussianCurvature g p * jetEnergy g p v) u :=
    (jetEnergy_differentiableAt g p u).const_mul (gaussianCurvature g p)
  change DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2 +
    gaussianCurvature g p * jetEnergy g p v) u
  simpa only [Pi.add_def] using hsq.add hKE

theorem coordPartial_jetNumerator (g : MetricField) (p u : Coord) (b : ℝ) (i : Fin 2) :
    coordPartial i (jetNumerator g p b) u =
      -2 * jetMixed g p b u * christoffel g i 0 1 p +
        gaussianCurvature g p * coordPartial i (jetEnergy g p) u := by
  have hsq : DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2) u := by
    simpa only [pow_two] using
      ((jetMixed_differentiableAt g p u b).hasFDerivAt.fun_mul
        (jetMixed_differentiableAt g p u b).hasFDerivAt).differentiableAt
  have hKE : DifferentiableAt ℝ
      (fun v => gaussianCurvature g p * jetEnergy g p v) u :=
    (jetEnergy_differentiableAt g p u).const_mul (gaussianCurvature g p)
  change coordPartial i (fun v => (jetMixed g p b v) ^ 2 +
    gaussianCurvature g p * jetEnergy g p v) u = _
  rw [HessianCalculus.coordPartial_add_at hsq hKE i,
    DarbouxJetCalculus.coordPartial_sq (jetMixed_differentiableAt g p u b) i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (gaussianCurvature g p))
      (jetEnergy_differentiableAt g p u) i,
    coordPartial_jetMixed]
  simp only [DarbouxJetCalculus.coordPartial_const, zero_mul, zero_add]
  ring

theorem solvedDarboux_firstJet_expanded (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetYY g p c u ≠ 0) (i : Fin 2) :
    coordPartial i (solvedDarboux g p b c) u =
      christoffel g i 0 0 p - 2 * (jetMixed g p b u / jetYY g p c u) * christoffel g i 0 1 p +
        (jetMixed g p b u / jetYY g p c u) ^ 2 * christoffel g i 1 1 p +
        gaussianCurvature g p *
          (coordPartial i (jetEnergy g p) u / jetYY g p c u +
            jetEnergy g p u * christoffel g i 1 1 p / (jetYY g p c u) ^ 2) := by
  have hN := jetNumerator_differentiableAt g p u b
  have hH := jetYY_differentiableAt g p u c
  have hQ : DifferentiableAt ℝ
      (fun v => jetNumerator g p b v / jetYY g p c v) u := by
    simpa only [div_eq_mul_inv, Function.comp_def] using
      (hN.hasFDerivAt.fun_mul
        ((hasDerivAt_inv hne).comp_hasFDerivAt u hH.hasFDerivAt)).differentiableAt
  change coordPartial i (fun v => jetConnection g p 0 0 v +
    jetNumerator g p b v / jetYY g p c v) u = _
  rw [HessianCalculus.coordPartial_add_at (jetConnection_differentiableAt g p u 0 0) hQ i,
    coordPartial_jetConnection, coordPartial_div hN hH hne i,
    coordPartial_jetNumerator, coordPartial_jetYY]
  simp only [jetNumerator]
  field_simp [hne]
  ring

theorem christoffelAlongD_eq {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (q : ℝ) (i : Fin 2) :
    christoffelAlongD g p q i =
      christoffel g i 0 0 p - 2 * q * christoffel g i 0 1 p +
        q ^ 2 * christoffel g i 1 1 p := by
  simp only [christoffelAlongD, Fin.sum_univ_two, jetDriftVector,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [christoffel_lower_symm hg hU hp i 1 0]
  ring

theorem solvedDarboux_firstJet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (u : Coord) (b c : ℝ) (hne : jetYY g p c u ≠ 0) (i : Fin 2) :
    coordPartial i (solvedDarboux g p b c) u =
      christoffelAlongD g p (jetMixed g p b u / jetYY g p c u) i +
        gaussianCurvature g p *
          (coordPartial i (jetEnergy g p) u / jetYY g p c u +
            jetEnergy g p u * christoffel g i 1 1 p / (jetYY g p c u) ^ 2) := by
  rw [christoffelAlongD_eq hg hU hp]
  exact solvedDarboux_firstJet_expanded g p u b c hne i

theorem jetEnergy_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (z : Coord → ℝ) :
    jetEnergy g p (fun i => coordPartial i z p) = heightEnergy g z p := by
  symm
  exact heightEnergy_polynomial z hg hp

theorem jetMixed_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetMixed g p (coordPartial 0 (coordPartial 1 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 1 := rfl

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

theorem product_one (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i : Fin 2) :
    iteratedCoordPartial [i] (fun x => a x * b x) p =
      iteratedCoordPartial [i] a p * b p + a p * iteratedCoordPartial [i] b p :=
  HessianCalculus.coordPartial_mul_at
    (iterated_differentiableAt ha hU hp []) (iterated_differentiableAt hb hU hp []) i

theorem product_two (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    iteratedCoordPartial [i, j] (fun x => a x * b x) p =
      iteratedCoordPartial [i, j] a p * b p +
      iteratedCoordPartial [j] a p * iteratedCoordPartial [i] b p +
      iteratedCoordPartial [i] a p * iteratedCoordPartial [j] b p +
      a p * iteratedCoordPartial [i, j] b p := by
  have he : coordPartial j (fun x => a x * b x) =ᶠ[𝓝 p]
      (fun x => coordPartial j a x * b x + a x * coordPartial j b x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact product_one ha hb hU hx j
  change coordPartial i (coordPartial j (fun x => a x * b x)) p = _
  rw [coordPartial_eq_of_eventuallyEq he i]
  have ha0 := iterated_differentiableAt ha hU hp []
  have hb0 := iterated_differentiableAt hb hU hp []
  have haj := iterated_differentiableAt ha hU hp [j]
  have hbj := iterated_differentiableAt hb hU hp [j]
  have ht0 : DifferentiableAt ℝ (fun x => coordPartial j a x * b x) p := haj.mul hb0
  have ht1 : DifferentiableAt ℝ (fun x => a x * coordPartial j b x) p := ha0.mul hbj
  rw [HessianCalculus.coordPartial_add_at
      (f := fun x => coordPartial j a x * b x) (h := fun x => a x * coordPartial j b x) ht0 ht1 i,
    HessianCalculus.coordPartial_mul_at (f := coordPartial j a) (h := b) haj hb0 i,
    HessianCalculus.coordPartial_mul_at (f := a) (h := coordPartial j b) ha0 hbj i]
  dsimp [iteratedCoordPartial]
  ring

theorem product_three (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] (fun x => a x * b x) p =
      iteratedCoordPartial [i, j, k] a p * b p +
      iteratedCoordPartial [j, k] a p * iteratedCoordPartial [i] b p +
      iteratedCoordPartial [i, k] a p * iteratedCoordPartial [j] b p +
      iteratedCoordPartial [k] a p * iteratedCoordPartial [i, j] b p +
      iteratedCoordPartial [i, j] a p * iteratedCoordPartial [k] b p +
      iteratedCoordPartial [j] a p * iteratedCoordPartial [i, k] b p +
      iteratedCoordPartial [i] a p * iteratedCoordPartial [j, k] b p +
      a p * iteratedCoordPartial [i, j, k] b p := by
  have he : iteratedCoordPartial [j, k] (fun x => a x * b x) =ᶠ[𝓝 p]
      (fun x => iteratedCoordPartial [j, k] a x * b x +
        iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x +
        iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x +
        a x * iteratedCoordPartial [j, k] b x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact product_two ha hb hU hx j k
  change coordPartial i (iteratedCoordPartial [j, k] (fun x => a x * b x)) p = _
  rw [coordPartial_eq_of_eventuallyEq he i]
  have ha0 := iterated_differentiableAt ha hU hp []
  have hb0 := iterated_differentiableAt hb hU hp []
  have haj := iterated_differentiableAt ha hU hp [j]
  have hak := iterated_differentiableAt ha hU hp [k]
  have hajk := iterated_differentiableAt ha hU hp [j, k]
  have hbj := iterated_differentiableAt hb hU hp [j]
  have hbk := iterated_differentiableAt hb hU hp [k]
  have hbjk := iterated_differentiableAt hb hU hp [j, k]
  have ht0 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x) p := hajk.mul hb0
  have ht1 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x) p := hak.mul hbj
  have ht2 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x) p := haj.mul hbk
  have ht3 : DifferentiableAt ℝ (fun x => a x * iteratedCoordPartial [j, k] b x) p := ha0.mul hbjk
  have ht01 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x +
      iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x) p := ht0.add ht1
  have ht012 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x +
      iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x +
      iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x) p := ht01.add ht2
  rw [HessianCalculus.coordPartial_add_at
      ht012 ht3 i,
    HessianCalculus.coordPartial_add_at ht01 ht2 i,
    HessianCalculus.coordPartial_add_at ht0 ht1 i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [j, k] a) (h := b) hajk hb0 i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [k] a) (h := iteratedCoordPartial [j] b) hak hbj i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [j] a) (h := iteratedCoordPartial [k] b) haj hbk i,
    HessianCalculus.coordPartial_mul_at (f := a) (h := iteratedCoordPartial [j, k] b) ha0 hbjk i]
  dsimp [iteratedCoordPartial]
  ring

theorem denominator_mul_quotient_word
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (ds : List (Fin 2)) :
    iteratedCoordPartial ds (fun x => b x * (a x / b x)) p =
      iteratedCoordPartial ds a p := by
  have he : (fun x => b x * (a x / b x)) =ᶠ[𝓝 p] a := by
    filter_upwards [hU.mem_nhds hp] with x hx
    field_simp [hne x hx]
  exact (iteratedCoordPartial_eventuallyEq he ds).self_of_nhds

theorem quotient_one (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i : Fin 2) :
    iteratedCoordPartial [i] (fun x => a x / b x) p =
      (iteratedCoordPartial [i] a p -
        iteratedCoordPartial [i] b p * (a p / b p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i]
  rw [product_one hb (quotient_contDiffOn ha hb hne) hU hp i] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

theorem quotient_two (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i j : Fin 2) :
    iteratedCoordPartial [i, j] (fun x => a x / b x) p =
      (iteratedCoordPartial [i, j] a p -
        (iteratedCoordPartial [i, j] b p * (a p / b p) +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j] (fun x => a x / b x) p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i, j]
  rw [product_two hb (quotient_contDiffOn ha hb hne) hU hp i j] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

theorem quotient_three (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] (fun x => a x / b x) p =
      (iteratedCoordPartial [i, j, k] a p -
        (iteratedCoordPartial [i, j, k] b p * (a p / b p) +
        iteratedCoordPartial [j, k] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i, k] b p * iteratedCoordPartial [j] (fun x => a x / b x) p +
        iteratedCoordPartial [k] b p * iteratedCoordPartial [i, j] (fun x => a x / b x) p +
        iteratedCoordPartial [i, j] b p * iteratedCoordPartial [k] (fun x => a x / b x) p +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i, k] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j, k] (fun x => a x / b x) p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i, j, k]
  rw [product_three hb (quotient_contDiffOn ha hb hne) hU hp i j k] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

end LowQuotient
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem hessianQuotient_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U :=
  (covHessian_contDiffOn hg hU hz 0 1).div (covHessian_contDiffOn hg hU hz 1 1) hyy

theorem darbouxG_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (darbouxG g z) U :=
  (heightEnergy_contDiffOn hg hU hz).div ((covHessian_contDiffOn hg hU hz 1 1).pow 2)
    (fun p hp => pow_ne_zero 2 (hyy p hp))

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.LowQuotient

theorem abs_add_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B := (abs_add_le x y).trans (add_le_add hx hy)

theorem abs_mul_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) (hA : 0 ≤ A) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) hA

theorem abs_sub_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x - y| ≤ A + B := (abs_sub x y).trans (add_le_add hx hy)

theorem abs_div_bound {x y N c : ℝ} (hN : 0 ≤ N) (hnum : |x| ≤ N)
    (hc : 0 < c) (hden : c ≤ |y|) : |x / y| ≤ N / c := by
  rw [abs_div]
  exact div_le_div₀ hN hnum hc hden

variable {U : Set Coord} {a b : Coord → ℝ} {M c : ℝ}

theorem denominator_ne_zero (hc : 0 < c) (hden : ∀ p ∈ U, c ≤ |b p|) :
    ∀ p ∈ U, b p ≠ 0 := by
  intro p hp hzero
  have hh := hden p hp
  rw [hzero, abs_zero] at hh
  linarith

theorem quotient_bound_zero (hM : 0 ≤ M) (hc : 0 < c)
    (ha0 : ∀ p ∈ U, |a p| ≤ M) (hden : ∀ p ∈ U, c ≤ |b p|)
    {p : Coord} (hp : p ∈ U) : |a p / b p| ≤ bound0 M c :=
  abs_div_bound hM (ha0 p hp) hc (hden p hp)

section SmoothQuotient
variable (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hU : IsOpen U)
variable (hM : 0 ≤ M) (hc : 0 < c)
variable (haB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds a p| ≤ M)
variable (hbB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds b p| ≤ M)
variable (hden : ∀ p ∈ U, c ≤ |b p|)
include ha hb hU hM hc haB hbB hden

theorem quotient_bound_one {p : Coord} (hp : p ∈ U) (i : Fin 2) :
    |iteratedCoordPartial [i] (fun x => a x / b x) p| ≤ bound1 M c := by
  rw [quotient_one ha hb hU hp (denominator_ne_zero hc hden) i]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  apply abs_div_bound (by have := (bounds_nonneg hM hc).1; positivity) _ hc (hden p hp)
  exact abs_sub_bound (haB [i] (by norm_num) p hp)
    (abs_mul_bound (hbB [i] (by norm_num) p hp) hq0 hM)

theorem quotient_bound_two {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    |iteratedCoordPartial [i, j] (fun x => a x / b x) p| ≤ bound2 M c := by
  rw [quotient_two ha hb hU hp (denominator_ne_zero hc hden) i j]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  have hqi := quotient_bound_one ha hb hU hM hc haB hbB hden hp i
  have hqj := quotient_bound_one ha hb hU hM hc haB hbB hden hp j
  have hterm0 := abs_mul_bound (hbB [i, j] (by norm_num) p hp) hq0 hM
  have htermi := abs_mul_bound (hbB [j] (by norm_num) p hp) hqi hM
  have htermj := abs_mul_bound (hbB [i] (by norm_num) p hp) hqj hM
  have hrest := abs_add_bound (abs_add_bound hterm0 htermi) htermj
  have hnum := abs_sub_bound (haB [i, j] (by norm_num) p hp) hrest
  have hnum' :
      |iteratedCoordPartial [i, j] a p -
        (iteratedCoordPartial [i, j] b p * (a p / b p) +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j] (fun x => a x / b x) p)| ≤
        M + M * bound0 M c + 2 * M * bound1 M c := by
    convert hnum using 1 <;> first | rfl | ring
  exact abs_div_bound (by obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc; positivity)
    hnum' hc (hden p hp)

theorem quotient_bound_three {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    |iteratedCoordPartial [i, j, k] (fun x => a x / b x) p| ≤ bound3 M c := by
  rw [quotient_three ha hb hU hp (denominator_ne_zero hc hden) i j k]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  have hqi := quotient_bound_one ha hb hU hM hc haB hbB hden hp i
  have hqj := quotient_bound_one ha hb hU hM hc haB hbB hden hp j
  have hqk := quotient_bound_one ha hb hU hM hc haB hbB hden hp k
  have hqij := quotient_bound_two ha hb hU hM hc haB hbB hden hp i j
  have hqik := quotient_bound_two ha hb hU hM hc haB hbB hden hp i k
  have hqjk := quotient_bound_two ha hb hU hM hc haB hbB hden hp j k
  have h0 := abs_mul_bound (hbB [i, j, k] (by norm_num) p hp) hq0 hM
  have h1 := abs_mul_bound (hbB [j, k] (by norm_num) p hp) hqi hM
  have h2 := abs_mul_bound (hbB [i, k] (by norm_num) p hp) hqj hM
  have h3 := abs_mul_bound (hbB [k] (by norm_num) p hp) hqij hM
  have h4 := abs_mul_bound (hbB [i, j] (by norm_num) p hp) hqk hM
  have h5 := abs_mul_bound (hbB [j] (by norm_num) p hp) hqik hM
  have h6 := abs_mul_bound (hbB [i] (by norm_num) p hp) hqjk hM
  have hrest := abs_add_bound (abs_add_bound (abs_add_bound (abs_add_bound
    (abs_add_bound (abs_add_bound h0 h1) h2) h3) h4) h5) h6
  have hnum := abs_sub_bound (haB [i, j, k] (by norm_num) p hp) hrest
  have hnum' :
      |iteratedCoordPartial [i, j, k] a p -
        (iteratedCoordPartial [i, j, k] b p * (a p / b p) +
        iteratedCoordPartial [j, k] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i, k] b p * iteratedCoordPartial [j] (fun x => a x / b x) p +
        iteratedCoordPartial [k] b p * iteratedCoordPartial [i, j] (fun x => a x / b x) p +
        iteratedCoordPartial [i, j] b p * iteratedCoordPartial [k] (fun x => a x / b x) p +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i, k] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j, k] (fun x => a x / b x) p)| ≤
        M + M * bound0 M c + 3 * M * bound1 M c + 3 * M * bound2 M c := by
    convert hnum using 1 <;> first | rfl | ring
  exact abs_div_bound (by obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc; positivity)
    hnum' hc (hden p hp)

theorem quotient_bound_through_three (ds : List (Fin 2)) (hlen : ds.length ≤ 3)
    {p : Coord} (hp : p ∈ U) :
    |iteratedCoordPartial ds (fun x => a x / b x) p| ≤ boundThroughThree M c := by
  obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc
  have hB0 : bound0 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB1 : bound1 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB2 : bound2 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  have hB3 : bound3 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree]; linarith
  cases ds with
  | nil => exact (quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp).trans hB0
  | cons i ds =>
    cases ds with
    | nil => exact (quotient_bound_one ha hb hU hM hc haB hbB hden hp i).trans hB1
    | cons j ds =>
      cases ds with
      | nil => exact (quotient_bound_two ha hb hU hM hc haB hbB hden hp i j).trans hB2
      | cons k ds =>
        cases ds with
        | nil => exact (quotient_bound_three ha hb hU hM hc haB hbB hden hp i j k).trans hB3
        | cons l ds => simp only [List.length_cons] at hlen; omega

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

theorem solutionJet_contDiffOn {z : Coord → ℝ} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (solutionJet z) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_apply ℝ ℝ 0 U
  · exact contDiffOn_apply ℝ ℝ 1 U
  · exact partial_contDiffOn hz hU 0
  · exact partial_contDiffOn hz hU 1
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1

theorem solutionJet_mem_domain (g : MetricField) (z : Coord → ℝ) {p : Coord}
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    solutionJet z p ∈ darbouxStateDomain g U := by
  constructor
  · simpa only [statePoint_solutionJet] using hp
  · simpa only [stateDenominator_solutionJet] using hyy

end SmoothLocal.HighEquation

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

theorem iterated_append (ds es : List (Fin 2)) (f : Coord → ℝ) :
    iteratedCoordPartial (ds ++ es) f = iteratedCoordPartial ds (iteratedCoordPartial es f) := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [List.cons_append, iteratedCoordPartial, ih]

theorem partial_bound {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hf : CoordinateBound f U (n + 1) M) (i : Fin 2) :
    CoordinateBound (coordPartial i f) U n M := by
  intro ds hds p hp
  have hh := hf (ds ++ [i]) (by simpa only [List.length_append, List.length_singleton] using Nat.add_le_add_right hds 1) p hp
  rw [iterated_append] at hh
  exact hh

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

theorem iterated_sub {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => f x - h x) p =
      iteratedCoordPartial ds f p - iteratedCoordPartial ds h p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => f x - h x) =ᶠ[𝓝 p]
        (fun x => iteratedCoordPartial ds f x - iteratedCoordPartial ds h x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => f x - h x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    exact HessianCalculus.coordPartial_sub_at
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

theorem add {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hfB : CoordinateBound f U n A) (hhB : CoordinateBound h U n B) :
    CoordinateBound (fun x => f x + h x) U n (A + B) := by
  intro ds hds p hp
  rw [iterated_add hf hh hU ds hp]
  exact (abs_add_le _ _).trans (add_le_add (hfB ds hds p hp) (hhB ds hds p hp))

theorem sub {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hfB : CoordinateBound f U n A) (hhB : CoordinateBound h U n B) :
    CoordinateBound (fun x => f x - h x) U n (A + B) := by
  intro ds hds p hp
  rw [iterated_sub hf hh hU ds hp]
  exact (abs_sub _ _).trans (add_le_add (hfB ds hds p hp) (hhB ds hds p hp))

theorem const_mul {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {A : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hfB : CoordinateBound f U n A) (c : ℝ) :
    CoordinateBound (fun x => c * f x) U n (|c| * A) := by
  intro ds hds p hp
  rw [iterated_const_mul hf hU c ds hp, abs_mul]
  exact mul_le_mul_of_nonneg_left (hfB ds hds p hp) (abs_nonneg c)

theorem neg {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {A : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hfB : CoordinateBound f U n A) :
    CoordinateBound (fun x => -f x) U n A := by
  simpa only [neg_one_mul, abs_neg, abs_one, one_mul] using const_mul hf hU hfB (-1)

theorem abs_add_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x + y| ≤ A + B := (abs_add_le x y).trans (add_le_add hx hy)

theorem mul_through_three {f h : Coord → ℝ} {U : Set Coord} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : CoordinateBound f U 3 A) (hhB : CoordinateBound h U 3 B) :
    CoordinateBound (fun x => f x * h x) U 3 (8 * A * B) := by
  intro ds hds p hp
  have hab (vs ws : List (Fin 2)) (hv : vs.length ≤ 3) (hw : ws.length ≤ 3) :
      |iteratedCoordPartial vs f p * iteratedCoordPartial ws h p| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hfB vs hv p hp) (hhB ws hw p hp) (abs_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  cases ds with
  | nil =>
    exact (hab [] [] (by norm_num) (by norm_num)).trans (by nlinarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.product_one hf hh hU hp i]
      exact (abs_add_bound (hab [i] [] (by norm_num) (by norm_num))
        (hab [] [i] (by norm_num) (by norm_num))).trans (by nlinarith)
    | cons j ds =>
      cases ds with
      | nil =>
        rw [LowQuotient.product_two hf hh hU hp i j]
        exact (abs_add_bound (abs_add_bound (abs_add_bound
          (hab [i, j] [] (by norm_num) (by norm_num))
          (hab [j] [i] (by norm_num) (by norm_num)))
          (hab [i] [j] (by norm_num) (by norm_num)))
          (hab [] [i, j] (by norm_num) (by norm_num))).trans (by nlinarith)
      | cons k ds =>
        cases ds with
        | nil =>
          rw [LowQuotient.product_three hf hh hU hp i j k]
          have hsum := abs_add_bound (abs_add_bound (abs_add_bound (abs_add_bound
            (abs_add_bound (abs_add_bound (abs_add_bound
            (hab [i, j, k] [] (by norm_num) (by norm_num))
            (hab [j, k] [i] (by norm_num) (by norm_num)))
            (hab [i, k] [j] (by norm_num) (by norm_num)))
            (hab [k] [i, j] (by norm_num) (by norm_num)))
            (hab [i, j] [k] (by norm_num) (by norm_num)))
            (hab [j] [i, k] (by norm_num) (by norm_num)))
            (hab [i] [j, k] (by norm_num) (by norm_num)))
            (hab [] [i, j, k] (by norm_num) (by norm_num))
          convert hsum using 1 <;> first | rfl | ring
        | cons l ds => simp only [List.length_cons] at hds; omega

end CoordinateBound
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

def solutionJetCurve (z : Coord → ℝ) (x : ℝ) : ℝ → DarbouxState :=
  fun y => solutionJet z ![x, y]

theorem verticalPoint_contDiff (x : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => (![x, y] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

theorem solutionJetCurve_contDiffAt {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U) :
    ContDiffAt ℝ ∞ (solutionJetCurve z x) y :=
  ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).comp y
    (verticalPoint_contDiff x).contDiffAt

theorem sixVariableP_contDiffAt_solutionJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    ContDiffAt ℝ ∞ (sixVariableP g) (solutionJet z p) :=
  (sixVariableP_contDiffOn hg hU).contDiffAt
    ((darbouxStateDomain_isOpen hg hU).mem_nhds (solutionJet_mem_domain g z hp hyy))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem heightPFirst_eq
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    heightPFirst g z i p = christoffelAlongD g p (hessianQuotient g z p) i +
      gaussianCurvature g p *
        (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
          heightEnergy g z p * christoffel g i 1 1 p / (covHessian g z p 1 1) ^ 2) := by
  simpa only [heightPFirst, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z, hessianQuotient] using
    solvedDarboux_firstJet hg hU hp (fun r => coordPartial r z p)
      (coordPartial 0 (coordPartial 1 z) p) (coordPartial 1 (coordPartial 1 z) p) hyy i

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {M c : ℝ}

theorem hessianQuotient_coordinate_bound_through_three
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hM : 0 ≤ M) (hc : 0 < c)
    (hH : ∀ i j : Fin 2, ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
      |iteratedCoordPartial ds (fun x => covHessian g z x i j) p| ≤ M)
    (hden : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U ∧
      ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
        |iteratedCoordPartial ds (hessianQuotient g z) p| ≤ LowQuotient.boundThroughThree M c := by
  have hxy := covHessian_contDiffOn hg hU hz 0 1
  have hyy := covHessian_contDiffOn hg hU hz 1 1
  refine ⟨hessianQuotient_contDiffOn hg hU hz (LowQuotient.denominator_ne_zero hc hden), ?_⟩
  intro ds hlen p hp
  exact LowQuotient.quotient_bound_through_three hxy hyy hU hM hc (hH 0 1) (hH 1 1) hden ds hlen hp

end SmoothLocal.Geometry

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

theorem verticalPoint_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (![x, t] : Coord)) (Pi.single 1 (1 : ℝ)) y := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using hasDerivAt_const y x
  · convert hasDerivAt_id y using 1 <;> rfl

theorem verticalJet_slice_hasDerivAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (n : ℕ)
    (hp : (![x, y] : Coord) ∈ U) :
    HasDerivAt (fun t => verticalJet f n ![x, t]) (verticalJet f (n + 1) ![x, y]) y := by
  have hd : DifferentiableAt ℝ (verticalJet f n) ![x, y] :=
    (((verticalJet_contDiffOn hU hf n).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  exact hd.hasFDerivAt.comp_hasDerivAt y (verticalPoint_hasDerivAt x y)

theorem verticalJet_slice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (x : ℝ) : ∀ n y, (![x, y] : Coord) ∈ U →
      iteratedDeriv n (fun t => f ![x, t]) y = verticalJet f n ![x, y] := by
  intro n
  induction n with
  | zero => intro y hy; rfl
  | succ n hn =>
    intro y hy
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun t => f ![x, t]) =ᶠ[𝓝 y]
        (fun t => verticalJet f n ![x, t]) := by
      filter_upwards [(hU.preimage (verticalPoint_contDiff x).continuous).mem_nhds hy] with t ht
      exact hn t ht
    rw [heq.deriv_eq]
    exact (verticalJet_slice_hasDerivAt hU hf n hy).deriv

theorem verticalJet_coordPartial
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (i : Fin 2) : ∀ n p, p ∈ U →
      verticalJet (coordPartial i f) n p = coordPartial i (verticalJet f n) p := by
  intro n
  induction n with
  | zero => intro p hp; rfl
  | succ n hn =>
    intro p hp
    have heq : verticalJet (coordPartial i f) n =ᶠ[𝓝 p] coordPartial i (verticalJet f n) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact hn q hq
    have hd : coordPartial 1 (verticalJet (coordPartial i f) n) p =
        coordPartial 1 (coordPartial i (verticalJet f n)) p := by
      exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single 1 1)) heq.fderiv_eq
    change coordPartial 1 (verticalJet (coordPartial i f) n) p =
      coordPartial i (coordPartial 1 (verticalJet f n)) p
    rw [hd]
    exact coordPartial_comm (verticalJet_contDiffOn hU hf n) hU hp 1 i

theorem verticalJet_two_coordPartials
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hp : p ∈ U) (n : ℕ) (i j : Fin 2) :
    verticalJet (coordPartial i (coordPartial j f)) n p =
      coordPartial i (coordPartial j (verticalJet f n)) p := by
  rw [verticalJet_coordPartial hU (normed_coordPartial_contDiffOn hf hU j) i n p hp]
  have heq : verticalJet (coordPartial j f) n =ᶠ[𝓝 p] coordPartial j (verticalJet f n) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact verticalJet_coordPartial hU hf j n q hq
  exact congrArg (fun L : Coord →L[ℝ] V => L (Pi.single i 1)) heq.fderiv_eq

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
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

theorem metricDet_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G) :
    CoordinateBound (fun p => (g p).det) U 3 (16 * G^2) := by
  have hdiag := CoordinateBound.mul_through_three (hg.1 0 0) (hg.1 1 1) hU hG hG (hgB 0 0) (hgB 1 1)
  have hoff := CoordinateBound.mul_through_three (hg.1 0 1) (hg.1 1 0) hU hG hG (hgB 0 1) (hgB 1 0)
  have hdet := CoordinateBound.sub ((hg.1 0 0).mul (hg.1 1 1))
    ((hg.1 0 1).mul (hg.1 1 0)) hU hdiag hoff
  have hc : 8 * G * G + 8 * G * G = 16 * G^2 := by ring
  simpa only [Matrix.det_fin_two, hc] using hdet

theorem metricAdjugate_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G) (i j : Fin 2) :
    CoordinateBound (fun p => (g p).adjugate i j) U 3 G := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hgB 1 1
  · simpa [Matrix.adjugate_fin_two] using CoordinateBound.neg (hg.1 0 1) hU (hgB 0 1)
  · simpa [Matrix.adjugate_fin_two] using CoordinateBound.neg (hg.1 1 0) hU (hgB 1 0)
  · simpa [Matrix.adjugate_fin_two] using hgB 0 0

theorem inverseMetric_eq_adjugate_div (g : MetricField) (i j : Fin 2) :
    (fun p => inverseMetric g p i j) = (fun p => (g p).adjugate i j / (g p).det) := by
  funext p
  simp [inverseMetric, Matrix.inv_def, Ring.inverse_eq_inv, div_eq_mul_inv, smul_eq_mul, mul_comm]

theorem inverseMetric_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => inverseMetric g p i j) U 3 (metricInverseJetBound G d) := by
  have hN : 0 ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound]; positivity
  have hGN : G ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound]; nlinarith [sq_nonneg G]
  have hDN : 16 * G^2 ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound]; linarith
  have hadj := (metricAdjugate_coordinate_bound hg hU hgB i j).mono le_rfl hGN
  have hdetB := (metricDet_coordinate_bound hg hU hG hgB).mono le_rfl hDN
  rw [inverseMetric_eq_adjugate_div]
  intro ds hds p hp
  exact LowQuotient.quotient_bound_through_three (metricAdjugate_contDiffOn hg i j)
    (metricDet_contDiffOn hg) hU hN hd hadj hdetB hdet ds hds hp

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.CoordinateBound

theorem congr_on {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hU : IsOpen U) (hf : CoordinateBound f U n M) (he : EqOn h f U) :
    CoordinateBound h U n M := by
  intro ds hds p hp
  have hlocal : h =ᶠ[𝓝 p] f := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact he hx
  rw [(iteratedCoordPartial_eventuallyEq hlocal ds).self_of_nhds]
  exact hf ds hds p hp

theorem mul_through_one {f h : Coord → ℝ} {U : Set Coord} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : CoordinateBound f U 1 A) (hhB : CoordinateBound h U 1 B) :
    CoordinateBound (fun x => f x * h x) U 1 (2 * A * B) := by
  intro ds hds p hp
  have hab (vs ws : List (Fin 2)) (hv : vs.length ≤ 1) (hw : ws.length ≤ 1) :
      |iteratedCoordPartial vs f p * iteratedCoordPartial ws h p| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hfB vs hv p hp) (hhB ws hw p hp) (abs_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  cases ds with
  | nil => exact (hab [] [] (by norm_num) (by norm_num)).trans (by nlinarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.product_one hf hh hU hp i]
      exact ((abs_add_le _ _).trans
        (add_le_add (hab [i] [] (by norm_num) (by norm_num))
          (hab [] [i] (by norm_num) (by norm_num)))).trans (le_of_eq (by ring))
    | cons j ds => simp only [List.length_cons] at hds; omega

theorem div_through_one {f h : Coord → ℝ} {U : Set Coord} {A B c : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    (hfB : CoordinateBound f U 1 A) (hhB : CoordinateBound h U 1 B)
    (hden : ∀ p ∈ U, c ≤ |h p|) :
    CoordinateBound (fun x => f x / h x) U 1 (A / c + (A + B * (A / c)) / c) := by
  have hne := LowQuotient.denominator_ne_zero hc hden
  have hval (p : Coord) (hp : p ∈ U) : |f p / h p| ≤ A / c :=
    LowQuotient.abs_div_bound hA (hfB [] (by norm_num) p hp) hc (hden p hp)
  have h0 : 0 ≤ A / c := by positivity
  have h1 : 0 ≤ (A + B * (A / c)) / c := by positivity
  intro ds hds p hp
  cases ds with
  | nil => exact (hval p hp).trans (by linarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.quotient_one hf hh hU hp hne i]
      have hprod : |coordPartial i h p * (f p / h p)| ≤ B * (A / c) := by
        rw [abs_mul]
        exact mul_le_mul (hhB [i] (by norm_num) p hp) (hval p hp) (abs_nonneg _) hB
      have hnum := (abs_sub (coordPartial i f p) (coordPartial i h p * (f p / h p))).trans
        (add_le_add (hfB [i] (by norm_num) p hp) hprod)
      exact (LowQuotient.abs_div_bound (by positivity) hnum hc (hden p hp)).trans (by linarith)
    | cons j ds => simp only [List.length_cons] at hds; omega

end SmoothLocal.Geometry.CoordinateBound

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
open Set Filter
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Geometry

def connectionBracket (g : MetricField) (i j l : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (fun x => g x j l) p + coordPartial j (fun x => g x i l) p -
    coordPartial l (fun x => g x i j) p

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem connectionBracket_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (i j l : Fin 2) : ContDiffOn ℝ ∞ (connectionBracket g i j l) U :=
  ((partial_contDiffOn (hg.1 j l) hU i).add
    (partial_contDiffOn (hg.1 i l) hU j)).sub (partial_contDiffOn (hg.1 i j) hU l)

theorem connectionBracket_coordinate_bound (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G) (i j l : Fin 2) :
    CoordinateBound (connectionBracket g i j l) U 3 (3 * G) := by
  have h1 : CoordinateBound (coordPartial i (fun p => g p j l)) U 3 G := (hgB j l).partial_bound i
  have h2 : CoordinateBound (coordPartial j (fun p => g p i l)) U 3 G := (hgB i l).partial_bound j
  have h3 : CoordinateBound (coordPartial l (fun p => g p i j)) U 3 G := (hgB i j).partial_bound l
  have hb := CoordinateBound.sub
    ((partial_contDiffOn (hg.1 j l) hU i).add (partial_contDiffOn (hg.1 i l) hU j))
    (partial_contDiffOn (hg.1 i j) hU l) hU
    (CoordinateBound.add (partial_contDiffOn (hg.1 j l) hU i)
      (partial_contDiffOn (hg.1 i l) hU j) hU h1 h2) h3
  have he : G + G + G = 3 * G := by ring
  rw [he] at hb
  exact hb

theorem christoffel_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (k i j : Fin 2) :
    CoordinateBound (christoffel g k i j) U 3 (christoffelJetBound G d) := by
  have hg3 (a b : Fin 2) : CoordinateBound (fun p => g p a b) U 3 G :=
    (hgB a b).mono (by norm_num) le_rfl
  have hI := metricInverseJetBound_nonneg hG hd
  have hprod (l : Fin 2) : CoordinateBound
      (fun p => inverseMetric g p k l * connectionBracket g i j l p) U 3
      (8 * metricInverseJetBound G d * (3 * G)) :=
    CoordinateBound.mul_through_three (inverseMetric_contDiffOn hg k l)
      (connectionBracket_contDiffOn hg hU i j l) hU hI (by positivity)
      (inverseMetric_coordinate_bound hg hU hG hd hg3 hdet k l)
      (connectionBracket_coordinate_bound hg hU hgB i j l)
  have hs := CoordinateBound.add
    ((inverseMetric_contDiffOn hg k 0).mul (connectionBracket_contDiffOn hg hU i j 0))
    ((inverseMetric_contDiffOn hg k 1).mul (connectionBracket_contDiffOn hg hU i j 1))
    hU (hprod 0) (hprod 1)
  have hhalf := CoordinateBound.const_mul
    (((inverseMetric_contDiffOn hg k 0).mul (connectionBracket_contDiffOn hg hU i j 0)).add
      ((inverseMetric_contDiffOn hg k 1).mul (connectionBracket_contDiffOn hg hU i j 1)))
    hU hs (1 / 2 : ℝ)
  have hc : |(1 / 2 : ℝ)| *
      (8 * metricInverseJetBound G d * (3 * G) + 8 * metricInverseJetBound G d * (3 * G)) =
      christoffelJetBound G d := by
    norm_num [christoffelJetBound]
    ring
  rw [hc] at hhalf
  convert hhalf using 1
  funext p
  simp only [christoffel, Fin.sum_univ_two, connectionBracket]

theorem covHessian_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => covHessian g z p i j) U 3 (hessianJetBound G Z d) := by
  have hz4 (a : Fin 2) : CoordinateBound (coordPartial a z) U 4 Z := hzB.partial_bound a
  have hz1 (a : Fin 2) : CoordinateBound (coordPartial a z) U 3 Z :=
    (hz4 a).mono (by norm_num) le_rfl
  have hz2 : CoordinateBound (coordPartial i (coordPartial j z)) U 3 Z := (hz4 j).partial_bound i
  have hΓ := christoffelJetBound_nonneg hG hd
  have hprod (a : Fin 2) : CoordinateBound
      (fun p => christoffel g a i j p * coordPartial a z p) U 3
      (8 * christoffelJetBound G d * Z) :=
    CoordinateBound.mul_through_three (christoffel_contDiffOn hg hU a i j)
      (partial_contDiffOn hz hU a) hU hΓ hZ
      (christoffel_coordinate_bound hg hU hG hd hgB hdet a i j) (hz1 a)
  have hs := CoordinateBound.add
    ((christoffel_contDiffOn hg hU 0 i j).mul (partial_contDiffOn hz hU 0))
    ((christoffel_contDiffOn hg hU 1 i j).mul (partial_contDiffOn hz hU 1))
    hU (hprod 0) (hprod 1)
  have hh := CoordinateBound.sub (partial_contDiffOn (partial_contDiffOn hz hU j) hU i)
    (((christoffel_contDiffOn hg hU 0 i j).mul (partial_contDiffOn hz hU 0)).add
      ((christoffel_contDiffOn hg hU 1 i j).mul (partial_contDiffOn hz hU 1))) hU hz2 hs
  have hc : Z + (8 * christoffelJetBound G d * Z + 8 * christoffelJetBound G d * Z) =
      hessianJetBound G Z d := by dsimp [hessianJetBound]; ring
  simpa only [covHessian, Fin.sum_univ_two, hc] using hh

theorem hessianQuotient_bound_from_metric_height_jets
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U ∧
      CoordinateBound (hessianQuotient g z) U 3
        (LowQuotient.boundThroughThree (hessianJetBound G Z d) c) := by
  exact hessianQuotient_coordinate_bound_through_three hg hU hz
    (hessianJetBound_nonneg hG hZ hd) hc
    (fun i j => covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet i j) hyy

end SmoothLocal.Geometry

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
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

theorem riemann_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (l k i j : Fin 2) :
    CoordinateBound (riemann g l k i j) U 1 (riemannFirstBound G d) := by
  have hΓ := christoffelJetBound_nonneg hG hd
  have hΓB (a b c : Fin 2) := christoffel_coordinate_bound hg hU hG hd hgB hdet a b c
  have hΓ1 (a b c : Fin 2) : CoordinateBound (christoffel g a b c) U 1 (christoffelJetBound G d) :=
    (hΓB a b c).mono (by norm_num) le_rfl
  have hΓd (a b c e : Fin 2) : CoordinateBound (coordPartial e (christoffel g a b c)) U 1
      (christoffelJetBound G d) :=
    ((hΓB a b c).mono (by norm_num : 2 ≤ 3) le_rfl).partial_bound e
  have hΓs (a b c : Fin 2) := christoffel_contDiffOn hg hU a b c
  have hm (m : Fin 2) := CoordinateBound.sub
    ((hΓs m j k).mul (hΓs l i m)) ((hΓs m i k).mul (hΓs l j m)) hU
    (CoordinateBound.mul_through_one (hΓs m j k) (hΓs l i m) hU hΓ hΓ (hΓ1 m j k) (hΓ1 l i m))
    (CoordinateBound.mul_through_one (hΓs m i k) (hΓs l j m) hU hΓ hΓ (hΓ1 m i k) (hΓ1 l j m))
  have hms (m : Fin 2) := ((hΓs m j k).mul (hΓs l i m)).sub ((hΓs m i k).mul (hΓs l j m))
  have hs := CoordinateBound.add (hms 0) (hms 1) hU (hm 0) (hm 1)
  have hdiff := CoordinateBound.sub (partial_contDiffOn (hΓs l j k) hU i)
    (partial_contDiffOn (hΓs l i k) hU j) hU (hΓd l j k i) (hΓd l i k j)
  have hb := CoordinateBound.add
    ((partial_contDiffOn (hΓs l j k) hU i).sub (partial_contDiffOn (hΓs l i k) hU j))
    ((hms 0).add (hms 1)) hU hdiff hs
  convert hb using 1 <;> first
    | (funext p; simp only [riemann, Fin.sum_univ_two])
    | (dsimp [riemannFirstBound]; ring)

theorem gaussianCurvature_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) :
    CoordinateBound (gaussianCurvature g) U 1 (curvatureFirstBound G d) := by
  have hR := riemannFirstBound_nonneg hG hd
  have hprod (l : Fin 2) := CoordinateBound.mul_through_one (hg.1 0 l)
    (riemann_contDiffOn hg hU l 1 0 1) hU hG hR
    ((hgB 0 l).mono (by norm_num) le_rfl)
    (riemann_coordinate_bound_one hg hU hG hd hgB hdet l 1 0 1)
  have hprodS (l : Fin 2) := (hg.1 0 l).mul (riemann_contDiffOn hg hU l 1 0 1)
  have hsum := CoordinateBound.add (hprodS 0) (hprodS 1) hU (hprod 0) (hprod 1)
  have hn : CoordinateBound (fun p => g p 0 0 * riemann g 0 1 0 1 p +
      g p 0 1 * riemann g 1 1 0 1 p) U 1 (curvatureNumeratorFirstBound G d) := by
    convert hsum using 1
    dsimp [curvatureNumeratorFirstBound]
    ring
  have hnb : 0 ≤ curvatureNumeratorFirstBound G d := by dsimp [curvatureNumeratorFirstBound]; positivity
  have hdb : CoordinateBound (fun p => (g p).det) U 1 (16 * G^2) :=
    (metricDet_coordinate_bound hg hU hG (fun i j => (hgB i j).mono (by norm_num) le_rfl)).mono
      (by norm_num) le_rfl
  have hb := CoordinateBound.div_through_one ((hprodS 0).add (hprodS 1))
    (metricDet_contDiffOn hg) hU hnb (by positivity : 0 ≤ 16 * G^2) hd hn hdb hdet
  convert hb using 1 <;> try rfl
  funext p
  simp only [gaussianCurvature, Fin.sum_univ_two]

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
open SmoothLocal.Flow SmoothLocal.ODE

theorem exists_open_hessianQuotient_domain
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : modelSquare ⊆ U)
    (hyy : ∀ p ∈ modelSquare, covHessian g z p 1 1 ≠ 0) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      ContDiffOn ℝ ∞ (hessianQuotient g z) V := by
  let V := U ∩ (fun p => covHessian g z p 1 1) ⁻¹' ({0} : Set ℝ)ᶜ
  have hV : IsOpen V :=
    (covHessian_contDiffOn hg hU hz 1 1).continuousOn.isOpen_inter_preimage
      hU isClosed_singleton.isOpen_compl
  have hVU : V ⊆ U := fun _ hp => hp.1
  have hSV : modelSquare ⊆ V := fun p hp => ⟨hSU hp, hyy p hp⟩
  have hnonzero : ∀ p ∈ V, covHessian g z p 1 1 ≠ 0 := fun _ hp => hp.2
  have hgv : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  exact ⟨V, hV, hSV, hVU, hnonzero,
    hessianQuotient_contDiffOn hgv hV (hz.mono hVU) hnonzero⟩

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
open SmoothLocal.Flow SmoothLocal.ODE

theorem modelSquare_closure_interior : closure (interior modelSquare) = modelSquare := by
  unfold modelSquare
  rw [← Set.pi_univ_Icc, interior_pi_set (Set.finite_univ : (Set.univ : Set (Fin 2)).Finite)]
  simp only [interior_Icc, closure_pi_set,
    closure_Ioo (by norm_num : (-3 : ℝ) ≠ 3), Set.pi_univ_Icc]

theorem CoordinateBound.restrict_domain {f : Coord → ℝ} {S T : Set Coord} {n : ℕ} {M : ℝ}
    (hf : CoordinateBound f S n M) (hTS : T ⊆ S) : CoordinateBound f T n M :=
  fun ds hds p hp => hf ds hds p (hTS hp)

theorem CoordinateBound.of_modelSquare_interior {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hB : CoordinateBound f (interior modelSquare) n M) : CoordinateBound f modelSquare n M := by
  intro ds hds p hp
  have hcont : ContinuousOn (fun x => |iteratedCoordPartial ds f x|) modelSquare :=
    ((LowQuotient.iterated_contDiffOn hf hU ds).continuousOn.mono hSU).abs
  have hcl : p ∈ closure (interior modelSquare) := by rw [modelSquare_closure_interior]; exact hp
  apply le_on_closure (fun x hx => hB ds hds x hx) _ continuousOn_const hcl
  rw [modelSquare_closure_interior]
  exact hcont

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem exists_open_quotient_domain_with_closed_low_bounds
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      ContDiffOn ℝ ∞ (hessianQuotient g z) V ∧
      CoordinateBound (hessianQuotient g z) modelSquare 3
        (LowQuotient.boundThroughThree (hessianJetBound G Z d) c) := by
  obtain ⟨V, hV, hSV, hVU, hVne, hqV⟩ := exists_open_hessianQuotient_domain hg hU hz hSU
    (LowQuotient.denominator_ne_zero hc hyy)
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun a b => (hg.1 a b).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hBI := (hessianQuotient_bound_from_metric_height_jets hgI isOpen_interior (hz.mono hIU)
    hG hZ hd hc (fun a b => (hgB a b).restrict_domain interior_subset)
    (hzB.restrict_domain interior_subset) (fun p hp => hdet p (interior_subset hp))
    (fun p hp => hyy p (interior_subset hp))).2
  exact ⟨V, hV, hSV, hVU, hVne, hqV,
    CoordinateBound.of_modelSquare_interior hqV hV hSV hBI⟩

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

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem height_jetEnergy_first_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p)) U := by
  have h0 := partial_contDiffOn hz hU 0
  have h1 := partial_contDiffOn hz hU 1
  fin_cases i
  · have hf : ContDiffOn ℝ ∞ (fun p => -2 * g p 1 1 * coordPartial 0 z p +
        (g p 0 1 + g p 1 0) * coordPartial 1 z p) U :=
      ((contDiffOn_const.mul (hg.1 1 1)).mul h0).add (((hg.1 0 1).add (hg.1 1 0)).mul h1)
    apply hf.congr
    intro p _
    simpa only [Fin.mk_zero, ↓reduceIte] using
      coordPartial_jetEnergy g p (fun r => coordPartial r z p) 0
  · have hf : ContDiffOn ℝ ∞ (fun p => (g p 0 1 + g p 1 0) * coordPartial 0 z p -
        2 * g p 0 0 * coordPartial 1 z p) U :=
      (((hg.1 0 1).add (hg.1 1 0)).mul h0).sub ((contDiffOn_const.mul (hg.1 0 0)).mul h1)
    apply hf.congr
    intro p _
    simpa only [Fin.mk_one, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
      coordPartial_jetEnergy g p (fun r => coordPartial r z p) 1

theorem height_christoffelAlongD_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => christoffelAlongD g p (hessianQuotient g z p) i) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  have hf : ContDiffOn ℝ ∞ (fun p => christoffel g i 0 0 p -
      2 * hessianQuotient g z p * christoffel g i 0 1 p +
      (hessianQuotient g z p)^2 * christoffel g i 1 1 p) U :=
    ((christoffel_contDiffOn hg hU i 0 0).sub
      ((contDiffOn_const.mul hq).mul (christoffel_contDiffOn hg hU i 0 1))).add
      ((hq.pow 2).mul (christoffel_contDiffOn hg hU i 1 1))
  exact hf.congr (fun p hp => christoffelAlongD_eq hg hU hp _ i)

theorem heightPFirst_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (heightPFirst g z i) U := by
  have hh := covHessian_contDiffOn hg hU hz 1 1
  have hf : ContDiffOn ℝ ∞ (fun p => christoffelAlongD g p (hessianQuotient g z p) i +
      gaussianCurvature g p *
        (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
          heightEnergy g z p * christoffel g i 1 1 p / (covHessian g z p 1 1)^2)) U :=
    (height_christoffelAlongD_contDiffOn hg hU hz hyy i).add
      ((gaussianCurvature_contDiffOn hg hU).mul
        (((height_jetEnergy_first_contDiffOn hg hU hz i).div hh hyy).add
          (((heightEnergy_contDiffOn hg hU hz).mul (christoffel_contDiffOn hg hU i 1 1)).div
            (hh.pow 2) (fun p hp => pow_ne_zero 2 (hyy p hp)))))
  exact hf.congr (fun p hp => heightPFirst_eq hg hU hp (hyy p hp) i)

end SmoothLocal.Geometry

namespace SmoothLocal.Flow
open SmoothLocal.Geometry

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

theorem heightEnergy_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hzB : CoordinateBound z U 4 Z) :
    CoordinateBound (heightEnergy g z) U 3 (heightEnergyJetBound G Z) := by
  have hzi (i : Fin 2) := partial_contDiffOn hz hU i
  have hzBi (i : Fin 2) : CoordinateBound (coordPartial i z) U 3 Z := hzB.partial_bound i
  have hsquare (i : Fin 2) : CoordinateBound (fun p => (coordPartial i z p)^2) U 3 (8 * Z^2) := by
    convert CoordinateBound.mul_through_three (hzi i) (hzi i) hU hZ hZ (hzBi i) (hzBi i) using 1 <;>
      simp only [pow_two, mul_assoc]
  have hdiag0 := CoordinateBound.mul_through_three (hg.1 1 1) ((hzi 0).pow 2) hU hG
    (by positivity : 0 ≤ 8 * Z^2) (hgB 1 1) (hsquare 0)
  have hdiag1 := CoordinateBound.mul_through_three (hg.1 0 0) ((hzi 1).pow 2) hU hG
    (by positivity : 0 ≤ 8 * Z^2) (hgB 0 0) (hsquare 1)
  have hsum := CoordinateBound.add (hg.1 0 1) (hg.1 1 0) hU (hgB 0 1) (hgB 1 0)
  have hcross1 := CoordinateBound.mul_through_three ((hg.1 0 1).add (hg.1 1 0))
    (hzi 0) hU (by positivity : 0 ≤ G + G) hZ hsum (hzBi 0)
  have hcross := CoordinateBound.mul_through_three
    (((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)) (hzi 1) hU
    (by positivity : 0 ≤ 8 * (G + G) * Z) hZ hcross1 (hzBi 1)
  have hinner := CoordinateBound.add
    (((hg.1 1 1).mul ((hzi 0).pow 2)).sub ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1)))
    ((hg.1 0 0).mul ((hzi 1).pow 2)) hU
    (CoordinateBound.sub ((hg.1 1 1).mul ((hzi 0).pow 2))
      ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1)) hU hdiag0 hcross) hdiag1
  have hfull := CoordinateBound.sub (metricDet_contDiffOn hg)
    ((((hg.1 1 1).mul ((hzi 0).pow 2)).sub
      ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1))).add
        ((hg.1 0 0).mul ((hzi 1).pow 2))) hU (metricDet_coordinate_bound hg hU hG hgB) hinner
  have hc : 16 * G^2 + (8 * G * (8 * Z^2) + 8 * (8 * (G + G) * Z) * Z + 8 * G * (8 * Z^2)) =
      heightEnergyJetBound G Z := by dsimp [heightEnergyJetBound]; ring
  rw [hc] at hfull
  exact CoordinateBound.congr_on hU hfull (fun p hp => heightEnergy_polynomial z hg hp)

theorem darbouxG_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    CoordinateBound (darbouxG g z) U 3 (darbouxGJetBound G Z d c) := by
  have hH := hessianJetBound_nonneg hG hZ hd
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  have hh := covHessian_contDiffOn hg hU hz 1 1
  have hhB := covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet 1 1
  have hhsq : CoordinateBound (fun p => (covHessian g z p 1 1)^2) U 3
      (8 * (hessianJetBound G Z d)^2) := by
    convert CoordinateBound.mul_through_three hh hh hU hH hH hhB hhB using 1 <;>
      simp only [pow_two, mul_assoc]
  have hEB := heightEnergy_coordinate_bound hg hU hz hG hZ
    (fun i j => (hgB i j).mono (by norm_num) le_rfl) (hzB.mono (by norm_num) le_rfl)
  let N := heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hn : heightEnergyJetBound G Z ≤ N := by dsimp [N]; nlinarith [sq_nonneg (hessianJetBound G Z d)]
  have hb : 8 * (hessianJetBound G Z d)^2 ≤ N := by dsimp [N]; linarith
  have hden (p : Coord) (hp : p ∈ U) : c^2 ≤ |(covHessian g z p 1 1)^2| := by
    rw [abs_pow]
    exact pow_le_pow_left₀ hc.le (hyy p hp) 2
  intro ds hds p hp
  exact LowQuotient.quotient_bound_through_three (heightEnergy_contDiffOn hg hU hz)
    (hh.pow 2) hU hN (pow_pos hc 2) (hEB.mono le_rfl hn) (hhsq.mono le_rfl hb) hden ds hds hp

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

theorem height_jetEnergy_first_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hzB : CoordinateBound z U 4 Z) (i : Fin 2) :
    CoordinateBound (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p)) U 3
      (32 * G * Z) := by
  have hzS (j : Fin 2) := partial_contDiffOn hz hU j
  have hzD (j : Fin 2) : CoordinateBound (coordPartial j z) U 3 Z := hzB.partial_bound j
  have hdiag (a j : Fin 2) := CoordinateBound.const_mul
    ((hg.1 a a).mul (hzS j)) hU
    (CoordinateBound.mul_through_three (hg.1 a a) (hzS j) hU hG hZ (hgB a a) (hzD j)) (2 : ℝ)
  have hoff (j : Fin 2) := CoordinateBound.mul_through_three
    ((hg.1 0 1).add (hg.1 1 0)) (hzS j) hU (by positivity : 0 ≤ G + G) hZ
    (CoordinateBound.add (hg.1 0 1) (hg.1 1 0) hU (hgB 0 1) (hgB 1 0)) (hzD j)
  fin_cases i
  · have hb := CoordinateBound.sub (((hg.1 0 1).add (hg.1 1 0)).mul (hzS 1))
      (contDiffOn_const.mul ((hg.1 1 1).mul (hzS 0))) hU (hoff 1) (hdiag 1 0)
    have hc : 8 * (G + G) * Z + |(2 : ℝ)| * (8 * G * Z) = 32 * G * Z := by norm_num; ring
    rw [hc] at hb
    apply CoordinateBound.congr_on hU hb
    intro p hp
    change coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p) =
      (g p 0 1 + g p 1 0) * coordPartial 1 z p - 2 * (g p 1 1 * coordPartial 0 z p)
    rw [coordPartial_jetEnergy]
    norm_num
    ring
  · have hb := CoordinateBound.sub (((hg.1 0 1).add (hg.1 1 0)).mul (hzS 0))
      (contDiffOn_const.mul ((hg.1 0 0).mul (hzS 1))) hU (hoff 0) (hdiag 0 1)
    have hc : 8 * (G + G) * Z + |(2 : ℝ)| * (8 * G * Z) = 32 * G * Z := by norm_num; ring
    rw [hc] at hb
    apply CoordinateBound.congr_on hU hb
    intro p hp
    change coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p) =
      (g p 0 1 + g p 1 0) * coordPartial 0 z p - 2 * (g p 0 0 * coordPartial 1 z p)
    rw [coordPartial_jetEnergy]
    norm_num
    ring

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem height_christoffelAlongD_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) (i : Fin 2) :
    CoordinateBound (fun p => christoffelAlongD g p (hessianQuotient g z p) i) U 3
      (heightAlongDJetBound G Z d c) := by
  obtain ⟨hqs, hqb⟩ := hessianQuotient_bound_from_metric_height_jets hg hU hz hG hZ hd hc hgB hzB hdet hyy
  have hqN := heightQuotientJetBound_nonneg hG hZ hd hc
  have hΓN := christoffelJetBound_nonneg hG hd
  have hΓs (a b : Fin 2) := christoffel_contDiffOn hg hU i a b
  have hΓb (a b : Fin 2) := christoffel_coordinate_bound hg hU hG hd hgB hdet i a b
  have hqb' : CoordinateBound (hessianQuotient g z) U 3 (heightQuotientJetBound G Z d c) := hqb
  have hqΓ := CoordinateBound.mul_through_three hqs (hΓs 0 1) hU hqN hΓN hqb' (hΓb 0 1)
  have htwice := CoordinateBound.const_mul (hqs.mul (hΓs 0 1)) hU hqΓ (2 : ℝ)
  have hqsq : CoordinateBound (fun p => (hessianQuotient g z p)^2) U 3
      (8 * (heightQuotientJetBound G Z d c)^2) := by
    convert CoordinateBound.mul_through_three hqs hqs hU hqN hqN hqb' hqb' using 1 <;>
      simp only [pow_two, mul_assoc]
  have hthird := CoordinateBound.mul_through_three (hqs.pow 2) (hΓs 1 1) hU
    (by positivity : 0 ≤ 8 * (heightQuotientJetBound G Z d c)^2) hΓN hqsq (hΓb 1 1)
  have hb := CoordinateBound.add
    ((hΓs 0 0).sub (contDiffOn_const.mul (hqs.mul (hΓs 0 1))))
    ((hqs.pow 2).mul (hΓs 1 1)) hU
    (CoordinateBound.sub (hΓs 0 0) (contDiffOn_const.mul (hqs.mul (hΓs 0 1))) hU (hΓb 0 0) htwice) hthird
  have hconstant : christoffelJetBound G d + |(2 : ℝ)| *
      (8 * heightQuotientJetBound G Z d c * christoffelJetBound G d) +
      8 * (8 * (heightQuotientJetBound G Z d c)^2) * christoffelJetBound G d =
      heightAlongDJetBound G Z d c := by norm_num [heightAlongDJetBound]; ring
  rw [hconstant] at hb
  apply CoordinateBound.congr_on hU hb
  intro p hp
  change christoffelAlongD g p (hessianQuotient g z p) i =
    christoffel g i 0 0 p - 2 * (hessianQuotient g z p * christoffel g i 0 1 p) +
      (hessianQuotient g z p)^2 * christoffel g i 1 1 p
  rw [christoffelAlongD_eq hg hU hp]
  ring

theorem heightPFirst_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) (i : Fin 2) :
    CoordinateBound (heightPFirst g z i) U 1 (heightPFirstBound G Z d c) := by
  have hne := LowQuotient.denominator_ne_zero hc hyy
  have hH := hessianJetBound_nonneg hG hZ hd
  have hΓ := christoffelJetBound_nonneg hG hd
  have hD := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hJ := heightEnergyFirstQuotientBound_nonneg hG hZ hd hc
  have hK := curvatureFirstBound_nonneg hG hd
  have hsH := covHessian_contDiffOn hg hU hz 1 1
  have hsJ := height_jetEnergy_first_contDiffOn hg hU hz i
  have hsG := darbouxG_contDiffOn hg hU hz hne
  have hsΓ := christoffel_contDiffOn hg hU i 1 1
  have hJB := height_jetEnergy_first_coordinate_bound hg hU hz hG hZ
    (fun a b => (hgB a b).mono (by norm_num) le_rfl) (hzB.mono (by norm_num) le_rfl) i
  have hHB := covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet 1 1
  let N := 32 * G * Z + hessianJetBound G Z d
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hJN : 32 * G * Z ≤ N := by dsimp [N]; linarith
  have hHN : hessianJetBound G Z d ≤ N := by dsimp [N]; nlinarith [mul_nonneg hG hZ]
  have hdiv : CoordinateBound (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) /
      covHessian g z p 1 1) U 3 (heightEnergyFirstQuotientBound G Z d c) := by
    intro ds hds p hp
    exact LowQuotient.quotient_bound_through_three hsJ hsH hU hN hc
      (hJB.mono le_rfl hJN) (hHB.mono le_rfl hHN) hyy ds hds hp
  have hGΓ := CoordinateBound.mul_through_three hsG hsΓ hU hD hΓ
    (darbouxG_coordinate_bound hg hU hz hG hZ hd hc hgB hzB hdet hyy)
    (christoffel_coordinate_bound hg hU hG hd hgB hdet i 1 1)
  have hsdiv := hsJ.div hsH hne
  have hbracket := CoordinateBound.add hsdiv (hsG.mul hsΓ) hU hdiv hGΓ
  have hmul := CoordinateBound.mul_through_one (gaussianCurvature_contDiffOn hg hU)
    (hsdiv.add (hsG.mul hsΓ)) hU hK
    (by positivity : 0 ≤ heightEnergyFirstQuotientBound G Z d c + 8 * darbouxGJetBound G Z d c * christoffelJetBound G d)
    (gaussianCurvature_coordinate_bound_one hg hU hG hd hgB hdet)
    (hbracket.mono (by norm_num) le_rfl)
  have hbs := height_christoffelAlongD_contDiffOn hg hU hz hne i
  have hb := CoordinateBound.add hbs ((gaussianCurvature_contDiffOn hg hU).mul (hsdiv.add (hsG.mul hsΓ))) hU
    ((height_christoffelAlongD_coordinate_bound hg hU hz hG hZ hd hc hgB hzB hdet hyy i).mono
      (by norm_num) le_rfl) hmul
  apply CoordinateBound.congr_on hU hb
  intro p hp
  change heightPFirst g z i p = christoffelAlongD g p (hessianQuotient g z p) i +
    gaussianCurvature g p *
      (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
        darbouxG g z p * christoffel g i 1 1 p)
  rw [heightPFirst_eq hg hU hp (hne p hp) i]
  unfold darbouxG
  simp only [div_eq_mul_inv]
  ring

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
open SmoothLocal.Geometry

def stateBaseOrder : Fin 6 → ℕ := ![0, 0, 1, 1, 2, 2]

theorem stateBaseOrder_le_two (i : Fin 6) : stateBaseOrder i ≤ 2 := by
  fin_cases i <;> norm_num [stateBaseOrder]

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

def coordinateChainCoefficient (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)
    (fun i => Pi.single (r i) (1 : ℝ))

def coordinateChainFactor (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (i : Fin w.arity) (p : Coord) : ℝ :=
  verticalJet (solutionJet z) (w.order i) p (r i)

def chainFactorOrder (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) : ℕ :=
  w.order i + stateBaseOrder (r i)

theorem coordinateChainTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    (w : ChainWord) (p : Coord) :
    coordinateChainTerm g z w p =
      ∑ r : Fin w.arity → Fin 6,
        coordinateChainCoefficient g z w r p * ∏ i, coordinateChainFactor z w r i p :=
  multilinear_state_components _ _

theorem solutionJetCurve_iteratedDeriv_positive
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U)
    (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (solutionJetCurve z x) y =
      ![0, if n = 1 then 1 else 0,
        coordPartial 0 (verticalJet z n) ![x, y],
        coordPartial 1 (verticalJet z n) ![x, y],
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y],
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]] := by
  have hc := solutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · change iteratedDeriv n (fun _ : ℝ => x) y = 0
    simp [iteratedDeriv_const, Nat.ne_of_gt hn]
  · change iteratedDeriv n id y = if n = 1 then 1 else 0
    simp [iteratedDeriv_id, Nat.ne_of_gt hn]
  · change iteratedDeriv n (fun t => coordPartial 0 z ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn hz hU 0) x n y hp,
      verticalJet_coordPartial hU hz 0 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn hz hU 1) x n y hp,
      verticalJet_coordPartial hU hz 1 n ![x, y] hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 0 1]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 (coordPartial 1 z) ![x, t]) y = _
    rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1) x n y hp,
      verticalJet_two_coordPartials hU hz hp n 1 1]
    rfl

theorem coordinate_solutionJet_vertical_positive
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 0 < n) :
    verticalJet (solutionJet z) n p =
      ![0, if n = 1 then 1 else 0,
        coordPartial 0 (verticalJet z n) p,
        coordPartial 1 (verticalJet z n) p,
        coordPartial 0 (coordPartial 1 (verticalJet z n)) p,
        coordPartial 1 (coordPartial 1 (verticalJet z n)) p] := by
  have he : (![p 0, p 1] : Coord) = p := by
    ext i
    fin_cases i <;> rfl
  have h := solutionJetCurve_iteratedDeriv_positive hU hz
    (x := p 0) (y := p 1) (by simpa only [he] using hp) n hn
  have hv := verticalJet_slice hU (solutionJet_contDiffOn hU hz) (p 0) n (p 1)
    (by simpa only [he] using hp)
  change iteratedDeriv n (solutionJetCurve z (p 0)) (p 1) = _ at hv
  rw [hv] at h
  simpa only [he] using h

theorem ChainWord.arity_le_total {w : ChainWord} (hw : w.Positive) : w.arity ≤ w.total := by
  have hsum : ∑ _i : Fin w.arity, (1 : ℕ) ≤ ∑ i : Fin w.arity, w.order i :=
    Finset.sum_le_sum (fun index _ => hw index)
  simpa [ChainWord.total] using hsum

theorem residual_scalar_factor_orders {m : ℕ} {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    (∀ i, chainFactorOrder w r i ≤ m + 3) ∧ w.arity ≤ m + 3 := by
  obtain ⟨hp, ht, hb⟩ := topResidualWords_properties m w hw
  constructor
  · intro i
    have hi := hb i
    have hr := stateBaseOrder_le_two (r i)
    unfold chainFactorOrder
    omega
  · exact ht ▸ ChainWord.arity_le_total hp

theorem residual_scalar_high_unique {m : ℕ} (hm : 8 ≤ m + 3) {w : ChainWord}
    (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) {i j : Fin w.arity}
    (hi : m + 2 ≤ chainFactorOrder w r i) (hj : m + 2 ≤ chainFactorOrder w r j) : i = j :=
  topResidual_high_unique hm hw (fun k => stateBaseOrder (r k))
    (fun k => stateBaseOrder_le_two (r k)) hi hj

end SmoothLocal.HighEquation

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

theorem exists_open_low_height_coefficients
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      CoordinateBound (hessianQuotient g z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      CoordinateBound (heightEnergy g z) modelSquare 3 (heightEnergyJetBound G Z) ∧
      CoordinateBound (darbouxG g z) modelSquare 3 (darbouxGJetBound G Z d c) ∧
      (∀ i : Fin 2, CoordinateBound (heightPFirst g z i) modelSquare 1 (heightPFirstBound G Z d c)) ∧
      (∀ k i j : Fin 2, CoordinateBound (christoffel g k i j) modelSquare 3 (christoffelJetBound G d)) := by
  obtain ⟨V, hV, hSV, hVU, hVne, _, hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG hZ hd hc hgB hzB hdet hyy
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun i j => (hg.1 i j).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  have hgBI (i j : Fin 2) := (hgB i j).restrict_domain interior_subset
  have hzBI := hzB.restrict_domain interior_subset
  have hdI (p : Coord) (hp : p ∈ interior modelSquare) := hdet p (interior_subset hp)
  have hyyI (p : Coord) (hp : p ∈ interior modelSquare) := hyy p (interior_subset hp)
  refine ⟨V, hV, hSV, hVU, hVne, hqB, ?_, ?_, ?_, ?_⟩
  · apply CoordinateBound.of_modelSquare_interior (heightEnergy_contDiffOn hg hU hz) hU hSU
    exact heightEnergy_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ
      (fun i j => (hgBI i j).mono (by norm_num) le_rfl) (hzBI.mono (by norm_num) le_rfl)
  · apply CoordinateBound.of_modelSquare_interior
      (darbouxG_contDiffOn hgV hV (hz.mono hVU) hVne) hV hSV
    exact darbouxG_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ hd hc hgBI hzBI hdI hyyI
  · intro i
    apply CoordinateBound.of_modelSquare_interior
      (heightPFirst_contDiffOn hgV hV (hz.mono hVU) hVne i) hV hSV
    exact heightPFirst_coordinate_bound_one hgI isOpen_interior (hz.mono hIU) hG hZ hd hc hgBI hzBI hdI hyyI i
  · intro k i j
    apply CoordinateBound.of_modelSquare_interior (christoffel_contDiffOn hg hU k i j) hU hSU
    exact christoffel_coordinate_bound hgI isOpen_interior hG hd hgBI hdI k i j

end SmoothLocal.Geometry

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

def heightComponentIndex : Fin 4 → Fin 6 := ![2, 3, 4, 5]

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem heightStateFactor_contDiffOn (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (n : ℕ) (j : Fin 4) : ContDiffOn ℝ ∞ (heightStateFactor z n j) U := by
  have hv := verticalJet_contDiffOn hU hz n
  fin_cases j
  · exact partial_contDiffOn hv hU 0
  · exact partial_contDiffOn hv hU 1
  · exact partial_contDiffOn (partial_contDiffOn hv hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hv hU 1) hU 1

theorem coordinateChainFactor_continuousOn (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (w : ChainWord) (r : Fin w.arity → Fin 6) (i : Fin w.arity) :
    ContinuousOn (coordinateChainFactor z w r i) U := by
  exact ((ContinuousLinearMap.proj (r i) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (verticalJet_contDiffOn hU (solutionJet_contDiffOn hU hz) (w.order i)).continuousOn)

theorem coordinateChainCoefficient_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (coordinateChainCoefficient g z w r) U := by
  intro p hp
  have hP := sixVariableP_contDiffAt_solutionJet hg hU hp (hyy p hp)
  have houter := (hP.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).continuousAt
  have hjet := ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).continuousAt
  have heval := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.arity => DarbouxState) ℝ
    (fun i => Pi.single (r i) (1 : ℝ))).continuous.continuousAt
      (x := iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p))
  exact ((heval.comp houter).comp hjet).continuousWithinAt

theorem coordinateScalarTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (fun p => coordinateChainCoefficient g z w r p *
      ∏ i, coordinateChainFactor z w r i p) U := by
  exact (coordinateChainCoefficient_continuousOn hg hU hz hyy w r).mul
    (continuousOn_finsetProd Finset.univ
      (fun index _ => coordinateChainFactor_continuousOn hU hz w r index))

theorem coordinateChainTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (w : ChainWord) :
    ContinuousOn (coordinateChainTerm g z w) U := by
  have h := continuousOn_finsetSum Finset.univ
    (fun indices _ => coordinateScalarTerm_continuousOn hg hU hz hyy w indices)
  exact h.congr (fun point _ => coordinateChainTerm_scalar_expansion g z w point)

theorem coordinateChainSum_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ws : List ChainWord) :
    ContinuousOn (coordinateChainSum g z ws) U :=
  continuousOn_list_sum ws (fun word _ => coordinateChainTerm_continuousOn hg hU hz hyy word)

theorem vertical_state_height_ae (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (n : ℕ) (hn : 0 < n) (j : Fin 4) :
    (fun p => verticalJet (solutionJet z) n p (heightComponentIndex j)) =ᵐ[volume.restrict V]
      heightStateFactor z n j := by
  filter_upwards [ae_restrict_mem hV] with p hp
  rw [coordinate_solutionJet_vertical_positive hU hz (hVU hp) n hn]
  fin_cases j <;> rfl

theorem vertical_state_component_low_bound
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hVU : V ⊆ U)
    {m : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (n : ℕ) (hn : 0 < n) (k : Fin 6) (hk : n + stateBaseOrder k ≤ m + 1)
    {p : Coord} (hp : p ∈ V) :
    ‖verticalJet (solutionJet z) n p k‖ ≤ B := by
  rw [coordinate_solutionJet_vertical_positive hU hz (hVU hp) n hn]
  fin_cases k
  · simpa using le_trans (by norm_num : (0 : ℝ) ≤ 1) hB
  · by_cases he : n = 1
    · simpa [he] using hB
    · simpa [he] using le_trans (by norm_num : (0 : ℝ) ≤ 1) hB
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 0 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 1 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 2 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp
  · simpa [heightStateFactor, Real.norm_eq_abs] using
      hlow n 3 (by simpa [heightStateBaseOrder, stateBaseOrder] using hk) p hp

theorem vertical_state_component_high_eLpNorm
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} {H : ℝ≥0}
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (n : ℕ) (hn : 0 < n) (hnlow : n ≤ m + 1) (k : Fin 6)
    (hhigh : m + 2 ≤ n + stateBaseOrder k) (htop : n + stateBaseOrder k ≤ m + 3) :
    eLpNorm (fun p => verticalJet (solutionJet z) n p k) 2 (volume.restrict V) ≤
      (H : ℝ≥0∞) := by
  fin_cases k
  · norm_num [stateBaseOrder] at hhigh
    omega
  · norm_num [stateBaseOrder] at hhigh
    omega
  · calc
      _ = eLpNorm (heightStateFactor z n 0) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 0)
      _ ≤ _ := hheight n 0 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 1) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 1)
      _ ≤ _ := hheight n 1 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 2) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 2)
      _ ≤ _ := hheight n 2 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)
  · calc
      _ = eLpNorm (heightStateFactor z n 3) 2 (volume.restrict V) := by
        simpa [heightComponentIndex] using eLpNorm_congr_ae
          (vertical_state_height_ae hU hz hV hVU n hn 3)
      _ ≤ _ := hheight n 3 (by simpa [heightStateBaseOrder, stateBaseOrder] using htop)

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
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem enorm_pow_mono_of_one_le {B : ℝ} (hB : 1 ≤ B) {a b : ℕ} (hab : a ≤ b) :
    ‖B ^ a‖ₑ ≤ ‖B ^ b‖ₑ := by
  rw [enorm_le_iff_norm_le, Real.norm_of_nonneg (pow_nonneg (by linarith) _),
    Real.norm_of_nonneg (pow_nonneg (by linarith) _)]
  exact pow_le_pow_right₀ hB hab

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

theorem scalar_coefficient_eLpNorm_two {V : Set Coord} (hV : MeasurableSet V)
    {a f : Coord → ℝ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p ∈ V, |a p| ≤ C) :
    eLpNorm' (fun p => a p * f p) (2 : ℝ) (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict V) := by
  have hdom : ∀ᵐ p ∂(volume.restrict V), ‖a p * f p‖ ≤ ‖C * f p‖ := by
    filter_upwards [ae_restrict_mem hV] with p hp
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (ha p hp) (abs_nonneg _)
  calc
    _ ≤ eLpNorm' (fun p => C * f p) (2 : ℝ) (volume.restrict V) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f) C (by norm_num)

theorem scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    {V : Set Coord} (hV : MeasurableSet V)
    {a f : Coord → ℝ} {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p ∈ V, |a p| ≤ C)
    (hmeas : AEStronglyMeasurable (fun p => a p * f p) (volume.restrict V)) :
    eLpNorm (fun p => a p * f p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm f 2 (volume.restrict V) := by
  have hraw : eLpNorm' f (2 : ℝ) (volume.restrict V) ≤
      eLpNorm f 2 (volume.restrict V) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  calc
    _ = eLpNorm' (fun p => a p * f p) (2 : ℝ) (volume.restrict V) := by
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
    _ ≤ ‖C‖ₑ * eLpNorm' f (2 : ℝ) (volume.restrict V) :=
      scalar_coefficient_eLpNorm_two hV hC ha
    _ ≤ _ := mul_le_mul' le_rfl hraw

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem residual_product_eLpNorm_two
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {B : ℝ} (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    {w : ChainWord} (hw : w ∈ topResidualWords m) (r : Fin w.arity → Fin 6) :
    eLpNorm (fun p => ∏ i, coordinateChainFactor z w r i p) 2 (volume.restrict V) ≤
      chainProductL2Budget B H V (m + 3) := by
  classical
  obtain ⟨hpos, -, horders⟩ := topResidualWords_properties m w hw
  obtain ⟨hfactorOrders, harity⟩ := residual_scalar_factor_orders hw r
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hmeas : AEStronglyMeasurable (fun p => ∏ i, coordinateChainFactor z w r i p)
      (volume.restrict V) :=
    Finset.univ.aestronglyMeasurable_fun_prod (fun index _ =>
      ((coordinateChainFactor_continuousOn hU hz w r index).mono hVU).aestronglyMeasurable
        (μ := volume) hV)
  by_cases hhigh : ∃ j, m + 2 ≤ chainFactorOrder w r j
  · obtain ⟨j, hj⟩ := hhigh
    have hlowOther : ∀ i ∈ (Finset.univ : Finset (Fin w.arity)).erase j,
        ∀ p ∈ V, ‖coordinateChainFactor z w r i p‖ ≤ B := by
      intro i hi p hp
      have hiorder : chainFactorOrder w r i ≤ m + 1 := by
        by_contra hiorder
        have hieq := residual_scalar_high_unique (i := i) (j := j) hm hw r (by omega) hj
        exact (Finset.mem_erase.mp hi).1 hieq
      exact vertical_state_component_low_bound hU hz hVU hB hlow
        (w.order i) (hpos i) (r i) hiorder hp
    have hjL2 : eLpNorm (coordinateChainFactor z w r j) 2 (volume.restrict V) ≤
        (H : ℝ≥0∞) :=
      vertical_state_component_high_eLpNorm hU hz hV hVU hheight
        (w.order j) (hpos j) (horders j) (r j) hj (hfactorOrders j)
    have hcard : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ m + 3 := by
      have he := Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin w.arity)))
      have he' : ((Finset.univ : Finset (Fin w.arity)).erase j).card ≤ w.arity := by
        simpa only [Finset.card_univ, Fintype.card_fin] using he
      exact he'.trans harity
    have hp := finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (coordinateChainFactor z w r) (Finset.mem_univ j) hB0 hV hlowOther hmeas
    calc
      _ ≤ ‖B ^ ((Finset.univ : Finset (Fin w.arity)).erase j).card‖ₑ *
          eLpNorm (coordinateChainFactor z w r j) 2 (volume.restrict V) := hp
      _ ≤ ‖B ^ (m + 3)‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ))) :=
        mul_le_mul' (enorm_pow_mono_of_one_le hB hcard)
          (hjL2.trans (le_add_of_nonneg_right (by positivity)))
      _ = _ := rfl
  · have hlowAll : ∀ i ∈ (Finset.univ : Finset (Fin w.arity)),
        ∀ p ∈ V, ‖coordinateChainFactor z w r i p‖ ≤ B := by
      intro i _ p hp
      have hiorder : chainFactorOrder w r i ≤ m + 1 := by
        have hni : ¬ m + 2 ≤ chainFactorOrder w r i := fun hi => hhigh ⟨i, hi⟩
        omega
      exact vertical_state_component_low_bound hU hz hVU hB hlow
        (w.order i) (hpos i) (r i) hiorder hp
    have hp := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable
      (μ := volume) Finset.univ (coordinateChainFactor z w r) hB0 hV hlowAll hmeas
    calc
      _ ≤ ‖B ^ w.arity‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hp
      _ ≤ ‖B ^ (m + 3)‖ₑ * ((H : ℝ≥0∞) + (volume V) ^ (1 / (2 : ℝ))) :=
        mul_le_mul' (enorm_pow_mono_of_one_le hB harity)
          (le_add_of_nonneg_left (by positivity))
      _ = _ := rfl

theorem coordinateChainTerm_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    {w : ChainWord} (hw : w ∈ topResidualWords m)
    (hcoeff : ∀ r, ∀ p ∈ V, |coordinateChainCoefficient g z w r p| ≤ C) :
    eLpNorm (coordinateChainTerm g z w) 2 (volume.restrict V) ≤
      chainWordL2Budget C B H V (m + 3) w := by
  classical
  have hmeas (r : Fin w.arity → Fin 6) :
      AEStronglyMeasurable (fun p => coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p) (volume.restrict V) :=
    ((coordinateScalarTerm_continuousOn hg hU hz hyy w r).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hterm (r : Fin w.arity → Fin 6) :
      eLpNorm (fun p => coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p) 2 (volume.restrict V) ≤
        ‖C‖ₑ * chainProductL2Budget B H V (m + 3) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (hcoeff r) (hmeas r)).trans
      (mul_le_mul' le_rfl (residual_product_eLpNorm_two hU hz hV hVU hm hB hlow hheight hw r))
  have he : coordinateChainTerm g z w = fun p =>
      ∑ r : Fin w.arity → Fin 6, coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p :=
    funext (coordinateChainTerm_scalar_expansion g z w)
  rw [he]
  exact finite_sum_eLpNorm_two Finset.univ _
    (fun _ => ‖C‖ₑ * chainProductL2Budget B H V (m + 3))
    (fun indices _ => hmeas indices) (fun indices _ => hterm indices)

theorem coordinateChainSum_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (ws : List ChainWord) (hws : ∀ w ∈ ws, w ∈ topResidualWords m) :
    eLpNorm (coordinateChainSum g z ws) 2 (volume.restrict V) ≤
      chainSumL2Budget C B H V (m + 3) ws := by
  induction ws with
  | nil =>
      change eLpNorm (0 : Coord → ℝ) 2 (volume.restrict V) ≤ 0
      simp
  | cons w ws ih =>
      have hw := hws w List.mem_cons_self
      have ht := coordinateChainTerm_eLpNorm_two hg hU hz hyy hV hVU hm hC hB
        hlow hheight hw (hcoeff w hw)
      have hs := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
      change eLpNorm (fun p => coordinateChainTerm g z w p + coordinateChainSum g z ws p)
        2 (volume.restrict V) ≤
          chainWordL2Budget C B H V (m + 3) w + chainSumL2Budget C B H V (m + 3) ws
      exact (eLpNorm_add_le
        (((coordinateChainTerm_continuousOn hg hU hz hyy w).mono hVU).aestronglyMeasurable (μ := volume) hV)
        (((coordinateChainSum_continuousOn hg hU hz hyy ws).mono hVU).aestronglyMeasurable (μ := volume) hV)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
        (add_le_add ht hs)

theorem firstJetPairRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (n : ℕ) :
    ContinuousOn (firstJetPairRemainder g z n) U := by
  have h0 := (partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy 0) hU 1).continuousOn
  have h1 := (partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy 1) hU 1).continuousOn
  exact (h0.mul (heightStateFactor_contDiffOn hU hz n 0).continuousOn).add
    (h1.mul (heightStateFactor_contDiffOn hU hz n 1).continuousOn)

theorem firstJetPairRemainder_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} {Cfirst : ℝ} (hCfirst : 0 ≤ Cfirst) {H : ℝ≥0}
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    eLpNorm (firstJetPairRemainder g z (m + 2)) 2 (volume.restrict V) ≤
      firstJetPairL2Budget Cfirst H := by
  have h0 : eLpNorm (heightStateFactor z (m + 2) 0) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
    hheight (m + 2) 0 (by norm_num [heightStateBaseOrder])
  have h1 : eLpNorm (heightStateFactor z (m + 2) 1) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
    hheight (m + 2) 1 (by norm_num [heightStateBaseOrder])
  have hm (i : Fin 2) : AEStronglyMeasurable
      (fun p => coordPartial 1 (heightPFirst g z i) p * coordPartial i (verticalJet z (m + 2)) p)
      (volume.restrict V) :=
    (((partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy i) hU 1).continuousOn.mul
      (partial_contDiffOn (verticalJet_contDiffOn hU hz (m + 2)) hU i).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hb0 := (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    (f := heightStateFactor z (m + 2) 0) hV hCfirst (hfirst 0) (hm 0)).trans
    (mul_le_mul' le_rfl h0)
  have hb1 := (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
    (f := heightStateFactor z (m + 2) 1) hV hCfirst (hfirst 1) (hm 1)).trans
    (mul_le_mul' le_rfl h1)
  exact (eLpNorm_add_le (hm 0) (hm 1) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add hb0 hb1)

theorem actualHighRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) :
    ContinuousOn (actualHighRemainder g z m) U :=
  (coordinateChainSum_continuousOn hg hU hz hyy (topResidualWords m)).add
    (continuousOn_const.mul (firstJetPairRemainder_continuousOn hg hU hz hyy (m + 2)))

theorem actualHighRemainder_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C Cfirst B : ℝ}
    (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
      actualHighRemainderL2Budget C Cfirst B H V m := by
  have hs := coordinateChainSum_eLpNorm_two hg hU hz hyy hV hVU hm hC hB
    hlow hheight hcoeff (topResidualWords m) (fun _ hw => hw)
  have hp := firstJetPairRemainder_eLpNorm_two hg hU hz hyy hV hVU hCfirst hheight hfirst
  have hscaled : eLpNorm (fun p => (m + 3 : ℝ) * firstJetPairRemainder g z (m + 2) p)
      2 (volume.restrict V) ≤ ‖(m + 3 : ℝ)‖ₑ * firstJetPairL2Budget Cfirst H := by
    change eLpNorm ((m + 3 : ℝ) • firstJetPairRemainder g z (m + 2))
      2 (volume.restrict V) ≤ _
    rw [eLpNorm_const_smul (𝕜 := ℝ) (F := ℝ)]
    exact mul_le_mul' le_rfl hp
  exact (eLpNorm_add_le
    (((coordinateChainSum_continuousOn hg hU hz hyy (topResidualWords m)).mono hVU).aestronglyMeasurable (μ := volume) hV)
    (((continuousOn_const.mul (firstJetPairRemainder_continuousOn hg hU hz hyy (m + 2))).mono hVU).aestronglyMeasurable (μ := volume) hV)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hs hscaled)

theorem actualHighRemainder_memLp_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVfinite : volume V < (⊤ : ℝ≥0∞))
    {m : ℕ} (hm : 8 ≤ m + 3) {C Cfirst B : ℝ}
    (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  exact ⟨((actualHighRemainder_continuousOn hg hU hz hyy m).mono hVU).aestronglyMeasurable (μ := volume) hV,
    (actualHighRemainder_eLpNorm_two hg hU hz hyy hV hVU hm hC hCfirst hB
    hlow hheight hcoeff hfirst).trans_lt
      (actualHighRemainderL2Budget_lt_top C Cfirst B H hVfinite m)⟩

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
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem coordinateChainCoefficient_abs_le_full_derivative
    (g : MetricField) (z : Coord → ℝ) (w : ChainWord)
    (r : Fin w.arity → Fin 6) (p : Coord) :
    |coordinateChainCoefficient g z w r p| ≤
      ‖iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)‖ := by
  have h := (iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)).le_opNorm
    (fun i => Pi.single (r i) (1 : ℝ))
  simpa only [coordinateChainCoefficient, Pi.norm_single, norm_one,
    Finset.prod_const_one, mul_one, Real.norm_eq_abs] using h

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

theorem exists_same_region_remainder_outer_bound (G Z : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → S ⊆ U → S ⊆ modelSquare →
      (∀ i j k, k ≤ m + 5 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 2 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 1 1|) →
      ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ S,
        |coordinateChainCoefficient g z w r p| ≤ C := by
  obtain ⟨C, hC, hP⟩ := exists_same_region_solution_P_jet_bound G Z hG hd hc (m + 3)
  refine ⟨C, hC, ?_⟩
  intro g z U S hg hU hSU hSS hgB hzB hdet hden w hw r p hp
  exact (coordinateChainCoefficient_abs_le_full_derivative g z w r p).trans
    (hP g z U S hg hU hSU hSS (fun i j k hk => hgB i j k (by omega)) hzB hdet hden
      w.arity (residual_scalar_factor_orders hw r).2 p hp)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem exists_localized_actualHighRemainder_bound
    (G Z M : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hM : 0 ≤ M)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U V : Set Coord),
      SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
      ContDiffOn ℝ ∞ z U →
      (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      MeasurableSet V → V ⊆ modelSquare → volume V < (⊤ : ℝ≥0∞) →
      (∀ i j k, k ≤ m + 5 → ∀ p ∈ V,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ M) →
      ∀ B : ℝ, 1 ≤ B → ∀ H : ℝ≥0,
      (∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
        ∀ p ∈ V, |heightStateFactor z n j p| ≤ B) →
      (∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) →
      eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
        actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m ∧
      actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m < (⊤ : ℝ≥0∞) ∧
      MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  obtain ⟨C, hC, houter⟩ := exists_same_region_remainder_outer_bound M Z hM hd hc m
  refine ⟨C, hC, ?_⟩
  intro g z U V hg hU hSU hgB hdet hz hzB hyy hV hVS hVfinite hgHigh B hB H hlow hheight
  have hgCoord (i j : Fin 2) : CoordinateBound (fun p => g p i j) modelSquare 4 G :=
    coordinateBound_of_frechet_bounds (hg.1 i j) hU hSU (hgB i j)
  have hzCoord : CoordinateBound z modelSquare 5 Z :=
    coordinateBound_five_of_frechet_eight hz hU hSU hzB
  obtain ⟨W, hW, hSW, hWU, hne, _, _, _, hfirst, _⟩ :=
    exists_open_low_height_coefficients hg hU hSU hz hG hZ hd hc hgCoord hzCoord hdet hyy
  have hgW : SmoothPositiveOn g W :=
    ⟨fun i j => (hg.1 i j).mono hWU, fun p hp => hg.2 p (hWU hp)⟩
  have hVW : V ⊆ W := hVS.trans hSW
  have hCfirst := heightPFirstBound_nonneg hG hZ hd hc
  have ho : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C :=
    houter g z U V hg hU (hVS.trans hSU) hVS hgHigh
      ((hzCoord.mono (by norm_num) le_rfl).restrict_domain hVS)
      (fun p hp => hdet p (hVS hp)) (fun p hp => hyy p (hVS hp))
  have hf : ∀ i : Fin 2, ∀ p ∈ V,
      |coordPartial 1 (heightPFirst g z i) p| ≤ heightPFirstBound G Z d c :=
    fun i p hp => hfirst i [1] (by norm_num) p (hVS hp)
  exact ⟨actualHighRemainder_eLpNorm_two hgW hW (hz.mono hWU) hne hV hVW hm hC hCfirst hB
      hlow hheight ho hf,
    actualHighRemainderL2Budget_lt_top C (heightPFirstBound G Z d c) B H hVfinite m,
    actualHighRemainder_memLp_two hgW hW (hz.mono hWU) hne hV hVW hVfinite hm hC hCfirst hB
      hlow hheight ho hf⟩

end SmoothLocal.HighEquation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.HighEquation.exists_localized_actualHighRemainder_bound := @OAI.SmoothLocal.HighEquation.exists_localized_actualHighRemainder_bound
