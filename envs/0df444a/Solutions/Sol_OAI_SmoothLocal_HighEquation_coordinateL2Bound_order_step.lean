-- Prove2me | solution 1 for OAI.SmoothLocal.HighEquation.coordinateL2Bound_order_step
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:42:28.856105+00:00
-- url     : https://prove2.me/submissions/65701f3e-1435-49c1-93c9-2cc09e0f4c12

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
open scoped BigOperators

namespace SmoothLocal.HighEquation

theorem ordered_partSize_sum {ell : ℕ} (c : OrderedFinpartition ell) :
    ∑ j, c.partSize j = ell := by
  have hh := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hh

theorem ordered_two_partSizes_le {ell : ℕ} (c : OrderedFinpartition ell)
    {i j : Fin c.length} (hij : i ≠ j) :
    c.partSize i + c.partSize j ≤ ell := by
  have hh : ∑ k ∈ ({i, j} : Finset (Fin c.length)), c.partSize k ≤
      ∑ k, c.partSize k :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simpa only [Finset.sum_pair hij, ordered_partSize_sum] using hh

end SmoothLocal.HighEquation

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

theorem covHessian_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j : Fin 2) :
    covHessian g z p i j = covHessian g z p j i := by
  unfold covHessian
  rw [coordPartial_comm hz hU hp i j]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [christoffel_lower_symm hg hU hp a i j]

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

theorem normed_second_coordPartial_eq_fderiv
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p =
      fderiv ℝ (fderiv ℝ F) p (Pi.single i 1) (Pi.single j 1) := by
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hs.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const (c := Pi.single j (1 : ℝ)))]
  simp

theorem normed_coordPartial_comm (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p = coordPartial j (coordPartial i F) p := by
  rw [normed_second_coordPartial_eq_fderiv hF hU hp, normed_second_coordPartial_eq_fderiv hF hU hp]
  exact ((hF.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt
    (by
      simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
      exact WithTop.coe_le_coe.mpr le_top)) _ _

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

theorem solvedDarboux_deriv_b (g : MetricField) (p u : Coord) (b c : ℝ)
    (_hne : jetYY g p c u ≠ 0) :
    deriv (fun t => solvedDarboux g p t c u) b =
      2 * (jetMixed g p b u / jetYY g p c u) := by
  have hd := (((((hasDerivAt_id b).sub_const (jetConnection g p 0 1 u)).pow 2).add_const
    (gaussianCurvature g p * jetEnergy g p u)).div_const (jetYY g p c u)).const_add
      (jetConnection g p 0 0 u)
  simp only [Pi.pow_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 0 0 u +
    ((t - jetConnection g p 0 1 u) ^ 2 + gaussianCurvature g p * jetEnergy g p u) /
      jetYY g p c u) b = _
  rw [hd.deriv]
  simp only [jetMixed, mul_one]
  ring

theorem solvedDarboux_deriv_c (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetYY g p c u ≠ 0) :
    deriv (fun t => solvedDarboux g p b t u) c =
      -((jetMixed g p b u / jetYY g p c u) ^ 2 +
        gaussianCurvature g p * jetEnergy g p u / (jetYY g p c u) ^ 2) := by
  have hdH := (hasDerivAt_id c).sub_const (jetConnection g p 1 1 u)
  have hd := ((hasDerivAt_const c (jetNumerator g p b u)).div hdH hne).const_add
    (jetConnection g p 0 0 u)
  simp only [Pi.div_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 0 0 u +
    jetNumerator g p b u / (t - jetConnection g p 1 1 u)) c = _
  rw [hd.deriv]
  change (0 * jetYY g p c u - jetNumerator g p b u * 1) / (jetYY g p c u) ^ 2 = _
  simp only [jetNumerator]
  field_simp [hne]
  ring

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
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem solvedDarboux_at_height
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    coordPartial 0 (coordPartial 0 z) p =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  have hsolve : covHessian g z p 0 0 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 1 1 := by
    apply (eq_div_iff hyy).2
    linarith [hdet]
  change coordPartial 0 (coordPartial 0 z) p -
    jetConnection g p 0 0 (fun i => coordPartial i z p) = _ at hsolve
  rw [solvedDarboux, jetNumerator, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z]
  linarith [hsolve]

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

theorem sixVariableP_solutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    sixVariableP g (solutionJet z p) =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) := by
  unfold sixVariableP
  rw [statePoint_solutionJet, stateGradient_solutionJet]
  rfl

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
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def coordinateDirections : (ds : List (Fin 2)) → Fin ds.length → Coord
  | [] => fun _ => 0
  | i :: ds => Fin.cons (Pi.single i 1) (coordinateDirections ds)

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
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

variable {q : Coord → ℝ} {U : Set Coord}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem fderiv_axis_eq_deriv_update {n : ℕ} {f : (Fin n → ℝ) → ℝ} {w : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f w) (i : Fin n) :
    fderiv ℝ f w (Pi.single i 1) = deriv (fun t => f (Function.update w i t)) (w i) := by
  have hd : HasFDerivAt f (fderiv ℝ f w) (Function.update w i (w i)) := by
    simpa using hf.hasFDerivAt
  exact (hd.comp_hasDerivAt (w i) (hasDerivAt_update w i (w i))).deriv.symm

def gradientStateIndex (i : Fin 2) : Fin 6 := if i = 0 then 2 else 3

theorem sixVariableP_update_gradient (g : MetricField) (w : DarbouxState) (i : Fin 2) (t : ℝ) :
    sixVariableP g (Function.update w (gradientStateIndex i) t) =
      solvedDarboux g (statePoint w) (w 4) (w 5) (Function.update (stateGradient w) i t) := by
  have hp : statePoint (Function.update w (gradientStateIndex i) t) = statePoint w := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, statePoint]
  have hv : stateGradient (Function.update w (gradientStateIndex i) t) =
      Function.update (stateGradient w) i t := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  fin_cases i <;> simp [gradientStateIndex]

theorem sixVariableP_update_mixed (g : MetricField) (w : DarbouxState) (t : ℝ) :
    sixVariableP g (Function.update w 4 t) =
      solvedDarboux g (statePoint w) t (w 5) (stateGradient w) := by
  have hp : statePoint (Function.update w 4 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 4 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  simp

theorem sixVariableP_update_yy (g : MetricField) (w : DarbouxState) (t : ℝ) :
    sixVariableP g (Function.update w 5 t) =
      solvedDarboux g (statePoint w) (w 4) t (stateGradient w) := by
  have hp : statePoint (Function.update w 5 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 5 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  simp

theorem solvedDarboux_first_variables_differentiableAt (g : MetricField) (p u : Coord) (b c : ℝ)
    (hyy : jetYY g p c u ≠ 0) : DifferentiableAt ℝ (solvedDarboux g p b c) u := by
  have hd := (jetConnection_differentiableAt g p u 0 0).add
    ((jetNumerator_differentiableAt g p u b).mul ((jetYY_differentiableAt g p u c).inv hyy))
  exact hd

theorem sixVariableP_gradient_axis
    {g : MetricField} {U : Set Coord} {w : DarbouxState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hw : w ∈ darbouxStateDomain g U) (i : Fin 2) :
    fderiv ℝ (sixVariableP g) w (Pi.single (gradientStateIndex i) 1) =
      coordPartial i (solvedDarboux g (statePoint w) (w 4) (w 5)) (stateGradient w) := by
  have hP : DifferentiableAt ℝ (sixVariableP g) w :=
    ((sixVariableP_contDiffOn hg hU).contDiffAt
      ((darbouxStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update w (gradientStateIndex i) t)) =
      (fun t => solvedDarboux g (statePoint w) (w 4) (w 5) (Function.update (stateGradient w) i t)) :=
    funext (sixVariableP_update_gradient g w i)
  rw [heq]
  have hi : w (gradientStateIndex i) = stateGradient w i := by
    fin_cases i <;> simp [gradientStateIndex, stateGradient]
  rw [hi]
  exact (fderiv_axis_eq_deriv_update
    (solvedDarboux_first_variables_differentiableAt g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2) i).symm

theorem sixVariableP_gradient_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single (gradientStateIndex i) 1) =
      heightPFirst g z i p := by
  rw [sixVariableP_gradient_axis hg hU (solutionJet_mem_domain g z hp hyy) i,
    statePoint_solutionJet, stateGradient_solutionJet]
  rfl

theorem sixVariableP_mixed_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 4 1) = 2 * hessianQuotient g z p := by
  have hP := (sixVariableP_contDiffAt_solutionJet hg hU hp hyy).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update (solutionJet z p) 4 t)) =
      (fun t => solvedDarboux g p t (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p)) := by
    funext t
    rw [sixVariableP_update_mixed, statePoint_solutionJet, stateGradient_solutionJet]
    rfl
  rw [heq]
  change deriv (fun t => solvedDarboux g p t (coordPartial 1 (coordPartial 1 z) p)
    (fun i => coordPartial i z p)) (coordPartial 0 (coordPartial 1 z) p) = _
  rw [solvedDarboux_deriv_b g p _ _ _ hyy, jetMixed_at_height, jetYY_at_height]
  rfl

theorem sixVariableP_yy_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 5 1) =
      -((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) := by
  have hP := (sixVariableP_contDiffAt_solutionJet hg hU hp hyy).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update (solutionJet z p) 5 t)) =
      (fun t => solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p) t (fun i => coordPartial i z p)) := by
    funext t
    rw [sixVariableP_update_yy, statePoint_solutionJet, stateGradient_solutionJet]
    rfl
  rw [heq]
  change deriv (fun t => solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p) t
    (fun i => coordPartial i z p)) (coordPartial 1 (coordPartial 1 z) p) = _
  rw [solvedDarboux_deriv_c g p _ _ _ hyy, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z]
  unfold hessianQuotient darbouxG
  ring

theorem sixVariableP_vertical_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) v =
      heightPFirst g z 0 p * v 2 + heightPFirst g z 1 p * v 3 +
        2 * hessianQuotient g z p * v 4 -
        ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) * v 5 := by
  have he : v = v 2 • (Pi.single 2 (1 : ℝ) : DarbouxState) +
      v 3 • Pi.single 3 1 + v 4 • Pi.single 4 1 + v 5 • Pi.single 5 1 := by
    ext i
    fin_cases i <;> simp [hv0, hv1]
  have h0 : fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 2 1) = heightPFirst g z 0 p := by
    simpa only [gradientStateIndex, ↓reduceIte] using sixVariableP_gradient_axis_at_height hg hU hp hyy 0
  have h1 : fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 3 1) = heightPFirst g z 1 p := by
    simpa only [gradientStateIndex, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
      sixVariableP_gradient_axis_at_height hg hU hp hyy 1
  have hl := congrArg (fderiv ℝ (sixVariableP g) (solutionJet z p)) he
  simp only [map_add, map_smul, h0, h1, sixVariableP_mixed_axis_at_height hg hU hp hyy,
    sixVariableP_yy_axis_at_height hg hU hp hyy, smul_eq_mul] at hl
  rw [hl]
  ring

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Function
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def fullBlockPartition (ell : ℕ) (hell : 0 < ell) : OrderedFinpartition ell where
  length := 1
  partSize _ := ell
  partSize_pos _ := hell
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro firstBlock _ secondBlock _ hne
    exact (hne (Subsingleton.elim firstBlock secondBlock)).elim
  cover i := ⟨0, i, rfl⟩

theorem ordered_full_size_length_one {ell : ℕ} (c : OrderedFinpartition ell)
    {i : Fin c.length} (hi : c.partSize i = ell) : c.length = 1 := by
  have hunique : ∀ j : Fin c.length, j = i := by
    intro j
    by_contra hji
    have hb := ordered_two_partSizes_le c hji
    have hj := c.partSize_pos j
    rw [hi] at hb
    omega
  have hsub : Subsingleton (Fin c.length) :=
    ⟨fun a b => (hunique a).trans (hunique b).symm⟩
  have hcard := Fintype.card_le_one_iff_subsingleton.mpr hsub
  simp only [Fintype.card_fin] at hcard
  have hi0 := i.isLt
  omega

theorem ordered_length_one_eq_full {ell : ℕ} (hell : 0 < ell)
    (c : OrderedFinpartition ell) (hc : c.length = 1) : c = fullBlockPartition ell hell := by
  rcases c with ⟨length, size, hpos, emb, hmono, horder, hdis, hcover⟩
  dsimp only at hc
  subst length
  have hsize0 : size 0 = ell := by
    have hh := ordered_partSize_sum
      (OrderedFinpartition.mk 1 size hpos emb hmono horder hdis hcover)
    simpa only [Fin.sum_univ_one] using hh
  have hsize : size = fun _ : Fin 1 => ell := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hsize0
  subst size
  have hemb : emb = fun _ : Fin 1 => (id : Fin ell → Fin ell) := by
    funext i
    exact (hmono i).eq_id
  subst emb
  rfl

theorem ordered_nonfull_partSize_le {ell : ℕ} (hell : 0 < ell)
    (c : OrderedFinpartition ell) (hc : c ≠ fullBlockPartition ell hell) (i : Fin c.length) :
    c.partSize i ≤ ell - 1 := by
  have hle := c.partSize_le i
  have hne : c.partSize i ≠ ell := by
    intro he
    exact hc (ordered_length_one_eq_full hell c (ordered_full_size_length_one c he))
  omega

end SmoothLocal.HighEquation

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

theorem orderedPartial_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {ds es : List (Fin 2)} (hperm : ds.Perm es) :
    ∀ p ∈ U, iteratedCoordPartial ds f p = iteratedCoordPartial es f p := by
  induction hperm with
  | nil => intro p _; rfl
  | cons i _perm ih =>
      rename_i l1 l2
      intro p hp
      have he : iteratedCoordPartial l1 f =ᶠ[𝓝 p] iteratedCoordPartial l2 f := by
        filter_upwards [hU.mem_nhds hp] with q hq
        exact ih q hq
      exact coordPartial_eq_of_eventuallyEq he i
  | swap i j ds =>
      intro p hp
      exact normed_coordPartial_comm (orderedPartial_contDiffOn hf hU ds) hU hp j i
  | trans _ _ ih₁ ih₂ =>
      intro p hp
      exact (ih₁ p hp).trans (ih₂ p hp)

theorem coordinateDirections_apply (ds : List (Fin 2)) (i : Fin ds.length) :
    coordinateDirections ds i = Pi.single (ds.get i) (1 : ℝ) := by
  induction ds with
  | nil => exact Fin.elim0 i
  | cons a ds ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih j

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

theorem state_fullJet_eval
    {f : Coord → DarbouxState} {p : Coord} (hf : ContDiffAt ℝ ∞ f p)
    (n : ℕ) (v : Fin n → Coord) (i : Fin 6) :
    (iteratedFDeriv ℝ n f p v) i = iteratedFDeriv ℝ n (fun q => f q i) p v := by
  let L : DarbouxState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  symm
  change iteratedFDeriv ℝ n (L ∘ f) p v = L (iteratedFDeriv ℝ n f p v)
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

theorem fullJet_linear_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Coord →L[ℝ] E) {n : ℕ} (hn : 2 ≤ n) (p : Coord) (v : Fin n → Coord) :
    iteratedFDeriv ℝ n L p v = 0 := by
  cases n with
  | zero => omega
  | succ n =>
      have hn0 : n ≠ 0 := by omega
      rw [iteratedFDeriv_succ_apply_right]
      have he : (fun q => fderiv ℝ L q) = fun _ : Coord => L := by
        funext q
        exact L.fderiv
      rw [he, iteratedFDeriv_const_of_ne hn0]
      simp

theorem solutionJet_fullJet_ge_two
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (n : ℕ) (hn : 2 ≤ n) (v : Fin n → Coord) :
    iteratedFDeriv ℝ n (solutionJet z) p v =
      ![0, 0, iteratedFDeriv ℝ n (coordPartial 0 z) p v,
        iteratedFDeriv ℝ n (coordPartial 1 z) p v,
        iteratedFDeriv ℝ n (coordPartial 0 (coordPartial 1 z)) p v,
        iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 z)) p v] := by
  have hJ := (solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)
  ext i
  rw [state_fullJet_eval hJ n v i]
  fin_cases i
  · exact fullJet_linear_zero (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ) hn p v
  · exact fullJet_linear_zero (ContinuousLinearMap.proj 1 : Coord →L[ℝ] ℝ) hn p v
  · rfl
  · rfl
  · rfl
  · rfl

theorem word_two_x_permutation (ds : List (Fin 2)) (hx : 2 ≤ ds.count 0) :
    ∃ es : List (Fin 2), ds.Perm (es ++ [0, 0]) := by
  have h0 : (0 : Fin 2) ∈ ds := List.count_pos_iff.mp (by omega)
  have h1 : (0 : Fin 2) ∈ ds.erase 0 := List.count_pos_iff.mp (by
    rw [List.count_erase_self]
    omega)
  refine ⟨(ds.erase 0).erase 0, ?_⟩
  have h := (List.perm_cons_erase h0).trans ((List.perm_cons_erase h1).cons 0)
  exact h.trans (show ([0, 0] ++ (ds.erase 0).erase 0).Perm
    ((ds.erase 0).erase 0 ++ [0, 0]) from List.perm_append_comm)

theorem mixed_principal_word_orders (es : List (Fin 2)) :
    (es ++ [0, 1]).length = (es ++ [0, 0]).length ∧
    (es ++ [1, 1]).length = (es ++ [0, 0]).length ∧
    (es ++ [0, 1]).count 0 < (es ++ [0, 0]).count 0 ∧
    (es ++ [1, 1]).count 0 < (es ++ [0, 0]).count 0 := by
  simp

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

def mixedFaaTerm (g : MetricField) (z : Coord → ℝ) {k : ℕ} (v : Fin k → Coord)
    (c : OrderedFinpartition k) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJet z p)
    (fun j => iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j))

def mixedFaaFactor (z : Coord → ℝ) {k : ℕ} (v : Fin k → Coord)
    (c : OrderedFinpartition k) (r : Fin c.length → Fin 6) (j : Fin c.length) (p : Coord) : ℝ :=
  (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j)) (r j)

def mixedFaaRemainder (g : MetricField) (z : Coord → ℝ) {k : ℕ} (hk : 0 < k)
    (v : Fin k → Coord) (p : Coord) : ℝ :=
  heightPFirst g z 0 p * iteratedFDeriv ℝ k (coordPartial 0 z) p v +
  heightPFirst g z 1 p * iteratedFDeriv ℝ k (coordPartial 1 z) p v +
  ∑ c ∈ (Finset.univ.erase (fullBlockPartition k hk)), mixedFaaTerm g z v c p

def mixedBlockWord (ds : List (Fin 2)) (c : OrderedFinpartition ds.length)
    (j : Fin c.length) : List (Fin 2) := List.ofFn (fun i => ds.get (c.emb j i))

def heightStateSuffix : Fin 4 → List (Fin 2) := ![[0], [1], [0, 1], [1, 1]]

theorem heightStateSuffix_length (i : Fin 4) :
    (heightStateSuffix i).length = heightStateBaseOrder i := by
  fin_cases i <;> rfl

theorem heightStateFactor_zero_eq_suffix (z : Coord → ℝ) (i : Fin 4) :
    heightStateFactor z 0 i = iteratedCoordPartial (heightStateSuffix i) z := by
  fin_cases i <;> rfl

theorem mixedFaaTerm_scalar_expansion (g : MetricField) (z : Coord → ℝ)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (p : Coord) :
    mixedFaaTerm g z v c p =
      ∑ r : Fin c.length → Fin 6,
        coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
          ∏ j, mixedFaaFactor z v c r j p :=
  multilinear_state_components _ _

theorem mixedFaaFactor_height_slot
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (j : Fin c.length)
    (i : Fin 4) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j)) (heightComponentIndex i) =
      iteratedFDeriv ℝ (c.partSize j) (heightStateFactor z 0 i) p (v ∘ c.emb j) := by
  rw [state_fullJet_eval ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))]
  fin_cases i <;> rfl

theorem mixed_coordinate_height_factor_eq_word
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (c : OrderedFinpartition ds.length) (j : Fin c.length)
    (i : Fin 4) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i) =
      iteratedCoordPartial (mixedBlockWord ds c j ++ heightStateSuffix i) z p := by
  rw [mixedFaaFactor_height_slot hU hz hp]
  have hdir : (coordinateDirections ds ∘ c.emb j) =
      fun a => Pi.single (ds.get (c.emb j a)) (1 : ℝ) := by
    funext a
    exact coordinateDirections_apply ds (c.emb j a)
  rw [hdir, fullJet_coordinate_inputs_eq_ordered (heightStateFactor_contDiffOn hU hz 0 i) hU
    (c.partSize j) (fun a => ds.get (c.emb j a)) hp,
    heightStateFactor_zero_eq_suffix]
  exact (congrFun (orderedPartial_append (mixedBlockWord ds c j) (heightStateSuffix i) z) p).symm

theorem mixedFaaFactor_spatial_slot
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) (j : Fin c.length)
    (i : Fin 2) :
    (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p (v ∘ c.emb j))
        (if i = 0 then 0 else 1) =
      iteratedFDeriv ℝ (c.partSize j) (fun q : Coord => q i) p (v ∘ c.emb j) := by
  rw [state_fullJet_eval ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))]
  fin_cases i <;> rfl

theorem mixed_nonfull_height_word_length (ds : List (Fin 2)) (hds : 0 < ds.length)
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length hds)
    (j : Fin c.length) (i : Fin 4) :
    (mixedBlockWord ds c j ++ heightStateSuffix i).length ≤ ds.length + 1 := by
  have hsize := ordered_nonfull_partSize_le hds c hc j
  have hbase : heightStateBaseOrder i ≤ 2 := by fin_cases i <;> norm_num [heightStateBaseOrder]
  simp only [List.length_append, mixedBlockWord, List.length_ofFn, heightStateSuffix_length]
  omega

theorem mixedFaaRemainder_coordinate_eq
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (hds : 0 < ds.length) :
    mixedFaaRemainder g z hds (coordinateDirections ds) p =
      heightPFirst g z 0 p * iteratedCoordPartial (ds ++ [0]) z p +
      heightPFirst g z 1 p * iteratedCoordPartial (ds ++ [1]) z p +
      ∑ c ∈ (Finset.univ.erase (fullBlockPartition ds.length hds)),
        mixedFaaTerm g z (coordinateDirections ds) c p := by
  unfold mixedFaaRemainder
  rw [← iteratedCoordPartial_eq_jet (partial_contDiffOn hz hU 0) hU ds hp,
    ← iteratedCoordPartial_eq_jet (partial_contDiffOn hz hU 1) hU ds hp,
    orderedPartial_append ds [0], orderedPartial_append ds [1]]
  rfl

theorem actualP_mixed_faaExpansion
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (k : ℕ) (v : Fin k → Coord) :
    iteratedFDeriv ℝ k (sixVariableP g ∘ solutionJet z) p v =
      ∑ c : OrderedFinpartition k, mixedFaaTerm g z v c p := by
  have h := congrArg (fun L => L v) (iteratedFDeriv_comp
    (sixVariableP_contDiffAt_solutionJet hg hU hp hyy)
    ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))
    (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)))
  simpa [FormalMultilinearSeries.taylorComp, ftaylorSeries,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, mixedFaaTerm] using h

theorem mixed_fullBlock_term (g : MetricField) (z : Coord → ℝ) {k : ℕ}
    (hk : 0 < k) (v : Fin k → Coord) (p : Coord) :
    mixedFaaTerm g z v (fullBlockPartition k hk) p =
      fderiv ℝ (sixVariableP g) (solutionJet z p)
        (iteratedFDeriv ℝ k (solutionJet z) p v) := by
  change iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)
    (fun _ : Fin 1 => iteratedFDeriv ℝ k (solutionJet z) p (v ∘ id)) = _
  rw [iteratedFDeriv_one_apply]
  rfl

theorem mixed_fullBlock_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) (v : Fin k → Coord) :
    mixedFaaTerm g z v (fullBlockPartition k (by omega)) p =
      heightPFirst g z 0 p * iteratedFDeriv ℝ k (coordPartial 0 z) p v +
      heightPFirst g z 1 p * iteratedFDeriv ℝ k (coordPartial 1 z) p v +
      2 * hessianQuotient g z p *
        iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 1 z)) p v -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedFDeriv ℝ k (coordPartial 1 (coordPartial 1 z)) p v := by
  rw [mixed_fullBlock_term, solutionJet_fullJet_ge_two hU hz hp k hk v]
  rw [sixVariableP_vertical_direction hg hU hp hyy _ (by rfl) (by rfl)]
  rfl

theorem actualDarboux_mixed_principal
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    {k : ℕ} (hk : 2 ≤ k) (v : Fin k → Coord) :
    iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 0 z)) p v =
      2 * hessianQuotient g z p *
        iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 1 z)) p v -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedFDeriv ℝ k (coordPartial 1 (coordPartial 1 z)) p v +
      mixedFaaRemainder g z (by omega) v p := by
  classical
  have heq : coordPartial 0 (coordPartial 0 z) =ᶠ[𝓝 p] sixVariableP g ∘ solutionJet z := by
    filter_upwards [hU.mem_nhds hp] with q hq
    change coordPartial 0 (coordPartial 0 z) q = sixVariableP g (solutionJet z q)
    rw [sixVariableP_solutionJet]
    exact solvedDarboux_at_height hg hU hz hq (hyy q hq) (hD q hq)
  have hder := congrArg (fun L => L v) ((heq.iteratedFDeriv ℝ k).self_of_nhds)
  have hfaa := actualP_mixed_faaExpansion hg hU hz hp (hyy p hp) k v
  have hsplit := (Finset.add_sum_erase (Finset.univ : Finset (OrderedFinpartition k))
    (fun c => mixedFaaTerm g z v c p) (Finset.mem_univ (fullBlockPartition k (by omega)))).symm
  rw [mixed_fullBlock_linearization hg hU hz hp (hyy p hp) hk v] at hsplit
  have hfull := hder.trans (hfaa.trans hsplit)
  calc
    _ = _ := hfull
    _ = _ := by unfold mixedFaaRemainder; ring

theorem actualDarboux_ordered_mixed_elimination
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    (ds : List (Fin 2)) (hds : 2 ≤ ds.length) :
    iteratedCoordPartial (ds ++ [0, 0]) z p =
      2 * hessianQuotient g z p * iteratedCoordPartial (ds ++ [0, 1]) z p -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedCoordPartial (ds ++ [1, 1]) z p +
      mixedFaaRemainder g z (by omega) (coordinateDirections ds) p := by
  have h := actualDarboux_mixed_principal hg hU hz hD hyy hp hds (coordinateDirections ds)
  have hxx := partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0
  have hxy := partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  have hyyS := partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1
  rw [← iteratedCoordPartial_eq_jet hxx hU ds hp,
    ← iteratedCoordPartial_eq_jet hxy hU ds hp,
    ← iteratedCoordPartial_eq_jet hyyS hU ds hp] at h
  rw [orderedPartial_append ds [0, 0], orderedPartial_append ds [0, 1],
    orderedPartial_append ds [1, 1]]
  exact h

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
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem fullJet_fixed_input_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (n : ℕ) (v : Fin n → Coord) :
    ContinuousOn (fun p => iteratedFDeriv ℝ n f p v) U := by
  intro p hp
  have hD := ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)).continuousAt
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Coord) E v).continuous.continuousAt
    (x := iteratedFDeriv ℝ n f p)
  exact (hev.comp hD).continuousWithinAt

theorem mixedFaaFactor_continuousOn
    {z : Coord → ℝ} {U : Set Coord} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k)
    (r : Fin c.length → Fin 6) (j : Fin c.length) :
    ContinuousOn (mixedFaaFactor z v c r j) U :=
  (ContinuousLinearMap.proj (r j) : DarbouxState →L[ℝ] ℝ).continuous.comp_continuousOn
    (fullJet_fixed_input_continuousOn (solutionJet_contDiffOn hU hz) hU (c.partSize j) (v ∘ c.emb j))

theorem mixedFaaTerm_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) :
    ContinuousOn (mixedFaaTerm g z v c) U := by
  have hm (r : Fin c.length → Fin 6) : ContinuousOn
      (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z v c r j p) U :=
    (coordinateChainCoefficient_continuousOn hg hU hz hyy ⟨c.length, c.partSize⟩ r).mul
      (continuousOn_finsetProd Finset.univ
        (fun index _ => mixedFaaFactor_continuousOn hU hz v c r index))
  exact (continuousOn_finsetSum Finset.univ (fun indices _ => hm indices)).congr
    (fun point _ => mixedFaaTerm_scalar_expansion g z v c point)

theorem fullJet_coordinate_projection_abs_le_one {n : ℕ} (hn : 0 < n)
    (d : Fin n → Fin 2) (i : Fin 2) (p : Coord) :
    |iteratedFDeriv ℝ n (fun q : Coord => q i) p (fun j => Pi.single (d j) (1 : ℝ))| ≤ 1 := by
  by_cases hn1 : n = 1
  · subst n
    change |iteratedFDeriv ℝ 1 (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ) p _| ≤ 1
    rw [iteratedFDeriv_one_apply, ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.proj_apply, Pi.single_apply]
    split_ifs <;> norm_num
  · change |iteratedFDeriv ℝ n (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ) p _| ≤ 1
    rw [fullJet_linear_zero _ (by omega)]
    norm_num

theorem mixedBlock_spatial_abs_le_one
    {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (ds : List (Fin 2)) (c : OrderedFinpartition ds.length) (j : Fin c.length) (i : Fin 2) :
    |(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) (if i = 0 then 0 else 1)| ≤ 1 := by
  rw [mixedFaaFactor_spatial_slot hU hz hp]
  have hd : (coordinateDirections ds ∘ c.emb j) = fun a => Pi.single (ds.get (c.emb j a)) (1 : ℝ) := by
    funext a
    exact coordinateDirections_apply ds (c.emb j a)
  rw [hd]
  exact fullJet_coordinate_projection_abs_le_one (c.partSize_pos j) _ i p

theorem mixed_high_factor_unique {k : ℕ} (hk : 5 ≤ k)
    (c : OrderedFinpartition k) (r : Fin c.length → Fin 6) {i j : Fin c.length}
    (hi : k ≤ c.partSize i + stateBaseOrder (r i))
    (hj : k ≤ c.partSize j + stateBaseOrder (r j)) : i = j := by
  by_contra hij
  have hb := ordered_two_partSizes_le c hij
  have hbi := stateBaseOrder_le_two (r i)
  have hbj := stateBaseOrder_le_two (r j)
  omega

theorem mixedBlock_low_norm_bound
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hVU : V ⊆ U)
    (ds : List (Fin 2)) {B : ℝ} (hB : 1 ≤ B)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (c : OrderedFinpartition ds.length) (j : Fin c.length) (a : Fin 6)
    (horder : c.partSize j + stateBaseOrder a ≤ ds.length - 1)
    {p : Coord} (hp : p ∈ V) :
    ‖(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) a‖ ≤ B := by
  have hh (i : Fin 4) (hi : c.partSize j + heightStateBaseOrder i ≤ ds.length - 1) :
      |(iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)| ≤ B := by
    rw [mixed_coordinate_height_factor_eq_word hU hz (hVU hp)]
    exact hlow _ (by simpa [mixedBlockWord, heightStateSuffix_length] using hi) p hp
  fin_cases a
  · simpa [Real.norm_eq_abs] using (mixedBlock_spatial_abs_le_one hU hz (hVU hp) ds c j 0).trans hB
  · simpa [Real.norm_eq_abs] using (mixedBlock_spatial_abs_le_one hU hz (hVU hp) ds c j 1).trans hB
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 0
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 1
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 2
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)
  · simpa [heightComponentIndex, Real.norm_eq_abs] using hh 3
      (by simpa [heightStateBaseOrder, stateBaseOrder] using horder)

theorem mixedBlock_high_eLpNorm_bound
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 0 < ds.length) {H : ℝ≥0}
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length hds)
    (j : Fin c.length) (a : Fin 6)
    (hhigh : ds.length ≤ c.partSize j + stateBaseOrder a) :
    eLpNorm (fun p => (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
      (coordinateDirections ds ∘ c.emb j)) a) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  have hn := ordered_nonfull_partSize_le hds c hc j
  have hh (i : Fin 4) : eLpNorm (fun p =>
      (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)) 2 (volume.restrict V) ≤
      (H : ℝ≥0∞) := by
    have he : (fun p => (iteratedFDeriv ℝ (c.partSize j) (solutionJet z) p
        (coordinateDirections ds ∘ c.emb j)) (heightComponentIndex i)) =ᵐ[volume.restrict V]
        iteratedCoordPartial (mixedBlockWord ds c j ++ heightStateSuffix i) z := by
      filter_upwards [ae_restrict_mem hV] with p hp
      exact mixed_coordinate_height_factor_eq_word hU hz (hVU hp) ds c j i
    rw [eLpNorm_congr_ae he]
    exact hheight _ (mixed_nonfull_height_word_length ds hds c hc j i)
  fin_cases a
  · norm_num [stateBaseOrder] at hhigh
    omega
  · norm_num [stateBaseOrder] at hhigh
    omega
  · simpa [heightComponentIndex] using hh 0
  · simpa [heightComponentIndex] using hh 1
  · simpa [heightComponentIndex] using hh 2
  · simpa [heightComponentIndex] using hh 3

theorem heightPFirst_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    |heightPFirst g z i p| ≤ ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single (gradientStateIndex i) (1 : ℝ))
  simpa only [sixVariableP_gradient_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

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

theorem mixedRemainderL2Budget_lt_top (C B : ℝ) (H : ℝ≥0) {V : Set Coord}
    (hVfinite : volume V < (⊤ : ℝ≥0∞)) (k : ℕ) : mixedRemainderL2Budget C B H V k < (⊤ : ℝ≥0∞) := by
  unfold mixedRemainderL2Budget
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · unfold firstJetPairL2Budget
    finiteness
  · exact ENNReal.sum_lt_top.mpr (fun c _ =>
      chainWordL2Budget_lt_top C B H hVfinite k ⟨c.length, c.partSize⟩)

theorem mixedFaaRemainder_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (hk : 0 < k) (v : Fin k → Coord) :
    ContinuousOn (mixedFaaRemainder g z hk v) U :=
  (((heightPFirst_contDiffOn hg hU hz hyy 0).continuousOn.mul
      (fullJet_fixed_input_continuousOn (partial_contDiffOn hz hU 0) hU k v)).add
    ((heightPFirst_contDiffOn hg hU hz hyy 1).continuousOn.mul
      (fullJet_fixed_input_continuousOn (partial_contDiffOn hz hU 1) hU k v))).add
    (continuousOn_finsetSum (Finset.univ.erase (fullBlockPartition k hk))
      (fun c _ => mixedFaaTerm_continuousOn hg hU hz hyy v c))

theorem mixed_product_eLpNorm_two
    {z : Coord → ℝ} {U V : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {B : ℝ} (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length (by omega))
    (r : Fin c.length → Fin 6) :
    eLpNorm (fun p => ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p)
      2 (volume.restrict V) ≤ chainProductL2Budget B H V ds.length := by
  classical
  have hB0 : 0 ≤ B := by linarith
  have hprod : AEStronglyMeasurable
      (fun point => ∏ index, mixedFaaFactor z (coordinateDirections ds) c r index point)
      (volume.restrict V) :=
    ((continuousOn_finsetProd Finset.univ
      (fun index _ => mixedFaaFactor_continuousOn hU hz (coordinateDirections ds) c r index)).mono
        hVU).aestronglyMeasurable (μ := volume) hV
  by_cases hh : ∃ j, ds.length ≤ c.partSize j + stateBaseOrder (r j)
  · obtain ⟨j, hj⟩ := hh
    have hlo : ∀ i ∈ (Finset.univ : Finset (Fin c.length)).erase j,
        ∀ p ∈ V, ‖mixedFaaFactor z (coordinateDirections ds) c r i p‖ ≤ B := by
      intro i hi p hp
      have ho : c.partSize i + stateBaseOrder (r i) ≤ ds.length - 1 := by
        by_contra hn
        have he := mixed_high_factor_unique (i := i) (j := j) hds c r (by omega) hj
        exact (Finset.mem_erase.mp hi).1 he
      exact mixedBlock_low_norm_bound hU hz hVU ds hB hlow c i (r i) ho hp
    have hjL := mixedBlock_high_eLpNorm_bound hU hz hV hVU ds (by omega)
      hheight c hc j (r j) hj
    have hcard : ((Finset.univ : Finset (Fin c.length)).erase j).card ≤ ds.length := by
      have he : ((Finset.univ : Finset (Fin c.length)).erase j).card ≤ c.length := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin c.length)))
      exact he.trans c.length_le
    exact (finite_product_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (mixedFaaFactor z (coordinateDirections ds) c r) (Finset.mem_univ j) hB0 hV hlo hprod).trans
      (mul_le_mul' (enorm_pow_mono_of_one_le hB hcard)
        (hjL.trans (le_add_of_nonneg_right (by positivity))))
  · have hlo : ∀ i ∈ (Finset.univ : Finset (Fin c.length)),
        ∀ p ∈ V, ‖mixedFaaFactor z (coordinateDirections ds) c r i p‖ ≤ B := by
      intro i _ p hp
      have ho : c.partSize i + stateBaseOrder (r i) ≤ ds.length - 1 := by
        have hn : ¬ ds.length ≤ c.partSize i + stateBaseOrder (r i) := fun h => hh ⟨i, h⟩
        omega
      exact mixedBlock_low_norm_bound hU hz hVU ds hB hlow c i (r i) ho hp
    have hb := finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable (μ := volume) Finset.univ
      (mixedFaaFactor z (coordinateDirections ds) c r) hB0 hV hlo hprod
    have hb' : eLpNorm (fun p => ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p)
        2 (volume.restrict V) ≤ ‖B ^ c.length‖ₑ * (volume V) ^ (1 / (2 : ℝ)) := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hb
    exact hb'.trans (mul_le_mul' (enorm_pow_mono_of_one_le hB c.length_le)
      (le_add_of_nonneg_left (by positivity)))

theorem mixedFaaTerm_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ ds.length, ∀ p ∈ V, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length (by omega)) :
    eLpNorm (mixedFaaTerm g z (coordinateDirections ds) c) 2 (volume.restrict V) ≤
      chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩ := by
  classical
  have hcoeff (r : Fin c.length → Fin 6) (p : Coord) (hp : p ∈ V) :
      |coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p| ≤ C :=
    (coordinateChainCoefficient_abs_le_full_derivative g z ⟨c.length, c.partSize⟩ r p).trans
      (hP c.length c.length_le p hp)
  have hm (r : Fin c.length → Fin 6) : AEStronglyMeasurable
      (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p) (volume.restrict V) :=
    (((coordinateChainCoefficient_continuousOn hg hU hz hyy ⟨c.length, c.partSize⟩ r).mul
      (continuousOn_finsetProd Finset.univ
        (fun j _ => mixedFaaFactor_continuousOn hU hz (coordinateDirections ds) c r j))).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hterm (r : Fin c.length → Fin 6) :
      eLpNorm (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p) 2 (volume.restrict V) ≤
        ‖C‖ₑ * chainProductL2Budget B H V ds.length :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (hcoeff r) (hm r)).trans
      (mul_le_mul' le_rfl (mixed_product_eLpNorm_two hU hz hV hVU ds hds hB hlow hheight c hc r))
  have he : mixedFaaTerm g z (coordinateDirections ds) c = fun p =>
      ∑ r : Fin c.length → Fin 6,
        coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
          ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p :=
    funext (mixedFaaTerm_scalar_expansion g z (coordinateDirections ds) c)
  rw [he]
  exact finite_sum_eLpNorm_two Finset.univ _
    (fun _ => ‖C‖ₑ * chainProductL2Budget B H V ds.length)
    (fun r _ => hm r) (fun r _ => hterm r)

theorem mixedFaaRemainder_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ ds.length, ∀ p ∈ V, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) :
    eLpNorm (mixedFaaRemainder g z (by omega) (coordinateDirections ds)) 2 (volume.restrict V) ≤
      mixedRemainderL2Budget C B H V ds.length := by
  classical
  let s := (Finset.univ : Finset (OrderedFinpartition ds.length)).erase (fullBlockPartition ds.length (by omega))
  let f0 : Coord → ℝ := fun p => heightPFirst g z 0 p * iteratedCoordPartial (ds ++ [0]) z p
  let f1 : Coord → ℝ := fun p => heightPFirst g z 1 p * iteratedCoordPartial (ds ++ [1]) z p
  let fs : Coord → ℝ := fun p => ∑ c ∈ s, mixedFaaTerm g z (coordinateDirections ds) c p
  have hfirst (i : Fin 2) (p : Coord) (hp : p ∈ V) : |heightPFirst g z i p| ≤ C :=
    (heightPFirst_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp)) i).trans
      (hP 1 (by omega) p hp)
  have hm0 : AEStronglyMeasurable f0 (volume.restrict V) :=
    (((heightPFirst_contDiffOn hg hU hz hyy 0).continuousOn.mul
      (orderedPartial_contDiffOn hz hU (ds ++ [0])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hm1 : AEStronglyMeasurable f1 (volume.restrict V) :=
    (((heightPFirst_contDiffOn hg hU hz hyy 1).continuousOn.mul
      (orderedPartial_contDiffOn hz hU (ds ++ [1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hb0 : eLpNorm f0 2 (volume.restrict V) ≤ ‖C‖ₑ * (H : ℝ≥0∞) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
      (f := iteratedCoordPartial (ds ++ [0]) z) hV hC (hfirst 0) hm0).trans
      (mul_le_mul' le_rfl (hheight (ds ++ [0]) (by simp)))
  have hb1 : eLpNorm f1 2 (volume.restrict V) ≤ ‖C‖ₑ * (H : ℝ≥0∞) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
      (f := iteratedCoordPartial (ds ++ [1]) z) hV hC (hfirst 1) hm1).trans
      (mul_le_mul' le_rfl (hheight (ds ++ [1]) (by simp)))
  have hbs : eLpNorm fs 2 (volume.restrict V) ≤
      ∑ c : OrderedFinpartition ds.length, chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩ := by
    have hsum := finite_sum_eLpNorm_two s (fun c => mixedFaaTerm g z (coordinateDirections ds) c)
      (fun c => chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩)
      (fun c _ => ((mixedFaaTerm_continuousOn hg hU hz hyy (coordinateDirections ds) c).mono hVU).aestronglyMeasurable (μ := volume) hV)
      (fun c hc => mixedFaaTerm_eLpNorm_two hg hU hz hyy hV hVU ds hds hC hB hP hlow hheight c
        (Finset.mem_erase.mp hc).1)
    exact hsum.trans (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
  have he : mixedFaaRemainder g z (by omega) (coordinateDirections ds) =ᵐ[volume.restrict V]
      (fun p => f0 p + f1 p + fs p) := by
    filter_upwards [ae_restrict_mem hV] with p hp
    exact mixedFaaRemainder_coordinate_eq hU hz (hVU hp) ds (by omega)
  have hms : AEStronglyMeasurable fs (volume.restrict V) :=
    ((continuousOn_finset_sum s (fun c _ =>
      mixedFaaTerm_continuousOn hg hU hz hyy (coordinateDirections ds) c)).mono hVU).aestronglyMeasurable (μ := volume) hV
  rw [eLpNorm_congr_ae he]
  exact (eLpNorm_add_le (hm0.add hm1) hms (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add ((eLpNorm_add_le hm0 hm1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add hb0 hb1)) hbs)

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

theorem word_no_x_eq_replicate (ds : List (Fin 2)) (hx : ds.count 0 = 0) :
    ds = List.replicate ds.length 1 := by
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, ?_⟩
  intro i hi
  fin_cases i
  · have hpos : 0 < ds.count 0 := List.count_pos_iff.mpr hi
    omega
  · rfl

theorem orderedPartial_replicate_y (z : Coord → ℝ) (n : ℕ) :
    iteratedCoordPartial (List.replicate n 1) z = verticalJet z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, iteratedCoordPartial, verticalJet, ih]

theorem orderedPartial_at_most_one_x_eLpNorm
    {z : Coord → ℝ} {U V : Set Coord} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} {Htop : ℝ≥0}
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N - 1))) 2
      (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) (hx : ds.count 0 ≤ 1) :
    eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞) := by
  by_cases hzcount : ds.count 0 = 0
  · rw [word_no_x_eq_replicate ds hzcount, orderedPartial_replicate_y, hlen]
    exact hv
  · have hcount : ds.count 0 = 1 := by omega
    have hmem : (0 : Fin 2) ∈ ds := List.count_pos_iff.mp (by omega)
    have hperm := List.perm_cons_erase hmem
    have herase : (ds.erase 0).count 0 = 0 := by
      rw [List.count_erase_self, hcount]
    have heraseLen : (ds.erase 0).length = N - 1 := by
      have h := hperm.length_eq
      simp only [List.length_cons] at h
      omega
    have he : iteratedCoordPartial ds z =ᵐ[volume.restrict V]
        coordPartial 0 (verticalJet z (N - 1)) := by
      filter_upwards [ae_restrict_mem hV] with p hp
      have h := orderedPartial_perm hz hU hperm p (hVU hp)
      rw [word_no_x_eq_replicate (ds.erase 0) herase, heraseLen] at h
      simpa only [iteratedCoordPartial, orderedPartial_replicate_y] using h
    rw [eLpNorm_congr_ae he]
    exact hxv

theorem principal_mixed_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    |2 * hessianQuotient g z p| ≤
      ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single 4 (1 : ℝ))
  simpa only [sixVariableP_mixed_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

theorem principal_yy_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    |-((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p)| ≤
      ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single 5 (1 : ℝ))
  simpa only [sixVariableP_yy_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

theorem ordered_mixed_eLpNorm_step
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ N - 2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N - 3) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ N - 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) (hx : 2 ≤ ds.count 0) :
    ∃ es : List (Fin 2), es.length + 2 = N ∧
      (es ++ [0, 1]).count 0 < ds.count 0 ∧
      (es ++ [1, 1]).count 0 < ds.count 0 ∧
      eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤
        ‖C‖ₑ * eLpNorm (iteratedCoordPartial (es ++ [0, 1]) z) 2 (volume.restrict V) +
        ‖C‖ₑ * eLpNorm (iteratedCoordPartial (es ++ [1, 1]) z) 2 (volume.restrict V) +
        mixedRemainderL2Budget C B H V (N - 2) := by
  obtain ⟨es, hperm⟩ := word_two_x_permutation ds hx
  have heslen : es.length + 2 = N := by simpa [hlen] using hperm.length_eq.symm
  have hesN : es.length = N - 2 := by omega
  have hes : 5 ≤ es.length := by omega
  have hc := hperm.count_eq (0 : Fin 2)
  obtain ⟨_, _, hxy, hyyc⟩ := mixed_principal_word_orders es
  refine ⟨es, heslen, ?_, ?_, ?_⟩
  · simpa only [hc] using hxy
  · simpa only [hc] using hyyc
  let a : Coord → ℝ := fun p => 2 * hessianQuotient g z p
  let b : Coord → ℝ := fun p =>
    -((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p)
  let f : Coord → ℝ := iteratedCoordPartial (es ++ [0, 1]) z
  let h : Coord → ℝ := iteratedCoordPartial (es ++ [1, 1]) z
  let R : Coord → ℝ := mixedFaaRemainder g z (by omega) (coordinateDirections es)
  have haS : ContinuousOn a U :=
    continuousOn_const.mul (hessianQuotient_contDiffOn hg hU hz hyy).continuousOn
  have hbS : ContinuousOn b U :=
    (((hessianQuotient_contDiffOn hg hU hz hyy).continuousOn.pow 2).add
      ((gaussianCurvature_contDiffOn hg hU).continuousOn.mul
        (darbouxG_contDiffOn hg hU hz hyy).continuousOn)).neg
  have haf : AEStronglyMeasurable (fun p => a p * f p) (volume.restrict V) :=
    ((haS.mul (orderedPartial_contDiffOn hz hU (es ++ [0, 1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hbh : AEStronglyMeasurable (fun p => b p * h p) (volume.restrict V) :=
    ((hbS.mul (orderedPartial_contDiffOn hz hU (es ++ [1, 1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hafB : eLpNorm (fun p => a p * f p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm f 2 (volume.restrict V) :=
    scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (fun p hp =>
      (principal_mixed_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp))).trans
        (hP 1 (by omega) p hp)) haf
  have hbhB : eLpNorm (fun p => b p * h p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm h 2 (volume.restrict V) :=
    scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (fun p hp =>
      (principal_yy_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp))).trans
        (hP 1 (by omega) p hp)) hbh
  have hRB : eLpNorm R 2 (volume.restrict V) ≤ mixedRemainderL2Budget C B H V (N - 2) := by
    have hP' : ∀ n ≤ es.length, ∀ p ∈ V,
        ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C := by
      simpa only [hesN] using hP
    have hlo' : CoordinateBound z V (es.length - 1) B := by
      convert hlow using 1 <;> try with_reducible_and_instances rfl
      omega
    have hh' : ∀ fs : List (Fin 2), fs.length ≤ es.length + 1 →
        eLpNorm (iteratedCoordPartial fs z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
      fun fs hfs => hheight fs (by omega)
    simpa only [hesN] using
      mixedFaaRemainder_eLpNorm_two hg hU hz hyy hV hVU es hes hC hB hP' hlo' hh'
  have he : iteratedCoordPartial ds z =ᵐ[volume.restrict V]
      (fun p => (a p * f p + b p * h p) + R p) := by
    filter_upwards [ae_restrict_mem hV] with p hp
    have he := (orderedPartial_perm hz hU hperm p (hVU hp)).trans
      (actualDarboux_ordered_mixed_elimination hg hU hz hD hyy (hVU hp) es (by omega))
    dsimp only [a, b, f, h, R]
    simpa only [neg_mul, sub_eq_add_neg] using he
  rw [eLpNorm_congr_ae he]
  have he1 := eLpNorm_add_le
    (f := fun point => a point * f point) (g := fun point => b point * h point)
    (μ := volume.restrict V) haf hbh (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he2 := eLpNorm_add_le
    (f := fun point => a point * f point + b point * h point) (g := R)
    (μ := volume.restrict V) (haf.add hbh)
    (((mixedFaaRemainder_continuousOn hg hU hz hyy (by omega) (coordinateDirections es)).mono hVU).aestronglyMeasurable (μ := volume) hV)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact he2.trans (add_le_add (he1.trans (add_le_add hafB hbhB)) hRB)

theorem mixedXBudget_monotone (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) :
    Monotone (mixedXBudget C R Htop) := by
  apply monotone_nat_of_le_succ
  intro n
  have h : (1 : ℝ≥0∞) ≤ 1 + ‖C‖ₑ + ‖C‖ₑ :=
    (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  calc
    mixedXBudget C R Htop n = 1 * mixedXBudget C R Htop n := (one_mul _).symm
    _ ≤ (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n := mul_le_mul' h le_rfl
    _ = mixedXBudget C R Htop (n + 1) := rfl

theorem mixedXBudget_base_le (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) (n : ℕ) :
    (Htop : ℝ≥0∞) + R ≤ mixedXBudget C R Htop n :=
  mixedXBudget_monotone C R Htop (Nat.zero_le n)

theorem mixedXBudget_step (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) (n : ℕ)
    {a b : ℝ≥0∞} (ha : a ≤ mixedXBudget C R Htop n)
    (hb : b ≤ mixedXBudget C R Htop n) :
    ‖C‖ₑ * a + ‖C‖ₑ * b + R ≤ mixedXBudget C R Htop (n + 1) := by
  have hR : R ≤ mixedXBudget C R Htop n :=
    (le_add_of_nonneg_left (by positivity)).trans (mixedXBudget_base_le C R Htop n)
  calc
    _ ≤ ‖C‖ₑ * mixedXBudget C R Htop n +
        ‖C‖ₑ * mixedXBudget C R Htop n + mixedXBudget C R Htop n :=
      add_le_add (add_le_add (mul_le_mul' le_rfl ha) (mul_le_mul' le_rfl hb)) hR
    _ = mixedXBudget C R Htop (n + 1) := by rw [mixedXBudget]; ring

theorem mixedXBudget_lt_top (C : ℝ) {R : ℝ≥0∞} (hR : R < (⊤ : ℝ≥0∞))
    (Htop : ℝ≥0) (n : ℕ) : mixedXBudget C R Htop n < (⊤ : ℝ≥0∞) := by
  induction n with
  | zero => simpa only [mixedXBudget] using ENNReal.add_lt_top.mpr ⟨by finiteness, hR⟩
  | succ n ih =>
      change (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n < (⊤ : ℝ≥0∞)
      exact ENNReal.mul_lt_top (by finiteness) ih

theorem all_orderN_mixed_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H Htop : ℝ≥0}
    (hP : ∀ n ≤ N - 2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N - 3) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ N - 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N - 1))) 2
      (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) :
    eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤
      mixedXBudget C (mixedRemainderL2Budget C B H V (N - 2)) Htop N := by
  let R := mixedRemainderL2Budget C B H V (N - 2)
  have hind : ∀ j : ℕ, ∀ es : List (Fin 2), es.length = N → es.count 0 = j →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ mixedXBudget C R Htop j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro es hes hecount
      by_cases hj : j ≤ 1
      · exact (orderedPartial_at_most_one_x_eLpNorm hU hz hV hVU hv hxv es hes
          (by omega)).trans ((le_add_of_nonneg_right (by positivity)).trans
            (mixedXBudget_base_le C R Htop j))
      · obtain ⟨fs, hflen, hfc0, hfc1, hstep⟩ := ordered_mixed_eLpNorm_step
          hg hU hz hD hyy hV hVU hN hC hB hP hlow hheight es hes (by omega)
        have hlen0 : (fs ++ [0, 1]).length = N := by simpa using hflen
        have hlen1 : (fs ++ [1, 1]).length = N := by simpa using hflen
        have hb0 := ih ((fs ++ [0, 1]).count 0) (by omega) (fs ++ [0, 1]) hlen0 rfl
        have hb1 := ih ((fs ++ [1, 1]).count 0) (by omega) (fs ++ [1, 1]) hlen1 rfl
        have hb0' := hb0.trans (mixedXBudget_monotone C R Htop (by omega :
          (fs ++ [0, 1]).count 0 ≤ j - 1))
        have hb1' := hb1.trans (mixedXBudget_monotone C R Htop (by omega :
          (fs ++ [1, 1]).count 0 ≤ j - 1))
        have hsum := hstep.trans (mixedXBudget_step C R Htop (j - 1) hb0' hb1')
        simpa only [show j - 1 + 1 = j by omega] using hsum
  exact (hind (ds.count 0) ds hlen rfl).trans
    (mixedXBudget_monotone C R Htop (hlen ▸ List.count_le_length))

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

end SmoothLocal.Analytic

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem CoordinateL2Bound.eLpNorm_le {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (hbound : CoordinateL2Bound z V N H) (word : List (Fin 2)) (hword : word.length ≤ N)
    (hmeas : AEStronglyMeasurable (iteratedCoordPartial word z) (volume.restrict V)) :
    eLpNorm (iteratedCoordPartial word z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact hbound word hword

end SmoothLocal.HighEquation

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev
open SmoothLocal.HighEquation

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

theorem mixedRemainderL2Budget_mono_area (C B : ℝ) (H : ℝ≥0) {V W : Set Coord}
    (hVW : volume V ≤ volume W) (k : ℕ) :
    mixedRemainderL2Budget C B H V k ≤ mixedRemainderL2Budget C B H W k := by
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro composition _
  exact chainWordL2Budget_mono_area C B H hVW k ⟨composition.length, composition.partSize⟩

theorem mixedXBudget_mono_remainder (C : ℝ) {R S : ℝ≥0∞} (hRS : R ≤ S)
    (Htop : ℝ≥0) (n : ℕ) : mixedXBudget C R Htop n ≤ mixedXBudget C S Htop n := by
  induction n with
  | zero => exact add_le_add le_rfl hRS
  | succ _ ih => exact mul_le_mul' le_rfl ih

theorem uniformMixedOrderBudget_coe (C B : ℝ) (H Htop : ℝ≥0) (N : ℕ) :
    (uniformMixedOrderBudget C B H Htop N : ℝ≥0∞) =
      max (H : ℝ≥0∞) (mixedXBudget C (mixedRemainderL2Budget C B H modelSquare (N-2)) Htop N) := by
  unfold uniformMixedOrderBudget
  rw [ENNReal.coe_max, ENNReal.coe_toNNReal
    (mixedXBudget_lt_top C
      (mixedRemainderL2Budget_lt_top C B H modelSquare_isCompact.measure_lt_top (N-2)) Htop N).ne]

theorem coordinateL2Bound_order_step
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVS : V ⊆ modelSquare)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H Htop : ℝ≥0}
    (hP : ∀ n ≤ N-2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N-3) B)
    (hheight : CoordinateL2Bound z V (N-1) H)
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N-1))) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞)) :
    CoordinateL2Bound z V N (uniformMixedOrderBudget C B H Htop N) := by
  have hmeas (word : List (Fin 2)) :
      AEStronglyMeasurable (iteratedCoordPartial word z) (volume.restrict V) :=
    ((orderedPartial_contDiffOn hz hU word).continuousOn.mono
      hVU).aestronglyMeasurable (μ := volume) hV
  intro ds hds
  rw [uniformMixedOrderBudget_coe]
  by_cases hloworder : ds.length ≤ N-1
  · exact (hheight ds hloworder).trans (le_max_left _ _)
  · have hlen : ds.length = N := by omega
    have hhigh := all_orderN_mixed_eLpNorm_two hg hU hz hD hyy hV hVU hN hC hB hP hlow
      (fun word hword => hheight.eLpNorm_le word hword (hmeas word)) hv hxv ds hlen
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
      ENNReal.toReal_ofNat] at hhigh
    exact (hhigh.trans (mixedXBudget_mono_remainder C
        (mixedRemainderL2Budget_mono_area C B H (measure_mono hVS) (N-2)) Htop N)).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.HighEquation.coordinateL2Bound_order_step := @OAI.SmoothLocal.HighEquation.coordinateL2Bound_order_step
