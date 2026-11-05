-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.exists_original_pulse_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:18:21.650044+00:00
-- url     : https://prove2.me/submissions/b54b9bc0-39a8-4d56-ae9a-2a018ca924ff

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Flow_exists_C8_one_flow_physical_cap_estimates
import Theorems.Thm_OAI_SmoothLocal_Perturbation_actual_central_sheared_solution_margins
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_reference_segment_at_radius
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_original_class_comparison_with_low_data

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

theorem integral_product_abs_le_sqrt_squares
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have he : (∫ x, f x * g x ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    change (∫ x, f x * g x ∂μ) = ∫ x, inner ℝ (hf.toLp f x) (hg.toLp g x) ∂μ
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp only [hfx, hgx, Real.inner_apply]
  rw [he, sqrt_integral_square_eq_L2_norm hf, sqrt_integral_square_eq_L2_norm hg]
  exact abs_real_inner_le_norm _ _

end SmoothLocal.Hyperbolic

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
namespace SmoothLocal.Geometry

theorem SmoothPositiveOn.mono {g : MetricField} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hVU : V ⊆ U) : SmoothPositiveOn g V :=
  ⟨fun i j => (hg.1 i j).mono hVU,fun p hp => hg.2 p (hVU hp)⟩

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

theorem coordPartial_eval (i j : Fin 2) (u : Coord) :
    coordPartial i (fun v : Coord => v j) u = if j = i then 1 else 0 := by
  simp [coordPartial, (hasFDerivAt_apply j u).fderiv, Pi.single_apply]

end DarbouxJetCalculus

theorem jetEnergy_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (z : Coord → ℝ) :
    jetEnergy g p (fun i => coordPartial i z p) = heightEnergy g z p := by
  symm
  exact heightEnergy_polynomial z hg hp

theorem jetMixed_at_height (g : MetricField) (p : Coord) (z : Coord → ℝ) :
    jetMixed g p (coordPartial 0 (coordPartial 1 z) p) (fun i => coordPartial i z p) =
      covHessian g z p 0 1 := rfl

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

theorem rectangleIntegral_congr (ht : tl ≤ tr) (hs : sb ≤ st)
    (heq : EqOn f g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f = rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  apply intervalIntegral.integral_congr
  intro s hs'
  apply intervalIntegral.integral_congr
  intro t ht'
  exact heq (boxPoint_mem
    (by simpa only [uIcc_of_le ht] using ht')
    (by simpa only [uIcc_of_le hs] using hs'))

theorem rectangleIntegral_add (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st))
    (hg : ContinuousOn g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => f p + g p) =
      rectangleIntegral tl tr sb st f + rectangleIntegral tl tr sb st g := by
  have hfg : ContinuousOn (fun p => f p + g p) (closedRectangle tl tr sb st) := hf.add hg
  rw [rectangleIntegral_eq_area ht hs hfg,
    rectangleIntegral_eq_area ht hs hf, rectangleIntegral_eq_area ht hs hg]
  exact integral_add (rectangle_area_integrable hf) (rectangle_area_integrable hg)

variable {U : Set Coord}

theorem rectangleIntegral_partial_t_zero
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 0 f) = 0 := by
  have hinner (s : ℝ) (hs' : s ∈ Icc sb st) :
      (∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun t => coordPartial 0 f (boxPoint t s)) (uIcc tl tr) := by
      rw [uIcc_of_le ht]
      exact (partial_contDiffOn hf hU 0).continuousOn.comp
        (by unfold boxPoint; fun_prop) (fun t ht' => hbox (boxPoint_mem ht' hs'))
    have hderiv (t : ℝ) (ht' : t ∈ uIcc tl tr) :
        HasDerivAt (fun x => f (boxPoint x s)) (coordPartial 0 f (boxPoint t s)) t := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem
        (by simpa only [uIcc_of_le ht] using ht') hs')
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt t (boxPoint_hasDerivAt_t t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge s hs').1, (hedge s hs').2, sub_self] at he
    exact he
  unfold rectangleIntegral
  calc
    (∫ s in sb..st, ∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) =
        ∫ _ in sb..st, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs'
      exact hinner s (by simpa only [uIcc_of_le hs] using hs')
    _ = 0 := intervalIntegral.integral_zero

end SmoothLocal.Weighted

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

namespace CoordinateBound

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
open Set
open scoped ContDiff

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted

def hyperbolicOperator (P S v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (coordPartial 1 v) p -
    P p * coordPartial 0 (coordPartial 1 v) p -
    S p * coordPartial 0 (coordPartial 0 v) p

variable {P S bTheta bXi v R : Coord → ℝ} {U : Set Coord} {p : Coord}

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem statePoint_segment {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) (sigma : ℝ) :
    statePoint (stateSegment w0 w1 sigma) = statePoint w0 := by
  have h0 : w0 0 = w1 0 := congrFun hp 0
  have h1 : w0 1 = w1 1 := congrFun hp 1
  ext i
  fin_cases i <;> simp [statePoint, stateSegment, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ← h0, ← h1] <;> ring

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

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem rectangleIntegral_neg (tl tr sb st : ℝ) (g : Coord → ℝ) :
    rectangleIntegral tl tr sb st (fun p => -g p) = -rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_neg]

variable {tl tr sb st : ℝ}

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
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

variable {tl tr sb st : ℝ}

theorem rectangleIntegral_sub {F G : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => F p - G p) =
      rectangleIntegral tl tr sb st F - rectangleIntegral tl tr sb st G := by
  simp only [sub_eq_add_neg]
  have hneg : ContinuousOn (fun p => -G p) (closedRectangle tl tr sb st) := hG.neg
  rw [rectangleIntegral_add ht hs hF hneg, rectangleIntegral_neg]

end SmoothLocal.Weighted

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

theorem solvedDarbouxQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    coordPartial 1 (coordPartial 1 z) p =
      solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  have hsolve : covHessian g z p 1 1 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 0 0 := by
    apply (eq_div_iff hxx).2
    nlinarith [hdet]
  change coordPartial 1 (coordPartial 1 z) p -
    jetConnection g p 1 1 (fun i => coordPartial i z p) = _ at hsolve
  rw [solvedDarbouxQ, jetNumerator, jetMixed_at_height, jetXX_at_height,
    jetEnergy_at_height hg hp z]
  linarith [hsolve]

theorem darbouxDet_of_solvedQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : coordPartial 1 (coordPartial 1 z) p =
      solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p)) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p := by
  rw [solvedDarbouxQ, jetNumerator, jetMixed_at_height, jetXX_at_height,
    jetEnergy_at_height hg hp z] at hQ
  have hsolve : covHessian g z p 1 1 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 0 0 := by
    change coordPartial 1 (coordPartial 1 z) p -
      jetConnection g p 1 1 (fun i => coordPartial i z p) = _
    linarith [hQ]
  have hmul := (eq_div_iff hxx).1 hsolve
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    nlinarith [hmul]
  simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hdet

theorem darbouxDet_iff_solvedQ_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 1 (coordPartial 1 z) p =
        solvedDarbouxQ g p (coordPartial 0 (coordPartial 1 z) p)
          (coordPartial 0 (coordPartial 0 z) p) (fun i => coordPartial i z p) :=
  ⟨solvedDarbouxQ_at_height hg hU hz hp hxx,
    darbouxDet_of_solvedQ_at_height hg hU hz hp hxx⟩

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

universe u
namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def compactParameterIntegral (H : Coord × ℝ → F) (p : Coord) : F :=
  ∫ s in Icc (0 : ℝ) 1, H (p,s)

def compactParameterPartial (H : Coord × ℝ → F) (q : Coord × ℝ) : Coord →L[ℝ] F :=
  (fderiv ℝ H q).comp (ContinuousLinearMap.inl ℝ Coord ℝ)

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem parameter_slice_continuousOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D)
    {p : Coord} (hp : p ∈ U) : ContinuousOn (fun s => H (p,s)) (Icc (0 : ℝ) 1) :=
  hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => hUD ⟨hp,hs⟩)

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem exists_local_parameter_norm_bound
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) :
    ∃ e B : ℝ, 0 < e ∧ 0 ≤ B ∧ Metric.ball p e ⊆ U ∧
      ∀ x ∈ Metric.ball p e, ∀ s ∈ Icc (0 : ℝ) 1, ‖H (x,s)‖ ≤ B := by
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let K := Metric.closedBall p (e/2) ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall p (e/2)).prod isCompact_Icc
  have hKD : K ⊆ D := by
    intro q hq
    exact hUD ⟨hball (Metric.closedBall_subset_ball (half_lt_self he) hq.1),hq.2⟩
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (hH.mono hKD)
  refine ⟨e/2,max B 0,half_pos he,le_max_right _ _,?_,?_⟩
  · intro x hx
    exact hball ((Metric.ball_subset_ball (half_le_self he.le)) hx)
  · intro x hx s hs
    exact (hB (x,s) ⟨Metric.ball_subset_closedBall hx,hs⟩).trans (le_max_left _ _)

omit [CompleteSpace F] in
theorem compactParameterIntegral_continuousOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) : ContinuousOn (compactParameterIntegral H) U := by
  intro p hp
  obtain ⟨e,B,he,hB,hball,hbound⟩ := exists_local_parameter_norm_bound hH hU hUD hp
  have hmeas : ∀ᶠ x in 𝓝 p, AEStronglyMeasurable (fun s => H (x,s))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact ((parameter_slice_continuousOn hH hUD hx).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  have hdom : ∀ᶠ x in 𝓝 p, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ‖H (x,s)‖ ≤ B := by
    filter_upwards [Metric.ball_mem_nhds p he] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hbound x hx s hs
  have hint : Integrable (fun _ : ℝ => B) (volume.restrict (Icc (0 : ℝ) 1)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ContinuousAt (fun x => H (x,s)) p := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (hH.continuousAt (hD.mem_nhds (hUD ⟨hp,hs⟩))).comp
      (continuous_id.prodMk continuous_const).continuousAt
  exact (continuousAt_of_dominated hmeas hdom hint hpoint).continuousWithinAt

omit [CompleteSpace F] in
theorem compactParameterPartial_contDiffOn
    {H : Coord × ℝ → F} {D : Set (Coord × ℝ)} (hD : IsOpen D) (n : ℕ)
    (hH : ContDiffOn ℝ (n+1 : ℕ) H D) :
    ContDiffOn ℝ n (compactParameterPartial H) D := by
  have hd : ContDiffOn ℝ n (fderiv ℝ H) D := hH.fderiv_of_isOpen hD (by simp)
  exact hd.clm_comp contDiffOn_const

omit [CompleteSpace F] in
theorem compactParameter_slice_hasFDerivAt
    {H : Coord × ℝ → F} {D : Set (Coord × ℝ)} (hH : ContDiffOn ℝ 1 H D)
    (hD : IsOpen D) {p : Coord} {s : ℝ} (hp : (p,s) ∈ D) :
    HasFDerivAt (fun x => H (x,s)) (compactParameterPartial H (p,s)) p := by
  have hd := ((hH.contDiffAt (hD.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  have hi : HasFDerivAt (fun x : Coord => (x,s)) (ContinuousLinearMap.inl ℝ Coord ℝ) p :=
    hasFDerivAt_prodMk_left p s
  exact hd.comp p hi

omit [CompleteSpace F] in
theorem compactParameterIntegral_hasFDerivAt
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ 1 H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) :
    HasFDerivAt (compactParameterIntegral H)
      (compactParameterIntegral (compactParameterPartial H) p) p := by
  have hpart : ContinuousOn (compactParameterPartial H) D :=
    (compactParameterPartial_contDiffOn hD 0 hH).continuousOn
  obtain ⟨e,B,he,hB,hball,hbound⟩ := exists_local_parameter_norm_bound hpart hU hUD hp
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (bound := fun _ => B)
    (s := Metric.ball p e) (F' := fun x s => compactParameterPartial H (x,s))
    (Metric.ball_mem_nhds p he)
  · filter_upwards [hU.mem_nhds hp] with x hx
    exact ((parameter_slice_continuousOn hH.continuousOn hUD hx).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · exact (parameter_slice_continuousOn hH.continuousOn hUD hp).integrableOn_compact isCompact_Icc
  · exact ((parameter_slice_continuousOn hpart hUD hp).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    intro x hx
    exact hbound x hx s hs
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    intro x hx
    exact compactParameter_slice_hasFDerivAt hH hD (hUD ⟨hball hx,hs⟩)

theorem compactParameterIntegral_contDiffOn_finite (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)},
      ContDiffOn ℝ n H D → IsOpen D → IsOpen U →
      U ×ˢ Icc (0 : ℝ) 1 ⊆ D → ContDiffOn ℝ n (compactParameterIntegral H) U := by
  induction n with
  | zero =>
    intro F _ _ _ H U D hH hD hU hUD
    simpa only [Nat.cast_zero,contDiffOn_zero] using
      compactParameterIntegral_continuousOn hH.continuousOn hD hU hUD
  | succ n ih =>
    intro F _ _ _ H U D hH hD hU hUD
    have hH1 : ContDiffOn ℝ 1 H D := hH.of_le (by exact_mod_cast (show 1 ≤ n+1 by omega))
    have hd (p : Coord) (hp : p ∈ U) := compactParameterIntegral_hasFDerivAt hH1 hD hU hUD hp
    have hpart : ContDiffOn ℝ n (compactParameterPartial H) D :=
      compactParameterPartial_contDiffOn hD n hH
    have hmeanPart : ContDiffOn ℝ n (compactParameterIntegral (compactParameterPartial H)) U :=
      ih hpart hD hU hUD
    have hs : ContDiffOn ℝ ((n : ℕ∞ω)+1) (compactParameterIntegral H) U := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
      exact hmeanPart.congr (fun p hp => (hd p hp).fderiv)
    simpa only [Nat.cast_add,Nat.cast_one] using hs

theorem compactParameterIntegral_contDiffOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ ∞ H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) :
    ContDiffOn ℝ ∞ (compactParameterIntegral H) U :=
  contDiffOn_infty.mpr (fun n => compactParameterIntegral_contDiffOn_finite n
    (hH.of_le (WithTop.coe_le_coe.mpr le_top)) hD hU hUD)

end SmoothLocal.Analytic

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

theorem perturbationTensor_tsupport_subset (η : SymmetricPerturbation) :
    tsupport (perturbationTensor η) ⊆ patchBox := η.val.tsupport_subset

end SmoothLocal.Perturbation

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

theorem darbouxDet_iff_sixVariableQ {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 1 (coordPartial 1 z) p = sixVariableQ g (qSolutionJet z p) := by
  rw [sixVariableQ_explicit hg hU (by simpa only [statePoint_qSolutionJet] using hp),
    statePoint_qSolutionJet, stateGradient_qSolutionJet]
  exact darbouxDet_iff_solvedQ_at_height hg hU hz hp hxx

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateBaseCompact (S : Set Coord) (M : ℝ) : Set DarbouxState :=
  (statePoint ⁻¹' S) ∩ Icc (fun _ => -M) (fun _ => M)

theorem stateBaseCompact_isCompact {S : Set Coord} (hS : IsCompact S) (M : ℝ) :
    IsCompact (stateBaseCompact S M) :=
  isCompact_Icc.inter_left (hS.isClosed.preimage statePoint_contDiff.continuous)

theorem stateSegment_coord_bound {w0 w1 : DarbouxState} {sigma M : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1)
    (h0 : ∀ i, |w0 i| ≤ M) (h1 : ∀ i, |w1 i| ≤ M) (i : Fin 6) :
    |stateSegment w0 w1 sigma i| ≤ M := by
  change |(1 - sigma) * w0 i + sigma * w1 i| ≤ M
  calc
    _ ≤ |(1 - sigma) * w0 i| + |sigma * w1 i| := abs_add_le _ _
    _ = (1 - sigma) * |w0 i| + sigma * |w1 i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
    _ ≤ (1 - sigma) * M + sigma * M :=
      add_le_add (mul_le_mul_of_nonneg_left (h0 i) (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left (h1 i) hs.1)
    _ = M := by ring

end SmoothLocal.HighEquation

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

theorem axisBump_nonneg (a t : ℝ) : 0 ≤ axisBump a t := expNegInvGlue.nonneg _

theorem shearCoordinates_contDiff (q0 : ℝ) : ContDiff ℝ ∞ (shearCoordinates q0) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Coord => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Coord => x 1 + q0 * x 0)
    fun_prop

theorem inverseShearCoordinates_contDiff (q0 : ℝ) : ContDiff ℝ ∞ (inverseShearCoordinates q0) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Coord => x 0)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Coord => x 1 - q0 * x 0)
    fun_prop

theorem shear_inverse (q0 : ℝ) (p : Coord) :
    shearCoordinates q0 (inverseShearCoordinates q0 p) = p := by
  ext i
  fin_cases i <;> simp [shearCoordinates, inverseShearCoordinates]

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

end SmoothLocal.Pulse

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
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

@[simp] theorem inverseShearMatrix_det (q0 : ℝ) : (inverseShearMatrix q0).det = 1 := by
  simp [inverseShearMatrix,Matrix.det_fin_two]

theorem inverseShearMatrix_isUnit (q0 : ℝ) : IsUnit (inverseShearMatrix q0) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp

end SmoothLocal.Pulse

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

theorem axisBumpDerivativeBound_pos {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 < axisBumpDerivativeBound a ha k := by
  unfold axisBumpDerivativeBound
  positivity

theorem axisBump_derivative_le {a : ℝ} (ha : 0 < a) (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (axisBump a) t‖ ≤ axisBumpDerivativeBound a ha k := by
  have hc := Classical.choose_spec (axisBump_derivative_bound_exists ha k) t
  have habs := le_abs_self (Classical.choose (axisBump_derivative_bound_exists ha k))
  unfold axisBumpDerivativeBound
  linarith

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

@[simp] theorem stateSegment_zero (w0 w1 : DarbouxState) : stateSegment w0 w1 0 = w0 := by
  simp [stateSegment]

@[simp] theorem stateSegment_one (w0 w1 : DarbouxState) : stateSegment w0 w1 1 = w1 := by
  simp [stateSegment]

theorem stateSegment_hasDerivAt (w0 w1 : DarbouxState) (sigma : ℝ) :
    HasDerivAt (stateSegment w0 w1) (w1 - w0) sigma := by
  have he : (AffineMap.lineMap w0 w1 : ℝ → DarbouxState) = stateSegment w0 w1 := by
    funext t
    ext i
    simp [AffineMap.lineMap_apply_module, stateSegment]
  rw [← he]
  exact AffineMap.hasDerivAt_lineMap

theorem stateSegment_continuous (w0 w1 : DarbouxState) : Continuous (stateSegment w0 w1) :=
  continuous_iff_continuousAt.mpr (fun sigma => (stateSegment_hasDerivAt w0 w1 sigma).continuousAt)

theorem statePoint_qHeightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) :
    statePoint (qHeightJetSegment z0 z sigma p) = p := by
  rw [qHeightJetSegment, statePoint_segment (by simp only [statePoint_qSolutionJet]),
    statePoint_qSolutionJet]

end SmoothLocal.HighEquation

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
open Set
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem stateQDenominator_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateQDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 0 0)

def qCompactTube (g : MetricField) (S : Set Coord) (M c : ℝ) : Set DarbouxState :=
  stateBaseCompact S M ∩ (fun w => |stateQDenominator g w|) ⁻¹' Ici c

theorem qCompactTube_isCompact {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M c : ℝ) : IsCompact (qCompactTube g S M c) := by
  have hbase := stateBaseCompact_isCompact hS M
  have hc : ContinuousOn (fun w => |stateQDenominator g w|) (stateBaseCompact S M) :=
    (stateQDenominator_contDiffOn hg hU).continuousOn.abs.mono (fun w hw => hSU hw.1)
  have hclosed : IsClosed (qCompactTube g S M c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed isClosed_Ici
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem qCompactTube_subset_domain {g : MetricField} {U S : Set Coord}
    (hSU : S ⊆ U) (M : ℝ) {c : ℝ} (hc : 0 < c) :
    qCompactTube g S M c ⊆ darbouxQStateDomain g U := by
  intro w hw
  refine ⟨hSU hw.1.1, ?_⟩
  intro hz
  have hh : c ≤ |stateQDenominator g w| := hw.2
  rw [hz, abs_zero] at hh
  linarith

theorem qCompactTube_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) {f : DarbouxState → ℝ}
    (hf : ContDiffOn ℝ ∞ f (darbouxQStateDomain g U)) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c, ‖iteratedFDeriv ℝ k f w‖ ≤ C := by
  have hDo := darbouxQStateDomain_isOpen hg hU
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) (darbouxQStateDomain g U) := by
    apply (hf.continuousOn_iteratedFDerivWithin (WithTop.coe_le_coe.mpr le_top)
      hDo.uniqueDiffOn).congr
    intro w hw
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hDo.uniqueDiffOn
      ((hf.contDiffAt (hDo.mem_nhds hw)).of_le (WithTop.coe_le_coe.mpr le_top)) hw).symm
  exact (qCompactTube_isCompact hg hU hS hSU M c).exists_bound_of_continuousOn
    (hcont.mono (qCompactTube_subset_domain hSU M hc))

theorem qCoefficient_uniform_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (i : Fin 6) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ k (qFirstCoefficient g i) w‖ ≤ C :=
  qCompactTube_derivative_bound hg hU hS hSU M hc (qFirstCoefficient_contDiffOn hg hU i) k

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulsePairRectangle_isCompact (a delta tau : ℝ) :
    IsCompact (pulsePairRectangle a delta tau) := isCompact_Icc.prod isCompact_Icc

theorem pulsePairPoint_continuous : Continuous pulsePairPoint := by
  unfold pulsePairPoint boxPoint
  fun_prop

theorem pulsePairPoint_mem {a delta tau : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ pulsePairRectangle a delta tau) : pulsePairPoint q ∈ pulseStrip a delta tau :=
  boxPoint_mem hq.2 hq.1

theorem pulsePair_integrableOn {a delta tau : ℝ} {f : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    IntegrableOn (fun q => f (pulsePairPoint q)) (pulsePairRectangle a delta tau)
      (volume.prod volume) :=
  (hf.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).integrableOn_compact
    (pulsePairRectangle_isCompact a delta tau)

theorem pulsePair_integral_eq_rectangleIntegral {a delta tau : ℝ} {f : Coord → ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    (∫ q in pulsePairRectangle a delta tau, f (pulsePairPoint q) ∂volume.prod volume) =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau) f := by
  have htime : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hspace : -a ≤ a := by linarith
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl,
    setIntegral_prod _ (pulsePair_integrableOn hf)]
  unfold rectangleIntegral
  rw [intervalIntegral.integral_of_le htime,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta htheta
  dsimp only
  rw [intervalIntegral.integral_of_le hspace,←integral_Icc_eq_integral_Ioc]
  rfl

theorem pulseTest_continuous (a tau : ℝ) : Continuous (pulseTest a tau) :=
  (axisBump_contDiff a).continuous.mul (by fun_prop)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse

theorem compact_weight_cos_phase_step {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) (phase : ℝ) :
    (∫ x : ℝ, f x*Real.cos (tau*x+phase)) =
      -(∫ x : ℝ, deriv f x*Real.cos (tau*x+(phase-Real.pi/2)))/tau := by
  let v : ℝ → ℝ := fun x => Real.sin (tau*x+phase)/tau
  have hc : Continuous (fun x : ℝ => Real.cos (tau*x+phase)) := by fun_prop
  have hvcont : Continuous v := by dsimp only [v]; fun_prop
  have hdcont : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hdcompact : HasCompactSupport (deriv f) := hcompact.deriv
  have hfc : Integrable (fun x : ℝ => f x*Real.cos (tau*x+phase)) :=
    (hf.continuous.mul hc).integrable_of_hasCompactSupport hcompact.mul_right
  have hdfv : Integrable (fun x : ℝ => deriv f x*v x) :=
    (hdcont.mul hvcont).integrable_of_hasCompactSupport hdcompact.mul_right
  have hfv : Integrable (fun x : ℝ => f x*v x) :=
    (hf.continuous.mul hvcont).integrable_of_hasCompactSupport hcompact.mul_right
  have hv (x : ℝ) : HasDerivAt v (Real.cos (tau*x+phase)) x := by
    have h := ((Real.hasDerivAt_sin (tau*x+phase)).comp x
      (((hasDerivAt_id x).const_mul tau).add_const phase)).div_const tau
    simp only [id_eq,Function.comp_def] at h
    convert h using 1 <;> try with_reducible_and_instances rfl
    field_simp [htau.ne']
  have hibp : (∫ x : ℝ, f x*Real.cos (tau*x+phase)) = -∫ x : ℝ, deriv f x*v x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
      (fun x _ => hv x) hfc hdfv hfv
  have heq : (fun x : ℝ => deriv f x*v x) =
      fun x => (deriv f x*Real.cos (tau*x+(phase-Real.pi/2)))/tau := by
    funext x
    have hp : tau*x+(phase-Real.pi/2) = (tau*x+phase)-Real.pi/2 := by ring
    rw [hp,Real.cos_sub_pi_div_two]
    dsimp only [v]
    ring
  rw [hibp,heq,integral_div]
  ring

theorem compact_weight_cos_phase_order_le (N : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) (phase : ℝ) :
    |∫ x : ℝ, f x*Real.cos (tau*x+phase)| ≤
      (∫ x : ℝ, |iteratedDeriv N f x|)/tau^N := by
  induction N generalizing f phase with
  | zero =>
      have hi : Integrable (fun x : ℝ => |f x|) :=
        hf.continuous.abs.integrable_of_hasCompactSupport hcompact.abs
      have hnorm : ∀ x : ℝ, ‖f x*Real.cos (tau*x+phase)‖ ≤ |f x| := by
        intro x
        simp only [Real.norm_eq_abs,abs_mul]
        exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
      simpa only [iteratedDeriv_zero,pow_zero,div_one,Real.norm_eq_abs] using
        norm_integral_le_of_norm_le hi (Eventually.of_forall hnorm)
  | succ N ih =>
      have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
      have hnext := ih hdf hcompact.deriv (phase-Real.pi/2)
      rw [compact_weight_cos_phase_step hf hcompact htau phase,abs_div,abs_neg,abs_of_pos htau]
      calc
        _ ≤ ((∫ x : ℝ, |iteratedDeriv N (deriv f) x|)/tau^N)/tau :=
          div_le_div_of_nonneg_right hnext htau.le
        _ = _ := by rw [iteratedDeriv_succ',pow_succ]; field_simp [htau.ne']

theorem compact_weight_cos_order_le (N : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ (∫ x : ℝ, |iteratedDeriv N f x|)/tau^N := by
  simpa only [add_zero] using compact_weight_cos_phase_order_le N hf hcompact htau 0

theorem finite_oscillatory_weight_bound (N : ℕ) {f : ℝ → ℝ} {B tau : ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) (htau : 0 < tau)
    (hB : (∫ x : ℝ, |iteratedDeriv N f x|) ≤ B) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ B/tau^N :=
  (compact_weight_cos_order_le N hf hcompact htau).trans
    (div_le_div_of_nonneg_right hB (pow_nonneg htau.le N))

end SmoothLocal.Pulse

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

theorem metricInShearCoordinates_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (q0 : ℝ) :
    SmoothPositiveOn (metricInShearCoordinates g q0) (inverseShearCoordinates q0 ⁻¹' U) := by
  simpa only [metricInShearCoordinates, inverseShearCoordinates_eq_affine] using
    affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
      (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse

def cutoffEdgeWeight (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := axisBump a x*f x

theorem cutoffEdgeWeight_contDiff {a : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) :
    ContDiff ℝ ∞ (cutoffEdgeWeight a f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ I
  · exact (axisBump_contDiff a).contDiffAt.mul (hf.contDiffAt (hI.mem_nhds hx))
  · have hnot : x ∉ tsupport (axisBump a) := fun ht => hx (hsub (axisBump_tsupport_subset ha ht))
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hnot
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    change axisBump a y*f y = 0
    change axisBump a y = (0 : ℝ) at hy
    rw [hy,zero_mul]

theorem cutoffEdgeWeight_hasCompactSupport {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    HasCompactSupport (cutoffEdgeWeight a f) := (axisBump_hasCompactSupport ha).mul_right

theorem iteratedDeriv_tsupport_subset (N : ℕ) (f : ℝ → ℝ) :
    tsupport (iteratedDeriv N f) ⊆ tsupport f := by
  induction N with
  | zero => simp only [iteratedDeriv_zero,subset_refl]
  | succ N ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

theorem cutoffEdgeWeight_iteratedDeriv_zero_off {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ)
    (N : ℕ) {x : ℝ} (hx : x ∉ Icc (-a) a) :
    iteratedDeriv N (cutoffEdgeWeight a f) x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hx (axisBump_tsupport_subset ha (tsupport_mul_subset_left
    (iteratedDeriv_tsupport_subset N (cutoffEdgeWeight a f) hmem)))

def cutoffEdgeDerivativeBound (a : ℝ) (ha : 0 < a) (N : ℕ) (B : ℝ) : ℝ :=
  derivativeConvolution (axisBumpDerivativeBound a ha) (fun _ => B) N

theorem cutoffEdgeWeight_iteratedDeriv_bound {a B : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I)
    (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc (-a) a) :
    |iteratedDeriv N (cutoffEdgeWeight a f) x| ≤ cutoffEdgeDerivativeBound a ha N B := by
  have hχ : ContDiffAt ℝ N (axisBump a) x := (axisBump_contDiff a).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfx : ContDiffAt ℝ N f x := (hf.contDiffAt (hI.mem_nhds (hsub hx))).of_le (WithTop.coe_le_coe.mpr le_top)
  have hprod := iteratedDeriv_mul hχ hfx
  change iteratedDeriv N (cutoffEdgeWeight a f) x = _ at hprod
  rw [←Real.norm_eq_abs,hprod]
  refine (norm_sum_le _ _).trans ?_
  unfold cutoffEdgeDerivativeBound derivativeConvolution
  apply Finset.sum_le_sum
  intro index _
  have hχb : ‖iteratedDeriv index (axisBump a) x‖ ≤ axisBumpDerivativeBound a ha index := by
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact axisBump_derivative_le ha index x
  have hfb : ‖iteratedDeriv (N-index) f x‖ ≤ B := by
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hjet (N-index) (Nat.sub_le _ _) x hx
  simp only [norm_mul,Real.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hfb
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hχb (Nat.cast_nonneg _)) hB)

theorem cutoffEdgeWeight_iteratedDeriv_L1 {a B : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I)
    (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    (∫ x : ℝ, |iteratedDeriv N (cutoffEdgeWeight a f) x|) ≤
      (2*a)*cutoffEdgeDerivativeBound a ha N B := by
  have hglobal := cutoffEdgeWeight_contDiff ha hI hf hsub
  have hcont : Continuous (fun x => |iteratedDeriv N (cutoffEdgeWeight a f) x|) :=
    (hglobal.continuous_iteratedDeriv N (WithTop.coe_le_coe.mpr le_top)).abs
  have hrestrict : (∫ x in Icc (-a) a, |iteratedDeriv N (cutoffEdgeWeight a f) x|) =
      ∫ x : ℝ, |iteratedDeriv N (cutoffEdgeWeight a f) x| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [cutoffEdgeWeight_iteratedDeriv_zero_off ha f N hx,abs_zero]
  rw [←hrestrict]
  have hm := integral_mono_ae (μ := volume.restrict (Icc (-a) a)) hcont.continuousOn.integrableOn_Icc
    ((continuous_const : Continuous (fun _ : ℝ => cutoffEdgeDerivativeBound a ha N B)).continuousOn.integrableOn_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact cutoffEdgeWeight_iteratedDeriv_bound ha hB hI hf hsub N hjet hx)
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -a ≤ a),smul_eq_mul] at hm
  simpa only [sub_neg_eq_add,two_mul] using hm

theorem cutoffEdgeWeight_cos_integral_bound {a B tau : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (htau : 0 < tau)
    (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    |∫ x : ℝ, axisBump a x*f x*Real.cos (tau*x)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N :=
  finite_oscillatory_weight_bound N (cutoffEdgeWeight_contDiff ha hI hf hsub)
    (cutoffEdgeWeight_hasCompactSupport ha f) htau
    (cutoffEdgeWeight_iteratedDeriv_L1 ha hB hI hf hsub N hjet)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem sixVariableQ_fderiv_apply (g : MetricField) (w v : DarbouxState) :
    fderiv ℝ (sixVariableQ g) w v = ∑ i, qFirstCoefficient g i w * v i := by
  calc
    _ = fderiv ℝ (sixVariableQ g) w (∑ i, v i • Pi.single i 1) :=
      congrArg (fderiv ℝ (sixVariableQ g) w) (pi_eq_sum_univ' v)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, qFirstCoefficient, mul_comm]

theorem qCoefficient_segment_continuousOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContinuousOn (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) (Icc (0 : ℝ) 1) :=
  (qFirstCoefficient_contDiffOn hg hU i).continuousOn.comp
    (stateSegment_continuous w0 w1).continuousOn (fun t ht => hsegment t ht)

theorem sixVariableQ_segment_FTC {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) :
    sixVariableQ g w1 - sixVariableQ g w0 =
      ∑ i, averagedQCoefficient g w0 w1 i * (w1 i - w0 i) := by
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun sigma => sixVariableQ g (stateSegment w0 w1 sigma))
        (∑ i, qFirstCoefficient g i (stateSegment w0 w1 t) * (w1 i - w0 i)) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hQ := ((sixVariableQ_contDiffOn hg hU).contDiffAt
      ((darbouxQStateDomain_isOpen hg hU).mem_nhds (hsegment t ht'))).differentiableAt (by simp)
    have hh := hQ.hasFDerivAt.comp_hasDerivAt t (stateSegment_hasDerivAt w0 w1 t)
    change HasDerivAt (fun sigma => sixVariableQ g (stateSegment w0 w1 sigma))
      (fderiv ℝ (sixVariableQ g) (stateSegment w0 w1 t) (w1 - w0)) t at hh
    rw [sixVariableQ_fderiv_apply] at hh
    exact hh
  have hi (i : Fin 6) : IntervalIntegrable
      (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
        volume (0 : ℝ) 1 :=
    ((qCoefficient_segment_continuousOn hg hU hsegment i).mul_const _).intervalIntegrable_of_Icc zero_le_one
  have hint : IntervalIntegrable
      (fun sigma => ∑ i, qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
        volume (0 : ℝ) 1 := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
    change IntervalIntegrable
      (fun sigma => ∑ i, qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
      volume (0 : ℝ) 1 at hh
    exact hh
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [stateSegment_zero, stateSegment_one] at hFTC
  calc
    _ = ∫ sigma in (0 : ℝ)..1, ∑ i,
        qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i) := hFTC.symm
    _ = ∑ i, ∫ sigma in (0 : ℝ)..1,
        qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i) :=
      intervalIntegral.integral_finsetSum (fun i _ => hi i)
    _ = _ := by simp only [intervalIntegral.integral_mul_const, averagedQCoefficient]

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulseTest_abs_le (a tau x : ℝ) : |pulseTest a tau x| ≤ axisBump a x := by
  unfold pulseTest
  rw [abs_mul,abs_of_nonneg (axisBump_nonneg a x)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (axisBump_nonneg a x)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem pulseTest_contDiff (a tau : ℝ) : ContDiff ℝ ∞ (pulseTest a tau) :=
  (axisBump_contDiff a).mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem pulseTest_hasDerivAt (a tau x : ℝ) :
    HasDerivAt (pulseTest a tau)
      (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x)) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by simp) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := hχ.mul hc
  simp only [Function.comp_def,mul_one] at h
  convert h using 1 <;> (first | rfl | ring)

theorem pulseTest_deriv (a tau x : ℝ) :
    deriv (pulseTest a tau) x =
      deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x) :=
  (pulseTest_hasDerivAt a tau x).deriv

def pulseTestDerivativeBound (a : ℝ) (ha : 0 < a) : ℝ :=
  axisBumpDerivativeBound a ha 1+axisBumpDerivativeBound a ha 0

theorem pulseTestDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ pulseTestDerivativeBound a ha :=
  add_nonneg (axisBumpDerivativeBound_pos ha 1).le (axisBumpDerivativeBound_pos ha 0).le

theorem pulseTest_deriv_bound {a tau : ℝ} (ha : 0 < a) (ht : 1 ≤ tau) (x : ℝ) :
    |deriv (pulseTest a tau) x| ≤ pulseTestDerivativeBound a ha*tau := by
  have hA0 := (axisBumpDerivativeBound_pos ha 0).le
  have hA1 := (axisBumpDerivativeBound_pos ha 1).le
  have hχ : |axisBump a x| ≤ axisBumpDerivativeBound a ha 0 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using axisBump_derivative_le ha 0 x
  have hχ' : |deriv (axisBump a) x| ≤ axisBumpDerivativeBound a ha 1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_one,Real.norm_eq_abs]
      using axisBump_derivative_le ha 1 x
  have ht0 : 0 ≤ tau := zero_le_one.trans ht
  rw [pulseTest_deriv]
  calc
    _ ≤ |deriv (axisBump a) x*Real.cos (tau*x)|+
        |tau*axisBump a x*Real.sin (tau*x)| := abs_sub _ _
    _ ≤ axisBumpDerivativeBound a ha 1+tau*axisBumpDerivativeBound a ha 0 := by
      apply add_le_add
      · rw [abs_mul]
        simpa only [mul_one] using mul_le_mul hχ' (Real.abs_cos_le_one _) (abs_nonneg _) hA1
      · rw [abs_mul,abs_mul,abs_of_nonneg ht0]
        simpa only [mul_one] using mul_le_mul
          (mul_le_mul_of_nonneg_left hχ ht0) (Real.abs_sin_le_one _) (abs_nonneg _) (mul_nonneg ht0 hA0)
    _ ≤ _ := by
      unfold pulseTestDerivativeBound
      nlinarith [mul_le_mul_of_nonneg_left ht hA1]

theorem real_Icc_memLp_two {f : ℝ → ℝ} {l r : ℝ} (hf : ContinuousOn f (Icc l r)) :
    MemLp f 2 (volume.restrict (Icc l r)) :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Icc)).mpr
    ((hf.pow 2).integrableOn_Icc)

theorem sqrt_Icc_square_le_of_abs {f : ℝ → ℝ} {l r F : ℝ}
    (hlr : l ≤ r) (hF : 0 ≤ F) (hf : ContinuousOn f (Icc l r))
    (hbound : ∀ x ∈ Icc l r, |f x| ≤ F) :
    Real.sqrt (∫ x in Icc l r, f x^2) ≤ F*Real.sqrt (r-l) := by
  have hsq : (∫ x in Icc l r, f x^2) ≤ F^2*(r-l) := by
    have hm := integral_mono_ae (μ := volume.restrict (Icc l r)) ((hf.pow 2).integrableOn_Icc)
      ((continuous_const : Continuous (fun _ : ℝ => F^2)).continuousOn.integrableOn_Icc) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hh := (sq_le_sq₀ (abs_nonneg (f x)) hF).mpr (hbound x hx)
        simpa only [Pi.pow_apply,sq_abs] using hh)
    rw [setIntegral_const,Real.volume_real_Icc_of_le hlr,smul_eq_mul] at hm
    simpa only [Pi.pow_apply,mul_comm] using hm
  apply (Real.sqrt_le_sqrt hsq).trans_eq
  rw [Real.sqrt_mul (sq_nonneg F),Real.sqrt_sq_eq_abs,abs_of_nonneg hF]

theorem real_Icc_pairing_bound {f h : ℝ → ℝ} {l r F G : ℝ}
    (hlr : l ≤ r) (hF : 0 ≤ F) (hf : ContinuousOn f (Icc l r))
    (hh : ContinuousOn h (Icc l r)) (hbound : ∀ x ∈ Icc l r, |f x| ≤ F)
    (hL2 : Real.sqrt (∫ x in Icc l r, h x^2) ≤ G) :
    |∫ x in Icc l r, f x*h x| ≤ F*Real.sqrt (r-l)*G := by
  have hcs := integral_product_abs_le_sqrt_squares (real_Icc_memLp_two hf) (real_Icc_memLp_two hh)
  exact hcs.trans (mul_le_mul (sqrt_Icc_square_le_of_abs hlr hF hf hbound) hL2
    (Real.sqrt_nonneg _) (mul_nonneg hF (Real.sqrt_nonneg _)))

theorem pulse_strip_pairing_bound (i : Fin 2) {a delta tau F S0 G : ℝ}
    {test : ℝ → ℝ} {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hF : 0 ≤ F) (hS0 : 0 ≤ S0) (_ : 0 ≤ G)
    (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (htest : Continuous test) (htestB : ∀ x, |test x| ≤ F)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ G) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (F*S0*Real.sqrt (2*a)*G)*(2*delta/tau) := by
  have hslice (theta : ℝ) (htheta : theta ∈ Icc (-(delta/tau)) (delta/tau)) :
      |∫ x in Icc (-a) a, test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
        F*S0*Real.sqrt (2*a)*G := by
    have hmap : ∀ x ∈ Icc (-a) a, boxPoint x theta ∈ U :=
      fun x hx => hSU (boxPoint_mem hx htheta)
    have hSc : ContinuousOn (fun x => S (boxPoint x theta)) (Icc (-a) a) :=
      hS.continuousOn.comp (by unfold boxPoint; fun_prop) hmap
    have hvc : ContinuousOn (fun x => coordPartial i v (boxPoint x theta)) (Icc (-a) a) :=
      (partial_contDiffOn hv hU i).continuousOn.comp (by unfold boxPoint; fun_prop) hmap
    have hproduct : ∀ x ∈ Icc (-a) a, |test x*S (boxPoint x theta)| ≤ F*S0 := by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (htestB x) (hSB _ (boxPoint_mem hx htheta)) (abs_nonneg _) hF
    have hh := real_Icc_pairing_bound (by linarith : -a ≤ a) (mul_nonneg hF hS0)
      (htest.continuousOn.mul hSc) hvc hproduct (hL2 theta htheta)
    simpa only [Pi.mul_apply,sub_neg_eq_add,←two_mul] using hh
  have htime : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hmajor : Integrable (fun _ : ℝ => F*S0*Real.sqrt (2*a)*G)
      (volume.restrict (Icc (-(delta/tau)) (delta/tau))) :=
    (continuous_const : Continuous
      (fun _ : ℝ => F*S0*Real.sqrt (2*a)*G)).continuousOn.integrableOn_Icc
  have hpoint : ∀ᵐ theta ∂volume.restrict (Icc (-(delta/tau)) (delta/tau)),
      ‖∫ x in Icc (-a) a, test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)‖ ≤
        F*S0*Real.sqrt (2*a)*G := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with theta htheta
    simpa only [Real.norm_eq_abs] using hslice theta htheta
  have hi := norm_integral_le_of_norm_le hmajor hpoint
  rw [setIntegral_const,Real.volume_real_Icc_of_le htime,smul_eq_mul] at hi
  simp only [Real.norm_eq_abs] at hi
  apply hi.trans_eq
  ring

theorem pulse_derivative_pairing_delta_sq (i : Fin 2) {a delta tau S0 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hM : 0 ≤ M) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      deriv (pulseTest a tau) x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N := by
  have htpos : 0 < tau := zero_lt_one.trans_le ht
  have hF : 0 ≤ pulseTestDerivativeBound a ha*tau :=
    mul_nonneg (pulseTestDerivativeBound_nonneg ha) htpos.le
  have hG : 0 ≤ M*delta*tau/tau^N := by positivity
  have htest : Continuous (deriv (pulseTest a tau)) :=
    (contDiff_infty_iff_deriv.mp (pulseTest_contDiff a tau)).2.continuous
  have hh := pulse_strip_pairing_bound i ha hd htpos hF hS0 hG hU hSU hS hv htest
    (pulseTest_deriv_bound ha ht) hSB hL2
  apply hh.trans_eq
  field_simp [htpos.ne']

theorem pulse_test_pairing_extra_inv_tau (i : Fin 2) {a delta tau S0 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hM : 0 ≤ M) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      pulseTest a tau x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (2*axisBumpDerivativeBound a ha 0*S0*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos : 0 < tau := zero_lt_one.trans_le ht
  have hF := (axisBumpDerivativeBound_pos ha 0).le
  have hG : 0 ≤ M*delta*tau/tau^N := by positivity
  have htest (x : ℝ) : |pulseTest a tau x| ≤ axisBumpDerivativeBound a ha 0 := by
    have hχ : |axisBump a x| ≤ axisBumpDerivativeBound a ha 0 := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using axisBump_derivative_le ha 0 x
    exact (pulseTest_abs_le a tau x).trans ((le_abs_self _).trans hχ)
  have hh := pulse_strip_pairing_bound i ha hd htpos hF hS0 hG hU hSU hS hv
    (pulseTest_continuous a tau) htest hSB hL2
  apply hh.trans_eq
  field_simp [htpos.ne']

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulse_boxPoint_zero (x t : ℝ) : boxPoint x t 0 = x := by
  change x*1+t*0=x
  ring

theorem pulse_boxPoint_one (x t : ℝ) : boxPoint x t 1 = t := by
  change x*0+t*1=t
  ring

def pulseSpatialTest (a tau : ℝ) (p : Coord) : ℝ := pulseTest a tau (p 0)

theorem pulseSpatialTest_contDiff (a tau : ℝ) : ContDiff ℝ ∞ (pulseSpatialTest a tau) :=
  (pulseTest_contDiff a tau).comp (contDiff_apply ℝ ℝ 0)

theorem pulseSpatialTest_partial (a tau : ℝ) (p : Coord) :
    coordPartial 0 (pulseSpatialTest a tau) p = deriv (pulseTest a tau) (p 0) := by
  have hψ := ((pulseTest_contDiff a tau).differentiable (by simp) (p 0)).hasDerivAt
  have hproj : HasFDerivAt (fun q : Coord => q 0) (ContinuousLinearMap.proj 0) p :=
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ).hasFDerivAt
  have hh := hψ.comp_hasFDerivAt p hproj
  change fderiv ℝ ((pulseTest a tau) ∘ (fun q : Coord => q 0)) p (Pi.single 0 1) = _
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.proj_apply,Pi.single_eq_same,smul_eq_mul,mul_one]

theorem rectangleIntegral_eq_Icc_slices (f : Coord → ℝ) {l r b t : ℝ}
    (hlr : l ≤ r) (hbt : b ≤ t) :
    rectangleIntegral l r b t f = ∫ theta in Icc b t, ∫ x in Icc l r, f (boxPoint x theta) := by
  unfold rectangleIntegral
  rw [intervalIntegral.integral_of_le hbt,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta htheta
  dsimp only
  rw [intervalIntegral.integral_of_le hlr,←integral_Icc_eq_integral_Ioc]

theorem pulse_spatial_flux_partial (i : Fin 2) {a tau : ℝ}
    {S v : Coord → ℝ} {U : Set Coord}
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    coordPartial 0 (fun q => pulseSpatialTest a tau q*S q*coordPartial i v q) p =
      deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p+
      pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p+
      pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p := by
  have hψ := (pulseSpatialTest_contDiff a tau).differentiable (by simp) p
  have hSd := (hS.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hvid := ((partial_contDiffOn hv hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have houter := HessianCalculus.coordPartial_mul_at (hψ.mul hSd) hvid 0
  dsimp only [Pi.mul_apply] at houter
  have hinner := HessianCalculus.coordPartial_mul_at hψ hSd 0
  change coordPartial 0 (pulseSpatialTest a tau * S) p = _ at hinner
  rw [houter,hinner,pulseSpatialTest_partial]
  ring

theorem pulse_spatial_second_parts (i : Fin 2) {a delta tau : ℝ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    (hSU : pulseStrip a delta tau ⊆ U) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p) =
      -rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p)-
       rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hψ : ContDiffOn ℝ ∞ (pulseSpatialTest a tau) U := (pulseSpatialTest_contDiff a tau).contDiffOn
  have hψ' : ContDiffOn ℝ ∞ (fun p : Coord => deriv (pulseTest a tau) (p 0)) U :=
    ((contDiff_infty_iff_deriv.mp (pulseTest_contDiff a tau)).2.comp (contDiff_apply ℝ ℝ 0)).contDiffOn
  have hvi := partial_contDiffOn hv hU i
  have hflux : ContDiffOn ℝ ∞ (fun p => pulseSpatialTest a tau p*S p*coordPartial i v p) U :=
    (hψ.mul hS).mul hvi
  have hminus : axisBump a (-a) = 0 := axisBump_zero ha.le (by simp [abs_of_pos ha])
  have hplus : axisBump a a = 0 := axisBump_zero ha.le (by simp [abs_of_pos ha])
  have hedge : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      (pulseSpatialTest a tau (boxPoint (-a) theta)*S (boxPoint (-a) theta)*
        coordPartial i v (boxPoint (-a) theta)) = 0 ∧
      (pulseSpatialTest a tau (boxPoint a theta)*S (boxPoint a theta)*
        coordPartial i v (boxPoint a theta)) = 0 := by
    intro theta htheta
    simp only [pulseSpatialTest,pulseTest,pulse_boxPoint_zero,hminus,hplus,zero_mul,and_self]
  have hzero := rectangleIntegral_partial_t_zero hlr hbt hU hflux hSU hedge
  have heq := rectangleIntegral_congr hlr hbt
    (fun p hp => pulse_spatial_flux_partial i (a := a) (tau := tau) hS hv hU (hSU hp))
  rw [heq] at hzero
  have h1 := ((hψ'.mul hS).mul hvi).continuousOn.mono hSU
  have h2 := ((hψ.mul (partial_contDiffOn hS hU 0)).mul hvi).continuousOn.mono hSU
  have h3 := ((hψ.mul hS).mul (partial_contDiffOn hvi hU 0)).continuousOn.mono hSU
  rw [rectangleIntegral_add (f := fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p+
      pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p)
      (g := fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p)
      hlr hbt (h1.add h2) h3,
    rectangleIntegral_add hlr hbt h1 h2] at hzero
  linarith

theorem pulse_spatial_second_cost (i : Fin 2) {a delta tau S0 S1 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hS1 : 0 ≤ S1) (hM : 0 ≤ M)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U)
    (hSU : pulseStrip a delta tau ⊆ U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hS1B : ∀ p ∈ pulseStrip a delta tau, |coordPartial 0 S p| ≤ S1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial i v) p)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
        (2*axisBumpDerivativeBound a ha 0*S1*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  have hfirst := pulse_derivative_pairing_delta_sq i ha hd ht hS0 hM hU hSU hS hv hSB hL2
  have hsecond := pulse_test_pairing_extra_inv_tau i ha hd ht hS1 hM hU hSU
    (partial_contDiffOn hS hU 0) hv hS1B hL2
  have hfirst' : |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => deriv (pulseTest a tau) (p 0)*S p*coordPartial i v p)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simpa only [pulse_boxPoint_zero] using hfirst
  have hsecond' : |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 0 S p*coordPartial i v p)| ≤
      (2*axisBumpDerivativeBound a ha 0*S1*Real.sqrt (2*a)*M)*delta^2/tau^N := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simpa only [pulseSpatialTest,pulse_boxPoint_zero] using hsecond
  rw [pulse_spatial_second_parts i ha hd htpos hS hv hU hSU]
  exact ((abs_sub _ _).trans (add_le_add (by simpa only [abs_neg] using hfirst') hsecond'))

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem spatialJet_firstJet_eq_word (z : Coord → ℝ) (n : ℕ) (i : Fin 2) :
    spatialJet (spatialFirstJet z i) n =
      iteratedCoordPartial (List.replicate n 0 ++ [i]) z := by
  induction n with
  | zero => rfl
  | succ n hn =>
      simp only [spatialJet, List.replicate_succ, List.cons_append, iteratedCoordPartial, hn]

theorem coordinateBound_spatialFirstJet
    {z : Coord → ℝ} {V : Set Coord} {N n : ℕ} {Z : ℝ}
    (hz : CoordinateBound z V (N + 1) Z) (hn : n ≤ N) (i : Fin 2) {p : Coord} (hp : p ∈ V) :
    |spatialJet (spatialFirstJet z i) n p| ≤ Z := by
  rw [spatialJet_firstJet_eq_word]
  apply hz _ _ p hp
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulseSpatialTest_partial_time (a tau : ℝ) (p : Coord) :
    coordPartial 1 (pulseSpatialTest a tau) p = 0 := by
  have hψ := ((pulseTest_contDiff a tau).differentiable (by simp) (p 0)).hasDerivAt
  have hproj : HasFDerivAt (fun q : Coord => q 0) (ContinuousLinearMap.proj 0) p :=
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ).hasFDerivAt
  have hh := hψ.comp_hasFDerivAt p hproj
  change fderiv ℝ ((pulseTest a tau) ∘ (fun q : Coord => q 0)) p (Pi.single 1 1) = 0
  rw [hh.fderiv]
  simp [smul_apply,ContinuousLinearMap.proj_apply]

theorem rectangleIntegral_partial_time_boundary {l r b t : ℝ}
    {f : Coord → ℝ} {U : Set Coord}
    (hlr : l ≤ r) (hbt : b ≤ t) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle l r b t ⊆ U) :
    rectangleIntegral l r b t (coordPartial 1 f) =
      (∫ x in l..r, f (boxPoint x t)) - (∫ x in l..r, f (boxPoint x b)) := by
  rw [rectangleIntegral_swap hlr hbt ((partial_contDiffOn hf hU 1).continuousOn.mono hbox)]
  have hinner (x : ℝ) (hx : x ∈ Icc l r) :
      (∫ theta in b..t, coordPartial 1 f (boxPoint x theta)) =
        f (boxPoint x t)-f (boxPoint x b) := by
    have hcont : ContinuousOn (fun theta => coordPartial 1 f (boxPoint x theta)) (uIcc b t) := by
      rw [uIcc_of_le hbt]
      exact (partial_contDiffOn hf hU 1).continuousOn.comp
        (by unfold boxPoint; fun_prop) (fun theta htheta => hbox (boxPoint_mem hx htheta))
    have hderiv (theta : ℝ) (htheta : theta ∈ uIcc b t) :
        HasDerivAt (fun s => f (boxPoint x s)) (coordPartial 1 f (boxPoint x theta)) theta := by
      have hp : boxPoint x theta ∈ U := hbox (boxPoint_mem hx
        (by simpa only [uIcc_of_le hbt] using htheta))
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt theta (boxPoint_hasDerivAt_s x theta)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  have htcont : ContinuousOn (fun x => f (boxPoint x t)) (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact hf.continuousOn.comp (by unfold boxPoint; fun_prop)
      (fun x hx => hbox (boxPoint_mem hx ⟨hbt,le_rfl⟩))
  have hbcont : ContinuousOn (fun x => f (boxPoint x b)) (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact hf.continuousOn.comp (by unfold boxPoint; fun_prop)
      (fun x hx => hbox (boxPoint_mem hx ⟨le_rfl,hbt⟩))
  calc
    _ = ∫ x in l..r, (f (boxPoint x t)-f (boxPoint x b)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hinner x (by simpa only [uIcc_of_le hlr] using hx)
    _ = _ := intervalIntegral.integral_sub htcont.intervalIntegrable hbcont.intervalIntegrable

theorem pulse_temporal_flux_partial {a tau : ℝ} {v : Coord → ℝ} {U : Set Coord}
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    coordPartial 1 (fun q => pulseSpatialTest a tau q*coordPartial 1 v q) p =
      pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p := by
  have hψ := (pulseSpatialTest_contDiff a tau).differentiable (by simp) p
  have hvt := ((partial_contDiffOn hv hU 1).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [HessianCalculus.coordPartial_mul_at hψ hvt 1,pulseSpatialTest_partial_time]
  ring

theorem pulse_temporal_second_parts {a delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p) =
      (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (delta/tau))) -
        (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (-(delta/tau)))) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hflux : ContDiffOn ℝ ∞ (fun p => pulseSpatialTest a tau p*coordPartial 1 v p) U :=
    (pulseSpatialTest_contDiff a tau).contDiffOn.mul (partial_contDiffOn hv hU 1)
  have hFTC := rectangleIntegral_partial_time_boundary hlr hbt hU hflux hSU
  have heq := rectangleIntegral_congr hlr hbt
    (fun p hp => pulse_temporal_flux_partial (a := a) (tau := tau) hv hU (hSU hp))
  rw [heq] at hFTC
  simpa only [pulseSpatialTest,pulse_boxPoint_zero] using hFTC

theorem pulse_temporal_second_parts_zero_initial {a delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0) :
    rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p) =
      ∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (delta/tau)) := by
  rw [pulse_temporal_second_parts ha hd ht hv hU hSU]
  have hzero : (∫ x in (-a)..a, pulseTest a tau x*coordPartial 1 v (boxPoint x (-(delta/tau)))) = 0 := by
    calc
      _ = ∫ _x in (-a)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [hinitial x (by simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hx),mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  rw [hzero,sub_zero]

end SmoothLocal.Pulse

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

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem spatialStrip_isOpen {I : Set ℝ} (hI : IsOpen I) : IsOpen (spatialStrip I) :=
  hI.preimage (continuous_apply 0)

end SmoothLocal.Taylor

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
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem initialPoint_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (fun x => (![x, a] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const

end SmoothLocal.Taylor

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
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.HighEquation

end SmoothLocal.Geometry

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

theorem boundedClassSpeed_pos {kappa : ℝ} (hkappa : 0 < kappa) {M : ℕ} (hM : 0 < M) :
    0 < boundedClassSpeed kappa M :=
  mul_pos (Real.sqrt_pos.mpr (div_pos hkappa (by norm_num)))
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hM) _)

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem real_near_closed_interval {a b e x : ℝ} (hab : a ≤ b)
    (he : 0 < e) (hx : x ∈ Ioo (a-e) (b+e)) :
    ∃ y ∈ Icc a b, |x-y| < e := by
  by_cases hxa : x < a
  · refine ⟨a,⟨le_rfl,hab⟩,?_⟩
    rw [abs_of_neg (sub_neg.mpr hxa)]
    linarith [hx.1]
  by_cases hbx : b < x
  · refine ⟨b,⟨hab,le_rfl⟩,?_⟩
    rw [abs_of_pos (sub_pos.mpr hbx)]
    linarith [hx.2]
  exact ⟨x,⟨le_of_not_gt hxa,le_of_not_gt hbx⟩,by simpa using he⟩

theorem closedRectangle_compact (l r a b : ℝ) : IsCompact (closedRectangle l r a b) := by
  have he : closedRectangle l r a b = Icc (![l,a] : Coord) ![r,b] := by
    ext p
    constructor
    · intro hp
      constructor
      · intro i
        fin_cases i
        · exact hp.1.1
        · exact hp.2.1
      · intro i
        fin_cases i
        · exact hp.1.2
        · exact hp.2.2
    · intro hp
      exact ⟨⟨hp.1 0,hp.2 0⟩,⟨hp.1 1,hp.2 1⟩⟩
  rw [he]
  exact isCompact_Icc

theorem exists_containing_coordinateRectangle {U : Set Coord} (hU : IsOpen U)
    {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b)
    (hbox : closedRectangle (-R) R a b ⊆ U) :
    ∃ radius lo hi : ℝ, R < radius ∧ lo < a ∧ b < hi ∧
      coordinateRectangle radius lo hi ⊆ U := by
  obtain ⟨e,he,hthick⟩ := (closedRectangle_compact (-R) R a b).exists_thickening_subset_open hU hbox
  refine ⟨R+e,a-e,b+e,by linarith,by linarith,by linarith,?_⟩
  intro p hp
  obtain ⟨x,hx,hxe⟩ := real_near_closed_interval (show -R ≤ R by linarith) he
    (show p 0 ∈ Ioo (-R-e) (R+e) by
      exact ⟨by linarith [hp.1.1],hp.1.2⟩)
  obtain ⟨t,ht,hte⟩ := real_near_closed_interval hab he hp.2
  apply hthick
  rw [Metric.mem_thickening_iff]
  refine ⟨![x,t],⟨hx,ht⟩,?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_lt_iff he).mpr
  intro i
  fin_cases i
  · change ‖p 0-x‖ < e
    simpa only [Real.norm_eq_abs] using hxe
  · change ‖p 1-t‖ < e
    simpa only [Real.norm_eq_abs] using hte

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation

theorem boundedClassShearHxxFloor_pos {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    0 < (boundedClassSpeed kappa M) ^ 2 / (2 * (M : ℝ)) :=
  div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Weighted

theorem heightCauchyVelocity_contDiffOn {z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (a : ℝ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U) :
    ContDiffOn ℝ ∞ (heightCauchyVelocity z a) I :=
  (partial_contDiffOn hz hU 1).comp (initialPoint_contDiff a).contDiffOn hcut

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem qSolutionJet_norm_bound_of_words {z : Coord → ℝ} {p : Coord} {R Z : ℝ}
    (hR : 0 ≤ R) (hpB : ‖p‖ ≤ R)
    (hjet : ∀ ds : List (Fin 2), ds.length ≤ 2 → |iteratedCoordPartial ds z p| ≤ Z) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  have hcoord (i : Fin 2) : |p i| ≤ R := (norm_le_pi_norm p i).trans hpB
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  fin_cases i
  · exact (hcoord 0).trans (le_max_left _ _)
  · exact (hcoord 1).trans (le_max_left _ _)
  · exact (hjet [0] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [1] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [0, 1] (by norm_num)).trans (le_max_right _ _)
  · exact (hjet [0, 0] (by norm_num)).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Taylor
open SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem actual_comparison_mean_identity
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (P z : Coord → ℝ) (p : Coord)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) :
    sixVariableQ g (qSolutionJet z p)-sixVariableQ g (qSolutionJet P p) =
      comparisonCoefficient g P z 2 p*(coordPartial 0 z p-coordPartial 0 P p)+
      comparisonCoefficient g P z 3 p*(coordPartial 1 z p-coordPartial 1 P p)+
      comparisonCoefficient g P z 4 p*(coordPartial 0 (coordPartial 1 z) p-
        coordPartial 0 (coordPartial 1 P) p)+
      comparisonCoefficient g P z 5 p*(coordPartial 0 (coordPartial 0 z) p-
        coordPartial 0 (coordPartial 0 P) p) := by
  have hh := sixVariableQ_segment_FTC hg hU hseg
  convert hh using 1 <;> try with_reducible_and_instances rfl
  simp [comparisonCoefficient,Fin.sum_univ_succ,qSolutionJet]
  ring

theorem comparison_equation_from_darboux
    {g g0 : MetricField} {U : Set Coord} {P z : Coord → ℝ}
    (hg : SmoothPositiveOn g U) (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p)
    (hxx : covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g0 U) :
    hyperbolicOperator (comparisonCoefficient g0 P z 4) (comparisonCoefficient g0 P z 5)
      (comparisonDifference P z) p =
        comparisonCoefficient g0 P z 3 p*coordPartial 1 (comparisonDifference P z) p+
        comparisonCoefficient g0 P z 2 p*coordPartial 0 (comparisonDifference P z) p+
        (sixVariableQ g (qSolutionJet z p)-sixVariableQ g0 (qSolutionJet z p)-qResidual g0 P p) := by
  have hQ := (darbouxDet_iff_sixVariableQ hg hU hz hp hxx).mp hD
  have hmean := actual_comparison_mean_identity hg0 hU P z p hseg
  have hsub (ds : List (Fin 2)) := CoordinateBound.iterated_sub hz hP hU ds hp
  have h0 : coordPartial 0 (comparisonDifference P z) p = coordPartial 0 z p-coordPartial 0 P p := hsub [0]
  have h1 : coordPartial 1 (comparisonDifference P z) p = coordPartial 1 z p-coordPartial 1 P p := hsub [1]
  have h00 : coordPartial 0 (coordPartial 0 (comparisonDifference P z)) p =
      coordPartial 0 (coordPartial 0 z) p-coordPartial 0 (coordPartial 0 P) p := hsub [0,0]
  have h01 : coordPartial 0 (coordPartial 1 (comparisonDifference P z)) p =
      coordPartial 0 (coordPartial 1 z) p-coordPartial 0 (coordPartial 1 P) p := hsub [0,1]
  have h11 : coordPartial 1 (coordPartial 1 (comparisonDifference P z)) p =
      coordPartial 1 (coordPartial 1 z) p-coordPartial 1 (coordPartial 1 P) p := hsub [1,1]
  unfold hyperbolicOperator qResidual
  rw [h0,h1,h00,h01,h11,hQ]
  linarith

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

theorem coordPartial_qSolutionJet_norm_bound
    {z : Coord → ℝ} {U S : Set Coord} {Z : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hSU : S ⊆ U)
    (hzB : CoordinateBound z S 3 Z) {p : Coord} (hp : p ∈ S) (j : Fin 2) :
    ‖coordPartial j (qSolutionJet z) p‖ ≤ max 1 Z := by
  have hJ : DifferentiableAt ℝ (qSolutionJet z) p :=
    ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds (hSU hp))).differentiableAt (by simp)
  have he (i : Fin 6) : coordPartial j (qSolutionJet z) p i =
      coordPartial j (fun r => qSolutionJet z r i) p := by
    unfold coordPartial
    rw [fderiv_apply hJ i]
    rfl
  apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans (le_max_left _ _))).mpr
  intro i
  rw [he, Real.norm_eq_abs]
  fin_cases i
  · change |coordPartial j (fun r : Coord => r 0) p| ≤ max 1 Z
    rw [DarbouxJetCalculus.coordPartial_eval]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_left _ _)
  · change |coordPartial j (fun r : Coord => r 1) p| ≤ max 1 Z
    rw [DarbouxJetCalculus.coordPartial_eval]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_left _ _)
  · change |iteratedCoordPartial [j, 0] z p| ≤ max 1 Z
    exact (hzB [j, 0] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 1] z p| ≤ max 1 Z
    exact (hzB [j, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 0, 1] z p| ≤ max 1 Z
    exact (hzB [j, 0, 1] (by norm_num) p hp).trans (le_max_right _ _)
  · change |iteratedCoordPartial [j, 0, 0] z p| ≤ max 1 Z
    exact (hzB [j, 0, 0] (by norm_num) p hp).trans (le_max_right _ _)

end SmoothLocal.HighEquation

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

theorem exists_capInductionFlow
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hh : CapInductionHeight (g0+eta) U Z c e0 z)
    (hk : 0 < kappa) (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (W : Set Coord) (Y : ℝ → ℝ → ℝ), CapInductionFlow (g0+eta) U G Z d c e0 kappa z Y W := by
  obtain ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hrange,hdisp50,hdisp,himages,hcap⟩ :=
    exists_C8_one_flow_physical_cap_estimates hg hU hSU hh.smooth hG hZ hd hc he0 hgB hh.lowJet
      hdet hh.denominator hh.energy hh.quotient hh.darboux hk hbackground hsupport hcentral
  refine ⟨V, Y, hV, hSV, hVU, hq, hqB, hY, hYs, hstart, hode, hrange, hdisp, ?_⟩
  intro m bStar r
  exact ((hcap m).2 r.left r.right r.bottom r.top ((r.top+bStar)/2) r.left_gt r.right_lt r.bottom_gt
    r.horizontal r.vertical (by linarith [r.top_lt]) (by linarith [r.top_lt,r.ceiling_le])).2

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def comparisonStateMap (P z : Coord → ℝ) (q : Coord × ℝ) : DarbouxState :=
  qHeightJetSegment P z q.2 q.1

def comparisonIntegrand (g : MetricField) (P z : Coord → ℝ) (i : Fin 6)
    (q : Coord × ℝ) : ℝ := qFirstCoefficient g i (comparisonStateMap P z q)

def comparisonParameterDomain (g : MetricField) (P z : Coord → ℝ) (U : Set Coord) :
    Set (Coord × ℝ) :=
  (U ×ˢ (univ : Set ℝ)) ∩ comparisonStateMap P z ⁻¹' darbouxQStateDomain g U

theorem comparisonStateMap_contDiffOn {P z : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (comparisonStateMap P z) (U ×ˢ (univ : Set ℝ)) := by
  have h0 : ContDiffOn ℝ ∞ (fun q : Coord × ℝ => qSolutionJet P q.1)
      (U ×ˢ (univ : Set ℝ)) := (qSolutionJet_contDiffOn hU hP).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)
  have h1 : ContDiffOn ℝ ∞ (fun q : Coord × ℝ => qSolutionJet z q.1)
      (U ×ˢ (univ : Set ℝ)) := (qSolutionJet_contDiffOn hU hz).comp contDiff_fst.contDiffOn
    (fun _ hq => hq.1)
  exact ((contDiffOn_const.sub contDiff_snd.contDiffOn).smul h0).add
    (contDiff_snd.contDiffOn.smul h1)

theorem comparisonParameterDomain_isOpen {g : MetricField} {P z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) :
    IsOpen (comparisonParameterDomain g P z U) :=
  (comparisonStateMap_contDiffOn hU hP hz).continuousOn.isOpen_inter_preimage
    (hU.prod isOpen_univ) (darbouxQStateDomain_isOpen hg hU)

theorem comparisonIntegrand_contDiffOn {g : MetricField} {P z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (comparisonIntegrand g P z i) (comparisonParameterDomain g P z U) :=
  (qFirstCoefficient_contDiffOn hg hU i).comp
    ((comparisonStateMap_contDiffOn hU hP hz).mono inter_subset_left) (fun _ hq => hq.2)

theorem comparisonCoefficient_eq_parameterIntegral (g : MetricField) (P z : Coord → ℝ)
    (i : Fin 6) :
    comparisonCoefficient g P z i = compactParameterIntegral (comparisonIntegrand g P z i) := by
  funext p
  change (∫ sigma in (0 : ℝ)..1, _) = ∫ sigma in Icc (0 : ℝ) 1, _
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rfl

theorem comparisonCoefficient_contDiffOn {g : MetricField} {P z : Coord → ℝ}
    {U W : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hW : IsOpen W) (hWU : W ⊆ U)
    (hsegment : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (comparisonCoefficient g P z i) W := by
  rw [comparisonCoefficient_eq_parameterIntegral]
  apply compactParameterIntegral_contDiffOn (comparisonIntegrand_contDiffOn hg hU hP hz i)
    (comparisonParameterDomain_isOpen hg hU hP hz) hW
  intro q hq
  exact ⟨⟨hWU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩

theorem exists_comparison_coefficient_neighborhood
    {g : MetricField} {P z : Coord → ℝ} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (hsegment : ∀ p ∈ S, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) :
    ∃ W : Set Coord, IsOpen W ∧ S ⊆ W ∧ W ⊆ U ∧
      (∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
        qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) ∧
      ∀ i : Fin 6, ContDiffOn ℝ ∞ (comparisonCoefficient g P z i) W := by
  have hprod : S ×ˢ Icc (0 : ℝ) 1 ⊆ comparisonParameterDomain g P z U := by
    intro q hq
    exact ⟨⟨hSU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩
  obtain ⟨W,J,hW,_,hSW,hIJ,hWJ⟩ := generalized_tube_lemma hS isCompact_Icc
    (comparisonParameterDomain_isOpen hg hU hP hz) hprod
  have hWU : W ⊆ U := by
    intro p hp
    have hj : (0 : ℝ) ∈ J := hIJ (by norm_num)
    exact (hWJ (show (p, (0 : ℝ)) ∈ W ×ˢ J from ⟨hp,hj⟩)).1.1
  have hseg : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U := by
    intro p hp sigma hs
    exact (hWJ (show (p, sigma) ∈ W ×ˢ J from ⟨hp,hIJ hs⟩)).2
  exact ⟨W,hW,hSW,hWU,hseg,fun i => comparisonCoefficient_contDiffOn hg hU hP hz hW hWU hseg i⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Taylor

theorem pulse_test_interval_eq_global {a : ℝ} (ha : 0 < a) (tau : ℝ) (f : ℝ → ℝ) :
    (∫ x in (-a)..a, pulseTest a tau x*f x) =
      ∫ x : ℝ, axisBump a x*f x*Real.cos (tau*x) := by
  rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),←integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ x in Icc (-a) a, axisBump a x*f x*Real.cos (tau*x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro _ _
      unfold pulseTest
      ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : axisBump a x = 0 := by
        by_contra hn
        have hs := abs_lt.mp (axisBump_support_bound ha hn)
        exact hx ⟨hs.1.le,hs.2.le⟩
      simp only [hz,zero_mul]

theorem pulse_test_interval_finite_bound {a B tau : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (htau : 0 < tau)
    (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    |∫ x in (-a)..a, pulseTest a tau x*f x| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N := by
  rw [pulse_test_interval_eq_global ha]
  exact cutoffEdgeWeight_cos_integral_bound ha hB htau hI hf hsub N hjet

theorem pulse_boxPoint_eq (x t : ℝ) : boxPoint x t = (![x,t] : Coord) := by
  ext i
  fin_cases i
  · change boxPoint x t 0=x
    exact pulse_boxPoint_zero x t
  · change boxPoint x t 1=t
    exact pulse_boxPoint_one x t

theorem pulse_temporal_moment_finite_bound {a B delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hd : 0 ≤ delta) (htau : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hI : IsOpen I) (hsub : Icc (-a) a ⊆ I)
    (hupper : ∀ x ∈ I, (![x,delta/tau] : Coord) ∈ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0)
    (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity v (delta/tau)) x‖ ≤ B) :
    |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N := by
  rw [pulse_temporal_second_parts_zero_initial ha hd htau hv hU hSU hinitial]
  have hf := heightCauchyVelocity_contDiffOn hv hU (delta/tau) hupper
  have hb := pulse_test_interval_finite_bound ha hB htau hI hf hsub N hjet
  simpa only [heightCauchyVelocity,pulse_boxPoint_eq] using hb

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

theorem compactParameterIntegral_coordPartial
    {H : Coord × ℝ → ℝ} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ ∞ H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) (j : Fin 2) :
    coordPartial j (compactParameterIntegral H) p =
      ∫ sigma in Icc (0 : ℝ) 1, compactParameterPartial H (p,sigma) (Pi.single j 1) := by
  have hH1 : ContDiffOn ℝ 1 H D := hH.of_le (by simp)
  have hd := compactParameterIntegral_hasFDerivAt hH1 hD hU hUD hp
  have hpart : ContinuousOn (compactParameterPartial H) D :=
    (compactParameterPartial_contDiffOn hD 0 hH1).continuousOn
  have hint : Integrable (fun sigma => compactParameterPartial H (p,sigma))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (parameter_slice_continuousOn hpart hUD hp).integrableOn_compact isCompact_Icc
  change fderiv ℝ (compactParameterIntegral H) p (Pi.single j 1) = _
  rw [hd.fderiv]
  exact ContinuousLinearMap.integral_apply hint (Pi.single j 1)

end SmoothLocal.Analytic

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem comparisonIntegrand_parameter_partial
    {g : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} {sigma : ℝ} (hp : p ∈ U)
    (hsegment : qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U)
    (i : Fin 6) (j : Fin 2) :
    compactParameterPartial (comparisonIntegrand g P z i) (p,sigma) (Pi.single j 1) =
      fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
        ((1-sigma) • coordPartial j (qSolutionJet P) p +
          sigma • coordPartial j (qSolutionJet z) p) := by
  have hJP := ((qSolutionJet_contDiffOn hU hP).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hJz := ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hQ := ((qFirstCoefficient_contDiffOn hg hU i).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hsegment)).differentiableAt (by simp)
  have hstate : HasFDerivAt (fun x => qHeightJetSegment P z sigma x)
      ((1-sigma) • fderiv ℝ (qSolutionJet P) p + sigma • fderiv ℝ (qSolutionJet z) p) p :=
    (hJP.hasFDerivAt.const_smul (1-sigma)).add (hJz.hasFDerivAt.const_smul sigma)
  have hchain := hQ.hasFDerivAt.comp p hstate
  have hparam := compactParameter_slice_hasFDerivAt
    ((comparisonIntegrand_contDiffOn hg hU hP hz i).of_le (by simp))
    (comparisonParameterDomain_isOpen hg hU hP hz)
    (show (p,sigma) ∈ comparisonParameterDomain g P z U from
      ⟨⟨hp,mem_univ _⟩,hsegment⟩)
  have he := hparam.unique hchain
  simpa only [ContinuousLinearMap.comp_apply,add_apply,
    smul_apply,coordPartial] using
      congrArg (fun A : Coord →L[ℝ] ℝ => A (Pi.single j 1)) he

theorem comparisonCoefficient_partial
    {g : MetricField} {P z : Coord → ℝ} {U W : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hW : IsOpen W) (hWU : W ⊆ U)
    (hsegment : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U)
    {p : Coord} (hp : p ∈ W) (i : Fin 6) (j : Fin 2) :
    coordPartial j (comparisonCoefficient g P z i) p =
      ∫ sigma in (0 : ℝ)..1,
        fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
          ((1-sigma) • coordPartial j (qSolutionJet P) p +
            sigma • coordPartial j (qSolutionJet z) p) := by
  rw [comparisonCoefficient_eq_parameterIntegral]
  have hUD : W ×ˢ Icc (0 : ℝ) 1 ⊆ comparisonParameterDomain g P z U := by
    intro q hq
    exact ⟨⟨hWU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩
  rw [compactParameterIntegral_coordPartial (comparisonIntegrand_contDiffOn hg hU hP hz i)
    (comparisonParameterDomain_isOpen hg hU hP hz) hW hUD hp j,
    intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro sigma hs
  exact comparisonIntegrand_parameter_partial hg hU hP hz (hWU hp) (hsegment p hp sigma hs) i j

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor
open SmoothLocal.HighEquation

def testedOperatorSource (R S b c v : Coord → ℝ) (p : Coord) : ℝ :=
  hyperbolicOperator R S v p-b p*coordPartial 1 v p-c p*coordPartial 0 v p

theorem testedOperatorSource_contDiffOn {R S b c v : Coord → ℝ} {U : Set Coord}
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (testedOperatorSource R S b c v) U :=
  ((((partial_contDiffOn (partial_contDiffOn hv hU 1) hU 1).sub
    (hR.mul (partial_contDiffOn (partial_contDiffOn hv hU 1) hU 0))).sub
    (hS.mul (partial_contDiffOn (partial_contDiffOn hv hU 0) hU 0))).sub
    (hb.mul (partial_contDiffOn hv hU 1))).sub (hc.mul (partial_contDiffOn hv hU 0))

theorem pulseWeightedMoment_eq_tested_rectangle {a delta tau : ℝ} {f : Coord → ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau f =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau) (fun p => pulseSpatialTest a tau p*f p) := by
  have hh := pulsePair_integral_eq_rectangleIntegral ha.le hd ht
    ((pulseSpatialTest_contDiff a tau).continuous.continuousOn.mul hf)
  simp only [Pi.mul_def] at hh
  have he : (fun q : ℝ × ℝ => pulseSpatialTest a tau (pulsePairPoint q)*f (pulsePairPoint q)) =
      (fun q => f (pulsePairPoint q)*pulseTest a tau q.2) := by
    funext q
    simp only [pulseSpatialTest,pulsePairPoint,pulse_boxPoint_zero,mul_comm]
  rw [he] at hh
  exact hh

theorem testedOperatorSource_moment_identity {a delta tau : ℝ}
    {R S b c v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U) :
    pulseWeightedMoment a delta tau (testedOperatorSource R S b c v) =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*b p*coordPartial 1 v p)-
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*c p*coordPartial 0 v p) := by
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hψ : ContinuousOn (pulseSpatialTest a tau) (pulseStrip a delta tau) :=
    (pulseSpatialTest_contDiff a tau).continuous.continuousOn
  have hvi (i : Fin 2) := (partial_contDiffOn hv hU i).continuousOn.mono hSU
  have hvij (i j : Fin 2) := (partial_contDiffOn (partial_contDiffOn hv hU j) hU i).continuousOn.mono hSU
  have h0 := hψ.mul (hvij 1 1)
  have h1 := (hψ.mul (hR.continuousOn.mono hSU)).mul (hvij 0 1)
  have h2 := (hψ.mul (hS.continuousOn.mono hSU)).mul (hvij 0 0)
  have h3 := (hψ.mul (hb.continuousOn.mono hSU)).mul (hvi 1)
  have h4 := (hψ.mul (hc.continuousOn.mono hSU)).mul (hvi 0)
  rw [pulseWeightedMoment_eq_tested_rectangle ha hd ht
    ((testedOperatorSource_contDiffOn hR hS hb hc hv hU).continuousOn.mono hSU)]
  have heq : (fun p => pulseSpatialTest a tau p*testedOperatorSource R S b c v p) =
      fun p => (((pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p-
        pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)-
        pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)-
        pulseSpatialTest a tau p*b p*coordPartial 1 v p)-
        pulseSpatialTest a tau p*c p*coordPartial 0 v p := by
    funext p
    unfold testedOperatorSource hyperbolicOperator
    ring
  have hs4 := rectangleIntegral_sub hlr hbt (((h0.sub h1).sub h2).sub h3) h4
  have hs3 := rectangleIntegral_sub hlr hbt ((h0.sub h1).sub h2) h3
  have hs2 := rectangleIntegral_sub hlr hbt (h0.sub h1) h2
  have hs1 := rectangleIntegral_sub hlr hbt h0 h1
  simp only [Pi.mul_def,Pi.sub_def] at hs4 hs3 hs2 hs1
  rw [heq,hs4,hs3,hs2,hs1]

theorem testedOperatorSource_moment_cost {a delta tau K K1 M B : ℝ} {N : ℕ}
    {R S b c v : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hK : 0 ≤ K) (hK1 : 0 ≤ K1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hR : ContDiffOn ℝ ∞ R U) (hS : ContDiffOn ℝ ∞ S U)
    (hb : ContDiffOn ℝ ∞ b U) (hc : ContDiffOn ℝ ∞ c U)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hcoeff : ∀ p ∈ pulseStrip a delta tau, |R p| ≤ K ∧ |S p| ≤ K ∧ |b p| ≤ K ∧ |c p| ≤ K)
    (hderiv : ∀ p ∈ pulseStrip a delta tau, |coordPartial 0 R p| ≤ K1 ∧ |coordPartial 0 S p| ≤ K1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau), ∀ i : Fin 2,
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N)
    (hI : IsOpen I) (hsub : Icc (-a) a ⊆ I)
    (hupper : ∀ x ∈ I, (![x,delta/tau] : Coord) ∈ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity v (delta/tau)) x‖ ≤ B) :
    |pulseWeightedMoment a delta tau (testedOperatorSource R S b c v)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N+
      (4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
      (4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hlr : -a ≤ a := by linarith
  have hbt : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  have htime := pulse_temporal_moment_finite_bound ha hB hd htpos hv hU hSU hI hsub hupper hinitial N hjet
  have hRcost := pulse_spatial_second_cost 1 ha hd ht hK hK1 hM hR hv hU hSU
    (fun p hp => (hcoeff p hp).1) (fun p hp => (hderiv p hp).1) (fun theta ht => hL2 theta ht 1)
  have hScost := pulse_spatial_second_cost 0 ha hd ht hK hK1 hM hS hv hU hSU
    (fun p hp => (hcoeff p hp).2.1) (fun p hp => (hderiv p hp).2) (fun theta ht => hL2 theta ht 0)
  have hbcost := pulse_test_pairing_extra_inv_tau 1 ha hd ht hK hM hU hSU hb hv
    (fun p hp => (hcoeff p hp).2.2.1) (fun theta ht => hL2 theta ht 1)
  have hccost := pulse_test_pairing_extra_inv_tau 0 ha hd ht hK hM hU hSU hc hv
    (fun p hp => (hcoeff p hp).2.2.2) (fun theta ht => hL2 theta ht 0)
  have hfirst (F : Coord → ℝ) (i : Fin 2) :
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*F p*coordPartial i v p) =
      ∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
        pulseTest a tau x*F (boxPoint x theta)*coordPartial i v (boxPoint x theta) := by
    rw [rectangleIntegral_eq_Icc_slices _ hlr hbt]
    simp only [pulseSpatialTest,pulse_boxPoint_zero]
  rw [testedOperatorSource_moment_identity ha hd htpos hR hS hb hc hv hU hSU]
  rw [← hfirst b 1] at hbcost
  rw [← hfirst c 0] at hccost
  have htriangle (a0 a1 a2 a3 a4 : ℝ) :
      |(((a0-a1)-a2)-a3)-a4| ≤ (((|a0|+|a1|)+|a2|)+|a3|)+|a4| := by
    have h01 := abs_sub a0 a1
    have h02 := (abs_sub (a0-a1) a2).trans (add_le_add h01 le_rfl)
    have h03 := (abs_sub ((a0-a1)-a2) a3).trans (add_le_add h02 le_rfl)
    exact (abs_sub (((a0-a1)-a2)-a3) a4).trans (add_le_add h03 le_rfl)
  calc
    _ ≤ (((|rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)|+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*R p*coordPartial 0 (coordPartial 1 v) p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*S p*coordPartial 0 (coordPartial 0 v) p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*b p*coordPartial 1 v p)|)+
      |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
        (fun p => pulseSpatialTest a tau p*c p*coordPartial 0 v p)| := by
      exact htriangle _ _ _ _ _
    _ ≤ _ := by
      have hsum := add_le_add (add_le_add (add_le_add (add_le_add htime hRcost) hScost) hbcost) hccost
      apply hsum.trans_eq
      ring

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem comparison_segment_direction_bound
    {P z : Coord → ℝ} {U T : Set Coord} {Z0 Z sigma : ℝ}
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hTU : T ⊆ U) (hPZ : CoordinateBound P T 3 Z0) (hzZ : CoordinateBound z T 3 Z)
    {p : Coord} (hp : p ∈ T) (hs : sigma ∈ Icc (0 : ℝ) 1) (j : Fin 2) :
    ‖(1-sigma) • coordPartial j (qSolutionJet P) p +
      sigma • coordPartial j (qSolutionJet z) p‖ ≤ max 1 Z0 + max 1 Z := by
  have h0 := coordPartial_qSolutionJet_norm_bound hU hP hTU hPZ hp j
  have h1 := coordPartial_qSolutionJet_norm_bound hU hz hTU hzZ hp j
  calc
    _ ≤ ‖(1-sigma) • coordPartial j (qSolutionJet P) p‖ +
        ‖sigma • coordPartial j (qSolutionJet z) p‖ := norm_add_le _ _
    _ = (1-sigma)*‖coordPartial j (qSolutionJet P) p‖ +
        sigma*‖coordPartial j (qSolutionJet z) p‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hs.2),abs_of_nonneg hs.1]
    _ ≤ (1-sigma)*max 1 Z0 + sigma*max 1 Z :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left h1 hs.1)
    _ ≤ max 1 Z0 + max 1 Z := by
      have hn0 : 0 ≤ max 1 Z0 := zero_le_one.trans (le_max_left _ _)
      have hn1 : 0 ≤ max 1 Z := zero_le_one.trans (le_max_left _ _)
      exact add_le_add (mul_le_of_le_one_left hn0 (by linarith [hs.1]))
        (mul_le_of_le_one_left hn1 hs.2)

theorem exists_uniform_comparison_coefficient_bounds
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P z : Coord → ℝ) (V T : Set Coord),
      IsOpen V → V ⊆ U → ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V → T ⊆ S → T ⊆ V →
      (∀ p ∈ T, ‖p‖ ≤ R) → CoordinateBound P T 3 Z0 → CoordinateBound z T 3 Z →
      (∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator g (qHeightJetSegment P z sigma p)|) →
      ∀ i : Fin 6, ∀ p ∈ T,
        |comparisonCoefficient g P z i p| ≤ C ∧
        ∀ j : Fin 2, |coordPartial j (comparisonCoefficient g P z i) p| ≤
          C*(max 1 Z0+max 1 Z) := by
  classical
  let A := max R (max Z0 Z)
  choose C0 hC0 using fun i : Fin 6 => qCoefficient_uniform_derivative_bound hg hU hS hSU A hc i 0
  choose C1 hC1 using fun i : Fin 6 => qCoefficient_uniform_derivative_bound hg hU hS hSU A hc i 1
  let C := 1 + ∑ i : Fin 6, (max 0 (C0 i)+max 0 (C1 i))
  have hnon (i : Fin 6) : 0 ≤ max 0 (C0 i)+max 0 (C1 i) := by positivity
  have hCle : 1 ≤ C := by
    have hs : 0 ≤ ∑ i : Fin 6, (max 0 (C0 i)+max 0 (C1 i)) :=
      Finset.sum_nonneg (fun i _ => hnon i)
    dsimp [C]
    linarith
  have hC0le (i : Fin 6) : C0 i ≤ C := by
    have hi := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_max_right 0 (C0 i),le_max_left 0 (C1 i)]
  have hC1le (i : Fin 6) : C1 i ≤ C := by
    have hi := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_max_right 0 (C1 i),le_max_left 0 (C0 i)]
  refine ⟨C,hCle,?_⟩
  intro P z V T hV hVU hP hz hTS hTV hpB hPZ hzZ hfloor i p hp
  have hgV : SmoothPositiveOn g V := hg.mono hVU
  have h0 : ‖qSolutionJet P p‖ ≤ A :=
    (qSolutionJet_norm_bound_of_words hR (hpB p hp)
      (fun ds hds => hPZ ds (by omega) p hp)).trans
      (max_le_max le_rfl (le_max_left _ _))
  have h1 : ‖qSolutionJet z p‖ ≤ A :=
    (qSolutionJet_norm_bound_of_words hR (hpB p hp)
      (fun ds hds => hzZ ds (by omega) p hp)).trans
      (max_le_max le_rfl (le_max_right _ _))
  have htube (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P z sigma p ∈ qCompactTube g S A c := by
    refine ⟨⟨?_,?_⟩,hfloor p hp sigma hs⟩
    · change statePoint (qHeightJetSegment P z sigma p) ∈ S
      rw [statePoint_qHeightJetSegment]
      exact hTS hp
    · have hb := stateSegment_coord_bound hs
        (fun j => (norm_le_pi_norm (qSolutionJet P p) j).trans h0)
        (fun j => (norm_le_pi_norm (qSolutionJet z p) j).trans h1)
      exact ⟨fun j => (abs_le.mp (hb j)).1,fun j => (abs_le.mp (hb j)).2⟩
  have hseg (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g V := by
    have hd := qCompactTube_subset_domain hSU A hc (htube sigma hs)
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hTV hp,hd.2⟩
  have hval (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      |qFirstCoefficient g i (qHeightJetSegment P z sigma p)| ≤ C := by
    have hb := (hC0 i _ (htube sigma hs)).trans (hC0le i)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb
  have hder (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      ‖fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using (hC1 i _ (htube sigma hs)).trans (hC1le i)
  constructor
  · change ‖∫ sigma in (0 : ℝ)..1,
        qFirstCoefficient g i (qHeightJetSegment P z sigma p)‖ ≤ C
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun sigma => qFirstCoefficient g i (qHeightJetSegment P z sigma p)) (by
        intro sigma hs
        have hs0 : sigma ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
        exact hval sigma ⟨hs0.1.le,hs0.2⟩)
    simpa only [sub_zero,abs_one,mul_one] using hb
  · intro j
    obtain ⟨W,hW,hpW,hWU,hWseg,_⟩ := exists_comparison_coefficient_neighborhood
      hgV hV hP hz isCompact_singleton (singleton_subset_iff.mpr (hTV hp))
      (fun _ hq sigma hs => by simpa only [mem_singleton_iff.mp hq] using hseg sigma hs)
    rw [comparisonCoefficient_partial hgV hV hP hz hW hWU hWseg (hpW (mem_singleton p)) i j,
      ← Real.norm_eq_abs]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C*(max 1 Z0+max 1 Z)) (f := fun sigma =>
        fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
          ((1-sigma) • coordPartial j (qSolutionJet P) p+sigma • coordPartial j (qSolutionJet z) p)) ?_
    · simpa only [sub_zero,abs_one,mul_one] using hb
    intro sigma hs
    have hs' : sigma ∈ Icc (0 : ℝ) 1 := by
      have hs0 : sigma ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
      exact ⟨hs0.1.le,hs0.2⟩
    exact ((fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)).le_opNorm _).trans
      (mul_le_mul (hder sigma hs')
        (comparison_segment_direction_bound hV hP hz hTV hPZ hzZ hp hs' j)
        (norm_nonneg _) (zero_le_one.trans hCle))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow

theorem bounded_class_actual_cap_data
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z) :
    ∃ U : Set Coord, IsOpen U ∧ modelSquare ⊆ U ∧ U ⊆ V ∧
      SmoothPositiveOn g0 U ∧ SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
      CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z := by
  obtain ⟨_,hadm,hjets,hyy,hE⟩ := hclass
  obtain ⟨W,hW,hSW,hg,hz,hD,_,_,hq⟩ := hadm
  let U := W ∩ V
  have hU : IsOpen U := hW.inter hV
  have hSU : modelSquare ⊆ U := fun p hp => ⟨hSW hp,hSV hp⟩
  have hg0U : SmoothPositiveOn g0 U :=
    ⟨fun i j => (hg0.1 i j).mono inter_subset_right,
      fun p hp => hg0.2 p hp.2⟩
  have hgU : SmoothPositiveOn (perturbedMetric g0 eta.val) U :=
    ⟨fun i j => (hg.1 i j).mono inter_subset_left,
      fun p hp => hg.2 p hp.1⟩
  refine ⟨U,hU,hSU,inter_subset_right,hg0U,hgU,?_⟩
  exact ⟨hz.mono inter_subset_left,hjets,(fun p hp => (hyy p hp).1),hE,hq,hD⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem actual_comparison_tested_source {g gRef : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det=gaussianCurvature g p*heightEnergy g z p)
    (hxx : covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef U) :
    sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p =
      testedOperatorSource (comparisonCoefficient gRef P z 4) (comparisonCoefficient gRef P z 5)
        (comparisonCoefficient gRef P z 3) (comparisonCoefficient gRef P z 2) (comparisonDifference P z) p := by
  have hh := comparison_equation_from_darboux hg hgRef hU hz hP hp hD hxx hseg
  unfold testedOperatorSource
  linarith

theorem actual_comparison_source_test_cost {a delta tau K K1 M B : ℝ} {N : ℕ}
    {g gRef : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hK : 0 ≤ K) (hK1 : 0 ≤ K1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hg : SmoothPositiveOn g U) (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) (hSU : pulseStrip a delta tau ⊆ U)
    (hD : ∀ p ∈ pulseStrip a delta tau,
      (covHessian g z p).det=gaussianCurvature g p*heightEnergy g z p)
    (hxx : ∀ p ∈ pulseStrip a delta tau, covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ p ∈ pulseStrip a delta tau, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef U)
    (hcoeff : ∀ i : Fin 6, ∀ p ∈ pulseStrip a delta tau, |comparisonCoefficient gRef P z i p| ≤ K)
    (hderiv : ∀ i : Fin 6, ∀ p ∈ pulseStrip a delta tau,
      |coordPartial 0 (comparisonCoefficient gRef P z i) p| ≤ K1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau), ∀ i : Fin 2,
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i (comparisonDifference P z) (boxPoint x theta))^2) ≤
        M*delta*tau/tau^N)
    (hinitial : ∀ x ∈ Icc (-a) a,
      coordPartial 1 (comparisonDifference P z) (boxPoint x (-(delta/tau)))=0)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity (comparisonDifference P z) (delta/tau)) x‖ ≤ B) :
    |pulseWeightedMoment a delta tau
      (fun p => sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N+
      (4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
      (4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hab : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  obtain ⟨W,hW,hSW,hWU,_,hcoeffSmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRef hU hP hz (closedRectangle_compact _ _ _ _) hSU hseg
  obtain ⟨radius,lo,hi,hRad,hlo,hhi,hRect⟩ := exists_containing_coordinateRectangle hW ha hab hSW
  have hI : IsOpen (Ioo (-radius) radius) := isOpen_Ioo
  have hsub : Icc (-a) a ⊆ Ioo (-radius) radius := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hupper (x : ℝ) (hx : x ∈ Ioo (-radius) radius) : (![x,delta/tau] : Coord) ∈ W := by
    apply hRect
    exact ⟨hx,⟨hlo.trans_le hab,hhi⟩⟩
  have hv : ContDiffOn ℝ ∞ (comparisonDifference P z) W := (hz.sub hP).mono hWU
  have hcost := testedOperatorSource_moment_cost ha hd ht hK hK1 hM hB
    (hcoeffSmooth 4) (hcoeffSmooth 5) (hcoeffSmooth 3) (hcoeffSmooth 2) hv hW hSW
    (fun p hp => ⟨hcoeff 4 p hp,hcoeff 5 p hp,hcoeff 3 p hp,hcoeff 2 p hp⟩)
    (fun p hp => ⟨hderiv 4 p hp,hderiv 5 p hp⟩) hL2 hI hsub hupper hinitial hjet
  have heq : pulseWeightedMoment a delta tau
      (fun p => sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p) =
      pulseWeightedMoment a delta tau
        (testedOperatorSource (comparisonCoefficient gRef P z 4) (comparisonCoefficient gRef P z 5)
          (comparisonCoefficient gRef P z 3) (comparisonCoefficient gRef P z 2) (comparisonDifference P z)) := by
    apply setIntegral_congr_fun (pulsePairRectangle_isCompact a delta tau).measurableSet
    intro q hq
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    rw [actual_comparison_tested_source hg hgRef hU hz hP (hSU (pulsePairPoint_mem hq))
      (hD _ (pulsePairPoint_mem hq)) (hxx _ (pulsePairPoint_mem hq)) (hseg _ (pulsePairPoint_mem hq))]
  rw [heq]
  exact hcost

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
namespace SmoothLocal.Pulse

theorem pulse_moment_bounds_incompatible {m c3 delta tau E C0 C1 : ℝ} (N : ℕ)
    (hc3 : 0 < c3) (hd : 0 < delta) (ht : 0 < tau)
    (hsmall : C0*delta ≤ c3/4)
    (hedge : E ≤ (c3/4)*delta*tau)
    (hlower : C1*delta ≤ (c3/4)*tau)
    (hpositive : c3*delta*tau/tau^N ≤ |m|)
    (hcost : |m| ≤ E/tau^N+C0*delta^2*tau/tau^N+C1*delta^2/tau^N) : False := by
  have hquot : c3*delta*tau/tau^N ≤ (E+C0*delta^2*tau+C1*delta^2)/tau^N := by
    calc
      _ ≤ |m| := hpositive
      _ ≤ _ := hcost
      _ = _ := by ring
  have hnum : c3*delta*tau ≤ E+C0*delta^2*tau+C1*delta^2 :=
    (div_le_div_iff_of_pos_right (pow_pos ht N)).mp hquot
  have hscaled := mul_le_mul_of_nonneg_right hsmall (mul_pos hd ht).le
  have hlowscaled := mul_le_mul_of_nonneg_right hlower hd.le
  have hlead : 0 < c3*delta*tau := mul_pos (mul_pos hc3 hd) ht
  nlinarith

theorem exists_delta_then_frequency_for_moment_contradiction {c3 C0 : ℝ}
    (hc3 : 0 < c3) (hC0 : 0 ≤ C0) (N : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1/2 ∧
      ∀ E C1 : ℝ, ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ m : ℝ,
        c3*delta*tau/tau^N ≤ |m| →
        |m| ≤ E/tau^N+C0*delta^2*tau/tau^N+C1*delta^2/tau^N → False := by
  let delta := min (1/4) (c3/(8*(C0+1)))
  have hden : 0 < 8*(C0+1) := by positivity
  have hd : 0 < delta := lt_min (by norm_num) (div_pos hc3 hden)
  have hd1 : delta ≤ 1/4 := min_le_left _ _
  have hd2 : delta ≤ c3/(8*(C0+1)) := min_le_right _ _
  have hsmall : C0*delta ≤ c3/4 := by
    have hh := (le_div_iff₀ hden).mp hd2
    nlinarith
  refine ⟨delta,hd,by linarith,?_⟩
  intro E C1
  let T := max 1 (max (4*E/(c3*delta)) (4*C1*delta/c3))
  refine ⟨T,le_max_left _ _,?_⟩
  intro tau ht m hpositive hcost
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have heT : 4*E/(c3*delta) ≤ tau := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hlT : 4*C1*delta/c3 ≤ tau := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hedge : E ≤ (c3/4)*delta*tau := by
    have hh := (div_le_iff₀ (mul_pos hc3 hd)).mp heT
    nlinarith
  have hlower : C1*delta ≤ (c3/4)*tau := by
    have hh := (div_le_iff₀ hc3).mp hlT
    nlinarith
  exact pulse_moment_bounds_incompatible N hc3 hd htpos hsmall hedge hlower hpositive hcost

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

theorem pulse_width_eventually {r : ℝ} (hr : 0 < r) (delta : ℝ) :
    ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧ delta/(2*tau) ≤ r/4 := by
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0))
  have hw : Tendsto (fun tau : ℝ => delta/(2*tau)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm] using hi.const_mul (delta/2)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hw.eventually_lt tendsto_const_nhds (show (0 : ℝ) < r/4 by linarith)] with tau ht hwidth
  exact ⟨ht,hwidth.le⟩

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix NNReal

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.ODE
open SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem coordinatePoint_eq_vector (x t : ℝ) : coordinatePoint x t = (![x,t] : Coord) := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem cauchyVelocity_iteratedDeriv {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {x t : ℝ}
    (hp : coordinatePoint x t ∈ U) (n : ℕ) :
    iteratedDeriv n (heightCauchyVelocity z t) x =
      spatialJet (spatialFirstJet z 1) n (coordinatePoint x t) := by
  have he : heightCauchyVelocity z t = (fun y => coordPartial 1 z (coordinatePoint y t)) := by
    funext y
    rw [coordinatePoint_eq_vector]
    rfl
  rw [he, horizontalJet_slice hU (partial_contDiffOn hz hU 1) t n x hp,
    horizontalJet_eq_spatialJet]
  rfl

theorem cauchyValue_iteratedDeriv_succ {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {x t : ℝ}
    (hp : coordinatePoint x t ∈ U) (n : ℕ) :
    iteratedDeriv (n+1) (heightCauchyValue z t) x =
      spatialJet (spatialFirstJet z 0) n (coordinatePoint x t) := by
  have he : heightCauchyValue z t = (fun y => z (coordinatePoint y t)) := by
    funext y
    rw [coordinatePoint_eq_vector]
    rfl
  rw [he, horizontalJet_slice hU hz t (n+1) x hp]
  change coordPartial 0 (horizontalJet z n) (coordinatePoint x t) = _
  rw [← horizontalJet_coordPartial hU hz 0 n _ hp, horizontalJet_eq_spatialJet]
  rfl

theorem cauchy_fullJets_of_actual_spatial_firstJets
    {z : Coord → ℝ} {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {x t : ℝ} (hp : coordinatePoint x t ∈ U) {N : ℕ} {Z B : ℝ}
    (hvalue : |z (coordinatePoint x t)| ≤ Z)
    (hspatial : ∀ i : Fin 2, ∀ n ≤ N,
      |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B) :
    ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (heightCauchyValue z t) x‖ ≤ max Z B ∧
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity z t) x‖ ≤ max Z B := by
  intro n hn
  constructor
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    cases n with
    | zero =>
      change |z ![x,t]| ≤ _
      rw [← coordinatePoint_eq_vector]
      exact hvalue.trans (le_max_left _ _)
    | succ n =>
      rw [cauchyValue_iteratedDeriv_succ hz hU hp n]
      exact (hspatial 0 n (by omega)).trans (le_max_right _ _)
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      cauchyVelocity_iteratedDeriv hz hU hp n]
    exact (hspatial 1 n hn).trans (le_max_right _ _)

end SmoothLocal.Taylor

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

theorem shearedModelSquare_eq_image (q0 : ℝ) :
    shearedModelSquare q0 = shearCoordinates q0 '' modelSquare := by
  ext p
  constructor
  · intro hp
    exact ⟨inverseShearCoordinates q0 p, hp, shear_inverse q0 p⟩
  · rintro ⟨x,hx,rfl⟩
    simpa only [shearedModelSquare, mem_preimage, inverse_shear] using hx

theorem shearedModelSquare_isCompact (q0 : ℝ) : IsCompact (shearedModelSquare q0) := by
  rw [shearedModelSquare_eq_image]
  exact modelSquare_isCompact.image (shearCoordinates_contDiff q0).continuous

theorem shearedModelSquare_subset_domain {U : Set Coord} (hSU : modelSquare ⊆ U) (q0 : ℝ) :
    shearedModelSquare q0 ⊆ inverseShearCoordinates q0 ⁻¹' U := fun _ hp => hSU hp

theorem shearedModelDomain_isOpen {U : Set Coord} (hU : IsOpen U) (q0 : ℝ) :
    IsOpen (inverseShearCoordinates q0 ⁻¹' U) :=
  hU.preimage (inverseShearCoordinates_contDiff q0).continuous

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
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem bounded_class_sheared_C3_on_actual_region
    {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight g M z) (q0 : ℝ) {S : Set Coord}
    (hS : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare) :
    CoordinateBound (heightInShearCoordinates z q0) S 3 ((2*(1+|q0|))^3*(M : ℝ)) := by
  obtain ⟨_,hadm,hjet,_,_⟩ := hclass
  obtain ⟨U,hU,hSU,_,hz,_,_,_,_⟩ := hadm
  have hzB : CoordinateBound z modelSquare 3 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  have hs := SmoothLocal.Pulse.CoordinateBound.inverse_shear hzB hz hU hSU (Nat.cast_nonneg M) q0
  intro ds hds p hp
  exact hs ds hds p (hS p hp)

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation
open SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem upper_cauchy_jets_of_actual_coordinate_bound
    {P : Coord → ℝ} {radius a delta tau C : ℝ} {N : ℕ}
    (hP : ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-radius) radius)))
    (ha : a < radius) (ht : 0 ≤ delta/tau)
    (hB : CoordinateBound P (pulseStrip a delta tau) (N+1) C)
    {x : ℝ} (hx : |x| ≤ a) :
    ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (heightCauchyValue P (delta/tau)) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity P (delta/tau)) x‖ ≤ C := by
  have hp : coordinatePoint x (delta/tau) ∈ pulseStrip a delta tau := by
    have hp0 : x ∈ Icc (-a) a ∧ delta/tau ∈ Icc (-(delta/tau)) (delta/tau) :=
      ⟨abs_le.mp hx,⟨(neg_nonpos.mpr ht).trans ht,le_rfl⟩⟩
    simpa [coordinatePoint,pulseStrip,SmoothLocal.Weighted.closedRectangle] using hp0
  have hpU : coordinatePoint x (delta/tau) ∈ spatialStrip (Ioo (-radius) radius) := by
    have hxU : x ∈ Ioo (-radius) radius :=
      ⟨(neg_lt_neg ha).trans_le (abs_le.mp hx).1,(abs_le.mp hx).2.trans_lt ha⟩
    simpa [coordinatePoint,spatialStrip] using hxU
  have hval : |P (coordinatePoint x (delta/tau))| ≤ C := hB [] (by simp) _ hp
  have hjet : ∀ i : Fin 2, ∀ n ≤ N,
      |spatialJet (spatialFirstJet P i) n (coordinatePoint x (delta/tau))| ≤ C := by
    intro i n hn
    exact coordinateBound_spatialFirstJet hB hn i hp
  simpa only [max_self] using cauchy_fullJets_of_actual_spatial_firstJets
    hP (spatialStrip_isOpen isOpen_Ioo) hpU hval hjet

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_comparison_coefficient_data_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) :
    ∃ K K1 : ℝ, 1 ≤ K ∧ 0 ≤ K1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          let zs := heightInShearCoordinates z q0
          let gs := metricInShearCoordinates gStar q0
          let P := taylorApproximation gs (-delta/(tau : ℝ))
            (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
          ∀ i : Fin 6, ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            |comparisonCoefficient gs P zs i p| ≤ K ∧
            |coordPartial 0 (comparisonCoefficient gs P zs i) p| ≤ K1 := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hc : 0 < c := div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  obtain ⟨CP,_,_,_,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  obtain ⟨K,hK,hcoeff⟩ := exists_uniform_comparison_coefficient_bounds hgs hVs
    (shearedModelSquare_isCompact q0) (shearedModelSquare_subset_domain hSV q0) 1 CP Z (by norm_num) hc
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨K,K*(max 1 CP+max 1 Z),hK,by positivity,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hsegment delta hdelt hdhalf,hwidth] with tau hsegmentTau hw
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  let T := pulseStrip (L*r/2) delta (tau : ℝ)
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hcoordinates (p : Coord) (hp : p ∈ T) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans (by linarith [mul_pos hL hr]),(abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ T) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hTD : T ⊆ D := by
    intro p hp
    exact ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,
      ⟨by linarith [hp.1.1,mul_pos hL hr],by linarith [hp.1.2,mul_pos hL hr]⟩⟩
  have hpoint (p : Coord) (hp : p ∈ T) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · exact (hcoordinates p hp).2.trans (hrhalf.le.trans (by norm_num))
  have ht := hsegmentTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hP : ContDiffOn ℝ ∞ P D := ht.1.mono inter_subset_right
  have hzs : ContDiffOn ℝ ∞ zs D := (heightInShearCoordinates_contDiffOn hh.smooth q0).mono
    (fun _ hp => hp.1.1)
  have hzB : CoordinateBound zs T 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have hactual := hcoeff P zs D T hD (fun _ hp => hp.1.2) hP hzs
    (fun p hp => hpS p hp) hTD hpoint ht.2.1 hzB (fun p hp sigma hs => (ht.2.2 p hp sigma hs).1)
  dsimp only
  intro i p hp
  exact ⟨(hactual i p hp).1,(hactual i p hp).2 0⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Taylor

theorem comparison_upper_velocity_jet_bound {P z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hU : IsOpen U) (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (b : ℝ) (hupper : ∀ x ∈ I, (![x,b] : Coord) ∈ U) {x : ℝ} (hx : x ∈ I)
    (N : ℕ) {BZ BP : ℝ}
    (hZB : ‖iteratedFDeriv ℝ N (heightCauchyVelocity z b) x‖ ≤ BZ)
    (hPB : ‖iteratedFDeriv ℝ N (heightCauchyVelocity P b) x‖ ≤ BP) :
    ‖iteratedFDeriv ℝ N (heightCauchyVelocity (comparisonDifference P z) b) x‖ ≤ BZ+BP := by
  have hzv := heightCauchyVelocity_contDiffOn hz hU b hupper
  have hPv := heightCauchyVelocity_contDiffOn hP hU b hupper
  have heq : heightCauchyVelocity (comparisonDifference P z) b =ᶠ[𝓝 x]
      (heightCauchyVelocity z b-heightCauchyVelocity P b) := by
    filter_upwards [hI.mem_nhds hx] with y hy
    exact CoordinateBound.iterated_sub hz hP hU [1] (hupper y hy)
  rw [(heq.iteratedFDeriv ℝ N).self_of_nhds,iteratedFDeriv_sub_apply
    ((hzv.contDiffAt (hI.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hPv.contDiffAt (hI.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_sub_le _ _).trans (add_le_add hZB hPB)

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor SmoothLocal.Model

theorem exists_original_pulse_exclusion
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      ∀ N : ℕ, 10 < N → ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1/2 ∧
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            ¬ (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) := by
  obtain ⟨G,d,r,hG,hd,hr,hrhalf,hGstar,hdstar,hlow,hLr,hrsmall,hcuts,hcomparison⟩ :=
    exists_original_class_comparison_with_low_data hg0 hgStar hV hSV M hkappa hM hq0 hbackground
  have hGstar2 : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G :=
    fun i j k hk p hp => hGstar i j k (by omega) p hp
  let L := boundedClassWidth kappa M
  let a := L*r/16
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hLrpos : 0 < L*r := mul_pos hL hr
  have ha : 0 < a := div_pos hLrpos (by norm_num)
  have haHalf : a ≤ L*r/2 := by dsimp only [a]; linarith
  have haI : a < L*r := by dsimp only [a]; linarith
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hxxfloor : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM)) (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  refine ⟨r,hr,hrhalf,hLr,?_⟩
  intro N hN
  obtain ⟨C,Csource,Cgradient,c3,_hC,_hCsource,hCgradient,hc3,hPfinite,hcomparisonN⟩ := hcomparison N hN
  obtain ⟨K,K1,hK,hK1,hcoefficients⟩ := exists_actual_comparison_coefficient_data_at_radius
    hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0 hr hrhalf hLr hrsmall N (by omega)
  obtain ⟨CPseg,Aseg,_hCPseg,_hAseg,hsegments⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0 hr hrhalf hLr hrsmall N (by omega)
  obtain ⟨BZ,hBZ,hZcuts⟩ := hcuts N
  obtain ⟨BP,hBP,hPjets⟩ := hPfinite (N+1)
  let E := (2*a)*cutoffEdgeDerivativeBound a ha N (BZ+BP)
  let C0 := 4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*Cgradient
  let C1 := 4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*Cgradient
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pulseTestDerivativeBound_nonneg ha)) hK0) (Real.sqrt_nonneg _)) hCgradient
  obtain ⟨delta,hdelt,hdhalf,hcontradict⟩ := exists_delta_then_frequency_for_moment_contradiction hc3 hC0 N
  obtain ⟨T,_hT,hcontradictT⟩ := hcontradict E C1
  refine ⟨delta,hdelt,hdhalf,?_⟩
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hcomparisonN delta hdelt hdhalf,hlow a ha N hN delta,
    hZcuts N hN delta hdelt,hPjets delta hdelt hdhalf,hcoefficients delta hdelt hdhalf,
    hsegments delta hdelt hdhalf,hlarge,hwidth]
    with tau hcomparisonTau hlowTau hZcutsTau hPjetsTau hcoeffTau hsegmentsTau ht hw
  intro eta z hclass hcenter happ
  let g := perturbedMetric g0 eta.val
  obtain ⟨U,hU,hSU,hUV,_hg0U,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  obtain ⟨hg8,hdet⟩ := hlowTau g U hgU hU hSU happ
  have hg4 : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G := fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p=modelCurvature kappa p := fun p hp => hbackground p (hUV hp)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hminv hminv hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  let zs := heightInShearCoordinates z q0
  let gs := metricInShearCoordinates gStar q0
  let gt := metricInShearCoordinates g q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := Us ∩ spatialStrip I
  let S := pulseStrip a delta (tau : ℝ)
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := hUs.inter (spatialStrip_isOpen isOpen_Ioo)
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have htime0 : 0 ≤ delta/(tau : ℝ) := div_nonneg hdelt.le htpos.le
  have hpointEq (x t : ℝ) : boxPoint x t = (![x,t] : Coord) := pulse_boxPoint_eq x t
  have hsubset : S ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,hp.2⟩
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans haI.le,(abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG.le hd hkappa hr.le hLr hq0 hrsmall hg4 hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hSD : S ⊆ D := by
    intro p hp
    exact ⟨hSU (hpS p hp),⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩⟩
  have hgStarU : SmoothPositiveOn gStar U :=
    ⟨fun i j => (hgStar.1 i j).mono hUV,fun p hp => hgStar.2 p (hUV hp)⟩
  have hgsUs := metricInShearCoordinates_smoothPositive hgStarU q0
  have hgtUs := metricInShearCoordinates_smoothPositive hgU q0
  have hgsD : SmoothPositiveOn gs D :=
    ⟨fun i j => (hgsUs.1 i j).mono inter_subset_left,fun p hp => hgsUs.2 p hp.1⟩
  have hgtD : SmoothPositiveOn gt D :=
    ⟨fun i j => (hgtUs.1 i j).mono inter_subset_left,fun p hp => hgtUs.2 p hp.1⟩
  have hzsUs := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD : ContDiffOn ℝ ∞ zs D := hzsUs.mono inter_subset_left
  obtain ⟨hP,hCauchy,_hdegree,_hres,_hresc,_hresm,_hsource,hgradient,_hsourcec,hpositive⟩ :=
    hcomparisonTau eta z hclass hcenter happ
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hcoeff := hcoeffTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ
  have hsegments := (hsegmentsTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ).2.2
  have hseg (p : Coord) (hp : p ∈ S) (sigma : ℝ) (hsigma : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P zs sigma p ∈ darbouxQStateDomain gs D := by
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hSD hp,
      abs_pos.mp (hxxfloor.trans_le (hsegments p (hsubset hp) sigma hsigma).1)⟩
  have hcut (x : ℝ) (hx : x ∈ I) (t : ℝ) (ht : |t| ≤ r) : (![x,t] : Coord) ∈ D := by
    refine ⟨hSU ?_,hx⟩
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,ht⟩
  have hinitial (x : ℝ) (hx : x ∈ Icc (-a) a) :
      coordPartial 1 (comparisonDifference P zs) (boxPoint x (-(delta/(tau : ℝ))))=0 := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have ht0 : |-(delta/(tau : ℝ))| ≤ r := by rw [abs_neg,abs_of_nonneg htime0]; exact hbr
    have hpD : boxPoint x (-(delta/(tau : ℝ))) ∈ D := by rw [hpointEq]; exact hcut x hxI _ ht0
    have hs := CoordinateBound.iterated_sub hzsD hPD hD [1] hpD
    change coordPartial 1 (comparisonDifference P zs) (boxPoint x (-(delta/(tau : ℝ)))) =
      coordPartial 1 zs (boxPoint x (-(delta/(tau : ℝ))))-
        coordPartial 1 P (boxPoint x (-(delta/(tau : ℝ)))) at hs
    have he := (hCauchy x hxI).2
    change coordPartial 1 P ![x,-delta/(tau : ℝ)] =
      coordPartial 1 zs ![x,-delta/(tau : ℝ)] at he
    rw [neg_div] at he
    rw [hpointEq,he,sub_self] at hs
    simpa only [hpointEq] using hs
  have hPjetsActual := hPjetsTau eta z hclass hcenter happ
  have hZcutsActual := hZcutsTau eta z hclass hcenter happ
  have hedge (n : ℕ) (hn : n ≤ N) (x : ℝ) (hx : x ∈ Icc (-a) a) :
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity (comparisonDifference P zs) (delta/(tau : ℝ))) x‖ ≤ BZ+BP := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hxhalf : |x| ≤ L*r/2 := (abs_le.mpr hx).trans haHalf
    have hPcut := upper_cauchy_jets_of_actual_coordinate_bound hPjetsActual.1
      (show L*r/2<L*r by linarith) htime0 hPjetsActual.2.2 hxhalf n hn
    have hzcut := (hZcutsActual x hxhalf n hn).2.2
    apply comparison_upper_velocity_jet_bound hD isOpen_Ioo hPD hzsD (delta/(tau : ℝ))
      (fun y hy => hcut y hy _ (by rw [abs_of_nonneg htime0]; exact hbr)) hxI n hzcut hPcut.2
  have hcost := actual_comparison_source_test_cost ha hdelt.le hw.1 hK0 hK1 hCgradient
    (add_nonneg hBZ hBP) hgtD hgsD hD hzsD hPD hSD
    (fun p hp => (hgeom p hp).2.2.2.2.2.1)
    (fun p hp => abs_pos.mp ((boundedClassShearHxxFloor_pos hkappa hM).trans_le (hgeom p hp).2.1))
    hseg (fun i p hp => (hcoeff i p (hsubset hp)).1)
    (fun i p hp => (hcoeff i p (hsubset hp)).2) hgradient hinitial hedge
  change |pulseWeightedMoment a delta (tau : ℝ) (actualComparisonSource gStar g z q0 P)| ≤
    E/(tau : ℝ)^N+C0*delta^2*(tau : ℝ)/(tau : ℝ)^N+C1*delta^2/(tau : ℝ)^N at hcost
  exact hcontradictT (tau : ℝ) ht
    (pulseWeightedMoment a delta (tau : ℝ) (actualComparisonSource gStar g z q0 P)) hpositive hcost

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.exists_original_pulse_exclusion := @OAI.SmoothLocal.Perturbation.exists_original_pulse_exclusion
