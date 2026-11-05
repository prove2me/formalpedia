-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.exists_original_class_comparison_with_low_data
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:22:48.855+00:00
-- url     : https://prove2.me/submissions/ec164d8e-8296-4ee2-bba6-45c10d94dda0

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Pulse_exists_actual_Q_moment_lower_with_remainder
import Theorems.Thm_OAI_SmoothLocal_Flow_exists_C8_one_flow_physical_cap_estimates
import Theorems.Thm_OAI_SmoothLocal_Perturbation_actual_central_sheared_solution_margins
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_bounded_patch_cauchy_bound
import Theorems.Thm_OAI_SmoothLocal_Pulse_exists_actual_finite_lower_cut_bound_at_radius
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_taylor_finite_jets_at_radius
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_upper_off_pulse_cauchy_bounds_at_radius
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_reference_segment_at_radius
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_uniform_comparison_gradient

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
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

namespace DarbouxJetCalculus

end DarbouxJetCalculus

theorem jetEnergy_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (z : Coord → ℝ) :
    jetEnergy g p (fun i => coordPartial i z p) = heightEnergy g z p := by
  symm
  exact heightEnergy_polynomial z hg hp

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem forcingCoefficient_eq_energy {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U) :
    forcingCoefficient g z p =
      heightEnergy g z p / (2 * (g p).det * covHessian g z p 0 0) := by
  unfold forcingCoefficient heightEnergy
  have hd := metricDet_ne_zero hg hp
  by_cases hh : covHessian g z p 0 0 = 0
  · simp [hh]
  · field_simp [hd, hh]

theorem forcingCoefficient_abs_eq {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    (hE : 0 ≤ heightEnergy g z p) :
    |forcingCoefficient g z p| =
      heightEnergy g z p / (2 * (g p).det * |covHessian g z p 0 0|) := by
  rw [forcingCoefficient_eq_energy hg z hp, abs_div, abs_of_nonneg hE]
  simp only [abs_mul, abs_of_pos (hg.2 p hp).det_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem forcingCoefficient_bounds {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    {e E d D c C : ℝ} (he : 0 < e) (hd : 0 < d) (hc : 0 < c)
    (hE : e ≤ heightEnergy g z p) (hEup : heightEnergy g z p ≤ E)
    (hdet : d ≤ (g p).det) (hdetup : (g p).det ≤ D)
    (hxx : c ≤ |covHessian g z p 0 0|) (hxxup : |covHessian g z p 0 0| ≤ C) :
    0 < e / (2 * D * C) ∧
      e / (2 * D * C) ≤ |forcingCoefficient g z p| ∧
      |forcingCoefficient g z p| ≤ E / (2 * d * c) := by
  have hDp : 0 < D := hd.trans_le (hdet.trans hdetup)
  have hCp : 0 < C := hc.trans_le (hxx.trans hxxup)
  have hgdet : 0 < (g p).det := hd.trans_le hdet
  have hgxx : 0 < |covHessian g z p 0 0| := hc.trans_le hxx
  have hden : 0 < 2 * (g p).det * |covHessian g z p 0 0| := by positivity
  have hdenlo : 2 * d * c ≤ 2 * (g p).det * |covHessian g z p 0 0| :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdet (by norm_num)) hxx hc.le
      (by positivity)
  have hdenup : 2 * (g p).det * |covHessian g z p 0 0| ≤ 2 * D * C :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdetup (by norm_num)) hxxup hgxx.le
      (by positivity)
  rw [forcingCoefficient_abs_eq hg hp (he.le.trans hE)]
  refine ⟨by positivity, ?_, ?_⟩
  · exact div_le_div₀ (he.le.trans hE) hE hden hdenup
  · exact div_le_div₀ (he.le.trans (hE.trans hEup)) hEup (by positivity) hdenlo

end SmoothLocal.Pulse

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

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

variable {U : Set Coord}

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

end AffineCalculus

theorem det_affinePullbackMetric (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) :
    (affinePullbackMetric g b R q).det =
      R.det ^ 2 * (g (affineCoordinates b R q)).det := by
  simp only [affinePullbackMetric, Matrix.det_mul, Matrix.det_transpose]
  ring

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
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def lowerChristoffelDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (d k i j : Fin 2) : ℝ :=
  (1/2 : ℝ) * ∑ l, inverseDerivativeJet G D d k l * (D i j l+D j i l-D l i j)

def curvatureLowerJet (G : MetricMatrix) (D : MetricFirstJet) : ℝ :=
  ∑ l, G 0 l * (lowerChristoffelDerivativeJet G D 0 l 1 1 -
    lowerChristoffelDerivativeJet G D 1 l 0 1 +
    ∑ m, (christoffelJet G D m 1 1 * christoffelJet G D l 0 m -
      christoffelJet G D m 0 1 * christoffelJet G D l 1 m))

def curvatureLowerTerm (g : MetricField) (p : Coord) : ℝ :=
  curvatureLowerJet (g p) (metricFirstJet g p)

theorem metric_inverse_first_row_contraction (G : MetricMatrix) (hdet : G.det ≠ 0)
    (T : Fin 2 → ℝ) :
    (∑ l, G 0 l * ∑ a, G⁻¹ l a * T a) = T 0 := by
  have hi := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet)
  have h0 := congrFun (congrFun hi 0) 0
  have h1 := congrFun (congrFun hi 0) 1
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,ite_true,
    show (0 : Fin 2) ≠ 1 by decide,ite_false] at h0 h1
  calc
    _ = (G 0 0*G⁻¹ 0 0+G 0 1*G⁻¹ 1 0)*T 0 +
        (G 0 0*G⁻¹ 0 1+G 0 1*G⁻¹ 1 1)*T 1 := by
      simp only [Fin.sum_univ_two]
      ring
    _ = T 0 := by rw [h0,h1]; ring

theorem curvatureJet_density_raw (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (hdet : G.det ≠ 0) :
    curvatureJet G D DD * G.det =
      (1/2 : ℝ)*(DD 0 1 1 0+DD 0 1 1 0-DD 0 0 1 1-
        DD 1 0 1 0-DD 1 1 0 0+DD 1 0 0 1) + curvatureLowerJet G D := by
  let T : Fin 2 → ℝ := fun a => DD 0 1 1 a+DD 0 1 1 a-DD 0 a 1 1-
    DD 1 0 1 a-DD 1 1 0 a+DD 1 a 0 1
  have hc := metric_inverse_first_row_contraction G hdet T
  simp only [T,Fin.sum_univ_two] at hc
  rw [curvatureJet,div_mul_cancel₀ _ hdet]
  simp only [riemannJet,christoffelDerivativeJet,curvatureLowerJet,
    lowerChristoffelDerivativeJet,Fin.sum_univ_two]
  linear_combination (1/2 : ℝ)*hc

theorem metric_coeff_second_partial_symm {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => g q i j)) p =
      coordPartial d (coordPartial e (fun q => g q j i)) p := by
  have he : coordPartial e (fun q => g q i j) =ᶠ[𝓝 p]
      coordPartial e (fun q => g q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_coeff_partial_symm hg hU hq e i j
  exact coordPartial_eq_of_eventuallyEq he d

theorem gaussianCurvature_density_principal_part {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature g p * (g p).det =
      coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p -
        (coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p +
          coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p)/2 +
        curvatureLowerTerm g p := by
  have hraw := curvatureJet_density_raw (g p) (metricFirstJet g p)
    (fun (d e i j : Fin 2) => coordPartial d (coordPartial e (fun q => g q i j)) p)
    (metricDet_ne_zero hg hp)
  have hfull := (congrArg (fun k : ℝ => k * (g p).det)
    (gaussianCurvature_eq_curvatureJet hg hU hp)).trans hraw
  rw [metric_coeff_second_partial_symm hg hU hp 0 1 1 0,
    metric_coeff_second_partial_symm hg hU hp 1 0 1 0,
    coordPartial_comm (hg.1 0 1) hU hp 1 0] at hfull
  rw [hfull]
  dsimp only [curvatureLowerTerm,metricFirstJet]
  ring

section SmoothLowerJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Set E} {G : E → MetricMatrix} {D : E → MetricFirstJet}

theorem metricMatrix_inverse_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => (G s)⁻¹ i j) S := by
  have hd : ContDiffOn ℝ ∞ (fun s => (G s).det) S := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have ha : ContDiffOn ℝ ∞ (fun s => (G s).adjugate i j) S := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · simpa [Matrix.adjugate_fin_two] using (hG 0 1).neg
    · simpa [Matrix.adjugate_fin_two] using (hG 1 0).neg
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  simpa [Matrix.inv_def,Ring.inverse_eq_inv,smul_eq_mul] using (hd.inv hdet).mul ha

theorem inverseDerivativeJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (d i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => inverseDerivativeJet (G s) (D s) d i j) S := by
  have hi := metricMatrix_inverse_contDiffOn hG hdet
  have ht (a b : Fin 2) :
      ContDiffOn ℝ ∞ (fun s => (G s)⁻¹ i a * D s d a b * (G s)⁻¹ b j) S :=
    ((hi i a).mul (hD d a b)).mul (hi b j)
  simpa only [inverseDerivativeJet,Fin.sum_univ_two] using
    (((ht 0 0).add (ht 0 1)).add ((ht 1 0).add (ht 1 1))).neg

theorem christoffelJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (k i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => christoffelJet (G s) (D s) k i j) S := by
  have hi := metricMatrix_inverse_contDiffOn hG hdet
  have ht (l : Fin 2) : ContDiffOn ℝ ∞
      (fun s => (G s)⁻¹ k l * (D s i j l+D s j i l-D s l i j)) S :=
    (hi k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [christoffelJet,Fin.sum_univ_two] using
    (contDiffOn_const (c := (1/2 : ℝ))).mul ((ht 0).add (ht 1))

theorem lowerChristoffelDerivativeJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (d k i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => lowerChristoffelDerivativeJet (G s) (D s) d k i j) S := by
  have hi := inverseDerivativeJet_contDiffOn hG hD hdet
  have ht (l : Fin 2) : ContDiffOn ℝ ∞
      (fun s => inverseDerivativeJet (G s) (D s) d k l *
        (D s i j l+D s j i l-D s l i j)) S :=
    (hi d k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [lowerChristoffelDerivativeJet,Fin.sum_univ_two] using
    (contDiffOn_const (c := (1/2 : ℝ))).mul ((ht 0).add (ht 1))

theorem curvatureLowerJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun s => curvatureLowerJet (G s) (D s)) S := by
  have hΓ := christoffelJet_contDiffOn hG hD hdet
  have hΓD := lowerChristoffelDerivativeJet_contDiffOn hG hD hdet
  have ht (l m : Fin 2) : ContDiffOn ℝ ∞ (fun s =>
      christoffelJet (G s) (D s) m 1 1 * christoffelJet (G s) (D s) l 0 m -
        christoffelJet (G s) (D s) m 0 1 * christoffelJet (G s) (D s) l 1 m) S :=
    ((hΓ m 1 1).mul (hΓ l 0 m)).sub ((hΓ m 0 1).mul (hΓ l 1 m))
  have hl (l : Fin 2) : ContDiffOn ℝ ∞ (fun s => G s 0 l *
      (lowerChristoffelDerivativeJet (G s) (D s) 0 l 1 1 -
        lowerChristoffelDerivativeJet (G s) (D s) 1 l 0 1 +
        ∑ m, (christoffelJet (G s) (D s) m 1 1 * christoffelJet (G s) (D s) l 0 m -
          christoffelJet (G s) (D s) m 0 1 * christoffelJet (G s) (D s) l 1 m))) S := by
    simpa only [Fin.sum_univ_two] using
      (hG 0 l).mul (((hΓD 0 l 1 1).sub (hΓD 1 l 0 1)).add ((ht l 0).add (ht l 1)))
  simpa only [curvatureLowerJet,Fin.sum_univ_two] using (hl 0).add (hl 1)

end SmoothLowerJet

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

end Smoothness
end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

def forcingFloor (e D C : ℝ) : ℝ := e/(2*max D 1*max C 1)

theorem forcingCoefficient_floor_of_reference_margins
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    {e c D C : ℝ} (he : 0 < e) (hc : 0 < c)
    (hE : e ≤ heightEnergy g z p) (hdet : (g p).det ≤ D)
    (hxx : c ≤ |covHessian g z p 0 0|) (hxxup : |covHessian g z p 0 0| ≤ C) :
    forcingFloor e D C ≤ |forcingCoefficient g z p| := by
  exact (forcingCoefficient_bounds hg hp he (hg.2 p hp).det_pos hc hE le_rfl le_rfl
    (hdet.trans (le_max_left _ _)) hxx (hxxup.trans (le_max_left _ _))).2.1

end SmoothLocal.Pulse

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
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

theorem jetConnection_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (i j : Fin 2) (u : Coord) :
    jetConnection (swappedMetric g) p i j (coordinateSwap u) =
      jetConnection g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) u := by
  simp only [jetConnection, christoffel_swappedMetric hg hU hp,
    coordinateSwap_apply, Fin.sum_univ_two, swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

theorem jetYY_swappedMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : coordinateSwap p ∈ U) (c : ℝ) (u : Coord) :
    jetYY (swappedMetric g) p c (coordinateSwap u) =
      jetXX g (coordinateSwap p) c u := by
  rw [jetYY, jetConnection_swappedMetric hg hU hp]
  rfl

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
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

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

theorem axisBump_pos {a t : ℝ} (ha : 0 < a) (ht : |t| < a) : 0 < axisBump a t := by
  have hs : |t| ^ 2 < a ^ 2 := (sq_lt_sq₀ (abs_nonneg t) ha.le).mpr ht
  exact expNegInvGlue.pos_of_pos (sub_pos.mpr (by simpa only [sq_abs] using hs))

theorem axisBump_pos_zero {a : ℝ} (ha : 0 < a) : 0 < axisBump a 0 :=
  axisBump_pos ha (by simpa using ha)

theorem axisBump_integral_pos {a : ℝ} (ha : 0 < a) : 0 < ∫ t : ℝ, axisBump a t :=
  (axisBump_contDiff a).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (axisBump_hasCompactSupport ha) (axisBump_nonneg a) (axisBump_pos_zero ha).ne'

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

theorem pulseScalar_contDiff (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulseScalar a N delta tau) := by
  unfold pulseScalar temporalCutoff
  exact ((contDiff_const.mul ((axisBump_contDiff a).comp (contDiff_apply ℝ ℝ 0))).mul
    ((axisBump_contDiff (1 / 2)).comp
      ((contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const delta))).mul
    (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0)))

theorem pulseTensor_contDiff (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulseTensor q0 a N delta tau) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (((pulseScalar_contDiff a N delta tau).comp (shearCoordinates_contDiff q0)).mul
    contDiff_const).mul contDiff_const

theorem pulseTensor_symmetric (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) (i j : Fin 2) :
    pulseTensor q0 a N delta tau p i j = pulseTensor q0 a N delta tau p j i := by
  unfold pulseTensor
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

theorem pulseTensor_inverseShear (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    affinePullbackMetric (pulseTensor q0 a N delta tau) 0 (inverseShearMatrix q0) p =
      !![0, 0; 0, pulseScalar a N delta tau p] := by
  rw [affinePullbackMetric, ← inverseShearCoordinates_eq_affine]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pulseTensor, shear_inverse, inverseShearMatrix, thetaCovector,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem testMetric_inverseShear (gStar : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) (p : Coord) :
    affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 (inverseShearMatrix q0) p =
      affinePullbackMetric gStar 0 (inverseShearMatrix q0) p +
        !![0, 0; 0, pulseScalar a N delta tau p] := by
  rw [← pulseTensor_inverseShear q0 a N delta tau p]
  simp only [affinePullbackMetric, testMetric, Pi.add_apply, mul_add, add_mul]

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def metricCoefficientCLM (i j : Fin 2) : MetricMatrix →L[ℝ] ℝ where
  toFun A := A i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  cont := (continuous_apply j).comp (continuous_apply i)

section JointMetric
variable {g0 : MetricField} {U : Set Coord}
variable (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
variable {η : SymmetricPerturbation} {p : Coord} (hp : p ∈ U)
include hg0 hU hp

end JointMetric

end SmoothLocal.Perturbation

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

def thetaPulseMetric (g : MetricField) (f : Coord → ℝ) : MetricField :=
  fun p => g p + !![0,0;0,f p]

def thetaPulseFirstJet (f : Coord → ℝ) (p : Coord) : MetricFirstJet :=
  fun d i j => if i=1 ∧ j=1 then coordPartial d f p else 0

theorem thetaPulseMetric_entry (g : MetricField) (f : Coord → ℝ) (p : Coord) (i j : Fin 2) :
    thetaPulseMetric g f p i j = g p i j + if i=1 ∧ j=1 then f p else 0 := by
  fin_cases i <;> fin_cases j <;> simp [thetaPulseMetric]

theorem metricFirstJet_thetaPulseMetric {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    metricFirstJet (thetaPulseMetric g f) p = metricFirstJet g p + thetaPulseFirstJet f p := by
  funext d i j
  have hgD : DifferentiableAt ℝ (fun q => g q i j) p :=
    ((hg.1 i j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hfD : DifferentiableAt ℝ f p :=
    (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  by_cases hij : i=1 ∧ j=1
  · have he : (fun q => thetaPulseMetric g f q i j) = (fun q => g q i j+f q) := by
      funext q
      simp only [thetaPulseMetric_entry,ite_eq_left hij]
    change coordPartial d (fun q => thetaPulseMetric g f q i j) p = _
    rw [he,HessianCalculus.coordPartial_add_at hgD hfD d]
    simp only [Pi.add_apply,Matrix.add_apply,metricFirstJet,thetaPulseFirstJet,ite_eq_left hij]
  · have he : (fun q => thetaPulseMetric g f q i j) = (fun q => g q i j) := by
      funext q
      simp only [thetaPulseMetric_entry,ite_eq_right hij,add_zero]
    change coordPartial d (fun q => thetaPulseMetric g f q i j) p = _
    rw [he]
    simp only [Pi.add_apply,Matrix.add_apply,metricFirstJet,thetaPulseFirstJet,ite_eq_right hij,add_zero]

@[simp] theorem inverseShearMatrix_det (q0 : ℝ) : (inverseShearMatrix q0).det = 1 := by
  simp [inverseShearMatrix,Matrix.det_fin_two]

theorem inverseShearMatrix_isUnit (q0 : ℝ) : IsUnit (inverseShearMatrix q0) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp

theorem metricInShearCoordinates_test (gStar : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) :
    metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0 =
      thetaPulseMetric (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) := by
  funext p
  exact testMetric_inverseShear gStar q0 a N delta tau p

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

def metricQuadraticValue (G : MetricMatrix) (v : Coord) : ℝ := v ⬝ᵥ (G *ᵥ v)

theorem metricQuadraticValue_continuousAt {T : Type*} [TopologicalSpace T]
    {G : T → MetricMatrix} {v : T → Coord} {t : T}
    (hG : ∀ i j, ContinuousAt (fun a => G a i j) t)
    (hv : ∀ i, ContinuousAt (fun a => v a i) t) :
    ContinuousAt (fun a => metricQuadraticValue (G a) (v a)) t := by
  simp only [metricQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fun_prop

theorem posDef_of_positive_on_sphere {G : MetricMatrix} (hG : G.IsHermitian)
    (hQ : ∀ v ∈ Metric.sphere (0 : Coord) 1, 0 < metricQuadraticValue G v) : G.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hG
  intro v hv
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w : Coord := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : Coord) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right]
    simp [w, norm_smul, hn]
  have heq : metricQuadraticValue G w = (‖v‖⁻¹)^2 * metricQuadraticValue G v := by
    simp only [metricQuadraticValue, w, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    ring
  have hmul : 0 < (‖v‖⁻¹)^2 * metricQuadraticValue G v := by
    rw [← heq]
    exact hQ w hw
  have hs : 0 < (‖v‖⁻¹)^2 := sq_pos_of_ne_zero (inv_ne_zero hn)
  have hvQ : 0 < metricQuadraticValue G v := (mul_pos_iff_of_pos_left hs).mp hmul
  simpa only [metricQuadraticValue, star_trivial] using hvQ

theorem centralBox_subset_modelSquare : centralBox ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

end SmoothLocal.Perturbation

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

theorem pulseScaleBound_pos (q0 delta : ℝ) : 0 < pulseScaleBound q0 delta := by
  unfold pulseScaleBound
  positivity

theorem pulseScaleBound_xi (q0 delta : ℝ) : ‖xiCLM‖ ≤ pulseScaleBound q0 delta := by
  have h := mul_nonneg (abs_nonneg delta⁻¹) (norm_nonneg (thetaCLM q0))
  unfold pulseScaleBound
  linarith

theorem pulseScaleBound_theta (q0 delta : ℝ) :
    |delta⁻¹| * ‖thetaCLM q0‖ ≤ pulseScaleBound q0 delta := by
  unfold pulseScaleBound
  linarith [norm_nonneg xiCLM]

theorem norm_scaled_theta_le (q0 delta : ℝ) {tau : ℝ} (ht : 0 ≤ tau) :
    ‖(tau / delta) • thetaCLM q0‖ ≤ tau * pulseScaleBound q0 delta := by
  rw [norm_smul, Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_nonneg ht]
  calc
    _ = tau * (|delta⁻¹| * ‖thetaCLM q0‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pulseScaleBound_theta q0 delta) ht

theorem norm_scaled_xi_le (q0 delta : ℝ) {tau : ℝ} (ht : 0 ≤ tau) :
    ‖tau • xiCLM‖ ≤ tau * pulseScaleBound q0 delta := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (pulseScaleBound_xi q0 delta) ht

theorem linear_comp_derivative_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : Coord →L[ℝ] ℝ) (k : ℕ) (p : Coord) {C s : ℝ}
    (hC : 0 ≤ C) (hfC : ∀ t, ‖iteratedFDeriv ℝ k f t‖ ≤ C)
    (hL : ‖L‖ ≤ s) :
    ‖iteratedFDeriv ℝ k (f ∘ L) p‖ ≤ C * s ^ k := by
  rw [L.iteratedFDeriv_comp_right hf p (WithTop.coe_le_coe.mpr le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L p)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k f (L p)‖ * ‖L‖ ^ k := by simp
    _ ≤ C * s ^ k := mul_le_mul (hfC _) (pow_le_pow_left₀ (norm_nonneg L) hL k)
      (pow_nonneg (norm_nonneg L) k) hC

theorem derivativeConvolution_nonneg {A B : ℕ → ℝ}
    (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k) (k : ℕ) :
    0 ≤ derivativeConvolution A B k :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))

theorem product_derivative_bound {f g : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {A B : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    {s : ℝ} (hs : 0 ≤ s)
    (hfa : ∀ k p, ‖iteratedFDeriv ℝ k f p‖ ≤ A k * s ^ k)
    (hgb : ∀ k p, ‖iteratedFDeriv ℝ k g p‖ ≤ B k * s ^ k) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => f q * g q) p‖ ≤ derivativeConvolution A B k * s ^ k := by
  refine (norm_iteratedFDeriv_mul_le hf hg p (WithTop.coe_le_coe.mpr le_top)).trans ?_
  rw [derivativeConvolution, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hpow : s ^ i * s ^ (k - i) = s ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hik]
  calc
    _ ≤ (k.choose i : ℝ) * (A i * s ^ i) * (B (k - i) * s ^ (k - i)) :=
      mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfa i p) (Nat.cast_nonneg _)
          (mul_nonneg (hA i) (pow_nonneg hs i))) (hgb (k - i) p)
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg (hB (k - i)) (pow_nonneg hs (k - i)))
    _ = ((k.choose i : ℝ) * A i * B (k - i)) * s ^ k := by
      rw [← hpow]
      ring

def pulseCore (q0 a delta tau : ℝ) (p : Coord) : ℝ :=
  axisBump a (xiCLM p) * axisBump (1 / 2) (((tau / delta) • thetaCLM q0) p) *
    Real.cos ((tau • xiCLM) p)

theorem pulseCore_contDiff (q0 a delta tau : ℝ) : ContDiff ℝ ∞ (pulseCore q0 a delta tau) :=
  (((axisBump_contDiff a).comp_continuousLinearMap).mul
    ((axisBump_contDiff (1 / 2)).comp_continuousLinearMap)).mul
      Real.contDiff_cos.comp_continuousLinearMap

theorem pulseCoreDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ pulseCoreDerivativeBound a ha k :=
  derivativeConvolution_nonneg
    (derivativeConvolution_nonneg (fun _ => (axisBumpDerivativeBound_pos ha _).le)
      (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le))
    (fun _ => zero_le_one) k

theorem pulseCore_derivative_le {a : ℝ} (ha : 0 < a) (q0 delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseCore q0 a delta tau) p‖ ≤
      pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k := by
  have ht0 : 0 ≤ tau := le_trans zero_le_one ht
  have hs : 0 ≤ tau * pulseScaleBound q0 delta :=
    mul_nonneg ht0 (pulseScaleBound_pos q0 delta).le
  have hxi : ‖xiCLM‖ ≤ tau * pulseScaleBound q0 delta :=
    (pulseScaleBound_xi q0 delta).trans
      (le_mul_of_one_le_left (pulseScaleBound_pos q0 delta).le ht)
  have hχ (j : ℕ) (p : Coord) :=
    linear_comp_derivative_bound (axisBump_contDiff a) xiCLM j p
      (axisBumpDerivativeBound_pos ha j).le (axisBump_derivative_le ha j) hxi
  have hφ (j : ℕ) (p : Coord) :=
    linear_comp_derivative_bound (axisBump_contDiff (1 / 2))
      ((tau / delta) • thetaCLM q0) j p
      (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) j).le
      (axisBump_derivative_le (by norm_num : (0 : ℝ) < 1 / 2) j)
      (norm_scaled_theta_le q0 delta ht0)
  have hcos (j : ℕ) (p : Coord) :
      ‖iteratedFDeriv ℝ j (Real.cos ∘ (tau • xiCLM)) p‖ ≤
        1 * (tau * pulseScaleBound q0 delta) ^ j := by
    apply linear_comp_derivative_bound Real.contDiff_cos (tau • xiCLM) j p zero_le_one
    · intro t
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        Real.abs_iteratedDeriv_cos_le_one j t
    · exact norm_scaled_xi_le q0 delta ht0
  have hχφ := product_derivative_bound
    (axisBump_contDiff a).comp_continuousLinearMap
    (axisBump_contDiff (1 / 2)).comp_continuousLinearMap
    (fun _ => (axisBumpDerivativeBound_pos ha _).le)
    (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le)
    hs hχ hφ
  exact product_derivative_bound
    ((axisBump_contDiff a).comp_continuousLinearMap.mul
      (axisBump_contDiff (1 / 2)).comp_continuousLinearMap)
    Real.contDiff_cos.comp_continuousLinearMap
    (derivativeConvolution_nonneg (fun _ => (axisBumpDerivativeBound_pos ha _).le)
      (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le))
    (fun _ => zero_le_one) hs hχφ hcos k p

def thetaTensor (q0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  thetaCovector q0 i * thetaCovector q0 j

theorem pulseTensor_eq_core (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    pulseTensor q0 a N delta tau = fun p =>
      (1 / tau ^ N) • (pulseCore q0 a delta tau p • thetaTensor q0) := by
  ext p i j
  simp only [pulseTensor, pulseScalar, pulseCore, shearCoordinates, thetaCLM, xiCLM,
    temporalCutoff, thetaTensor, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have harg : tau / delta * (p 1 + q0 * p 0) = tau * (p 1 + q0 * p 0) / delta := by ring
  rw [harg]
  ring

def pulseDerivativeBound (q0 a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) : ℝ :=
  ‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * pulseScaleBound q0 delta ^ k

theorem pulseTensor_derivative_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseTensor q0 a N delta tau) p‖ ≤
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N := by
  have ht0 : 0 < tau := lt_of_lt_of_le zero_lt_one ht
  let T : Fin 2 → Fin 2 → ℝ := thetaTensor q0
  let L := ContinuousLinearMap.toSpanSingleton ℝ T
  have hcore : ContDiff ℝ ∞ (pulseCore q0 a delta tau) := pulseCore_contDiff q0 a delta tau
  have hnorm := L.norm_iteratedFDeriv_comp_left hcore.contDiffAt
    (WithTop.coe_le_coe.mpr le_top) (n := k) (x := p)
  have hLnorm : ‖L‖ = ‖T‖ := ContinuousLinearMap.norm_toSpanSingleton (𝕜 := ℝ) T
  rw [hLnorm] at hnorm
  have hnorm' : ‖iteratedFDeriv ℝ k (L ∘ pulseCore q0 a delta tau) p‖ ≤
      ‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k := by
    refine hnorm.trans ?_
    exact (mul_le_mul_of_nonneg_left (pulseCore_derivative_le ha q0 delta ht k p)
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  rw [pulseTensor_eq_core]
  change ‖iteratedFDeriv ℝ k (fun q => (1 / tau ^ N) • (L ∘ pulseCore q0 a delta tau) q) p‖ ≤ _
  have hsmul :
      iteratedFDeriv ℝ k (fun q => (1 / tau ^ N : ℝ) • (L ∘ pulseCore q0 a delta tau) q) p =
        (1 / tau ^ N : ℝ) • iteratedFDeriv ℝ k (L ∘ pulseCore q0 a delta tau) p :=
    iteratedFDeriv_const_smul_apply' (i := k) (a := (1 / tau ^ N : ℝ))
      ((L.contDiff.comp hcore).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hsmul,
    norm_smul, Real.norm_of_nonneg (div_nonneg zero_le_one (pow_nonneg ht0.le N))]
  calc
    _ ≤ (1 / tau ^ N) *
        (‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k) :=
      mul_le_mul_of_nonneg_left hnorm' (div_nonneg zero_le_one (pow_nonneg ht0.le N))
    _ = _ := by rw [mul_pow]; unfold pulseDerivativeBound; ring

theorem fixed_order_pulse_bound_tendsto_zero (q0 a : ℝ) (ha : 0 < a)
    (delta : ℝ) (N k : ℕ) (hk : k < N) :
    Tendsto (fun tau : ℝ => pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N)
      atTop (𝓝 0) := by
  have hd : N - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hk)
  have h := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0)).pow (N - k)
  have h' : Tendsto (fun tau : ℝ => pulseDerivativeBound q0 a ha delta k * (tau⁻¹) ^ (N - k))
      atTop (𝓝 0) := by
    simpa only [zero_pow hd, mul_zero] using h.const_mul (pulseDerivativeBound q0 a ha delta k)
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau ht
  have htne : tau ≠ 0 := ht.ne'
  have hN : N = k + (N - k) := (Nat.add_sub_of_le hk.le).symm
  have hratio : tau ^ k / tau ^ N = (tau⁻¹) ^ (N - k) := by
    conv_lhs => rw [hN, pow_add]
    rw [inv_pow]
    field_simp
  simp only [mul_div_assoc, hratio]

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

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

theorem metricCoefficientCLM_norm_le (i j : Fin 2) :
    ‖(show (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ from metricCoefficientCLM i j)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

end SmoothLocal.Perturbation

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
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def curvatureFirstFunction (a : CurvatureFirstInput) : ℝ := curvatureLowerJet a.1 a.2
def curvatureFirstDomain : Set CurvatureFirstInput := {a | (Matrix.of a.1).det ≠ 0}
def curvatureFirstTube (M d : ℝ) : Set CurvatureFirstInput :=
  Metric.closedBall 0 M ∩ (fun a : CurvatureFirstInput => (Matrix.of a.1).det) ⁻¹' Ici d

def thetaCurvatureFirstIncrement (f : Coord → ℝ) (p : Coord) : CurvatureFirstInput :=
  ((fun i j => (!![0,0;0,f p] : MetricMatrix) i j),
    (fun d i j => thetaPulseFirstJet f p d i j))

theorem curvatureFirstDet_contDiff :
    ContDiff ℝ ∞ (fun a : CurvatureFirstInput => (Matrix.of a.1).det) := by
  simp only [Matrix.det_fin_two,Matrix.of_apply]
  fun_prop

theorem curvatureFirstFunction_contDiffOn :
    ContDiffOn ℝ ∞ curvatureFirstFunction curvatureFirstDomain :=
  curvatureLowerJet_contDiffOn (fun i j => by fun_prop)
    (fun d i j => by fun_prop) (fun _ h => h)

theorem curvatureFirstTube_isCompact (M d : ℝ) : IsCompact (curvatureFirstTube M d) :=
  (isCompact_closedBall (0 : CurvatureFirstInput) M).inter_right
    (isClosed_Ici.preimage curvatureFirstDet_contDiff.continuous)

theorem curvatureFirstTube_subset_domain (M : ℝ) {d : ℝ} (hd : 0 < d) :
    curvatureFirstTube M d ⊆ curvatureFirstDomain := by
  intro a ha
  exact ne_of_gt (hd.trans_le ha.2)

theorem thetaCurvatureFirstIncrement_norm_le (f : Coord → ℝ) (p : Coord) {e : ℝ}
    (he : 0 ≤ e) (hf : |f p| ≤ e) (hdf : ∀ i, |coordPartial i f p| ≤ e) :
    ‖thetaCurvatureFirstIncrement f p‖ ≤ e := by
  change max ‖(!![0,0;0,f p] : MetricMatrix)‖ ‖thetaPulseFirstJet f p‖ ≤ e
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    fin_cases i <;> fin_cases j
    · simpa using he
    · simpa using he
    · simpa using he
    · simpa [Matrix.of_apply,Real.norm_eq_abs] using hf
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    simp only [thetaPulseFirstJet,Real.norm_eq_abs]
    split_ifs
    · exact hdf d
    · simpa using he

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem pulsePrincipalRemainderBound_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ pulsePrincipalRemainderBound a ha := by
  exact mul_nonneg (axisBumpDerivativeBound_pos (by norm_num) 0).le
    (add_nonneg (axisBumpDerivativeBound_pos ha 1).le (axisBumpDerivativeBound_pos ha 2).le)

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

theorem pulsePairRectangle_isCompact (a delta tau : ℝ) :
    IsCompact (pulsePairRectangle a delta tau) := isCompact_Icc.prod isCompact_Icc

theorem pulsePairPoint_continuous : Continuous pulsePairPoint := by
  unfold pulsePairPoint boxPoint
  fun_prop

theorem pulsePairPoint_mem {a delta tau : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ pulsePairRectangle a delta tau) : pulsePairPoint q ∈ pulseStrip a delta tau :=
  boxPoint_mem hq.2 hq.1

theorem pulseTest_continuous (a tau : ℝ) : Continuous (pulseTest a tau) :=
  (axisBump_contDiff a).continuous.mul (by fun_prop)

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
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem scalarPulseDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) (delta : ℝ) (k : ℕ) :
    0 ≤ scalarPulseDerivativeBound a ha delta k :=
  mul_nonneg (pulseCoreDerivativeBound_nonneg ha k) (pow_nonneg (pulseScaleBound_pos 0 delta).le k)

theorem pulseScalar_eq_core (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    pulseScalar a N delta tau = fun p => (1/tau^N) • pulseCore 0 a delta tau p := by
  funext p
  simp only [pulseScalar,pulseCore,xiCLM,thetaCLM,temporalCutoff,
    add_apply,smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,zero_mul,add_zero]
  have ht : tau/delta*p 1 = tau*p 1/delta := by ring
  rw [ht]
  ring

theorem pulseScalar_derivative_le {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseScalar a N delta tau) p‖ ≤
      scalarPulseDerivativeBound a ha delta k * tau^k/tau^N := by
  have ht0 : 0 < tau := zero_lt_one.trans_le ht
  rw [pulseScalar_eq_core]
  rw [iteratedFDeriv_const_smul_apply' (i := k) (a := (1/tau^N : ℝ))
    ((pulseCore_contDiff 0 a delta tau).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
    norm_smul,Real.norm_of_nonneg (div_nonneg zero_le_one (pow_nonneg ht0.le N))]
  calc
    _ ≤ (1/tau^N)*(pulseCoreDerivativeBound a ha k*(tau*pulseScaleBound 0 delta)^k) :=
      mul_le_mul_of_nonneg_left (pulseCore_derivative_le ha 0 delta ht k p)
        (div_nonneg zero_le_one (pow_nonneg ht0.le N))
    _ = _ := by rw [mul_pow]; unfold scalarPulseDerivativeBound; ring

theorem scalarPulseFirstJetBound_nonneg {a : ℝ} (ha : 0 < a) (delta : ℝ) :
    0 ≤ scalarPulseFirstJetBound a ha delta :=
  (scalarPulseDerivativeBound_nonneg ha delta 0).trans (le_max_left _ _)

def scalarPulseFirstJetBudget (a : ℝ) (ha : 0 < a) (N : ℕ) (delta tau : ℝ) : ℝ :=
  scalarPulseFirstJetBound a ha delta * tau/tau^N

theorem scalarPulseFirstJetBudget_nonneg {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) : 0 ≤ scalarPulseFirstJetBudget a ha N delta tau :=
  div_nonneg (mul_nonneg (scalarPulseFirstJetBound_nonneg ha delta) (zero_le_one.trans ht))
    (pow_nonneg (zero_le_one.trans ht) N)

theorem pulseScalar_first_jet_bounds {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    |pulseScalar a N delta tau p| ≤ scalarPulseFirstJetBudget a ha N delta tau ∧
      ∀ i, |coordPartial i (pulseScalar a N delta tau) p| ≤ scalarPulseFirstJetBudget a ha N delta tau := by
  have ht0 : 0 ≤ tau := zero_le_one.trans ht
  have hden : 0 ≤ tau^N := pow_nonneg ht0 N
  have hB0 : scalarPulseDerivativeBound a ha delta 0 ≤ scalarPulseFirstJetBound a ha delta :=
    le_max_left _ _
  have hB1 : scalarPulseDerivativeBound a ha delta 1 ≤ scalarPulseFirstJetBound a ha delta :=
    le_max_right _ _
  constructor
  · have h := pulseScalar_derivative_le ha N delta ht 0 p
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,mul_one] at h
    exact h.trans (div_le_div_of_nonneg_right
      (hB0.trans (le_mul_of_one_le_right (scalarPulseFirstJetBound_nonneg ha delta) ht)) hden)
  · intro i
    have h := (norm_iteratedCoordPartial_le_jet
      (pulseScalar_contDiff a N delta tau).contDiffOn isOpen_univ [i] (mem_univ p)).trans
        (pulseScalar_derivative_le ha N delta ht 1 p)
    simp only [iteratedCoordPartial,Real.norm_eq_abs,pow_one] at h
    exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB1 ht0) hden)

theorem thetaPulse_first_increment_bound {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    ‖thetaCurvatureFirstIncrement (pulseScalar a N delta tau) p‖ ≤
      scalarPulseFirstJetBudget a ha N delta tau :=
  thetaCurvatureFirstIncrement_norm_le _ p (scalarPulseFirstJetBudget_nonneg ha N delta ht)
    (pulseScalar_first_jet_bounds ha N delta ht p).1 (pulseScalar_first_jet_bounds ha N delta ht p).2

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem metricApproximationAccuracy_pos {tau : ℕ} (htau : 0 < tau) :
    0 < metricApproximationAccuracy tau :=
  one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr htau) tau)

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
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem pulseWeightedMoment_integrable {a delta tau : ℝ} {f : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    IntegrableOn (fun q => f (pulsePairPoint q)*pulseTest a tau q.2)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
  ((hf.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).mul
    ((pulseTest_continuous a tau).comp continuous_snd).continuousOn).integrableOn_compact
      (pulsePairRectangle_isCompact a delta tau)

theorem pulseWeightedMoment_sub {a delta tau : ℝ} {f h : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) (hh : ContinuousOn h (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau (fun p => f p-h p) =
      pulseWeightedMoment a delta tau f-pulseWeightedMoment a delta tau h := by
  unfold pulseWeightedMoment
  simp_rw [sub_mul]
  exact integral_sub (pulseWeightedMoment_integrable hf) (pulseWeightedMoment_integrable hh)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem matrix_entry_abs_le_norm (G : MetricMatrix) (i j : Fin 2) : |G i j| ≤ ‖G‖ := by
  simpa only [Real.norm_eq_abs] using
    (Matrix.norm_entry_le_entrywise_sup_norm G (i := i) (j := j))

theorem det_sub_le_first_distance (G H : MetricMatrix) {B e : ℝ}
    (hB : 0 ≤ B) (he : 0 ≤ e) (hG : ‖G‖ ≤ B) (hD : ‖H-G‖ ≤ e) :
    |H.det-G.det| ≤ 4*B*e+2*e^2 := by
  let D := H-G
  have hg (i j : Fin 2) : |G i j| ≤ B := (matrix_entry_abs_le_norm G i j).trans hG
  have hd (i j : Fin 2) : |D i j| ≤ e := (matrix_entry_abs_le_norm D i j).trans hD
  have hgd (i j k l : Fin 2) : |G i j*D k l| ≤ B*e := by
    rw [abs_mul]
    exact mul_le_mul (hg i j) (hd k l) (abs_nonneg _) hB
  have hdg (i j k l : Fin 2) : |D i j*G k l| ≤ e*B := by
    rw [abs_mul]
    exact mul_le_mul (hd i j) (hg k l) (abs_nonneg _) he
  have hdd (i j k l : Fin 2) : |D i j*D k l| ≤ e^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (hd i j) (hd k l) (abs_nonneg _) he
  have hsum (i j k l : Fin 2) :
      |G i j*D k l+D i j*G k l+D i j*D k l| ≤ B*e+e*B+e^2 :=
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      (add_le_add (add_le_add (hgd i j k l) (hdg i j k l)) (hdd i j k l))
  have hEq : H.det-G.det =
      (G 0 0*D 1 1+D 0 0*G 1 1+D 0 0*D 1 1)-
        (G 0 1*D 1 0+D 0 1*G 1 0+D 0 1*D 1 0) := by
    simp only [D,Matrix.det_fin_two,Matrix.sub_apply]
    ring
  rw [hEq]
  calc
    _ ≤ |G 0 0*D 1 1+D 0 0*G 1 1+D 0 0*D 1 1|+
        |G 0 1*D 1 0+D 0 1*G 1 0+D 0 1*D 1 0| := abs_sub _ _
    _ ≤ (B*e+e*B+e^2)+(B*e+e*B+e^2) := add_le_add (hsum 0 0 1 1) (hsum 0 1 1 0)
    _ = _ := by ring

theorem det_sub_le_small_first_distance (G H : MetricMatrix) {B e : ℝ}
    (hB : 0 ≤ B) (he : 0 ≤ e) (he1 : e ≤ 1) (hG : ‖G‖ ≤ B) (hD : ‖H-G‖ ≤ e) :
    |H.det-G.det| ≤ (4*B+2)*e := by
  apply (det_sub_le_first_distance G H hB he hG hD).trans
  have hee : e^2 ≤ e := by nlinarith [mul_le_mul_of_nonneg_left he1 he]
  nlinarith

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem approximation_budget_le_pulse_error {N n : ℕ}
    (hN : 0 < N) (hn : 1 ≤ n) (hlarge : N-1 ≤ n) :
    1/(n : ℝ)^n ≤ (n : ℝ)/(n : ℝ)^N := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  calc
    _ ≤ 1/(n : ℝ)^(N-1) :=
      one_div_le_one_div_of_le (pow_pos hn0 _) (pow_le_pow_right₀ hn1 hlarge)
    _ = (n : ℝ)/(n : ℝ)^N := by
      have hN' : N = (N-1)+1 := by omega
      conv_rhs => rw [hN',pow_add,pow_one]
      field_simp [hn0.ne']

end SmoothLocal.Pulse

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

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qMetricDensityFactor (g : MetricField) (w : DarbouxState) : ℝ :=
  stateEnergy g w / ((g (statePoint w)).det*stateQDenominator g w)

theorem qMetricDensityFactor_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) :
    qMetricDensityFactor g (qSolutionJet z p) = 2*forcingCoefficient g z p := by
  unfold qMetricDensityFactor
  rw [stateQDenominator_qSolutionJet]
  unfold stateEnergy
  rw [statePoint_qSolutionJet,stateGradient_qSolutionJet,jetEnergy_at_height hg hp z,
    forcingCoefficient_eq_energy hg z hp]
  have hdet := metricDet_ne_zero hg hp
  field_simp [hdet,hxx]

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qFirstDet (a : QFirstInput) : ℝ := (Matrix.of a.1.1).det
def qFirstConnection (a : QFirstInput) (i j : Fin 2) : ℝ :=
  ∑ k, christoffelJet (Matrix.of a.1.1) a.1.2 k i j * stateGradient a.2 k
def qFirstXX (a : QFirstInput) : ℝ := a.2 5-qFirstConnection a 0 0

def qFirstEnergy (a : QFirstInput) : ℝ :=
  qFirstDet a-(a.1.1 1 1*(stateGradient a.2 0)^2-
    (a.1.1 0 1+a.1.1 1 0)*stateGradient a.2 0*stateGradient a.2 1+
      a.1.1 0 0*(stateGradient a.2 1)^2)
def qFirstDensityFactor (a : QFirstInput) : ℝ :=
  qFirstEnergy a/(qFirstDet a*qFirstXX a)

theorem qFirstDet_bundle (g : MetricField) (w : DarbouxState) :
    qFirstDet (qFirstBundle g w) = (g (statePoint w)).det := rfl

theorem qFirstXX_bundle (g : MetricField) (w : DarbouxState) :
    qFirstXX (qFirstBundle g w) = stateQDenominator g w := rfl
theorem qFirstDensityFactor_bundle (g : MetricField) (w : DarbouxState) :
    qFirstDensityFactor (qFirstBundle g w) = qMetricDensityFactor g w := rfl

def qFirstBase : Set QFirstInput := {a | qFirstDet a ≠ 0}
def qFirstDomain : Set QFirstInput := {a | qFirstDet a ≠ 0 ∧ qFirstXX a ≠ 0}
def qFirstBaseTube (M d : ℝ) : Set QFirstInput :=
  Metric.closedBall 0 M ∩ qFirstDet ⁻¹' Ici d
def qFirstTube (M d c : ℝ) : Set QFirstInput :=
  qFirstBaseTube M d ∩ qFirstXX ⁻¹' {v : ℝ | c ≤ |v|}

theorem qFirstDet_contDiff : ContDiff ℝ ∞ qFirstDet := by
  unfold qFirstDet
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  fun_prop

theorem qFirstBase_isOpen : IsOpen qFirstBase :=
  isOpen_ne_fun qFirstDet_contDiff.continuous continuous_const

theorem qFirstConnection_contDiffAt {a : QFirstInput} (ha : a ∈ qFirstBase)
    (i j : Fin 2) : ContDiffAt ℝ ∞ (fun b => qFirstConnection b i j) a := by
  have hΓ (k : Fin 2) : ContDiffAt ℝ ∞
      (fun b : QFirstInput => christoffelJet (Matrix.of b.1.1) b.1.2 k i j) a :=
    christoffelJet_contDiffAt (G := fun b : QFirstInput => Matrix.of b.1.1)
      (D := fun b : QFirstInput => b.1.2) (fun row column => by
        simp only [Matrix.of_apply]
        fun_prop)
      (fun d i j => by fun_prop) ha k i j
  have hv (k : Fin 2) : ContDiffAt ℝ ∞
      (fun b : QFirstInput => stateGradient b.2 k) a :=
    ((contDiff_apply ℝ ℝ k).comp (stateGradient_contDiff.comp (by fun_prop))).contDiffAt
  simpa only [qFirstConnection,Fin.sum_univ_two] using
    ((hΓ 0).mul (hv 0)).add ((hΓ 1).mul (hv 1))

theorem qFirstXX_contDiffOn : ContDiffOn ℝ ∞ qFirstXX qFirstBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : QFirstInput => b.2 5) a by fun_prop).sub
    (qFirstConnection_contDiffAt ha 0 0)).contDiffWithinAt

theorem qFirstEnergy_contDiff : ContDiff ℝ ∞ qFirstEnergy := by
  unfold qFirstEnergy
  have hv (k : Fin 2) : ContDiff ℝ ∞ (fun a : QFirstInput => stateGradient a.2 k) :=
    (contDiff_apply ℝ ℝ k).comp (stateGradient_contDiff.comp (by fun_prop))
  exact qFirstDet_contDiff.sub
    ((((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 1 1) by fun_prop).mul
      ((hv 0).pow 2)).sub
      ((((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 0 1) by fun_prop).add
        (show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 1 0) by fun_prop)).mul
          (hv 0)).mul (hv 1))).add
        ((show ContDiff ℝ ∞ (fun a : QFirstInput => a.1.1 0 0) by fun_prop).mul
          ((hv 1).pow 2)))

theorem qFirstDensityFactor_contDiffOn :
    ContDiffOn ℝ ∞ qFirstDensityFactor qFirstDomain := by
  intro a ha
  have hx := qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds ha.1)
  exact (qFirstEnergy_contDiff.contDiffAt.div
    (qFirstDet_contDiff.contDiffAt.mul hx) (mul_ne_zero ha.1 ha.2)).contDiffWithinAt

theorem qFirstBaseTube_isCompact (M d : ℝ) : IsCompact (qFirstBaseTube M d) :=
  (isCompact_closedBall (0 : QFirstInput) M).inter_right
    (isClosed_Ici.preimage qFirstDet_contDiff.continuous)

theorem qFirstBaseTube_subset_base (M : ℝ) {d : ℝ} (hd : 0 < d) :
    qFirstBaseTube M d ⊆ qFirstBase := by
  intro a ha
  exact ne_of_gt (hd.trans_le ha.2)

theorem qFirstTube_isCompact (M : ℝ) {d : ℝ} (hd : 0 < d) (c : ℝ) :
    IsCompact (qFirstTube M d c) := by
  have hbase := qFirstBaseTube_isCompact M d
  have hc : ContinuousOn qFirstXX (qFirstBaseTube M d) :=
    qFirstXX_contDiffOn.continuousOn.mono (qFirstBaseTube_subset_base M hd)
  have hclosed : IsClosed (qFirstTube M d c) :=
    hc.preimage_isClosed_of_isClosed hbase.isClosed (isClosed_le continuous_const continuous_abs)
  exact hbase.of_isClosed_subset hclosed inter_subset_left

theorem qFirstTube_subset_domain (M : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    qFirstTube M d c ⊆ qFirstDomain := by
  intro a ha
  refine ⟨qFirstBaseTube_subset_base M hd ha.1,?_⟩
  intro hz
  have hh : c ≤ |qFirstXX a| := ha.2
  rw [hz,abs_zero] at hh
  linarith

end SmoothLocal.Pulse

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
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def affineFirstJetMap (R : MetricMatrix) (a : CurvatureFirstInput) : CurvatureFirstInput :=
  ((fun i j => ∑ u, ∑ v, R u i*R v j*a.1 u v),
    (fun k i j => ∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v))

theorem affineFirstJetMap_sub (R : MetricMatrix) (a b : CurvatureFirstInput) :
    affineFirstJetMap R (a-b) = affineFirstJetMap R a-affineFirstJetMap R b := by
  apply Prod.ext
  · funext i j
    simp only [affineFirstJetMap,Prod.fst_sub,Pi.sub_apply,Fin.sum_univ_two]
    ring
  · funext k i j
    simp only [affineFirstJetMap,Prod.snd_sub,Pi.sub_apply,Fin.sum_univ_two]
    ring

theorem actualCurvatureFirstInput_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (b : Coord) (R : MetricMatrix)
    (p : Coord) (hp : affineCoordinates b R p ∈ U) :
    actualCurvatureFirstInput (affinePullbackMetric g b R) p =
      affineFirstJetMap R (actualCurvatureFirstInput g (affineCoordinates b R p)) := by
  apply Prod.ext
  · funext i j
    simp only [actualCurvatureFirstInput,affineFirstJetMap,affinePullbackMetric,
      Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
    ring
  · funext k i j
    exact coordPartial_affinePullbackMetric hg hU b R p hp k i j

theorem abs_sum_fin_two_le {f : Fin 2 → ℝ} {e : ℝ}
    (hf : ∀ i, |f i| ≤ e) : |∑ i, f i| ≤ 2*e := by
  simp only [Fin.sum_univ_two]
  exact ((abs_add_le _ _).trans (add_le_add (hf 0) (hf 1))).trans_eq (by ring)

theorem affineFirstJetMap_norm_le_eight (R : MetricMatrix)
    (hR : ∀ i j, |R i j| ≤ 1) (a : CurvatureFirstInput) {e : ℝ}
    (he : 0 ≤ e) (ha : ‖a‖ ≤ e) : ‖affineFirstJetMap R a‖ ≤ 8*e := by
  have hval (i j : Fin 2) : |a.1 i j| ≤ e := by
    simpa only [Real.norm_eq_abs] using
      (((norm_le_pi_norm (a.1 i) j).trans (norm_le_pi_norm a.1 i)).trans (norm_fst_le a)).trans ha
  have hder (k i j : Fin 2) : |a.2 k i j| ≤ e := by
    simpa only [Real.norm_eq_abs] using
      ((((norm_le_pi_norm (a.2 k i) j).trans (norm_le_pi_norm (a.2 k) i)).trans
        (norm_le_pi_norm a.2 k)).trans (norm_snd_le a)).trans ha
  have hR2 (i j u v : Fin 2) : |R u i*R v j| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR u i) (hR v j) (abs_nonneg _) zero_le_one
  have hR3 (i j k u v w : Fin 2) : |R u i*R v j*R w k| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR2 i j u v) (hR w k) (abs_nonneg _) zero_le_one
  have hv (i j u v : Fin 2) : |R u i*R v j*a.1 u v| ≤ e := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR2 i j u v) (hval u v) (abs_nonneg _) zero_le_one
  have hd (k i j u v w : Fin 2) : |R u i*R v j*R w k*a.2 w u v| ≤ e := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hR3 i j k u v w) (hder w u v) (abs_nonneg _) zero_le_one
  have hvsum (i j : Fin 2) : |∑ u, ∑ v, R u i*R v j*a.1 u v| ≤ 4*e := by
    have hh := abs_sum_fin_two_le (fun u => abs_sum_fin_two_le (hv i j u))
    convert hh using 1 <;> try with_reducible_and_instances rfl
    ring
  have hdsum (k i j : Fin 2) : |∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v| ≤ 8*e := by
    have hh := abs_sum_fin_two_le (fun u => abs_sum_fin_two_le
      (fun v => abs_sum_fin_two_le (hd k i j u v)))
    convert hh using 1 <;> try with_reducible_and_instances rfl
    ring
  change max ‖(affineFirstJetMap R a).1‖ ‖(affineFirstJetMap R a).2‖ ≤ 8*e
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro j
    change ‖∑ u, ∑ v, R u i*R v j*a.1 u v‖ ≤ _
    rw [Real.norm_eq_abs]
    exact (hvsum i j).trans (by nlinarith)
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro k
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 8*e)).mpr
    intro j
    change ‖∑ u, ∑ v, ∑ w, R u i*R v j*R w k*a.2 w u v‖ ≤ 8*e
    rw [Real.norm_eq_abs]
    exact hdsum k i j

theorem inverseShearMatrix_entry_le_one {q0 : ℝ} (hq : |q0| ≤ 1) (i j : Fin 2) :
    |inverseShearMatrix q0 i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [inverseShearMatrix,hq]

theorem actual_shear_first_jet_distance_le {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {q0 e : ℝ} (hq : |q0| ≤ 1) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput g (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput h (inverseShearCoordinates q0 p)‖ ≤ e) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates g q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates h q0) p‖ ≤ 8*e := by
  have he : 0 ≤ e := (norm_nonneg _).trans hjet
  have hp' : affineCoordinates 0 (inverseShearMatrix q0) p ∈ U := by
    simpa only [←inverseShearCoordinates_eq_affine] using hp
  unfold metricInShearCoordinates
  rw [actualCurvatureFirstInput_affinePullback hg hU 0 (inverseShearMatrix q0) p hp',
    actualCurvatureFirstInput_affinePullback hh hU 0 (inverseShearMatrix q0) p hp',
    ←affineFirstJetMap_sub]
  exact affineFirstJetMap_norm_le_eight _ (inverseShearMatrix_entry_le_one hq) _ he
    (by simpa only [←inverseShearCoordinates_eq_affine] using hjet)

theorem actualCurvatureFirstInput_thetaPulseMetric {g : MetricField} {f : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    actualCurvatureFirstInput (thetaPulseMetric g f) p =
      actualCurvatureFirstInput g p+thetaCurvatureFirstIncrement f p := by
  apply Prod.ext
  · rfl
  · exact metricFirstJet_thetaPulseMetric hg hf hU hp

theorem actual_sheared_solution_first_jet_error
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta tau e : ℝ} {N : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta tau) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (ht : 1 ≤ tau) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
        (inverseShearCoordinates q0 p)‖ ≤ e) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      8*e+scalarPulseFirstJetBudget a ha N delta tau := by
  have hcomp := actual_shear_first_jet_distance_le hgTau hgTest hU hq hp hjet
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hpV : p ∈ V := hp
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have heq : actualCurvatureFirstInput
      (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p-
        actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p =
      thetaCurvatureFirstIncrement (pulseScalar a N delta tau) p := by
    rw [metricInShearCoordinates_test,
      actualCurvatureFirstInput_thetaPulseMetric hgV (pulseScalar_contDiff a N delta tau).contDiffOn hV hpV]
    exact add_sub_cancel_left _ _
  calc
    _ ≤ ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
        actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p‖+
        ‖actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p-
          actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p)
        (actualCurvatureFirstInput (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) p)
        (actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p)
    _ ≤ _ := add_le_add hcomp (by rw [heq]; exact thetaPulse_first_increment_bound ha N delta ht p)

end SmoothLocal.Pulse

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
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qPulseFirstJetBudget (a : ℝ) (ha : 0 < a) (N : ℕ) (delta tau : ℝ) : ℝ :=
  (8+scalarPulseFirstJetBound a ha delta)*tau/tau^N

theorem qPulseFirstJetBudget_nonneg {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 0 ≤ tau) : 0 ≤ qPulseFirstJetBudget a ha N delta tau :=
  div_nonneg (mul_nonneg (by linarith [scalarPulseFirstJetBound_nonneg ha delta]) ht)
    (pow_nonneg ht N)

theorem actual_sheared_first_jet_error_nat
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta : ℝ} {N n : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta n) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (hN : 0 < N) (hn : 1 ≤ n) (hlarge : N-1 ≤ n)
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput (testMetric gStar q0 a N delta n)
        (inverseShearCoordinates q0 p)‖ ≤ 1/(n : ℝ)^n) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      qPulseFirstJetBudget a ha N delta n := by
  have ht : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfirst := actual_sheared_solution_first_jet_error hgStar hgTest hgTau hU hq ha ht hp hjet
  calc
    _ ≤ 8*(1/(n : ℝ)^n)+scalarPulseFirstJetBudget a ha N delta n := hfirst
    _ ≤ 8*((n : ℝ)/(n : ℝ)^N)+scalarPulseFirstJetBudget a ha N delta n :=
      add_le_add (mul_le_mul_of_nonneg_left
        (approximation_budget_le_pulse_error hN hn hlarge) (by norm_num : (0 : ℝ) ≤ 8)) le_rfl
    _ = _ := by unfold qPulseFirstJetBudget scalarPulseFirstJetBudget; ring

theorem qPulseFirstJetBudget_tendsto_zero {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hN : 1 < N) (delta : ℝ) :
    Tendsto (qPulseFirstJetBudget a ha N delta) atTop (𝓝 0) := by
  have hn : N-1 ≠ 0 := by omega
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).pow (N-1)
  have h : Tendsto (fun t : ℝ => (8+scalarPulseFirstJetBound a ha delta)*(t⁻¹)^(N-1))
      atTop (𝓝 0) := by
    simpa only [zero_pow hn,mul_zero] using hi.const_mul (8+scalarPulseFirstJetBound a ha delta)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hN' : N = 1+(N-1) := by omega
  have hr : t/t^N = (t⁻¹)^(N-1) := by
    conv_lhs => rw [hN',pow_add,pow_one]
    rw [inv_pow]
    field_simp [ht.ne']
  simp only [qPulseFirstJetBudget,mul_div_assoc,hr]

theorem qPulseFirstJetBudget_eventual_margins (B H : ℝ) {d c a : ℝ}
    (hd : 0 < d) (hc : 0 < c) (ha : 0 < a) (N : ℕ) (hN : 1 < N)
    (delta : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau →
      qPulseFirstJetBudget a ha N delta tau ≤ 1 ∧
      (4*max B 0+2)*qPulseFirstJetBudget a ha N delta tau ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta tau ≤ c/2 := by
  have htend := qPulseFirstJetBudget_tendsto_zero ha N hN delta
  have h1 : ∀ᶠ t : ℝ in atTop, qPulseFirstJetBudget a ha N delta t < 1 :=
    htend.eventually (eventually_lt_nhds zero_lt_one)
  have hd' : Tendsto (fun t : ℝ => (4*max B 0+2)*qPulseFirstJetBudget a ha N delta t)
      atTop (𝓝 0) := by simpa only [mul_zero] using htend.const_mul (4*max B 0+2)
  have hc' : Tendsto (fun t : ℝ => H*qPulseFirstJetBudget a ha N delta t)
      atTop (𝓝 0) := by simpa only [mul_zero] using htend.const_mul H
  have hev : ∀ᶠ t : ℝ in atTop,
      qPulseFirstJetBudget a ha N delta t ≤ 1 ∧
      (4*max B 0+2)*qPulseFirstJetBudget a ha N delta t ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta t ≤ c/2 := by
    filter_upwards [h1,hd'.eventually (eventually_lt_nhds (half_pos hd)),
      hc'.eventually (eventually_lt_nhds (half_pos hc))] with t ht1 htd htc
    exact ⟨ht1.le,htd.le,htc.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp hev
  exact ⟨max T 1,le_max_right _ _,fun t ht => hT t ((le_max_left _ _).trans ht)⟩

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

theorem metricDet_in_shear_coordinates (g : MetricField) (q0 : ℝ) (p : Coord) :
    (metricInShearCoordinates g q0 p).det = (g (inverseShearCoordinates q0 p)).det := by
  simp only [metricInShearCoordinates, det_affinePullbackMetric,
    inverseShearMatrix_det, one_pow, one_mul, ← inverseShearCoordinates_eq_affine]

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem iteratedCoordPartial_sub_actual {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun q => f q-h q) p =
      iteratedCoordPartial ds f p-iteratedCoordPartial ds h p := by
  rw [iteratedCoordPartial_eq_jet (hf.sub hh) hU ds hp]
  change iteratedFDeriv ℝ ds.length (f-h) p (coordinateDirections ds) = _
  rw [iteratedFDeriv_sub_apply (i := ds.length)
    ((hf.contDiffAt (hU.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hh.contDiffAt (hU.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)),
    sub_apply,
    ←iteratedCoordPartial_eq_jet hf hU ds hp,←iteratedCoordPartial_eq_jet hh hU ds hp]

theorem actual_metric_word_difference_le {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) (ds : List (Fin 2)) {epsilon : ℝ}
    (hjet : ‖iteratedFDeriv ℝ ds.length (fun q => g q i j-h q i j) p‖ ≤ epsilon) :
    |iteratedCoordPartial ds (fun q => g q i j) p-
      iteratedCoordPartial ds (fun q => h q i j) p| ≤ epsilon := by
  have hb := (norm_iteratedCoordPartial_le_jet ((hg.1 i j).sub (hh.1 i j)) hU ds hp).trans hjet
  rw [iteratedCoordPartial_sub_actual (hg.1 i j) (hh.1 i j) hU ds hp,
    Real.norm_eq_abs] at hb
  exact hb

theorem actual_metric_jet_approximation_inputs {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {epsilon : ℝ}
    (hjets : ∀ i j : Fin 2, ∀ k ≤ 2,
      ‖iteratedFDeriv ℝ k (fun q => g q i j-h q i j) p‖ ≤ epsilon) :
    ‖actualCurvatureFirstInput g p-actualCurvatureFirstInput h p‖ ≤ epsilon ∧
      ∀ i j k l : Fin 2,
        |coordPartial i (coordPartial j (fun q => g q k l)) p-
          coordPartial i (coordPartial j (fun q => h q k l)) p| ≤ epsilon := by
  have he : 0 ≤ epsilon := (norm_nonneg _).trans (hjets 0 0 0 (by omega))
  have hval (i j : Fin 2) : |g p i j-h p i j| ≤ epsilon := by
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp i j []
      (hjets i j 0 (by omega))
  have hder (d i j : Fin 2) :
      |coordPartial d (fun q => g q i j) p-coordPartial d (fun q => h q i j) p| ≤ epsilon := by
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp i j [d]
      (hjets i j 1 (by omega))
  constructor
  · change max ‖(fun i j => g p i j-h p i j)‖
      ‖(fun d i j => coordPartial d (fun q => g q i j) p-
        coordPartial d (fun q => h q i j) p)‖ ≤ epsilon
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg he).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hval i j
    · apply (pi_norm_le_iff_of_nonneg he).mpr
      intro d
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hder d i j
  · intro i j k l
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp k l [i,j]
      (hjets k l 2 (by omega))

theorem actual_sheared_first_jet_error_from_Ctau
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta : ℝ} {N n : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta n) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (hN : 0 < N) (hn : 2 ≤ n) (hlarge : N-1 ≤ n)
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjets : ∀ i j : Fin 2, ∀ k ≤ n,
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j-testMetric gStar q0 a N delta n q i j)
        (inverseShearCoordinates q0 p)‖ ≤ 1/(n : ℝ)^n) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      qPulseFirstJetBudget a ha N delta n := by
  apply actual_sheared_first_jet_error_nat hgStar hgTest hgTau hU hq ha hN
    (by omega) hlarge hp
  exact (actual_metric_jet_approximation_inputs hgTau hgTest hU hp
    (fun i j k hk => hjets i j k (hk.trans hn))).1

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem sheared_Q_on_height_contDiffOn {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) (hSU : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ U)
    (hxx : ∀ p ∈ S, covHessian (metricInShearCoordinates g q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => sixVariableQ (metricInShearCoordinates g q0)
      (qSolutionJet (heightInShearCoordinates z q0) p)) S := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates g q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : S ⊆ V := fun p hp => hSU p hp
  apply (sixVariableQ_contDiffOn hgV hV).comp ((qSolutionJet_contDiffOn hV hzV).mono hSV)
  intro p hp
  change statePoint (qSolutionJet (heightInShearCoordinates z q0) p) ∈ V ∧
    stateQDenominator (metricInShearCoordinates g q0)
      (qSolutionJet (heightInShearCoordinates z q0) p) ≠ 0
  rw [statePoint_qSolutionJet,stateQDenominator_qSolutionJet]
  exact ⟨hSV hp,hxx p hp⟩

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
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qMomentErrorCoefficient (A Cfirst Ctest Ccompare a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare)+
    Cfirst*(8+scalarPulseFirstJetBound a ha delta)

theorem qMomentErrorCoefficient_nonneg {A Cfirst Ctest Ccompare a : ℝ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare) (delta : ℝ) :
    0 ≤ qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta := by
  have hCd : 0 ≤ testDensityErrorCoefficient Ctest a ha delta :=
    add_nonneg (pulsePrincipalRemainderBound_nonneg a ha)
      (mul_nonneg hCt (scalarPulseFirstJetBound_nonneg ha delta))
  unfold qMomentErrorCoefficient
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) (add_nonneg hCd hCc))
    (mul_nonneg hCf (add_nonneg (by norm_num) (scalarPulseFirstJetBound_nonneg ha delta)))

theorem qForcingRemainderBudget_le_first_scale
    {A Cfirst Ctest Ccompare a delta tau epsilon epsilonQ : ℝ} {N : ℕ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCc : 0 ≤ Ccompare)
    (he : epsilon ≤ tau/tau^N) (heQ : epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau) :
    qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ ≤
      qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta*tau/tau^N := by
  unfold qForcingRemainderBudget
  calc
    _ ≤ 2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*(tau/tau^N))+
        Cfirst*qPulseFirstJetBudget a ha N delta tau :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left he hCc)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA))
        (mul_le_mul_of_nonneg_left heQ hCf)
    _ = _ := by unfold qMomentErrorCoefficient qPulseFirstJetBudget; ring

theorem qMoment_budget_absorption_threshold
    {A Cfirst Ctest Ccompare a c3 : ℝ} (ha : 0 < a) (hc3 : 0 < c3)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare)
    (N : ℕ) (delta : ℝ) (hdelta : 0 ≤ delta) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ epsilon epsilonQ : ℝ,
      epsilon ≤ tau/tau^N → epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau →
      qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
        (2*delta/tau)*(∫ x : ℝ, axisBump a x) ≤ (c3/2)*delta*tau/tau^N := by
  let K := qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta
  let I := ∫ x : ℝ, axisBump a x
  have hK : 0 ≤ K := qMomentErrorCoefficient_nonneg ha hA hCf hCt hCc delta
  have hI : 0 ≤ I := (axisBump_integral_pos ha).le
  refine ⟨max 1 (4*K*I/c3),le_max_left _ _,?_⟩
  intro tau ht epsilon epsilonQ he heQ
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have hthreshold : 4*K*I/c3 ≤ tau := (le_max_right _ _).trans ht
  have hcoeff : 2*K*I ≤ (c3/2)*tau := by
    have hh := (div_le_iff₀ hc3).mp hthreshold
    nlinarith
  have hB := qForcingRemainderBudget_le_first_scale (Ctest := Ctest) ha hA hCf hCc he heQ
  have hwidth : 0 ≤ 2*delta/tau := div_nonneg (mul_nonneg (by norm_num) hdelta) htpos.le
  have hscale : 0 ≤ delta/tau^N := div_nonneg hdelta (pow_nonneg htpos.le N)
  calc
    _ ≤ (K*tau/tau^N)*(2*delta/tau)*I :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hwidth) hI
    _ = (2*K*I)*(delta/tau^N) := by field_simp [htpos.ne']
    _ ≤ ((c3/2)*tau)*(delta/tau^N) := mul_le_mul_of_nonneg_right hcoeff hscale
    _ = _ := by ring

end SmoothLocal.Pulse

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
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem pulseTensor_coeff_derivative_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (i j : Fin 2) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤
      pulseDerivativeBound q0 a ha delta k*tau^k/tau^N := by
  let L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ := metricCoefficientCLM i j
  have h := L.norm_iteratedFDeriv_comp_left (pulseTensor_contDiff q0 a N delta tau).contDiffAt
    (WithTop.coe_le_coe.mpr le_top) (n := k) (x := p)
  change ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤
    ‖L‖*‖iteratedFDeriv ℝ k (pulseTensor q0 a N delta tau) p‖ at h
  exact h.trans ((mul_le_mul_of_nonneg_right (metricCoefficientCLM_norm_le i j)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      pulseTensor_derivative_le q0 a ha N delta ht k p))

theorem pulseTensor_finite_coeff_jets_eventually_small
    (q0 a : ℝ) (ha : 0 < a) (m N : ℕ) (hmN : m < N) (delta : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ ∀ i j : Fin 2, ∀ k ≤ m, ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j) p‖ ≤ epsilon := by
  have heach (k : Fin (m+1)) : ∀ᶠ tau : ℕ in atTop,
      pulseDerivativeBound q0 a ha delta k.val*(tau : ℝ)^k.val/(tau : ℝ)^N < epsilon :=
    ((fixed_order_pulse_bound_tendsto_zero q0 a ha delta N k.val (by omega)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop)).eventually
        (eventually_lt_nhds hepsilon)
  have hall : ∀ᶠ tau : ℕ in atTop, ∀ k : Fin (m+1),
      pulseDerivativeBound q0 a ha delta k.val*(tau : ℝ)^k.val/(tau : ℝ)^N < epsilon :=
    Filter.eventually_all.mpr heach
  filter_upwards [eventually_ge_atTop 1,hall] with tau htau hbound
  refine ⟨htau,?_⟩
  intro i j k hk p
  have hkBound := hbound ⟨k,by omega⟩
  change pulseDerivativeBound q0 a ha delta k*(tau : ℝ)^k/(tau : ℝ)^N < epsilon at hkBound
  exact (pulseTensor_coeff_derivative_le q0 a ha N delta (by exact_mod_cast htau) i j k p).trans
    hkBound.le

theorem metric_jet_norm_le_from_actual_pulse_approximation
    {gStar gTau : MetricField} {V U : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hgTau : SmoothPositiveOn gTau U)
    (hV : IsOpen V) (hU : IsOpen U) {p : Coord} (hpV : p ∈ V) (hpU : p ∈ U)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) (k : ℕ) {B P E : ℝ}
    (hbase : ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ B)
    (hpulse : ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤ P)
    (herror : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) p‖ ≤ E) :
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ B+P+E := by
  have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  have hbs := (hgStar.1 i j).contDiffAt (hV.mem_nhds hpV)
  have hgs := (hgTau.1 i j).contDiffAt (hU.mem_nhds hpU)
  have hts : ContDiffAt ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) p :=
    hbs.add hps.contDiffAt
  have hsplit := iteratedFDeriv_add_apply (i := k)
    (hbs.of_le (WithTop.coe_le_coe.mpr le_top))
    (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  have htest : ‖iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p‖ ≤ B+P := by
    change ‖iteratedFDeriv ℝ k ((fun q => gStar q i j)+
      (fun q => pulseTensor q0 a N delta tau q i j)) p‖ ≤ _
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hbase hpulse)
  have hsub := iteratedFDeriv_sub_apply (i := k)
    (hgs.of_le (WithTop.coe_le_coe.mpr le_top))
    (hts.of_le (WithTop.coe_le_coe.mpr le_top))
  change ‖iteratedFDeriv ℝ k ((fun q => gTau q i j)-
    (fun q => testMetric gStar q0 a N delta tau q i j)) p‖ ≤ E at herror
  rw [hsub] at herror
  calc
    _ = ‖(iteratedFDeriv ℝ k (fun q => gTau q i j) p-
          iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p)+
          iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p‖ := by
            rw [sub_add_cancel]
    _ ≤ E+(B+P) := (norm_add_le _ _).trans (add_le_add herror htest)
    _ = B+P+E := by ring

theorem exists_low_metric_budget_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) (m : ℕ) :
    ∃ G : ℝ, 0 < G ∧
      (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, m < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop, m ≤ tau ∧
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            ∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G := by
  obtain ⟨B,hB,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  refine ⟨B+2,by linarith,?_,?_⟩
  · intro i j k hk p hp
    exact (hbase i j k hk p hp).trans (by linarith)
  intro q0 a ha N hmN delta
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha m N hmN delta
    (by norm_num : (0 : ℝ)<1),eventually_ge_atTop m] with tau hsmall hmtau
  refine ⟨hmtau,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  have hb := metric_jet_norm_le_from_actual_pulse_approximation hgStar hgTau hV hU
    (hSV hp) (hSU hp) q0 a N delta (tau : ℝ) i j k (hbase i j k hk p hp)
      (hsmall.2 i j k hk p) (happ i j k (hk.trans hmtau) p hp)
  exact hb.trans (by linarith [metricApproximationAccuracy_le_one hsmall.1])

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise
namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_moment_positive_lower
    (B Bcompare BQ D A Dref Cref : ℝ) {d dcompare c e : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c) (he : 0 < e)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ c3 H Cfirst Ctest Ccompare : ℝ,
      0 < c3 ∧ 0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, 0 ≤ epsilon → 0 ≤ epsilonQ →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            epsilon ≤ tau/tau^N → epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau →
            (∀ p ∈ pulseStrip a delta tau,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p) →
            (∀ p ∈ pulseStrip a delta tau,
              covHessian (metricInShearCoordinates gTau q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0) →
            (∀ p ∈ pulseStrip a delta tau,
              e ≤ heightEnergy (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p) →
            (∀ p ∈ pulseStrip a delta tau, (metricInShearCoordinates gStar q0 p).det ≤ Dref) →
            (∀ p ∈ pulseStrip a delta tau,
              |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0| ≤ Cref) →
            c3*delta*tau/tau^N ≤
              |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| := by
  obtain ⟨c3,H,Cfirst,Ctest,Ccompare,hc3,hH,hCf,hCt,hCc,hbase⟩ :=
    exists_actual_Q_moment_lower_with_remainder B Bcompare BQ D A Dref Cref
      hd hdcompare hc he hD hA ha N hN
  refine ⟨c3/2,H,Cfirst,Ctest,Ccompare,half_pos hc3,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨Tbase,hTbase,hbaseT⟩ := hbase delta hdelta
  obtain ⟨Tabs,_,habs⟩ := qMoment_budget_absorption_threshold ha hc3 hA hCf hCt hCc N delta hdelta.le
  refine ⟨max Tbase Tabs,hTbase.trans (le_max_left _ _),?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ heps hepsQ
    heps1 hesmall hepsQ1 hepsQsmall hxxsmall heScale heQScale hpoint hxxTau hE hdetup hxxup
  have hbase' := hbaseT tau ((le_max_left _ _).trans ht) gStar gTau q0 U hgStar hgTest hgTau hU z hz
    epsilon epsilonQ heps hepsQ heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint hxxTau hE hdetup hxxup
  have habs' := habs tau ((le_max_right _ _).trans ht) epsilon epsilonQ heScale heQScale
  have hhalf : (c3/2)*delta*tau/tau^N = (c3*delta*tau/tau^N)/2 := by ring
  rw [hhalf] at habs' ⊢
  linarith

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor

theorem actualComparisonSource_moment {gStar gTau : MetricField} {z P : Coord → ℝ}
    {q0 a delta tau : ℝ}
    (hQ : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau))
    (hP : ContinuousOn (qResidual (metricInShearCoordinates gStar q0) P)
      (pulseStrip a delta tau)) :
    pulseWeightedMoment a delta tau (actualComparisonSource gStar gTau z q0 P) =
      pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P) :=
  pulseWeightedMoment_sub hQ hP

theorem actualComparisonSource_moment_triangle {gStar gTau : MetricField} {z P : Coord → ℝ}
    {q0 a delta tau : ℝ}
    (hQ : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau))
    (hP : ContinuousOn (qResidual (metricInShearCoordinates gStar q0) P)
      (pulseStrip a delta tau)) :
    |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| -
      |pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| ≤
        |pulseWeightedMoment a delta tau (actualComparisonSource gStar gTau z q0 P)| := by
  rw [actualComparisonSource_moment hQ hP]
  have ht : |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| ≤
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| +
      |pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| := by
    calc
      _ = |(pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0) -
        pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)) +
          pulseWeightedMoment a delta tau (qResidual (metricInShearCoordinates gStar q0) P)| := by
            congr 1
            ring
      _ ≤ _ := abs_add_le _ _
  linarith

theorem taylor_moment_absorption_threshold {R c3 : ℝ}
    (hR : 0 ≤ R) (hc3 : 0 < c3) (N : ℕ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ delta : ℝ, 0 ≤ delta →
      R*delta/tau^(N+1) ≤ (c3/2)*delta*tau/tau^N := by
  refine ⟨max 1 (2*R/c3),le_max_left _ _,?_⟩
  intro tau ht delta hdelta
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have hthreshold : 2*R/c3 ≤ tau := (le_max_right _ _).trans ht
  have hh := (div_le_iff₀ hc3).mp hthreshold
  have hcoeff : R/tau ≤ (c3/2)*tau := by
    calc
      R/tau ≤ R := div_le_self hR ht1
      _ ≤ (c3/2)*tau := by linarith only [hh]
  have hscale : 0 ≤ delta/tau^N := div_nonneg hdelta (pow_nonneg htpos.le N)
  calc
    _ = (R/tau)*(delta/tau^N) := by rw [pow_succ]; field_simp [htpos.ne']
    _ ≤ ((c3/2)*tau)*(delta/tau^N) := mul_le_mul_of_nonneg_right hcoeff hscale
    _ = _ := by ring

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
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Pulse

theorem actual_det_upper_of_entry_bound (g : MetricField) (p : Coord) {G : ℝ}
    (hG : 0 ≤ G) (hg : ∀ i j, |g p i j| ≤ G) : (g p).det ≤ 2*G^2 := by
  rw [Matrix.det_fin_two]
  calc
    g p 0 0*g p 1 1-g p 0 1*g p 1 0 ≤
        |g p 0 0*g p 1 1|+|g p 0 1*g p 1 0| := by
      linarith [le_abs_self (g p 0 0*g p 1 1),
        neg_le_abs (g p 0 1*g p 1 0)]
    _ = |g p 0 0| *|g p 1 1|+|g p 0 1| *|g p 1 0| := by rw [abs_mul,abs_mul]
    _ ≤ G*G+G*G := add_le_add
      (mul_le_mul (hg 0 0) (hg 1 1) (abs_nonneg _) hG)
      (mul_le_mul (hg 0 1) (hg 1 0) (abs_nonneg _) hG)
    _ = _ := by ring

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

end SmoothLocal.Pulse

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
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem inverseShear_slab_mem_centralBox {L r q0 : ℝ} {p : Coord}
    (hL : 1 ≤ L) (hr : 0 ≤ r) (hLr : L * r ≤ 1 / 20) (hq0 : |q0| ≤ 1 / 20)
    (hx : |p 0| ≤ L * r) (hy : |p 1| ≤ r) :
    inverseShearCoordinates q0 p ∈ centralBox := by
  have hrL : r ≤ L * r := by nlinarith
  have hrsmall : r ≤ 1 / 20 := hrL.trans hLr
  have hxsmall : |p 0| ≤ 1 / 20 := hx.trans hLr
  have hprod : |q0 * p 0| ≤ (1 / 20 : ℝ) * (1 / 20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hxsmall (abs_nonneg _) (by norm_num)
  have hysmall : |p 1 - q0 * p 0| ≤ (1 / 20 : ℝ) + (1 / 20) * (1 / 20) :=
    (abs_sub _ _).trans (add_le_add (hy.trans hrsmall) hprod)
  change (fun _ => -(1 / 5 : ℝ)) ≤ inverseShearCoordinates q0 p ∧
    inverseShearCoordinates q0 p ≤ (fun _ => (1 / 5 : ℝ))
  constructor
  · intro i
    fin_cases i
    · change -(1 / 5 : ℝ) ≤ p 0
      linarith [(abs_le.mp hxsmall).1]
    · change -(1 / 5 : ℝ) ≤ p 1 - q0 * p 0
      linarith [(abs_le.mp hysmall).1]
  · intro i
    fin_cases i
    · change p 0 ≤ (1 / 5 : ℝ)
      linarith [(abs_le.mp hxsmall).2]
    · change p 1 - q0 * p 0 ≤ (1 / 5 : ℝ)
      linarith [(abs_le.mp hysmall).2]

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
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Flow SmoothLocal.Perturbation

theorem actual_first_input_norm_le {g : MetricField} {p : Coord} {G : ℝ} (hG : 0 ≤ G)
    (hvalue : ∀ i j, |g p i j| ≤ G)
    (hpartial : ∀ a i j, |coordPartial a (fun q => g q i j) p| ≤ G) :
    ‖actualCurvatureFirstInput g p‖ ≤ G := by
  change max ‖(fun i j => g p i j)‖
    ‖(fun a i j => coordPartial a (fun q => g q i j) p)‖ ≤ G
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro j
    exact hvalue i j
  · apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro j
    exact hpartial a i j

theorem sheared_first_input_norm_le_of_original_jets
    {g : MetricField} {U : Set Coord} {p : Coord} {q0 G : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : inverseShearCoordinates q0 p ∈ U)
    (hG : 0 ≤ G) (hq0 : |q0| ≤ 1)
    (hgB : ∀ i j k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun a => g a i j) (inverseShearCoordinates q0 p)‖ ≤ G) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates g q0) p‖ ≤ 8 * G := by
  have hf : ‖actualCurvatureFirstInput g (inverseShearCoordinates q0 p)‖ ≤ G := by
    apply actual_first_input_norm_le hG
    · intro i j
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hgB i j 0 (by omega)
    · intro a i j
      exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU [a] hp).trans
        (hgB i j 1 (by omega))
  have hp' : affineCoordinates 0 (inverseShearMatrix q0) p ∈ U := by
    simpa only [← inverseShearCoordinates_eq_affine] using hp
  unfold metricInShearCoordinates
  rw [actualCurvatureFirstInput_affinePullback hg hU 0 (inverseShearMatrix q0) p hp']
  exact affineFirstJetMap_norm_le_eight _ (inverseShearMatrix_entry_le_one hq0) _ hG
    (by simpa only [← inverseShearCoordinates_eq_affine] using hf)

def boundedClassShearedStateBudget (q0 : ℝ) (M : ℕ) : ℝ :=
  max 1 ((2 * (1 + |q0|))^2 * (M : ℝ))

theorem boundedClassShearedStateBudget_pos (q0 : ℝ) (M : ℕ) :
    0 < boundedClassShearedStateBudget q0 M :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem bounded_class_sheared_solution_state_bound
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ SmoothLocal.Flow.modelSquare)
    (hcoords : |p 0| ≤ 1 ∧ |p 1| ≤ 1) :
    ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ boundedClassShearedStateBudget q0 M := by
  obtain ⟨_, hadm, hjet, _, _⟩ := h
  obtain ⟨U, hU, hSU, _, hz, _, _, _, _⟩ := hadm
  have hzB : CoordinateBound z SmoothLocal.Flow.modelSquare 2 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  have hshear := SmoothLocal.Pulse.CoordinateBound.inverse_shear hzB hz hU hSU (Nat.cast_nonneg M) q0
  have hstate : ∀ i : Fin 6, |qSolutionJet (heightInShearCoordinates z q0) p i| ≤
      boundedClassShearedStateBudget q0 M := by
    intro i
    fin_cases i
    · exact hcoords.1.trans (le_max_left _ _)
    · exact hcoords.2.trans (le_max_left _ _)
    · exact (hshear [0] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [1] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [0, 0] (by norm_num) p hp).trans (le_max_right _ _)
  exact (pi_norm_le_iff_of_nonneg (boundedClassShearedStateBudget_pos q0 M).le).mpr hstate

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem metricApproximationAccuracy_le_inverse {tau : ℕ} (htau : 1 ≤ tau) :
    metricApproximationAccuracy tau ≤ 1 / (tau : ℝ) := by
  have htauR : (1 : ℝ) ≤ (tau : ℝ) := by exact_mod_cast htau
  have htauP : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htauR
  unfold metricApproximationAccuracy
  exact one_div_le_one_div_of_le htauP (le_self_pow₀ htauR (Nat.ne_of_gt htau))

theorem exists_first_error_threshold {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ tau0 : ℕ, 1 ≤ tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      8 * metricApproximationAccuracy tau ≤ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (8 / epsilon)
  refine ⟨max 1 n, le_max_left _ _, ?_⟩
  intro tau htau
  have htauN : 1 ≤ tau := (le_max_left _ _).trans htau
  have hnN : n ≤ tau := (le_max_right _ _).trans htau
  have htauR : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le (by exact_mod_cast htauN)
  have hnR : (n : ℝ) ≤ (tau : ℝ) := by exact_mod_cast hnN
  have hh : 8 < (n : ℝ) * epsilon := (div_lt_iff₀ he).mp hn
  have hb : 8 / (tau : ℝ) ≤ epsilon := (div_le_iff₀ htauR).mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_left (metricApproximationAccuracy_le_inverse htauN) (by norm_num)).trans
    (by simpa only [mul_one_div] using hb)

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem centralBox_subset_modelOpenSquare : centralBox ⊆ modelOpenSquare := by
  intro p hp
  change p 0 ∈ Ioo (-3 : ℝ) 3 ∧ p 1 ∈ Ioo (-3 : ℝ) 3
  exact ⟨⟨by linarith [hp.1 0],by linarith [hp.2 0]⟩,
    ⟨by linarith [hp.1 1],by linarith [hp.2 1]⟩⟩

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
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_forcingCoefficient_bound (B : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U : Set Coord),
      SmoothPositiveOn g U → ∀ p ∈ U,
      ‖qFirstBundle g (qSolutionJet z p)‖ ≤ B → d ≤ (g p).det →
      c ≤ |covHessian g z p 0 0| → |forcingCoefficient g z p| ≤ A := by
  obtain ⟨A,hA⟩ := (qFirstTube_isCompact B hd c).exists_bound_of_continuousOn
    (qFirstDensityFactor_contDiffOn.continuousOn.mono (qFirstTube_subset_domain B hd hc))
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro g z U hg p hp hB hdet hxx
  have hin : qFirstBundle g (qSolutionJet z p) ∈ qFirstTube B d c := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using hB
    · change d ≤ qFirstDet (qFirstBundle g (qSolutionJet z p))
      simpa only [qFirstDet_bundle,statePoint_qSolutionJet] using hdet
    · change c ≤ |qFirstXX (qFirstBundle g (qSolutionJet z p))|
      simpa only [qFirstXX_bundle,stateQDenominator_qSolutionJet] using hxx
  have hne := abs_pos.mp (hc.trans_le hxx)
  have hh := hA _ hin
  rw [qFirstDensityFactor_bundle,qMetricDensityFactor_at_height hg z hp hne,
    Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hnonneg := abs_nonneg (forcingCoefficient g z p)
  linarith [le_max_left A 0]

theorem exists_actual_curvatureDensity_bound (G : ℝ) (hG : 0 ≤ G) {d : ℝ} (hd : 0 < d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ p ∈ U,
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      d ≤ (g p).det → |curvatureDensity g p| ≤ D := by
  obtain ⟨C,hC⟩ := (curvatureFirstTube_isCompact G d).exists_bound_of_continuousOn
    (curvatureFirstFunction_contDiffOn.continuousOn.mono (curvatureFirstTube_subset_domain G hd))
  refine ⟨2*G+max C 0,by positivity,?_⟩
  intro g U hg hU p hp hjet hdet
  have hfirst : ‖actualCurvatureFirstInput g p‖ ≤ G := by
    apply actual_first_input_norm_le hG
    · intro i j
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hjet i j 0 (by norm_num)
    · intro i j k
      exact (norm_iteratedCoordPartial_le_jet (hg.1 j k) hU [i] hp).trans
        (hjet j k 1 (by norm_num))
  have hin : actualCurvatureFirstInput g p ∈ curvatureFirstTube G d :=
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hfirst,hdet⟩
  have hlow : |curvatureLowerTerm g p| ≤ max C 0 := by
    exact (hC _ hin).trans (le_max_left _ _)
  have hsecond (i j k l : Fin 2) : |coordPartial i (coordPartial j (fun q => g q k l)) p| ≤ G :=
    (norm_iteratedCoordPartial_le_jet (hg.1 k l) hU [i,j] hp).trans (hjet k l 2 (by norm_num))
  have habs : |coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p+
      coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p| ≤ 2*G :=
    (abs_add_le _ _).trans ((add_le_add (hsecond 0 0 1 1) (hsecond 1 1 0 0)).trans_eq (by ring))
  have hhalf : |(coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p+
      coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p)/2| ≤ G := by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  unfold curvatureDensity
  rw [gaussianCurvature_density_principal_part hg hU hp]
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans ((add_le_add (hsecond 0 1 0 1) hhalf).trans_eq (by ring))) hlow))

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem exists_metric_value_det_tolerance
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ d epsilon : ℝ, 0 < d ∧ 0 < epsilon ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ (g : MetricField) (p : Coord), p ∈ modelSquare →
        (∀ i j : Fin 2, |g p i j-gStar p i j| ≤ epsilon) → d ≤ (g p).det := by
  obtain ⟨B,hB,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV 0
  obtain ⟨d0,hd0,hfloor⟩ := modelSquare_isCompact.exists_forall_le'
    ((metricDet_contDiffOn hgStar).continuousOn.mono hSV)
    (fun p hp => (hgStar.2 p (hSV hp)).det_pos)
  let D := 4*B+2
  have hD : 0 < D := by dsimp [D]; positivity
  let epsilon := min 1 (d0/(2*D))
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  refine ⟨d0/2,epsilon,by positivity,he,?_,?_⟩
  · intro p hp
    exact (by linarith : d0/2 ≤ d0).trans (hfloor p hp)
  intro g p hp hclose
  have hgB : ‖gStar p‖ ≤ B := by
    apply (Matrix.norm_le_iff hB).2
    intro i j
    simpa only [norm_iteratedFDeriv_zero] using hbase i j 0 le_rfl p hp
  have hdist : ‖g p-gStar p‖ ≤ epsilon := by
    apply (Matrix.norm_le_iff he.le).2
    intro i j
    simpa only [Matrix.sub_apply,Real.norm_eq_abs] using hclose i j
  have hdetdiff := det_sub_le_small_first_distance (gStar p) (g p) hB he.le
    (min_le_left _ _) hgB hdist
  have hsmall : D*epsilon ≤ d0/2 := by
    have htwoD : (0 : ℝ) < 2*D := mul_pos (by norm_num) hD
    have h := (le_div_iff₀ htwoD).mp (min_le_right 1 (d0/(2*D)))
    change epsilon*(2*D) ≤ d0 at h
    nlinarith
  have hdif : |(g p).det-(gStar p).det| ≤ d0/2 := hdetdiff.trans hsmall
  linarith [(abs_le.mp hdif).1,hfloor p hp]

theorem exists_actual_determinant_floor_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ d : ℝ, 0 < d ∧ (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, 0 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ gTau : MetricField,
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            ∀ p ∈ modelSquare, d ≤ (gTau p).det := by
  obtain ⟨d,epsilon,hd,he,hstar,htol⟩ := exists_metric_value_det_tolerance hgStar hV hSV
  refine ⟨d,hd,hstar,?_⟩
  intro q0 a ha N hN delta
  obtain ⟨tau0,_,herror⟩ := exists_first_error_threshold (by positivity : 0 < 4*epsilon)
  have hehalf : 0 < epsilon/2 := by positivity
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N hN delta hehalf,
    eventually_ge_atTop tau0] with tau hpulse htau
  intro gTau happ p hp
  apply htol gTau p hp
  intro i j
  have herrorhalf : metricApproximationAccuracy tau ≤ epsilon/2 := by
    have h := herror tau htau
    linarith
  have hE : |gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j| ≤ epsilon/2 := by
    have hzero : |gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j| ≤
        metricApproximationAccuracy tau := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
        happ i j 0 (Nat.zero_le tau) p hp
    exact hzero.trans herrorhalf
  have hP : |pulseTensor q0 a N delta (tau : ℝ) p i j| ≤ epsilon/2 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hpulse.2 i j 0 le_rfl p
  have heq : gTau p i j-gStar p i j =
      (gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j)+
        pulseTensor q0 a N delta (tau : ℝ) p i j := by
    change gTau p i j-gStar p i j =
      (gTau p i j-(gStar p i j+pulseTensor q0 a N delta (tau : ℝ) p i j))+
        pulseTensor q0 a N delta (tau : ℝ) p i j
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add hE hP).trans_eq (by ring))

theorem exists_actual_low_metric_data_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) (m : ℕ) :
    ∃ G d : ℝ, 0 < G ∧ 0 < d ∧
      (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, m < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop, m ≤ tau ∧
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) := by
  obtain ⟨G,hG,hGstar,hjets⟩ := exists_low_metric_budget_before_pulse_parameters hgStar hV hSV m
  obtain ⟨d,hd,hdstar,hfloor⟩ := exists_actual_determinant_floor_before_pulse_parameters hgStar hV hSV
  refine ⟨G,d,hG,hd,hGstar,hdstar,?_⟩
  intro q0 a ha N hmN delta
  filter_upwards [hjets q0 a ha N hmN delta,hfloor q0 a ha N (by omega) delta]
    with tau hjetTau hfloorTau
  refine ⟨hjetTau.1,?_⟩
  intro gTau U hgTau hU hSU happ
  exact ⟨hjetTau.2 gTau U hgTau hU hSU happ,
    fun p hp => (hfloorTau gTau happ p hp).trans (le_abs_self _)⟩

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem actual_Q_approximation_eventual_margins (Bcompare BQ H : ℝ)
    {d dcompare c a : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare)
    (hc : 0 < c) (ha : 0 < a) (N : ℕ) (hN : 1 < N) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop,
      2 ≤ tau ∧ N ≤ tau ∧
      0 ≤ metricApproximationAccuracy tau ∧ metricApproximationAccuracy tau ≤ 1 ∧
      (4*max Bcompare 0+2)*metricApproximationAccuracy tau ≤ dcompare/2 ∧
      metricApproximationAccuracy tau ≤ (tau : ℝ)/(tau : ℝ)^N ∧
      0 ≤ qPulseFirstJetBudget a ha N delta (tau : ℝ) ∧
      qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ 1 ∧
      (4*max BQ 0+2)*qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ c/2 := by
  let K := 4*max Bcompare 0+2
  have hK : 0 < K := by dsimp only [K]; have hh := le_max_right Bcompare 0; linarith
  let epsilon := min 1 (dcompare/(2*K))
  have he : 0 < epsilon := lt_min (by norm_num) (div_pos hdcompare (by positivity))
  obtain ⟨tau0,_,haccurate⟩ := exists_first_error_threshold (by positivity : 0 < 8*epsilon)
  obtain ⟨T,_,hQ⟩ := qPulseFirstJetBudget_eventual_margins BQ H hd hc ha N hN delta
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [eventually_ge_atTop tau0,eventually_ge_atTop 2,eventually_ge_atTop N,hlarge]
    with tau ht0 ht2 htN ht
  have ht1 : 1 ≤ tau := by omega
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast ht1)
  have herr : metricApproximationAccuracy tau ≤ epsilon := by linarith [haccurate tau ht0]
  have hsmall : K*metricApproximationAccuracy tau ≤ dcompare/2 := by
    have heK : epsilon ≤ dcompare/(2*K) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 2*K by positivity)).mp (herr.trans heK)
    nlinarith
  exact ⟨ht2,htN,(metricApproximationAccuracy_pos (by omega)).le,
    herr.trans (min_le_left _ _),hsmall,
    approximation_budget_le_pulse_error (by omega) ht1 (by omega),
    qPulseFirstJetBudget_nonneg ha N delta htpos.le,(hQ _ ht).1,(hQ _ ht).2.1,(hQ _ ht).2.2⟩

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem metricQuadraticValue_sub_bound {A B : MetricMatrix} {v : Coord} {epsilon : ℝ}
    (he : 0 ≤ epsilon) (hv : ‖v‖ ≤ 1)
    (hAB : ∀ i j, |A i j-B i j| ≤ epsilon) :
    |metricQuadraticValue A v-metricQuadraticValue B v| ≤ 4*epsilon := by
  have hvB (i : Fin 2) : |v i| ≤ 1 := (norm_le_pi_norm v i).trans hv
  have hterm (i j : Fin 2) : |v i*(A i j-B i j)*v j| ≤ epsilon := by
    rw [abs_mul,abs_mul]
    have hleft : |v i| * |A i j-B i j| ≤ epsilon :=
      (mul_le_mul (hvB i) (hAB i j) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    exact (mul_le_mul hleft (hvB j) (abs_nonneg _) he).trans_eq (mul_one _)
  have heq : metricQuadraticValue A v-metricQuadraticValue B v =
      (v 0*(A 0 0-B 0 0)*v 0+v 0*(A 0 1-B 0 1)*v 1)+
        (v 1*(A 1 0-B 1 0)*v 0+v 1*(A 1 1-B 1 1)*v 1) := by
    simp only [metricQuadraticValue,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_add_le _ _).trans (add_le_add (hterm 0 0) (hterm 0 1)))
    ((abs_add_le _ _).trans (add_le_add (hterm 1 0) (hterm 1 1)))).trans_eq (by ring))

theorem exists_metric_positive_value_tolerance
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ p ∈ modelSquare, ∀ A : MetricMatrix,
      A.IsHermitian → (∀ i j, |A i j-gStar p i j| ≤ epsilon) → A.PosDef := by
  let T := modelSquare ×ˢ Metric.sphere (0 : Coord) 1
  have hT : IsCompact T := modelSquare_isCompact.prod (isCompact_sphere (0 : Coord) 1)
  have hcont : ContinuousOn (fun pv : Coord × Coord => metricQuadraticValue (gStar pv.1) pv.2) T := by
    intro pv hpv
    apply (metricQuadraticValue_continuousAt (fun i j =>
      (((hgStar.1 i j).contDiffAt (hV.mem_nhds (hSV hpv.1))).continuousAt.comp
        continuous_fst.continuousAt)) (fun i => by fun_prop)).continuousWithinAt
  have hpos (pv : Coord × Coord) (hpv : pv ∈ T) : 0 < metricQuadraticValue (gStar pv.1) pv.2 := by
    have hnorm : ‖pv.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hpv.2
    have hne : pv.2 ≠ 0 := by intro he; rw [he,norm_zero] at hnorm; norm_num at hnorm
    simpa only [metricQuadraticValue,star_trivial] using (hgStar.2 pv.1 (hSV hpv.1)).dotProduct_mulVec_pos hne
  obtain ⟨lambda,hlambda,hfloor⟩ := hT.exists_forall_le' hcont hpos
  refine ⟨lambda/8,by positivity,?_⟩
  intro p hp A hA hclose
  apply posDef_of_positive_on_sphere hA
  intro v hv
  have hnorm : ‖v‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hv
  have hdiff := metricQuadraticValue_sub_bound (by positivity : 0 ≤ lambda/8) hnorm.le hclose
  have hl := hfloor (p,v) ⟨hp,hv⟩
  linarith [(abs_le.mp hdiff).1]

theorem testMetric_coeff_contDiffOn {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) V := by
  have hp : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  exact (hgStar.1 i j).add hp.contDiffOn

theorem testMetric_isHermitian {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    {p : Coord} (hp : p ∈ V) : (testMetric gStar q0 a N delta tau p).IsHermitian := by
  have hT : (pulseTensor q0 a N delta tau p).IsHermitian := by
    change (pulseTensor q0 a N delta tau p)ᴴ=pulseTensor q0 a N delta tau p
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using pulseTensor_symmetric q0 a N delta tau p j i
  exact (hgStar.2 p hp).isHermitian.add hT

theorem testMetric_positive_on_modelSquare_eventually
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 0 < N) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, ∀ p ∈ modelSquare,
      (testMetric gStar q0 a N delta (tau : ℝ) p).PosDef := by
  obtain ⟨epsilon,he,hpositive⟩ := exists_metric_positive_value_tolerance hgStar hV hSV
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N hN delta he]
    with tau hpulse
  intro p hp
  apply hpositive p hp _ (testMetric_isHermitian hgStar q0 a N delta (tau : ℝ) (hSV hp))
  intro i j
  have hh := hpulse.2 i j 0 le_rfl p
  simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,testMetric,Pi.add_apply,Matrix.add_apply,
    add_sub_cancel_left] using hh

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

end SmoothLocal.Pulse

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

theorem exists_actual_Q_point_bounds_from_reference_floor
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d c kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (N : ℕ) (hN : 1 < N) :
    ∃ A D dcompare : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ 0 < dcompare ∧
      ∀ delta : ℝ, 0 < delta → ∀ᶠ tau : ℕ in atTop,
        2 ≤ tau ∧ N ≤ tau ∧
        SmoothPositiveOn (testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ)) modelOpenSquare ∧
        ∀ (gTau : MetricField) (U : Set Coord) (z : Coord → ℝ),
          SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
          BoundedAdmissibleHeight gTau M z →
          (∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            c ≤ |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0|) →
          ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            QPulsePointBounds gStar gTau z modelOpenSquare q0 (boundedClassWidth kappa M*r/16)
              delta (tau : ℝ) N (8*G) (G+1) (max (8*G) (boundedClassShearedStateBudget q0 M))
              D A d dcompare c (metricApproximationAccuracy tau)
              (qPulseFirstJetBudget (boundedClassWidth kappa M*r/16)
                (div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)) N delta (tau : ℝ)) p := by
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let BQ := max (8*G) (boundedClassShearedStateBudget q0 M)
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have ha : 0 < a := div_pos (mul_pos hL hr) (by norm_num)
  have hq1 : |q0| ≤ 1 := hq0.trans (by norm_num)
  obtain ⟨A,hA,hforce⟩ := exists_actual_forcingCoefficient_bound BQ hd hc
  obtain ⟨D,hD,hdensity⟩ := exists_actual_curvatureDensity_bound G hG hd
  obtain ⟨dcompare,epsilon,hdcompare,he,_,hdetTolerance⟩ := exists_metric_value_det_tolerance hgStar hV hSV
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  refine ⟨A,D,dcompare,hA,hD,hdcompare,?_⟩
  intro delta hdelt
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [testMetric_positive_on_modelSquare_eventually hgStar hV hSV q0 a ha N (by omega) delta,
    pulseTensor_finite_coeff_jets_eventually_small q0 a ha 1 N hN delta (by norm_num : (0 : ℝ) < 1),
    pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N (by omega) delta he,
    hwidth,eventually_ge_atTop 2,eventually_ge_atTop N] with tau hpositive hsmall hsmall0 hw ht2 htN
  let test := testMetric gStar q0 a N delta (tau : ℝ)
  have htest : SmoothPositiveOn test modelOpenSquare :=
    ⟨fun i j => (testMetric_coeff_contDiffOn hgStar q0 a N delta (tau : ℝ) i j).mono hOV,
      fun p hp => hpositive p (modelOpenSquare_subset hp)⟩
  refine ⟨ht2,htN,htest,?_⟩
  intro gTau U z hgTau hU hSU hclass hgB hdet happ href p hp
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hx : |p 0| ≤ L*r := (abs_le.mpr hp.1).trans (by linarith [mul_pos hL hr])
  have ht : |p 1| ≤ r := (abs_le.mpr hp.2).trans hbr
  have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
  have hpC := inverseShear_slab_mem_centralBox hL1 hr.le hLr hq0 hx ht
  have hpO := centralBox_subset_modelOpenSquare hpC
  have hpS := centralBox_subset_modelSquare hpC
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgTauO : SmoothPositiveOn gTau modelOpenSquare :=
    ⟨fun i j => (hgTau.1 i j).mono hOU,fun p hp => hgTau.2 p (hOU hp)⟩
  have hfirst := sheared_first_input_norm_le_of_original_jets hgStar hV (hSV hpS) hG hq1
    (fun i j k hk => hgStarB i j k (by omega) _ hpS)
  have hdetRef : d ≤ (metricInShearCoordinates gStar q0 p).det := by
    rw [metricDet_in_shear_coordinates]
    exact hdStar _ hpS
  have htestJet (i j : Fin 2) (k : ℕ) (hk : k ≤ 1) :
      ‖iteratedFDeriv ℝ k (fun q => test q i j) (inverseShearCoordinates q0 p)‖ ≤ G+1 := by
    have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j) :=
      (contDiff_apply ℝ ℝ j).comp
        ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta (tau : ℝ)))
    change ‖iteratedFDeriv ℝ k ((fun q => gStar q i j)+
      (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j)) (inverseShearCoordinates q0 p)‖ ≤ _
    rw [iteratedFDeriv_add_apply
      (((hgStar.1 i j).contDiffAt (hV.mem_nhds (hSV hpS))).of_le (WithTop.coe_le_coe.mpr le_top))
      (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
    exact (norm_add_le _ _).trans (add_le_add (hgStarB i j k (by omega) _ hpS) (hsmall.2 i j k hk _))
  have htestFirst : ‖actualCurvatureFirstInput test (inverseShearCoordinates q0 p)‖ ≤ G+1 := by
    apply actual_first_input_norm_le (by linarith)
    · intro i j
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using htestJet i j 0 (by norm_num)
    · intro i j k
      exact (norm_iteratedCoordPartial_le_jet (htest.1 j k) modelOpenSquare_isOpen [i] hpO).trans
        (htestJet j k 1 le_rfl)
  have htestDet : dcompare ≤ (test (inverseShearCoordinates q0 p)).det := by
    apply hdetTolerance _ _ hpS
    intro i j
    have hh := hsmall0.2 i j 0 le_rfl (inverseShearCoordinates q0 p)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,test,testMetric,Pi.add_apply,
      Matrix.add_apply,add_sub_cancel_left] using hh
  have herr := actual_metric_jet_approximation_inputs hgTauO htest modelOpenSquare_isOpen hpO
    (fun i j k hk => happ i j k (hk.trans ht2) _ hpS)
  have hstate : ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ boundedClassShearedStateBudget q0 M := by
    apply bounded_class_sheared_solution_state_bound hclass q0 hpS
    refine ⟨hx.trans (hLr.trans (by norm_num)),ht.trans ?_⟩
    have hrsmall : r ≤ L*r := by nlinarith
    exact hrsmall.trans (hLr.trans (by norm_num))
  have hbundle : ‖qFirstBundle (metricInShearCoordinates gStar q0)
      (qSolutionJet (heightInShearCoordinates z q0) p)‖ ≤ BQ := by
    change max ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0)
      (statePoint (qSolutionJet (heightInShearCoordinates z q0) p))‖
      ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ BQ
    rw [statePoint_qSolutionJet]
    exact max_le_max hfirst hstate
  have hbase := actual_sheared_first_jet_error_from_Ctau hgStarO htest hgTauO modelOpenSquare_isOpen
    hq1 ha (by omega : 0 < N) ht2 (by omega : N-1 ≤ tau) hpO
      (fun i j k hk => happ i j k hk _ hpS)
  have hdetTau : d ≤ (gTau (inverseShearCoordinates q0 p)).det := by
    have hh := hdet _ hpS
    rwa [abs_of_pos (hgTau.2 _ (hSU hpS)).det_pos] at hh
  have hDactual := hdensity gTau U hgTau hU _ (hSU hpS)
    (fun i j k hk => hgB i j k hk _ hpS) hdetTau
  have hAactual := hforce (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0)
    (inverseShearCoordinates q0 ⁻¹' V) (metricInShearCoordinates_smoothPositive hgStar q0)
      p (hSV hpS) hbundle hdetRef (href p hp)
  exact ⟨hpO,hfirst,hdetRef,htestFirst,htestDet,herr.1,herr.2,hbundle,href p hp,hbase,hDactual,hAactual⟩

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
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem exists_actual_finite_sheared_lower_cut_bound_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L r : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
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
            |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ C := by
  obtain ⟨C,hC,hcut⟩ := exists_actual_finite_lower_cut_bound_at_radius
    (e0 := e0) (kappa := kappa) hgStar hV hSV hG hZ hd hc hL hq0 hr hrhalf hLr hrsmall n
  refine ⟨(2*(1+|q0|))^n*C,by positivity,?_⟩
  intro N delta hdelt
  filter_upwards [hcut N delta hdelt] with tau hcutTau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happ ds hds x hx
  let S : Set Coord := {p | ∃ t : ℝ, |t| ≤ L*r ∧ p = inverseShearCoordinates q0 (boxPoint t (-r))}
  have hSU : S ⊆ U := by
    rintro p ⟨t,ht,rfl⟩
    exact hf.domainSubset (hf.squareSubset (inverseShear_lower_cut_mem_modelSquare hr hrhalf hLr hq0 ht))
  have hbound : CoordinateBound z S n C := by
    intro es hes p hp
    obtain ⟨t,ht,rfl⟩ := hp
    exact hcutTau gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happ es hes t ht
  exact SmoothLocal.Pulse.CoordinateBound.inverse_shear hbound hh.smooth hU hSU hC q0 ds hds
    (coordinatePoint x (-r)) ⟨x,hx,rfl⟩

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

theorem exists_actual_off_pulse_cauchy_bounds_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
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
  obtain ⟨A0,hA0,hcutK⟩ := exists_actual_finite_sheared_lower_cut_bound_at_radius
    (G := G) (Z := (M : ℝ)) (d := d) (c := 1/(M : ℝ)) (e0 := 1/(M : ℝ))
    (kappa := kappa) (q0 := q0) (L := L) hgStar hV hSV hG (Nat.cast_nonneg M) hd
      (one_div_pos.mpr hMR) hL hq0 hr hrhalf hLr hrsmall (max 8 (K+2))
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

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow SmoothLocal.ODE
open SmoothLocal.HighEquation SmoothLocal.Weighted SmoothLocal.Taylor SmoothLocal.Model

theorem exists_actual_class_two_sided_cauchy_bounds_at_every_radius
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ G d : ℝ, 0 < G ∧ 0 < d ∧
      (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      (∀ a : ℝ, 0 < a → ∀ N : ℕ, 10 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|)) ∧
      ∀ r : ℝ, 0 < r → r < 1/2 → boundedClassWidth kappa M*r ≤ 1/20 →
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) →
      ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 10 < N → ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B) ∧
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B) := by
  obtain ⟨G,d,hG,hd,hGstar,hdstar,hlow⟩ :=
    exists_actual_low_metric_data_before_pulse_parameters hgStar hV hSV 8
  let L := boundedClassWidth kappa M
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr hMR
  refine ⟨G,d,hG,hd,hGstar,hdstar,?_,?_⟩
  · intro a ha N hN delta
    filter_upwards [hlow q0 a ha N (by omega) delta] with tau htau
    exact htau.2
  intro r hr hrhalf hLr hrsmall K
  obtain ⟨BL,hBL,hLbound⟩ := exists_actual_off_pulse_cauchy_bounds_at_radius
    hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall K
  obtain ⟨BU,hBU,hUbound⟩ := exists_actual_upper_off_pulse_cauchy_bounds_at_radius
    hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall K
  refine ⟨BL+BU,add_nonneg hBL hBU,?_⟩
  intro N hN delta hdelt
  have ha : 0 < L*r/16 := by positivity
  filter_upwards [hlow q0 (L*r/16) ha N (by omega) delta,
    hLbound N delta hdelt,hUbound N delta hdelt] with tau hlowTau hLTau hUTau
  intro eta z hclass hcenter happ x hx n hn
  obtain ⟨U,hU,hSU,hUV,hg0U,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  have hlowActual := hlowTau.2 (perturbedMetric g0 eta.val) U hgU hU hSU happ
  have hg8 := hlowActual.1
  have hdet := hlowActual.2
  have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
    fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
    fun p hp => hbackground p (hUV hp)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  have hleft := hLTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ x hx n hn
  have hright := hUTau g0 eta U z hg0U hgU hU hSU hmodel hh hclass hg8 hdet hcenter happ x hx n hn
  have hBLsum : BL ≤ BL+BU := by
    calc
      BL = BL+0 := by ring
      _ ≤ BL+BU := add_le_add le_rfl hBU
  have hBUsum : BU ≤ BL+BU := by
    calc
      BU = 0+BU := by ring
      _ ≤ BL+BU := add_le_add hBL le_rfl
  exact ⟨⟨hleft.1.trans hBLsum,hleft.2.trans hBLsum⟩,
    ⟨hright.1.trans hBUsum,hright.2.trans hBUsum⟩⟩

end SmoothLocal.Perturbation

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

theorem exists_actual_Q_applicability_at_radius
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
    ∃ Aref A D dcompare : ℝ, 1 ≤ Aref ∧ 0 ≤ A ∧ 0 ≤ D ∧ 0 < dcompare ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        2 ≤ tau ∧ N ≤ tau ∧
        SmoothPositiveOn (testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ)) modelOpenSquare ∧
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
          ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            QPulsePointBounds gStar (perturbedMetric g0 eta.val) z modelOpenSquare q0
              (boundedClassWidth kappa M*r/16) delta (tau : ℝ) N
              (8*G) (G+1) (max (8*G) (boundedClassShearedStateBudget q0 M)) D A d dcompare
              ((boundedClassSpeed kappa M)^2/(4*(M : ℝ))) (metricApproximationAccuracy tau)
              (qPulseFirstJetBudget (boundedClassWidth kappa M*r/16)
                (div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)) N delta (tau : ℝ)) p ∧
            (1/(M : ℝ))/2 ≤ heightEnergy (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p ∧
            |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0| ≤ Aref ∧
            (metricInShearCoordinates gStar q0 p).det ≤ 2*G^2 ∧
            forcingFloor ((1/(M : ℝ))/2) (2*G^2) Aref ≤
              |forcingCoefficient (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p| ∧
            covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
              (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
  let L := boundedClassWidth kappa M
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hc : 0 < c := by
    have hh := boundedClassShearHxxFloor_pos hkappa hM
    have he : c=((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))/2 := by dsimp only [c]; ring
    rw [he]
    exact half_pos hh
  have he : 0 < (1/(M : ℝ))/2 := half_pos (one_div_pos.mpr (Nat.cast_pos.mpr hM))
  obtain ⟨_,Aref,_,hAref,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨A,D,dcompare,hA,hD,hdcompare,hpoint⟩ := exists_actual_Q_point_bounds_from_reference_floor
    hgStar hV hSV M hG hd hc hgStarB hdStar hq0 hr hLr N (by omega)
  refine ⟨Aref,A,D,dcompare,hAref,hA,hD,hdcompare,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hsegment delta hdelt hdhalf,hpoint delta hdelt,hwidth] with tau hsTau hpTau hw
  refine ⟨hpTau.1,hpTau.2.1,hpTau.2.2.1,?_⟩
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let S := pulseStrip (L*r/2) delta (tau : ℝ)
  have hs := (hsTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ).2.2
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans (by linarith [mul_pos (boundedClassWidth_pos kappa M) hr]),
      (abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hreference (p : Coord) (hp : p ∈ S) :
      c ≤ |covHessian gs zs p 0 0| ∧ |covHessian gs zs p 0 0| ≤ Aref ∧
        (1/(M : ℝ))/2 ≤ heightEnergy gs zs p := by
    have hm := hs p hp 1 (by norm_num)
    simp only [qHeightJetSegment,stateSegment_one,stateQDenominator_qSolutionJet] at hm
    have hE := hm.2.2.1
    unfold stateEnergy at hE
    rw [statePoint_qSolutionJet,stateGradient_qSolutionJet,
      jetEnergy_at_height hgs (hSV (hpS p hp)) zs] at hE
    exact ⟨hm.1,hm.2.1,hE⟩
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hQ := hpTau.2.2.2 g U z hg hU hSU hclass
    (fun i j k hk => hgB i j k (by omega)) hdet happ (fun p hp => (hreference p hp).1)
  intro p hp
  have href := hreference p hp
  have hdetup : (gs p).det ≤ 2*G^2 := by
    rw [metricDet_in_shear_coordinates]
    apply actual_det_upper_of_entry_bound gStar _ hG
    intro i j
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hgStarB i j 0 (by norm_num) _ (hpS p hp)
  have hforcing := forcingCoefficient_floor_of_reference_margins hgs (hSV (hpS p hp))
    he hc href.2.2 hdetup href.1 href.2.1
  have hactual : covHessian (metricInShearCoordinates g q0) zs p 0 0 ≠ 0 :=
    abs_pos.mp ((boundedClassShearHxxFloor_pos hkappa hM).trans_le (hgeom p hp).2.1)
  exact ⟨hQ p hp,href.2.2,href.2.1,hdetup,hforcing,hactual⟩

end SmoothLocal.Perturbation

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
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_Q_forcing_moment_at_radius
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
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
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
          c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
              (actualShearedQForcing gStar (perturbedMetric g0 eta.val) z q0)| := by
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  let e := (1/(M : ℝ))/2
  let BQ := max (8*G) (boundedClassShearedStateBudget q0 M)
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  have hc : 0 < c := by
    have hh := boundedClassShearHxxFloor_pos hkappa hM
    have heq : c=((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))/2 := by dsimp only [c]; ring
    rw [heq]
    exact half_pos hh
  have he : 0 < e := half_pos (one_div_pos.mpr (Nat.cast_pos.mpr hM))
  obtain ⟨Aref,A,D,dcompare,_,hA,hD,hdcompare,happlicable⟩ :=
    exists_actual_Q_applicability_at_radius hgStar hV hSV M hG hd hgStarB hdStar
      hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨c3,H,_,_,_,hc3,_,_,_,_,hforcing⟩ :=
    exists_actual_Q_moment_positive_lower (8*G) (G+1) BQ D A (2*G^2) Aref
      hd hdcompare hc he hD hA ha N (by omega)
  refine ⟨c3,hc3,?_⟩
  intro delta hdelt hdhalf
  obtain ⟨T,_,hforcingT⟩ := hforcing delta hdelt
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [happlicable delta hdelt hdhalf,
    actual_Q_approximation_eventual_margins (G+1) BQ H hd hdcompare hc ha N (by omega) delta,hlarge]
    with tau hactual hmarg ht
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  have hzO := hh.smooth.mono hOU
  have hpoint := hactual.2.2.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hsubset : pulseStrip a delta (tau : ℝ) ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    refine ⟨⟨?_,?_⟩,hp.2⟩ <;> dsimp only [a] at hp <;>
      linarith [hp.1.1,hp.1.2,mul_pos (boundedClassWidth_pos kappa M) hr]
  rcases hmarg with ⟨_,_,heps,heps1,hepsSmall,hepsScale,hepsQ,hepsQ1,hepsQSmall,hxxSmall⟩
  exact hforcingT (tau : ℝ) ht gStar g q0 modelOpenSquare hgStarO hactual.2.2.1 hgO
    modelOpenSquare_isOpen z hzO (metricApproximationAccuracy tau) (qPulseFirstJetBudget a ha N delta (tau : ℝ))
      heps hepsQ heps1 hepsSmall hepsQ1 hepsQSmall hxxSmall hepsScale le_rfl
      (fun p hp => (hpoint p (hsubset hp)).1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.2.2.2)
      (fun p hp => (hpoint p (hsubset hp)).2.1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.2.1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.1)

end SmoothLocal.Perturbation

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
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_comparison_moment
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, 2 < N → ∃ C Csource Cgradient c3 : ℝ,
        0 ≤ C ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧ 0 < c3 ∧
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
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ poly : Polynomial ℝ, poly.natDegree ≤ N+1 ∧ ∀ t, poly.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P) (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) ∧
            ContinuousOn (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
              |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
                (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)| := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_comparison_gradient hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N hN
  let L := boundedClassWidth kappa M
  let a := L*r/16
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  obtain ⟨C,Csource,Cgradient,hC,hCsource,hCgradient,hTaylorN⟩ := hTaylor N hN
  obtain ⟨cQ,hcQ,hQmoment⟩ := exists_actual_class_Q_forcing_moment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨Aref,A,D,dcompare,_,_,_,_,happlicable⟩ :=
    exists_actual_Q_applicability_at_radius hgStar hV hSV M hG hd hgStarB hdStar
      hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  let R := 2*C*(∫ x : ℝ, axisBump a x)
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) hC) (axisBump_integral_pos ha).le
  obtain ⟨T,_,habsorb⟩ := taylor_moment_absorption_threshold hR hcQ N
  refine ⟨C,Csource,Cgradient,cQ/2,hC,hCsource,hCgradient,half_pos hcQ,?_⟩
  intro delta hdelt hdhalf
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [hTaylorN delta hdelt hdhalf,hQmoment delta hdelt hdhalf,
    happlicable delta hdelt hdhalf,hlarge] with tau hTaylorTau hQTau hATau ht
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  have hTaylorActual := hTaylorTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hQlower := hQTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hpoint := hATau.2.2.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hsub : pulseStrip a delta (tau : ℝ) ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    refine ⟨⟨?_,?_⟩,hp.2⟩ <;> dsimp only [a] at hp <;>
      linarith [hp.1.1,hp.1.2,mul_pos (boundedClassWidth_pos kappa M) hr]
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans (hf.squareSubset.trans hf.domainSubset)
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  have hzO := hh.smooth.mono hOU
  have hSU : ∀ p ∈ pulseStrip a delta (tau : ℝ), inverseShearCoordinates q0 p ∈ modelOpenSquare :=
    fun p hp => (hpoint p (hsub hp)).1.point_mem
  have hc : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM)) (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  have hxxRef : ∀ p ∈ pulseStrip a delta (tau : ℝ), covHessian gs zs p 0 0 ≠ 0 :=
    fun p hp => abs_pos.mp (hc.trans_le (hpoint p (hsub hp)).1.referenceXX)
  have hxxActual : ∀ p ∈ pulseStrip a delta (tau : ℝ),
      covHessian (metricInShearCoordinates g q0) zs p 0 0 ≠ 0 :=
    fun p hp => (hpoint p (hsub hp)).2.2.2.2.2
  have hQc : ContinuousOn (actualShearedQForcing gStar g z q0) (pulseStrip a delta (tau : ℝ)) :=
    ((sheared_Q_on_height_contDiffOn hgO hzO modelOpenSquare_isOpen q0 hSU hxxActual).sub
      (sheared_Q_on_height_contDiffOn hgStarO hzO modelOpenSquare_isOpen q0 hSU hxxRef)).continuousOn
  have hPc : ContinuousOn (qResidual gs P) (pulseStrip a delta (tau : ℝ)) := hTaylorActual.2.2.2.2.1
  have hPres := hTaylorActual.2.2.2.2.2.1
  have htriangle := actualComparisonSource_moment_triangle hQc hPc
  have habs := habsorb (tau : ℝ) ht delta hdelt.le
  change |pulseWeightedMoment a delta (tau : ℝ) (qResidual gs P)| ≤ R*delta/(tau : ℝ)^(N+1) at hPres
  refine ⟨hTaylorActual.1,hTaylorActual.2.1,hTaylorActual.2.2.1,hTaylorActual.2.2.2.1,
    hPc,hPres,hTaylorActual.2.2.2.2.2.2.1,hTaylorActual.2.2.2.2.2.2.2,hQc.sub hPc,?_⟩
  have hhalf : (cQ/2)*delta*(tau : ℝ)/(tau : ℝ)^N =
      (cQ*delta*(tau : ℝ)/(tau : ℝ)^N)/2 := by ring
  rw [hhalf] at habs ⊢
  linarith

end SmoothLocal.Perturbation

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

theorem exists_original_class_comparison_with_low_data
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ G d r : ℝ, 0 < G ∧ 0 < d ∧ 0 < r ∧ r < 1/2 ∧
      (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      (∀ a : ℝ, 0 < a → ∀ N : ℕ, 10 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|)) ∧
      boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      (∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 10 < N → ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B) ∧
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B)) ∧
      ∀ N : ℕ, 10 < N → ∃ C Csource Cgradient c3 : ℝ,
        0 ≤ C ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧ 0 < c3 ∧
        (∀ K : ℕ, ∃ CP : ℝ, 0 ≤ CP ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
            ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
              BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
              |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                  testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              let zs := heightInShearCoordinates z q0
              let gs := metricInShearCoordinates gStar q0
              let P := taylorApproximation gs (-delta/(tau : ℝ))
                (heightCauchyValue zs (-delta/(tau : ℝ)))
                (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
              ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
              (∀ j ≤ K, ∀ p : Coord, |p 0| ≤ boundedClassWidth kappa M*r/2 →
                |p 1| ≤ delta/(tau : ℝ) → ‖iteratedFDeriv ℝ j P p‖ ≤ CP) ∧
              CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) K CP) ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let P := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ poly : Polynomial ℝ, poly.natDegree ≤ N+1 ∧ ∀ t, poly.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P) (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) ∧
            ContinuousOn (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
              |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
                (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)| := by
  obtain ⟨G,d,hG,hd,hGstar,hdstar,hlow,hcuts⟩ :=
    exists_actual_class_two_sided_cauchy_bounds_at_every_radius
      hg0 hgStar hV hSV M hkappa hM hq0 hbackground
  have hGstar2 : ∀ i j : Fin 2, ∀ k ≤ 2, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G :=
    fun i j k hk p hp => hGstar i j k (by omega) p hp
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hcomparison⟩ :=
    exists_actual_class_comparison_moment hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0
  refine ⟨G,d,r,hG,hd,hr,hrhalf,hGstar,hdstar,hlow,hLr,hrsmall,
    hcuts r hr hrhalf hLr hrsmall,?_⟩
  intro N hN
  obtain ⟨C,Csource,Cgradient,c3,hC,hCs,hCg,hc3,hcomparisonN⟩ := hcomparison N (by omega)
  refine ⟨C,Csource,Cgradient,c3,hC,hCs,hCg,hc3,?_,?_⟩
  · intro K
    obtain ⟨CP,hCP,hPjets⟩ := exists_actual_taylor_finite_jets_at_radius
      hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall N K
    refine ⟨CP,hCP,?_⟩
    intro delta hdelt hdhalf
    have ha : 0 < boundedClassWidth kappa M*r/16 :=
      div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
    filter_upwards [hPjets delta hdelt hdhalf,
      hlow (boundedClassWidth kappa M*r/16) ha N hN delta] with tau hPjetsTau hlowTau
    intro eta z hclass hcenter happ
    obtain ⟨U,hU,hSU,hUV,_,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
    obtain ⟨hg8,hdet⟩ := hlowTau (perturbedMetric g0 eta.val) U hgU hU hSU happ
    have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
      fun i j k hk p hp => hg8 i j k (by omega) p hp
    have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
      fun p hp => hbackground p (hUV hp)
    have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
    obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
      hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
    exact hPjetsTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ
  intro delta hdelt hdhalf
  have ha : 0 < boundedClassWidth kappa M*r/16 := by
    exact div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  filter_upwards [hcomparisonN delta hdelt hdhalf,
    hlow (boundedClassWidth kappa M*r/16) ha N hN delta] with tau hcTau hlowTau
  intro eta z hclass hcenter happ
  obtain ⟨U,hU,hSU,hUV,_,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  obtain ⟨hg8,hdet⟩ := hlowTau (perturbedMetric g0 eta.val) U hgU hU hSU happ
  have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
    fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
    fun p hp => hbackground p (hUV hp)
  have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  exact hcTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.exists_original_class_comparison_with_low_data := @OAI.SmoothLocal.Perturbation.exists_original_class_comparison_with_low_data
