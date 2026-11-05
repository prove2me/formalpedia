-- Prove2me | solution 1 for OAI.SmoothLocal.HighEquation.exists_finite_actual_Q_spatial_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:53:46.908794+00:00
-- url     : https://prove2.me/submissions/4894bc50-dc2a-46b9-8b6c-4319cd0f36a7

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_HighEquation_exists_Q_spatial_induction_step

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

namespace SmoothLocal.Geometry

namespace DarbouxJetCalculus

theorem coordPartial_eval (i j : Fin 2) (u : Coord) :
    coordPartial i (fun v : Coord => v j) u = if j = i then 1 else 0 := by
  simp [coordPartial, (hasFDerivAt_apply j u).fderiv, Pi.single_apply]

end DarbouxJetCalculus

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
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem inward_interval_geometry
    {xl xr a b speed radius t : ℝ} (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (hlength : 2 * speed * (b - a) < xr - xl) (ht : t ∈ Icc a b) :
    inwardLeft xl a speed t ∈ Ioo (-radius) radius ∧
    inwardRight xr a speed t ∈ Ioo (-radius) radius ∧
    inwardLeft xl a speed t < inwardRight xr a speed t ∧
    0 < xr - xl - 2 * speed * (b - a) ∧
    xr - xl - 2 * speed * (b - a) ≤
      inwardRight xr a speed t - inwardLeft xl a speed t := by
  have hinc : 0 ≤ speed * (t - a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
  have hmax := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hspeed
  have hspan : 0 ≤ speed * (b - a) := mul_nonneg hspeed (sub_nonneg.mpr hab)
  have hupper : speed * (t - a) < xr - xl := by
    linarith only [hmax, hspan, hlength]
  unfold inwardLeft inwardRight
  constructor
  · constructor
    · linarith
    · linarith only [hupper, hxr]
  constructor
  · constructor <;> linarith
  constructor
  · linarith
  constructor <;> linarith

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

theorem point_mem_shrinkingSlab {xl xr a b speed x t : ℝ}
    (ht : t ∈ Icc a b)
    (hx : x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t)) :
    coordinatePoint x t ∈ shrinkingSlab xl xr a b speed := by
  simpa [shrinkingSlab, coordinatePoint] using And.intro ht hx

theorem shrinkingSlab_subset_rectangle
    {xl xr a b speed radius lo hi : ℝ} (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius)
    (ha : a ∈ Ioo lo hi) (hb : b ∈ Ioo lo hi)
    (hlength : 2 * speed * (b - a) < xr - xl) :
    shrinkingSlab xl xr a b speed ⊆ coordinateRectangle radius lo hi := by
  intro p hp
  have hgeo := inward_interval_geometry hab hspeed hxl hxr hlength hp.1
  exact ⟨⟨hgeo.1.1.trans_le hp.2.1, hp.2.2.trans_lt hgeo.2.1.2⟩,
    ⟨ha.1.trans_le hp.1.1, hp.1.2.trans_lt hb.2⟩⟩

end SmoothLocal.Hyperbolic

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

def firstJetSliceBudget (Z widthUpper : ℝ) : ℝ≥0 :=
  (‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ))).toNNReal

theorem firstJetSliceBudget_coe (Z widthUpper : ℝ) :
    (firstJetSliceBudget Z widthUpper : ℝ≥0∞) =
      ‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ)) := by
  exact ENNReal.coe_toNNReal (by finiteness)

theorem coordinateBound_to_spatialFirstJet_L2
    {z : Coord → ℝ} {V : Set Coord} {theta left right Z widthUpper : ℝ} {N : ℕ}
    (hz : CoordinateBound z V (N + 1) Z) (hZ : 0 ≤ Z)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ V)
    (hwidth : right - left ≤ widthUpper) :
    SpatialSliceL2Bound (spatialFirstJet z) theta left right N
      (firstJetSliceBudget Z widthUpper) := by
  intro i n hn
  have hmeas : Measurable (spatialJet (spatialFirstJet z i) n) := by
    cases n with
    | zero => exact measurable_fderiv_apply_const ℝ z (Pi.single i 1)
    | succ order =>
        exact measurable_fderiv_apply_const ℝ
          (spatialJet (spatialFirstJet z i) order) (Pi.single 0 1)
  have hpoint : Continuous (fun x : ℝ => coordinatePoint x theta) := by
    unfold coordinatePoint
    fun_prop
  have hdom : ∀ᵐ x ∂volume.restrict (Icc left right),
      ‖spatialJet (spatialFirstJet z i) n (coordinatePoint x theta)‖ ≤ ‖Z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hZ]
    exact coordinateBound_spatialFirstJet hz hn i (hseg x hx)
  have hvol : volume (Icc left right) ≤ ENNReal.ofReal widthUpper := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hwidth
  calc
    _ ≤ eLpNorm (fun _ : ℝ => Z) 2 (volume.restrict (Icc left right)) :=
      eLpNorm_mono_ae hdom
    _ = ‖Z‖ₑ * (volume (Icc left right)) ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_const' Z (by norm_num) (by norm_num)]
      simp only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat]
    _ ≤ ‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ)) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hvol (by norm_num))
    _ = _ := (firstJetSliceBudget_coe Z widthUpper).symm

theorem coordinateC8_to_spatialFirstJet_L2_seven
    {z : Coord → ℝ} {V : Set Coord} {theta left right Z widthUpper : ℝ}
    (hz : CoordinateBound z V 8 Z) (hZ : 0 ≤ Z)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ V)
    (hwidth : right - left ≤ widthUpper) :
    SpatialSliceL2Bound (spatialFirstJet z) theta left right 7
      (firstJetSliceBudget Z widthUpper) :=
  coordinateBound_to_spatialFirstJet_L2 hz hZ hseg hwidth

end SmoothLocal.Hyperbolic

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

theorem sixVariableQ_contDiffAt_solutionJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sixVariableQ g) (qSolutionJet z p) :=
  (sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds (qSolutionJet_mem_domain hp hxx))

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
open SmoothLocal.Geometry

theorem metricPBundle_mapsTo_Q_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    MapsTo (metricPBundle g) (darbouxQStateDomain g U) universalMetricQDomain := by
  intro w hw
  exact ⟨metricDet_ne_zero hg hw.1,
    by simpa only [universalQDenominator_metricPBundle] using hw.2⟩

theorem metricPBundle_mem_universalQTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d c : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateQDenominator g w|) :
    metricPBundle g w ∈ universalMetricQTube (max G W) d c := by
  refine ⟨⟨?_, hdet⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      metricPBundle_norm_bound hg hU hw hG hgB hwB
  · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, universalQDenominator_metricPBundle] using hden

theorem actualQ_jet_bound_from_universalTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) {N : ℕ} {G W d c C : ℝ}
    (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j k, k ≤ N + 2 →
      ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|)
    (hden : c ≤ |stateQDenominator g w|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricQTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := darbouxQStateDomain_isOpen hg hU
  have hsub : darbouxQStateDomain g U ⊆ stateBaseDomain U := fun _ hv => hv.1
  have hf := (metricPBundle_contDiffOn hg hU).mono hsub
  have hmap := metricPBundle_mapsTo_Q_domain hg
  have hmem := metricPBundle_mem_universalQTube hg hU hw.1 hG
    (fun i j k hk => hgB i j k (by omega)) hwB hdet hden
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricQ universalMetricQDomain (metricPBundle g w)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricQDomain_isOpen
      (universalMetricQTube_subset_domain (max G W) hd hc hmem)]
    exact hC i (hi.trans hn) (metricPBundle g w) hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricPBundle g) (darbouxQStateDomain g U) w‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hw]
    exact (metricPBundle_positive_jet_bound hg hU hw.1 hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricQ_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hw ho hi
  have heq : iteratedFDerivWithin ℝ n (sixVariableQ g) (darbouxQStateDomain g U) w =
      iteratedFDerivWithin ℝ n (universalMetricQ ∘ metricPBundle g) (darbouxQStateDomain g U) w :=
    iteratedFDerivWithin_congr (fun _ hv => sixVariableQ_eq_universalMetricQ hg hU hv.1) hw n
  rw [iteratedFDerivWithin_of_isOpen n hD hw] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_metric_Q_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ w : DarbouxState,
      statePoint w ∈ U →
      (∀ i j k, k ≤ N + 2 →
        ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → d ≤ |(g (statePoint w)).det| → c ≤ |stateQDenominator g w| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCP⟩ := universalMetricQTube_finite_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU w hw hgB hwB hdet hden n hn
  have hne : stateQDenominator g w ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hb := actualQ_jet_bound_from_universalTube hg hU ⟨hw, hne⟩ hG hd hc hgB hwB hdet hden hCP hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

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

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem SpatialSliceL2Bound.mono_order_budget
    {ι : Type*} {F : ι → Coord → ℝ} {theta left right : ℝ}
    {N n : ℕ} {H H' : ℝ≥0}
    (h : SpatialSliceL2Bound F theta left right N H) (hn : n ≤ N) (hH : H ≤ H') :
    SpatialSliceL2Bound F theta left right n H' := by
  intro i k hk
  exact (h i k (hk.trans hn)).trans (by exact_mod_cast hH)

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

theorem second_fderiv_comp_constant_coordinate
    {F : DarbouxState → ℝ} {J : Coord → DarbouxState} {p : Coord}
    (hF : ContDiffAt ℝ ∞ F (J p)) (hJ : DifferentiableAt ℝ J p)
    (j : Fin 2) (v : DarbouxState) :
    iteratedFDeriv ℝ 2 F (J p) ![coordPartial j J p, v] =
      coordPartial j (fun r => fderiv ℝ F (J r) v) p := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (J p) :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun r => fderiv ℝ F (J r)) p := hdF.comp p hJ
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold coordPartial
  have hcomp : fderiv ℝ (fun r => fderiv ℝ F (J r)) p =
      (fderiv ℝ (fderiv ℝ F) (J p)).comp (fderiv ℝ J p) := by
    exact fderiv_comp p hdF hJ
  rw [fderiv_clm_apply hc (differentiableAt_const (c := v)), hcomp]
  simp

theorem heightQCoefficient_partial_eq_second
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) (i : Fin 6) (j : Fin 2) :
    coordPartial j (heightQCoefficient g z i) p =
      iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)
        ![coordPartial j (qSolutionJet z) p, Pi.single i 1] := by
  exact (second_fderiv_comp_constant_coordinate
    (sixVariableQ_contDiffAt_solutionJet hg hU hp hxx)
    (((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    j (Pi.single i 1)).symm

theorem heightQCoefficient_value_bound {g : MetricField} {z : Coord → ℝ}
    {p : Coord} {C : ℝ}
    (hQ : ‖iteratedFDeriv ℝ 1 (sixVariableQ g) (qSolutionJet z p)‖ ≤ C) (i : Fin 6) :
    |heightQCoefficient g z i p| ≤ C := by
  change ‖fderiv ℝ (sixVariableQ g) (qSolutionJet z p) (Pi.single i 1)‖ ≤ C
  have hb := (fderiv ℝ (sixVariableQ g) (qSolutionJet z p)).le_opNorm (Pi.single i 1)
  simp only [Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (by simpa only [norm_iteratedFDeriv_one] using hQ)

theorem heightQCoefficient_partial_bound_of_second
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord} {Z C : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : S ⊆ U) (hzB : CoordinateBound z S 3 Z) (hC : 0 ≤ C)
    {p : Coord} (hp : p ∈ S) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : ‖iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)‖ ≤ C)
    (i : Fin 6) (j : Fin 2) :
    |coordPartial j (heightQCoefficient g z i) p| ≤ C * max 1 Z := by
  rw [heightQCoefficient_partial_eq_second hg hU hz (hSU hp) hxx i j, ← Real.norm_eq_abs]
  have hd := coordPartial_qSolutionJet_norm_bound hU hz hSU hzB hp j
  have hb := (iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)).le_opNorm
    ![coordPartial j (qSolutionJet z) p, Pi.single i (1 : ℝ)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (mul_le_mul hQ hd (norm_nonneg _) hC)

theorem exists_same_region_Q_low_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, ∀ p ∈ S,
        |heightQCoefficient g z i p| ≤ M ∧
          ∀ j : Fin 2, |coordPartial j (heightQCoefficient g z i) p| ≤ M := by
  obtain ⟨C, hC, hQ⟩ := exists_local_metric_Q_jet_bound G (max R Z) hG hd hc 2
  refine ⟨C * max 1 Z, mul_nonneg hC (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden i p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have hpoint := statePoint_qSolutionJet z p
  have hb (n : ℕ) (hn : n ≤ 2) :
      ‖iteratedFDeriv ℝ n (sixVariableQ g) (qSolutionJet z p)‖ ≤ C :=
    hQ g U hg hU (qSolutionJet z p) (by simpa only [hpoint] using hSU hp)
      (fun a b k hk => by simpa only [hpoint] using hgB a b k (by omega) p hp)
      (qSolutionJet_norm_bound_of_coordinateBound hR hz2 hcoords hp)
      (by simpa only [hpoint] using hdet p hp)
      (by simpa only [stateQDenominator_qSolutionJet] using hden p hp) n hn
  refine ⟨(heightQCoefficient_value_bound (hb 1 (by omega)) i).trans ?_, ?_⟩
  · exact le_mul_of_one_le_right hC (le_max_left _ _)
  · intro j
    exact heightQCoefficient_partial_bound_of_second hg hU hz hSU hzB hC hp hxx (hb 2 le_rfl) i j

theorem exists_same_region_Q_low_bound_of_coordinate
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) S 4 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, ∀ p ∈ S,
        |heightQCoefficient g z i p| ≤ M ∧
          ∀ j : Fin 2, |coordPartial j (heightQCoefficient g z i) p| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_same_region_Q_low_bound (16 * G) R Z (by positivity) hR hd hc
  refine ⟨M, hM, ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden
  apply hbound g z U S hg hU hz hSU hcoords ?_ hzB hdet hden
  intro i j k hk p hp
  have hb := (hgB i j).full_jet_norm_bound (hg.1 i j) hU hSU hG hk hp
  have hpow : (2 : ℝ)^k ≤ 16 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at hh ⊢
    exact hh
  exact hb.trans (mul_le_mul_of_nonneg_right hpow hG)

theorem exists_actual_QLowBounds
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) S 4 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ s0 speed : ℝ,
      (∀ p ∈ S, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ S, |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      QLowBounds g z S s0 M speed := by
  obtain ⟨M, hM, hbound⟩ := exists_same_region_Q_low_bound_of_coordinate G R Z hG hR hd hc
  refine ⟨M, hM, ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden s0 speed hs hspeed p hp
  have hb := hbound g z U S hg hU hz hSU hcoords hgB hzB hdet hden
  exact ⟨hs p hp, (hb 2 p hp).1, (hb 3 p hp).1, (hb 5 p hp).1,
    (hb 4 p hp).2 0, (hb 5 p hp).2 0, (hb 5 p hp).2 1, hspeed p hp⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_Q_spatial_induction_offset
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∀ k : ℕ, ∃ H : ℝ≥0,
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (k + 9) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ k + 8 → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (k + 7) H := by
  intro k
  induction k with
  | zero =>
      refine ⟨firstJetSliceBudget Z (xr - xl), ?_⟩
      intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords hgB hzB hdet hden hcut t ht
      apply coordinateC8_to_spatialFirstJet_L2_seven hzB hZ
        (fun x hx => point_mem_shrinkingSlab ht hx)
      unfold inwardLeft inwardRight
      have hh : 0 ≤ speed * (t - a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
      linarith
  | succ k ih =>
      obtain ⟨Hprev, hprev⟩ := ih
      obtain ⟨Hnew, hle, hstep⟩ := exists_Q_spatial_induction_step
        G R Z s0 M speed xl xr T lengthFloor Hprev A hG hR hs0 hM hspeed hT hlen hwidth
        hd hc (k + 5) (by omega)
      refine ⟨Hnew, ?_⟩
      intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords hgB hzB hdet hden hcut t ht
      have hold : ∀ v ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) v
          (inwardLeft xl a speed v) (inwardRight xr a speed v) (k + 7) Hprev :=
        hprev g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
          hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
          (fun ds hds x hx => hcut ds (by omega) x hx)
      have hnew := hstep g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
        (fun ds hds x hx => hcut ds (by omega) x hx)
        (by simpa only [Nat.add_assoc] using hold) t ht
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hnew

theorem exists_finite_Q_spatial_bound
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ H : ℝ≥0,
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 2)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 1) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) N H := by
  obtain ⟨H, hH⟩ := exists_Q_spatial_induction_offset
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc (N - 7)
  refine ⟨H, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut t ht
  have hmetricOrder : N - 7 + 9 ≤ max 9 (N + 2) := by omega
  have hcutOrder : N - 7 + 8 ≤ max 8 (N + 1) := by omega
  have hb := hH g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords (fun i j => (hgB i j).mono hmetricOrder le_rfl) hzB hdet hden
    (fun ds hds x hx => hcut ds (hds.trans hcutOrder) x hx) t ht
  exact SpatialSliceL2Bound.mono_order_budget hb (by omega) le_rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_finite_Q_spatial_pointwise_bound
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 3)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 2) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
        ∀ i : Fin 2, ∀ n ≤ N,
          |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B := by
  obtain ⟨H, hH⟩ := exists_finite_Q_spatial_bound
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc (N + 1)
  refine ⟨Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ), by positivity, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut t ht x hx i n hn
  have hnorm := hH g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
    (fun ds hds x hx => hcut ds (by omega) x hx) t ht
  have hU := coordinateRectangle_isOpen radius lo hi
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hlength_t : lengthFloor ≤ inwardRight xr a speed t - inwardLeft xl a speed t := by
    unfold inwardLeft inwardRight
    have hd : t - a ≤ T := (sub_le_sub_right ht.2 a).trans habT
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * speed)
    linarith
  exact hnorm.pointwise_below_top hU (fun j => partial_contDiffOn hz hU j)
    (fun y hy => hSU (point_mem_shrinkingSlab ht hy)) hlen hlength_t i n (Nat.succ_le_succ hn) hx

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_finite_actual_Q_spatial_pointwise_bound
    (G R Z s0 speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      (∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ shrinkingSlab xl xr a b speed,
        |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 3)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 2) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
        ∀ i : Fin 2, ∀ n ≤ N,
          |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B := by
  obtain ⟨M, hM, hlow⟩ := exists_actual_QLowBounds G R Z hG hR hd hc
  obtain ⟨B, hB, hbound⟩ := exists_finite_Q_spatial_pointwise_bound
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc N
  refine ⟨B, hB, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hs hchar hcoords hgB hzB hdet hden hcut
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hLow := hlow g z (coordinateRectangle radius lo hi) (shrinkingSlab xl xr a b speed)
    hg (coordinateRectangle_isOpen radius lo hi) hz hSU hcoords
    (fun i j => (hgB i j).mono (by omega) le_rfl)
    (hzB.mono (by norm_num) le_rfl) hdet hden s0 speed hs hchar
  exact hbound g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut

end SmoothLocal.HighEquation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.HighEquation.exists_finite_actual_Q_spatial_pointwise_bound := @OAI.SmoothLocal.HighEquation.exists_finite_actual_Q_spatial_pointwise_bound
