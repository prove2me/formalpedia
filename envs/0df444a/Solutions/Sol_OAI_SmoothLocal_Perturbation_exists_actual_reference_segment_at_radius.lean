-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.exists_actual_reference_segment_at_radius
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:17:29.267419+00:00
-- url     : https://prove2.me/submissions/c0a8cf98-7c80-4861-af15-305ec6c5c583

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Taylor_taylorApproximation_properties
import Theorems.Thm_OAI_SmoothLocal_Taylor_linearCauchy_height_initial_state
import Theorems.Thm_OAI_SmoothLocal_Perturbation_actual_central_sheared_solution_margins
import Theorems.Thm_OAI_SmoothLocal_Pulse_exists_bounded_patch_reference_initial_floor
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_taylor_finite_jets_at_radius

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

theorem boxPoint_hasDerivAt_s (t s : ℝ) :
    HasDerivAt (boxPoint t) (Pi.single 1 (1 : ℝ) : Coord) s := by
  change HasDerivAt (fun x : ℝ => t • (Pi.single 0 (1 : ℝ) : Coord) +
    x • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) s
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id s).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (t • (Pi.single 0 (1 : ℝ) : Coord))

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

theorem solvedDarbouxQ_deriv_b (g : MetricField) (p u : Coord) (b c : ℝ)
    (_hne : jetXX g p c u ≠ 0) :
    deriv (fun t => solvedDarbouxQ g p t c u) b =
      2 * (jetMixed g p b u / jetXX g p c u) := by
  have hd := (((((hasDerivAt_id b).sub_const (jetConnection g p 0 1 u)).pow 2).add_const
    (gaussianCurvature g p * jetEnergy g p u)).div_const (jetXX g p c u)).const_add
      (jetConnection g p 1 1 u)
  simp only [Pi.pow_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 1 1 u +
    ((t - jetConnection g p 0 1 u) ^ 2 + gaussianCurvature g p * jetEnergy g p u) /
      jetXX g p c u) b = _
  rw [hd.deriv]
  simp only [jetMixed, mul_one]
  ring

theorem solvedDarbouxQ_deriv_c (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetXX g p c u ≠ 0) :
    deriv (fun t => solvedDarbouxQ g p b t u) c =
      -((jetMixed g p b u / jetXX g p c u) ^ 2 +
        gaussianCurvature g p * jetEnergy g p u / (jetXX g p c u) ^ 2) := by
  have hdH := (hasDerivAt_id c).sub_const (jetConnection g p 0 0 u)
  have hd := ((hasDerivAt_const c (jetNumerator g p b u)).div hdH hne).const_add
    (jetConnection g p 1 1 u)
  simp only [Pi.div_apply, id_eq] at hd
  change deriv (fun t => jetConnection g p 1 1 u +
    jetNumerator g p b u / (t - jetConnection g p 0 0 u)) c = _
  rw [hd.deriv]
  change (0 * jetXX g p c u - jetNumerator g p b u * 1) / (jetXX g p c u) ^ 2 = _
  simp only [jetNumerator]
  field_simp [hne]
  ring

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

theorem sixVariableQ_update_mixed {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (t : ℝ) :
    sixVariableQ g (Function.update w 4 t) =
      solvedDarbouxQ g (statePoint w) t (w 5) (stateGradient w) := by
  have hp : statePoint (Function.update w 4 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 4 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  rw [sixVariableQ_explicit hg hU (by simpa only [hp] using hw), hp, hv]
  simp

theorem sixVariableQ_update_xx {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (t : ℝ) :
    sixVariableQ g (Function.update w 5 t) =
      solvedDarbouxQ g (statePoint w) (w 4) t (stateGradient w) := by
  have hp : statePoint (Function.update w 5 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 5 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  rw [sixVariableQ_explicit hg hU (by simpa only [hp] using hw), hp, hv]
  simp

theorem sixVariableQ_mixed_axis {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    fderiv ℝ (sixVariableQ g) w (Pi.single 4 1) =
      2 * (stateMixed g w / stateQDenominator g w) := by
  have hd := ((sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableQ g (Function.update w 4 t)) =
      (fun t => solvedDarbouxQ g (statePoint w) t (w 5) (stateGradient w)) :=
    funext (sixVariableQ_update_mixed hg hU hw.1)
  rw [heq, solvedDarbouxQ_deriv_b g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2]
  rfl

theorem sixVariableQ_xx_axis {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    fderiv ℝ (sixVariableQ g) w (Pi.single 5 1) =
      -((stateMixed g w / stateQDenominator g w) ^ 2 +
        gaussianCurvature g (statePoint w) * stateEnergy g w / (stateQDenominator g w) ^ 2) := by
  have hd := ((sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableQ g (Function.update w 5 t)) =
      (fun t => solvedDarbouxQ g (statePoint w) (w 4) t (stateGradient w)) :=
    funext (sixVariableQ_update_xx hg hU hw.1)
  rw [heq, solvedDarbouxQ_deriv_c g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2]
  rfl

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

theorem q_principal_discriminant {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    (qFirstCoefficient g 4 w / 2) ^ 2 + qFirstCoefficient g 5 w =
      -(gaussianCurvature g (statePoint w) * stateEnergy g w) / (stateQDenominator g w) ^ 2 := by
  unfold qFirstCoefficient
  rw [sixVariableQ_mixed_axis hg hU hw, sixVariableQ_xx_axis hg hU hw]
  ring

theorem hessian_time_ratio {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    (hessianQuotient g z p) ^ 2 + gaussianCurvature g p * darbouxG g z p =
      covHessian g z p 0 0 / covHessian g z p 1 1 := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold hessianQuotient darbouxG
  field_simp [hyy]
  nlinarith [hdet]

end SmoothLocal.HighEquation

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

theorem state_distance_le_of_coordinate_error {w0 w1 : DarbouxState} {epsilon : ℝ}
    (heps : 0 ≤ epsilon) (hjet : ∀ i : Fin 6, |w1 i - w0 i| ≤ epsilon) :
    ‖w1 - w0‖ ≤ epsilon := by
  apply (pi_norm_le_iff_of_nonneg heps).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hjet i

theorem qSolutionJet_coordinate_error (z0 z : Coord → ℝ) (p : Coord) {epsilon : ℝ}
    (heps : 0 ≤ epsilon)
    (hgrad : ∀ i : Fin 2, |coordPartial i z p - coordPartial i z0 p| ≤ epsilon)
    (hmixed : |coordPartial 0 (coordPartial 1 z) p -
      coordPartial 0 (coordPartial 1 z0) p| ≤ epsilon)
    (hxx : |coordPartial 0 (coordPartial 0 z) p -
      coordPartial 0 (coordPartial 0 z0) p| ≤ epsilon) :
    ∀ i : Fin 6, |qSolutionJet z p i - qSolutionJet z0 p i| ≤ epsilon := by
  intro i
  fin_cases i
  · simpa [qSolutionJet] using heps
  · simpa [qSolutionJet] using heps
  · exact hgrad 0
  · exact hgrad 1
  · exact hmixed
  · exact hxx

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
open Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qCoefficient_segment_continuousOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContinuousOn (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) (Icc (0 : ℝ) 1) :=
  (qFirstCoefficient_contDiffOn hg hU i).continuousOn.comp
    (stateSegment_continuous w0 w1).continuousOn (fun t ht => hsegment t ht)

theorem averagedQCoefficient_lower {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U)
    (i : Fin 6) {gamma : ℝ}
    (hgamma : ∀ sigma ∈ Icc (0 : ℝ) 1, gamma ≤ qFirstCoefficient g i (stateSegment w0 w1 sigma)) :
    gamma ≤ averagedQCoefficient g w0 w1 i := by
  have hi : IntervalIntegrable
      (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) volume (0 : ℝ) 1 :=
    (qCoefficient_segment_continuousOn hg hU hsegment i).intervalIntegrable_of_Icc zero_le_one
  have hc : IntervalIntegrable (fun _ : ℝ => gamma) volume (0 : ℝ) 1 := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on zero_le_one hc hi hgamma
  simpa [averagedQCoefficient] using h

theorem averagedQPrincipal_margin {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) {gamma : ℝ}
    (hgamma : ∀ sigma ∈ Icc (0 : ℝ) 1,
      gamma ≤ qFirstCoefficient g 5 (stateSegment w0 w1 sigma)) :
    gamma ≤ averagedQCoefficient g w0 w1 5 ∧
      gamma ≤ (averagedQCoefficient g w0 w1 4 / 2) ^ 2 + averagedQCoefficient g w0 w1 5 := by
  have h := averagedQCoefficient_lower hg hU hsegment 5 hgamma
  exact ⟨h, by nlinarith [sq_nonneg (averagedQCoefficient g w0 w1 4 / 2)]⟩

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
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem inverseShearMatrix_entry_le_one {q0 : ℝ} (hq : |q0| ≤ 1) (i j : Fin 2) :
    |inverseShearMatrix q0 i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [inverseShearMatrix,hq]

end SmoothLocal.Pulse

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
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

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
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem metricInShearCoordinates_sub (g h : MetricField) (q0 : ℝ) :
    metricInShearCoordinates (fun p => g p-h p) q0 =
      fun p => metricInShearCoordinates g q0 p-metricInShearCoordinates h q0 p := by
  funext p
  ext i j
  simp only [metricInShearCoordinates,affinePullbackMetric,Matrix.mul_apply,
    Matrix.transpose_apply,Matrix.sub_apply,Fin.sum_univ_two]
  ring

theorem sheared_metric_full_jet_bound {g : MetricField} {U : Set Coord}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U) (hU : IsOpen U)
    {q0 B : ℝ} (hq0 : |q0| ≤ 1) (hB : 0 ≤ B) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (n : ℕ)
    (hjet : ∀ i j, ‖iteratedFDeriv ℝ n (fun q => g q i j) (inverseShearCoordinates q0 p)‖ ≤ B)
    (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun q => metricInShearCoordinates g q0 q i j) p‖ ≤ 4*2^n*B := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  let c (a b : Fin 2) := inverseShearMatrix q0 a i*inverseShearMatrix q0 b j
  let f (a b : Fin 2) := heightInShearCoordinates (fun q => g q a b) q0
  let term (a b : Fin 2) : Coord → ℝ := fun q => c a b*f a b q
  have hfs (a b : Fin 2) : ContDiffOn ℝ ∞ (f a b) V :=
    heightInShearCoordinates_contDiffOn (hg a b) q0
  have hts (a b : Fin 2) : ContDiffAt ℝ n (term a b) p :=
    ((contDiffOn_const.mul (hfs a b)).contDiffAt (hV.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hc (a b : Fin 2) : |c a b| ≤ 1 := by
    dsimp only [c]
    rw [abs_mul]
    exact (mul_le_mul (inverseShearMatrix_entry_le_one hq0 a i)
      (inverseShearMatrix_entry_le_one hq0 b j) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hnormL : ‖inverseShearCLM q0‖ ≤ 2 := (inverseShearCLM_norm_le q0).trans (by linarith)
  have htB (a b : Fin 2) : ‖iteratedFDeriv ℝ n (term a b) p‖ ≤ B*2^n := by
    have hchain := local_linear_full_jet_norm_bound (hg a b) hU (inverseShearCLM q0) hp n
    have hfB : ‖iteratedFDeriv ℝ n (f a b) p‖ ≤ B*2^n := by
      exact hchain.trans (mul_le_mul (hjet a b)
        (pow_le_pow_left₀ (norm_nonneg _) hnormL n) (pow_nonneg (norm_nonneg _) n) hB)
    change ‖iteratedFDeriv ℝ n ((c a b) • f a b) p‖ ≤ B*2^n
    rw [iteratedFDeriv_const_smul_apply
      (((hfs a b).contDiffAt (hV.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)),norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hc a b) hfB (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  rw [metricInShearCoordinates_four_terms]
  change ‖iteratedFDeriv ℝ n ((term 0 0+term 0 1)+(term 1 0+term 1 1)) p‖ ≤ _
  rw [iteratedFDeriv_add_apply (f := term 0 0+term 0 1) (g := term 1 0+term 1 1)
      ((hts 0 0).add (hts 0 1)) ((hts 1 0).add (hts 1 1)),
    iteratedFDeriv_add_apply (hts 0 0) (hts 0 1),iteratedFDeriv_add_apply (hts 1 0) (hts 1 1)]
  calc
    _ ≤ (B*2^n+B*2^n)+(B*2^n+B*2^n) := (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add (htB 0 0) (htB 0 1)))
        ((norm_add_le _ _).trans (add_le_add (htB 1 0) (htB 1 1))))
    _ = _ := by ring

theorem sheared_metric_full_jet_difference_le {g h : MetricField} {U : Set Coord}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun p => h p i j) U) (hU : IsOpen U)
    {q0 epsilon : ℝ} (hq0 : |q0| ≤ 1) (he : 0 ≤ epsilon) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (n : ℕ)
    (hjet : ∀ i j, ‖iteratedFDeriv ℝ n (fun q => g q i j-h q i j)
      (inverseShearCoordinates q0 p)‖ ≤ epsilon) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun q => metricInShearCoordinates g q0 q i j-
      metricInShearCoordinates h q0 q i j) p‖ ≤ 4*2^n*epsilon := by
  have hb := sheared_metric_full_jet_bound
    (g := fun q => g q-h q) (fun a b => (hg a b).sub (hh a b)) hU hq0 he hp n hjet i j
  simpa only [metricInShearCoordinates_sub,Matrix.sub_apply] using hb

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
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def universalQDenominator (a : MetricPInput) : ℝ :=
  a.2.2.2 5 - universalConnection a 0 0

theorem universalQDenominator_metricPBundle (g : MetricField) (w : DarbouxState) :
    universalQDenominator (metricPBundle g w) = stateQDenominator g w := rfl

theorem universalQDenominator_contDiffOn :
    ContDiffOn ℝ ∞ universalQDenominator universalMetricBase := by
  intro a ha
  exact ((show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 5) a by fun_prop).sub
    (universalConnection_contDiffAt ha 0 0)).contDiffWithinAt

end SmoothLocal.HighEquation

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

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def universalQCurvature (a : MetricPInput) : ℝ :=
  curvatureJet a.1 a.2.1 a.2.2.1

def universalQNumerator (a : MetricPInput) : ℝ :=
  (a.2.2.2 4 - universalConnection a 0 1)^2 +
    universalQCurvature a * universalEnergy a

def universalQRaw (a : MetricPInput) : Fin 4 → ℝ :=
  ![universalQDenominator a, universalEnergy a,
    universalQNumerator a, universalQCurvature a]

theorem universalQCurvature_metricPBundle {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    universalQCurvature (metricPBundle g w) = gaussianCurvature g (statePoint w) :=
  (gaussianCurvature_eq_curvatureJet hg hU hw).symm

theorem universalQNumerator_metricPBundle {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    universalQNumerator (metricPBundle g w) = stateNumerator g w := by
  unfold universalQNumerator
  rw [universalQCurvature_metricPBundle hg hU hw, universalEnergy_metricPBundle,
    universalConnection_metricPBundle]
  rfl

theorem universalQCurvature_contDiffOn :
    ContDiffOn ℝ ∞ universalQCurvature universalMetricBase := by
  intro a ha
  exact (curvatureJet_contDiffAt (fun i j => by fun_prop)
    (fun d i j => by fun_prop) (fun d e i j => by fun_prop) ha).contDiffWithinAt

theorem universalQNumerator_contDiffOn :
    ContDiffOn ℝ ∞ universalQNumerator universalMetricBase := by
  intro a ha
  have hm : ContDiffAt ℝ ∞
      (fun b : MetricPInput => b.2.2.2 4 - universalConnection b 0 1) a :=
    (show ContDiffAt ℝ ∞ (fun b : MetricPInput => b.2.2.2 4) a by fun_prop).sub
      (universalConnection_contDiffAt ha 0 1)
  exact ((hm.pow 2).add
    ((universalQCurvature_contDiffOn.contDiffAt (universalMetricBase_isOpen.mem_nhds ha)).mul
      universalEnergy_contDiff.contDiffAt)).contDiffWithinAt

theorem universalQRaw_contDiffOn :
    ContDiffOn ℝ ∞ universalQRaw universalMetricBase := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact universalQDenominator_contDiffOn
  · exact universalEnergy_contDiff.contDiffOn
  · exact universalQNumerator_contDiffOn
  · exact universalQCurvature_contDiffOn

theorem universalQRaw_uniform_error (M : ℝ) {d error : ℝ}
    (hd : 0 < d) (he : 0 < error) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a ∈ universalMetricBaseTube M d,
      ∀ b ∈ universalMetricBaseTube M d, ‖b - a‖ ≤ epsilon →
        ∀ i : Fin 4, |universalQRaw b i - universalQRaw a i| ≤ error := by
  have hc := (universalMetricBaseTube_isCompact M d).uniformContinuousOn_of_continuous
    (universalQRaw_contDiffOn.continuousOn.mono (universalMetricBaseTube_subset_base M hd))
  obtain ⟨epsilon, hepsilon, herror⟩ := Metric.uniformContinuousOn_iff_le.mp hc error he
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a ha b hb hab i
  have hn : ‖universalQRaw b - universalQRaw a‖ ≤ error := by
    simpa only [dist_eq_norm] using herror b hb a ha (by simpa only [dist_eq_norm] using hab)
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (norm_le_pi_norm (universalQRaw b - universalQRaw a) i).trans hn

theorem universalQDenominator_uniform_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ a ∈ universalMetricBaseTube M d,
      |universalQDenominator a| ≤ A := by
  obtain ⟨C, hC⟩ := (universalMetricBaseTube_isCompact M d).exists_bound_of_continuousOn
    (universalQDenominator_contDiffOn.continuousOn.mono
      (universalMetricBaseTube_subset_base M hd))
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro a ha
  simpa only [Real.norm_eq_abs] using (hC a ha).trans (le_max_right 1 C)

theorem universalQRaw_uniform_margins (M : ℝ) {d nu eta beta kappa : ℝ}
    (hd : 0 < d) (hnu : 0 < nu) (heta : 0 < eta) (hbeta : 0 < beta)
    (hkappa : 0 < kappa) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a ∈ universalMetricBaseTube M d,
      ∀ b ∈ universalMetricBaseTube M d, ‖b - a‖ ≤ epsilon →
      nu ≤ |universalQDenominator a| → eta ≤ universalEnergy a →
      universalQNumerator a ≤ -beta → universalQCurvature a ≤ -kappa →
      nu / 2 ≤ |universalQDenominator b| ∧ eta / 2 ≤ universalEnergy b ∧
      universalQNumerator b ≤ -(beta / 2) ∧ universalQCurvature b ≤ -(kappa / 2) := by
  let error := min (nu / 2) (min (eta / 2) (min (beta / 2) (kappa / 2)))
  have he : 0 < error := lt_min (half_pos hnu)
    (lt_min (half_pos heta) (lt_min (half_pos hbeta) (half_pos hkappa)))
  obtain ⟨epsilon, hepsilon, herror⟩ := universalQRaw_uniform_error M hd he
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a ha b hb hab hden henergy hnum hK
  have h0 := herror a ha b hb hab 0
  have h1 := herror a ha b hb hab 1
  have h2 := herror a ha b hb hab 2
  have h3 := herror a ha b hb hab 3
  change |universalQDenominator b - universalQDenominator a| ≤ error at h0
  change |universalEnergy b - universalEnergy a| ≤ error at h1
  change |universalQNumerator b - universalQNumerator a| ≤ error at h2
  change |universalQCurvature b - universalQCurvature a| ≤ error at h3
  have he0 : error ≤ nu / 2 := min_le_left _ _
  have he1 : error ≤ eta / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have he2 : error ≤ beta / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he3 : error ≤ kappa / 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hdenerror := (abs_sub_abs_le_abs_sub (universalQDenominator a)
    (universalQDenominator b)).trans (by simpa only [abs_sub_comm] using h0)
  exact ⟨by linarith, by linarith [(abs_le.mp h1).1],
    by linarith [(abs_le.mp h2).2], by linarith [(abs_le.mp h3).2]⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem metricPBundle_sub_norm_bound {g g0 : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    {w w0 : DarbouxState} (hp : statePoint w = statePoint w0)
    (hw : statePoint w ∈ U) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hmetric : ∀ i j k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun p => g0 p i j - g p i j) (statePoint w)‖ ≤ epsilon)
    (hstate : ‖w0 - w‖ ≤ epsilon) :
    ‖metricPBundle g0 w0 - metricPBundle g w‖ ≤ epsilon := by
  have hwords (i j : Fin 2) (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
      |iteratedCoordPartial ds (fun p => g0 p i j) (statePoint w) -
        iteratedCoordPartial ds (fun p => g p i j) (statePoint w)| ≤ epsilon := by
    rw [← CoordinateBound.iterated_sub (hg0.1 i j) (hg.1 i j) hU ds hw]
    exact (norm_iteratedCoordPartial_le_jet ((hg0.1 i j).sub (hg.1 i j)) hU ds hw).trans
      (hmetric i j ds.length hds)
  have h0 : ‖g0 (statePoint w) - g (statePoint w)‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [] (by norm_num)
  have h1 : ‖(fun d i j => coordPartial d (fun p => g0 p i j) (statePoint w)) -
      (fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [d] (by norm_num)
  have h2 : ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g0 p i j)) (statePoint w)) -
      (fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖ ≤ epsilon := by
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro e
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact hwords i j [d, e] (by norm_num)
  change max ‖g0 (statePoint w0) - g (statePoint w)‖
    (max ‖(fun d i j => coordPartial d (fun p => g0 p i j) (statePoint w0)) -
      (fun d i j => coordPartial d (fun p => g p i j) (statePoint w))‖
      (max ‖(fun d e i j => coordPartial d (coordPartial e (fun p => g0 p i j)) (statePoint w0)) -
        (fun d e i j => coordPartial d (coordPartial e (fun p => g p i j)) (statePoint w))‖
        ‖w0 - w‖)) ≤ epsilon
  rw [← hp]
  exact max_le h0 (max_le h1 (max_le h2 hstate))

theorem metricPBundle_mem_baseTube {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) {G W d : ℝ} (hG : 0 ≤ G)
    (hgB : ∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G)
    (hwB : ‖w‖ ≤ W) (hdet : d ≤ |(g (statePoint w)).det|) :
    metricPBundle g w ∈ universalMetricBaseTube (max G W) d := by
  refine ⟨?_, hdet⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    metricPBundle_norm_bound hg hU hw hG hgB hwB

theorem qFirstCoefficient_five_eq_numerator {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    qFirstCoefficient g 5 w = -stateNumerator g w / (stateQDenominator g w)^2 := by
  unfold qFirstCoefficient
  rw [sixVariableQ_xx_axis hg hU hw]
  simp only [stateNumerator, jetNumerator, stateMixed, stateEnergy, div_pow]
  ring

theorem exists_uniform_Q_metric_state_margins (G W : ℝ)
    {d nu eta beta kappa : ℝ} (hG : 0 ≤ G) (hd : 0 < d)
    (hnu : 0 < nu) (heta : 0 < eta) (hbeta : 0 < beta) (hkappa : 0 < kappa) :
    ∃ epsilon A : ℝ, 0 < epsilon ∧ 1 ≤ A ∧
      ∀ (g g0 : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn g0 U → IsOpen U →
      ∀ w w0 : DarbouxState, statePoint w = statePoint w0 → statePoint w ∈ U →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g0 p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → ‖w0‖ ≤ W → d ≤ |(g (statePoint w)).det| → d ≤ |(g0 (statePoint w)).det| →
      (∀ i j k, k ≤ 2 →
        ‖iteratedFDeriv ℝ k (fun p => g0 p i j - g p i j) (statePoint w)‖ ≤ epsilon) →
      ‖w0 - w‖ ≤ epsilon → nu ≤ |stateQDenominator g w| → eta ≤ stateEnergy g w →
      stateNumerator g w ≤ -beta → gaussianCurvature g (statePoint w) ≤ -kappa →
      nu / 2 ≤ |stateQDenominator g0 w0| ∧ |stateQDenominator g0 w0| ≤ A ∧
      eta / 2 ≤ stateEnergy g0 w0 ∧
      (beta / 2) / A^2 ≤ qFirstCoefficient g0 5 w0 ∧
      ((kappa / 2) * (eta / 2)) / A^2 ≤
        (qFirstCoefficient g0 4 w0 / 2)^2 + qFirstCoefficient g0 5 w0 := by
  obtain ⟨epsilon, hepsilon, htransfer⟩ := universalQRaw_uniform_margins (max G W)
    hd hnu heta hbeta hkappa
  obtain ⟨A, hA, hAbound⟩ := universalQDenominator_uniform_bound (max G W) hd
  refine ⟨epsilon, A, hepsilon, hA, ?_⟩
  intro g g0 U hg hg0 hU w w0 hp hw hgB hg0B hwB hw0B hdet hdet0 hmetric hstate
    hden henergy hnum hK
  have hw0 : statePoint w0 ∈ U := by rw [← hp]; exact hw
  have ha := metricPBundle_mem_baseTube hg hU hw hG hgB hwB hdet
  have hb := metricPBundle_mem_baseTube hg0 hU hw0 hG
    (by simpa only [← hp] using hg0B) hw0B (by simpa only [← hp] using hdet0)
  have hab := metricPBundle_sub_norm_bound hg hg0 hU hp hw hepsilon.le hmetric hstate
  have hmargin := htransfer _ ha _ hb hab
    (by simpa only [universalQDenominator_metricPBundle] using hden)
    (by simpa only [universalEnergy_metricPBundle] using henergy)
    (by simpa only [universalQNumerator_metricPBundle hg hU hw] using hnum)
    (by simpa only [universalQCurvature_metricPBundle hg hU hw] using hK)
  have hd0 : nu / 2 ≤ |stateQDenominator g0 w0| := by
    simpa only [universalQDenominator_metricPBundle] using hmargin.1
  have hE0 : eta / 2 ≤ stateEnergy g0 w0 := by
    simpa only [universalEnergy_metricPBundle] using hmargin.2.1
  have hN0 : stateNumerator g0 w0 ≤ -(beta / 2) := by
    simpa only [universalQNumerator_metricPBundle hg0 hU hw0] using hmargin.2.2.1
  have hK0 : gaussianCurvature g0 (statePoint w0) ≤ -(kappa / 2) := by
    simpa only [universalQCurvature_metricPBundle hg0 hU hw0] using hmargin.2.2.2
  have hupper : |stateQDenominator g0 w0| ≤ A := by
    simpa only [universalQDenominator_metricPBundle] using hAbound _ hb
  have hne : stateQDenominator g0 w0 ≠ 0 :=
    abs_pos.mp ((half_pos hnu).trans_le hd0)
  have hdomain : w0 ∈ darbouxQStateDomain g0 U := ⟨hw0, hne⟩
  have hsq : (stateQDenominator g0 w0)^2 ≤ A^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((by norm_num : (0 : ℝ) ≤ 1).trans hA)).mpr hupper
  refine ⟨hd0, hupper, hE0, ?_, ?_⟩
  · rw [qFirstCoefficient_five_eq_numerator hg0 hU hdomain]
    have hnumle : beta / 2 ≤ -stateNumerator g0 w0 := by
      simpa only [neg_neg] using neg_le_neg hN0
    exact div_le_div₀ ((half_pos hbeta).le.trans hnumle) hnumle (sq_pos_of_ne_zero hne) hsq
  · rw [q_principal_discriminant hg0 hU hdomain]
    have hk : kappa / 2 ≤ -gaussianCurvature g0 (statePoint w0) := by
      simpa only [neg_neg] using neg_le_neg hK0
    have hprod : (kappa / 2) * (eta / 2) ≤
        -(gaussianCurvature g0 (statePoint w0) * stateEnergy g0 w0) := by
      simpa only [neg_mul] using
        mul_le_mul hk hE0 (half_pos heta).le ((half_pos hkappa).le.trans hk)
    exact div_le_div₀
      ((mul_nonneg (half_pos hkappa).le (half_pos heta).le).trans hprod)
      hprod (sq_pos_of_ne_zero hne) hsq

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem stateSegment_norm_le {w0 w1 : DarbouxState} {W sigma : ℝ}
    (h0 : ‖w0‖ ≤ W) (h1 : ‖w1‖ ≤ W) (hs : sigma ∈ Icc (0 : ℝ) 1) :
    ‖stateSegment w0 w1 sigma‖ ≤ W := by
  have hs0 : 0 ≤ 1 - sigma := sub_nonneg.mpr hs.2
  calc
    _ ≤ ‖(1 - sigma) • w0‖ + ‖sigma • w1‖ := norm_add_le _ _
    _ = (1 - sigma) * ‖w0‖ + sigma * ‖w1‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs0, abs_of_nonneg hs.1]
    _ ≤ (1 - sigma) * W + sigma * W :=
      add_le_add (mul_le_mul_of_nonneg_left h0 hs0) (mul_le_mul_of_nonneg_left h1 hs.1)
    _ = W := by ring

theorem stateSegment_sub_right_norm_le {w0 w1 : DarbouxState} {sigma : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) :
    ‖stateSegment w0 w1 sigma - w1‖ ≤ ‖w0 - w1‖ := by
  have he : stateSegment w0 w1 sigma - w1 = (1 - sigma) • (w0 - w1) := by
    ext i
    simp only [stateSegment, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hs.1])

theorem stateNumerator_qSolutionJet_eq_product {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    stateNumerator g (qSolutionJet z p) = covHessian g z p 0 0 * covHessian g z p 1 1 := by
  have hd : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1)^2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold stateNumerator jetNumerator
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  change (jetMixed g p (coordPartial 0 (coordPartial 1 z) p)
    (fun i => coordPartial i z p))^2 +
      gaussianCurvature g p * jetEnergy g p (fun i => coordPartial i z p) = _
  rw [jetMixed_at_height, jetEnergy_at_height hg hp z]
  linarith

theorem stateNumerator_negative_of_solution_floors {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    {nu c : ℝ} (_hnu : 0 < nu) (hc : 0 < c)
    (hxx : nu ≤ |covHessian g z p 0 0|) (hyy : c ≤ |covHessian g z p 1 1|)
    (htime : (hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p < 0) :
    stateNumerator g (qSolutionJet z p) ≤ -(nu * c) := by
  have hyne : covHessian g z p 1 1 ≠ 0 := abs_pos.mp (hc.trans_le hyy)
  have hratio : covHessian g z p 0 0 / covHessian g z p 1 1 < 0 := by
    rw [← hessian_time_ratio hg hU hz hp hyne hD]
    exact htime
  have heq : covHessian g z p 0 0 * covHessian g z p 1 1 =
      (covHessian g z p 0 0 / covHessian g z p 1 1) * (covHessian g z p 1 1)^2 := by
    field_simp [hyne]
  have hneg : covHessian g z p 0 0 * covHessian g z p 1 1 < 0 := by
    rw [heq]
    exact mul_neg_of_neg_of_pos hratio (sq_pos_of_ne_zero hyne)
  have hprod := mul_le_mul hxx hyy hc.le (abs_nonneg _)
  rw [← abs_mul, abs_of_neg hneg] at hprod
  rw [stateNumerator_qSolutionJet_eq_product hg hU hz hp hD]
  linarith

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem coordinate_word_vertical_variation {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Icc left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M : ℝ} (hB : CoordinateBound f (closedRectangle left right a b) 3 M)
    (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
    |iteratedCoordPartial ds f (boxPoint x t) -
      iteratedCoordPartial ds f (boxPoint x a)| ≤ M * |t - a| := by
  have hd (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivAt (fun y => iteratedCoordPartial ds f (boxPoint x y))
        (coordPartial 1 (iteratedCoordPartial ds f) (boxPoint x s)) s :=
    (LowQuotient.iterated_differentiableAt hf hU (hbox (boxPoint_mem hx hs)) ds).hasFDerivAt.comp_hasDerivAt
      s (boxPoint_hasDerivAt_s x s)
  have hb (s : ℝ) (hs : s ∈ Icc a b) :
      ‖deriv (fun y => iteratedCoordPartial ds f (boxPoint x y)) s‖ ≤ M := by
    rw [(hd s hs).deriv, Real.norm_eq_abs]
    exact hB (1 :: ds) (Nat.succ_le_succ hds) _ (boxPoint_mem hx hs)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hd s hs).differentiableAt) hb (show a ∈ Icc a b from ⟨le_rfl, hab⟩) ht

theorem coordinate_word_difference_on_strip {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Icc left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M M0 : ℝ} (hB : CoordinateBound z (closedRectangle left right a b) 3 M)
    (hB0 : CoordinateBound z0 (closedRectangle left right a b) 3 M0)
    (ds : List (Fin 2)) (hds : ds.length ≤ 2)
    (hinitial : iteratedCoordPartial ds z0 (boxPoint x a) =
      iteratedCoordPartial ds z (boxPoint x a)) :
    |iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x t)| ≤
      (M + M0) * |t - a| := by
  have h0 := coordinate_word_vertical_variation hz0 hU hbox hx hab ht hB0 ds hds
  have h1 := coordinate_word_vertical_variation hz hU hbox hx hab ht hB ds hds
  calc
    _ = |(iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z0 (boxPoint x a)) -
      (iteratedCoordPartial ds z (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x a))| := by
      rw [hinitial]
      congr 1
      ring
    _ ≤ |iteratedCoordPartial ds z0 (boxPoint x t) - iteratedCoordPartial ds z0 (boxPoint x a)| +
      |iteratedCoordPartial ds z (boxPoint x t) - iteratedCoordPartial ds z (boxPoint x a)| := abs_sub _ _
    _ ≤ M0 * |t - a| + M * |t - a| := add_le_add h0 h1
    _ = (M + M0) * |t - a| := by ring

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
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Weighted

theorem heightCauchyValue_contDiffOn {z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hz : ContDiffOn ℝ ∞ z U) (a : ℝ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U) :
    ContDiffOn ℝ ∞ (heightCauchyValue z a) I :=
  hz.comp (initialPoint_contDiff a).contDiffOn hcut

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
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise
namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem qSolutionJet_distance_on_closed_strip {z z0 : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hz0 : ContDiffOn ℝ ∞ z0 U) (hU : IsOpen U)
    {left right a b x t : ℝ}
    (hbox : closedRectangle left right a b ⊆ U)
    (hx : x ∈ Icc left right) (hab : a ≤ b) (ht : t ∈ Icc a b)
    {M M0 : ℝ} (hM : 0 ≤ M) (hM0 : 0 ≤ M0)
    (hB : CoordinateBound z (closedRectangle left right a b) 3 M)
    (hB0 : CoordinateBound z0 (closedRectangle left right a b) 3 M0)
    (hinitial : qSolutionJet z0 (boxPoint x a) = qSolutionJet z (boxPoint x a)) :
    ‖qSolutionJet z0 (boxPoint x t)-qSolutionJet z (boxPoint x t)‖ ≤ (M+M0)*(b-a) := by
  have hword (ds : List (Fin 2)) (hds : ds.length ≤ 2)
      (he : iteratedCoordPartial ds z0 (boxPoint x a) = iteratedCoordPartial ds z (boxPoint x a)) :
      |iteratedCoordPartial ds z0 (boxPoint x t)-iteratedCoordPartial ds z (boxPoint x t)| ≤
        (M+M0)*(b-a) := by
    apply (coordinate_word_difference_on_strip hz hz0 hU hbox hx hab ht hB hB0 ds hds he).trans
    apply mul_le_mul_of_nonneg_left _ (add_nonneg hM hM0)
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  apply state_distance_le_of_coordinate_error (mul_nonneg (add_nonneg hM hM0) (sub_nonneg.mpr hab))
  apply qSolutionJet_coordinate_error z z0 (boxPoint x t)
    (mul_nonneg (add_nonneg hM hM0) (sub_nonneg.mpr hab))
  · intro i
    fin_cases i
    · exact hword [0] (by norm_num) (congrFun hinitial 2)
    · exact hword [1] (by norm_num) (congrFun hinitial 3)
  · exact hword [0,1] (by norm_num) (congrFun hinitial 4)
  · exact hword [0,0] (by norm_num) (congrFun hinitial 5)

theorem exists_uniform_Q_closed_strip_margins (G R M M0 : ℝ)
    {d nu c eta kappa : ℝ} (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hM0 : 0 ≤ M0)
    (hd : 0 < d) (hnu : 0 < nu) (hc : 0 < c) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ epsilon A : ℝ, 0 < epsilon ∧ 1 ≤ A ∧
      ∀ (g g0 : MetricField) (z z0 : Coord → ℝ) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn g0 U → IsOpen U →
      ContDiffOn ℝ ∞ z U → ContDiffOn ℝ ∞ z0 U →
      ∀ left right a b : ℝ, a ≤ b →
      closedRectangle left right a b ⊆ U →
      (∀ p ∈ closedRectangle left right a b, ‖p‖ ≤ R) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g x i j) p‖ ≤ G) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g0 x i j) p‖ ≤ G) →
      CoordinateBound z (closedRectangle left right a b) 3 M →
      CoordinateBound z0 (closedRectangle left right a b) 3 M0 →
      (∀ p ∈ closedRectangle left right a b, d ≤ |(g p).det|) →
      (∀ p ∈ closedRectangle left right a b, d ≤ |(g0 p).det|) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g0 x i j - g x i j) p‖ ≤ epsilon) →
      (M + M0) * (b - a) ≤ epsilon →
      (∀ x ∈ Icc left right, qSolutionJet z0 (boxPoint x a) = qSolutionJet z (boxPoint x a)) →
      (∀ p ∈ closedRectangle left right a b, nu ≤ |covHessian g z p 0 0|) →
      (∀ p ∈ closedRectangle left right a b, c ≤ |covHessian g z p 1 1|) →
      (∀ p ∈ closedRectangle left right a b, eta ≤ heightEnergy g z p) →
      (∀ p ∈ closedRectangle left right a b, gaussianCurvature g p ≤ -kappa) →
      (∀ p ∈ closedRectangle left right a b,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ closedRectangle left right a b,
        (hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p < 0) →
      ∀ x ∈ Icc left right, ∀ t ∈ Icc a b,
      (∀ sigma ∈ Icc (0 : ℝ) 1,
        nu / 2 ≤ |stateQDenominator g0 (qHeightJetSegment z0 z sigma (boxPoint x t))| ∧
        |stateQDenominator g0 (qHeightJetSegment z0 z sigma (boxPoint x t))| ≤ A ∧
        eta / 2 ≤ stateEnergy g0 (qHeightJetSegment z0 z sigma (boxPoint x t)) ∧
        ((nu * c) / 2) / A^2 ≤ qFirstCoefficient g0 5 (qHeightJetSegment z0 z sigma (boxPoint x t)) ∧
        ((kappa / 2) * (eta / 2)) / A^2 ≤
          (qFirstCoefficient g0 4 (qHeightJetSegment z0 z sigma (boxPoint x t)) / 2)^2 +
            qFirstCoefficient g0 5 (qHeightJetSegment z0 z sigma (boxPoint x t))) ∧
      ((nu * c) / 2) / A^2 ≤
        averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 5 ∧
      ((nu * c) / 2) / A^2 ≤
        (averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 4 / 2)^2 +
          averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 5 := by
  let W := max R (max M M0)
  obtain ⟨epsilon, A, hepsilon, hA, htransfer⟩ :=
    exists_uniform_Q_metric_state_margins G W hG hd hnu heta (mul_pos hnu hc) hkappa
  refine ⟨epsilon, A, hepsilon, hA, ?_⟩
  intro g g0 z z0 U hg hg0 hU hz hz0 left right a b hab hbox hpoint
    hgB hg0B hzB hz0B hdet hdet0 hmetric hwidth hinitial
    hxx hyy henergy hK hD htime x hx t ht
  have hpbox : boxPoint x t ∈ closedRectangle left right a b :=
    boxPoint_mem hx ht
  have hp : boxPoint x t ∈ U := hbox hpbox
  have hwB : ‖qSolutionJet z (boxPoint x t)‖ ≤ W := by
    apply qSolutionJet_norm_bound_of_words hR (hpoint _ hpbox)
    intro ds hds
    exact (hzB ds (hds.trans (by norm_num)) _ hpbox).trans (le_max_left _ _)
  have hw0B : ‖qSolutionJet z0 (boxPoint x t)‖ ≤ W := by
    apply qSolutionJet_norm_bound_of_words hR (hpoint _ hpbox)
    intro ds hds
    exact (hz0B ds (hds.trans (by norm_num)) _ hpbox).trans (le_max_right _ _)
  have hjet : ‖qSolutionJet z0 (boxPoint x t) - qSolutionJet z (boxPoint x t)‖ ≤ epsilon :=
    (qSolutionJet_distance_on_closed_strip hz hz0 hU hbox hx hab ht hM hM0
      hzB hz0B (hinitial x hx)).trans hwidth
  have hnum := stateNumerator_negative_of_solution_floors hg hU hz hp
    (hD _ hpbox) hnu hc (hxx _ hpbox) (hyy _ hpbox) (htime _ hpbox)
  have hstateE : eta ≤ stateEnergy g (qSolutionJet z (boxPoint x t)) := by
    unfold stateEnergy
    rw [statePoint_qSolutionJet, stateGradient_qSolutionJet, jetEnergy_at_height hg hp z]
    exact henergy _ hpbox
  have hsegment (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :=
    htransfer g g0 U hg hg0 hU (qSolutionJet z (boxPoint x t))
      (qHeightJetSegment z0 z sigma (boxPoint x t))
      (by rw [statePoint_qSolutionJet, statePoint_qHeightJetSegment])
      (by simpa only [statePoint_qSolutionJet] using hp)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hgB i j k hk _ hpbox)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hg0B i j k hk _ hpbox)
      hwB (stateSegment_norm_le hw0B hwB hs)
      (by simpa only [statePoint_qSolutionJet] using hdet _ hpbox)
      (by simpa only [statePoint_qSolutionJet] using hdet0 _ hpbox)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hmetric i j k hk _ hpbox)
      ((stateSegment_sub_right_norm_le hs).trans hjet)
      (by simpa only [stateQDenominator_qSolutionJet] using hxx _ hpbox) hstateE hnum
      (by simpa only [statePoint_qSolutionJet] using hK _ hpbox)
  refine ⟨hsegment, ?_⟩
  apply averagedQPrincipal_margin hg0 hU
  · intro sigma hs
    refine ⟨?_, ?_⟩
    · change statePoint (qHeightJetSegment z0 z sigma (boxPoint x t)) ∈ U
      rw [statePoint_qHeightJetSegment]
      exact hp
    · have hm := (hsegment sigma hs).1
      exact abs_pos.mp ((half_pos hnu).trans_le hm)
  · intro sigma hs
    exact (hsegment sigma hs).2.2.2.1

end SmoothLocal.HighEquation

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
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.Hyperbolic

def shearedModelSquare (q0 : ℝ) : Set Coord :=
  inverseShearCoordinates q0 ⁻¹' modelSquare

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
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem metric_difference_jet_le_actual_pulse_error
    {gStar gTau : MetricField} {V U : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hgTau : SmoothPositiveOn gTau U)
    (hV : IsOpen V) (hU : IsOpen U) {p : Coord} (hpV : p ∈ V) (hpU : p ∈ U)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) (k : ℕ) {P E : ℝ}
    (hpulse : ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤ P)
    (herror : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) p‖ ≤ E) :
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j-gStar q i j) p‖ ≤ P+E := by
  have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  have hbs := (hgStar.1 i j).contDiffAt (hV.mem_nhds hpV)
  have hgs := (hgTau.1 i j).contDiffAt (hU.mem_nhds hpU)
  have hts : ContDiffAt ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) p :=
    hbs.add hps.contDiffAt
  have heq : (fun q => gTau q i j-gStar q i j) =
      (fun q => gTau q i j-testMetric gStar q0 a N delta tau q i j)+
        (fun q => pulseTensor q0 a N delta tau q i j) := by
    funext q
    simp only [testMetric,Pi.add_apply,Matrix.add_apply]
    ring
  rw [heq,iteratedFDeriv_add_apply
    ((hgs.sub hts).of_le (WithTop.coe_le_coe.mpr le_top))
    (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_add_le _ _).trans ((add_le_add herror hpulse).trans_eq (add_comm E P))

theorem actual_metric_finite_reference_closeness
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (q0 a : ℝ) (ha : 0 < a) (m N : ℕ) (hmN : m < N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ m ≤ tau ∧
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
            testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
        ∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-gStar q i j) p‖ ≤ epsilon := by
  obtain ⟨tau0,_,haccuracy⟩ := exists_first_error_threshold (by positivity : 0 < 4*epsilon)
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha m N hmN delta
    (half_pos hepsilon),eventually_ge_atTop tau0,eventually_ge_atTop m] with tau hpulse htau hmtau
  refine ⟨hpulse.1,hmtau,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  have he : metricApproximationAccuracy tau ≤ epsilon/2 := by linarith [haccuracy tau htau]
  have hb := metric_difference_jet_le_actual_pulse_error hgStar hgTau hV hU
    (hSV hp) (hSU hp) q0 a N delta (tau : ℝ) i j k
    (hpulse.2 i j k hk p) ((happ i j k (hk.trans hmtau) p hp).trans he)
  exact hb.trans_eq (by ring)

theorem actual_sheared_metric_finite_reference_closeness
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {q0 a : ℝ} (hq0 : |q0| ≤ 1) (ha : 0 < a) (m N : ℕ) (hmN : m < N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ m ≤ tau ∧
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
            testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
        ∀ i j : Fin 2, ∀ k ≤ m, ∀ p : Coord,
          inverseShearCoordinates q0 p ∈ modelSquare →
          ‖iteratedFDeriv ℝ k (fun q => metricInShearCoordinates gStar q0 q i j-
            metricInShearCoordinates gTau q0 q i j) p‖ ≤ epsilon := by
  let e := epsilon/(4*2^m)
  have he : 0 < e := div_pos hepsilon (by positivity)
  filter_upwards [actual_metric_finite_reference_closeness hgStar hV hSV q0 a ha m N hmN he delta]
    with tau htau
  refine ⟨htau.1,htau.2.1,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hpW : inverseShearCoordinates q0 p ∈ W := ⟨hSU hp,hSV hp⟩
  have hgW (i j : Fin 2) := (hgTau.1 i j).mono (inter_subset_left : W ⊆ U)
  have hsW (i j : Fin 2) := (hgStar.1 i j).mono (inter_subset_right : W ⊆ V)
  have herr (i j : Fin 2) :
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j-gTau q i j) (inverseShearCoordinates q0 p)‖ ≤ e := by
    have hdiff := htau.2.2 gTau U hgTau hU hSU happ i j k hk _ hp
    have heq : (fun q => gStar q i j-gTau q i j) =
        -(fun q => gTau q i j-gStar q i j) := by
      funext point
      simp only [Pi.neg_apply, neg_sub]
    rw [heq,iteratedFDeriv_neg_apply,norm_neg]
    exact hdiff
  have hshear := sheared_metric_full_jet_difference_le hsW hgW hW hq0 he.le hpW k herr i j
  apply hshear.trans
  calc
    4*2^k*e ≤ 4*2^m*e := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (by norm_num)) he.le
    _ = epsilon := by dsimp only [e]; field_simp

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
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_reference_segment_at_radius
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
    ∃ C A : ℝ, 0 ≤ C ∧ 1 ≤ A ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
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
          let zs := heightInShearCoordinates z q0
          let gs := metricInShearCoordinates gStar q0
          let P := taylorApproximation gs (-delta/(tau : ℝ))
            (heightCauchyValue zs (-delta/(tau : ℝ)))
            (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
          ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
          CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) 3 C ∧
          (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            ∀ sigma ∈ Icc (0 : ℝ) 1,
              (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) ≤
                |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ∧
              |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ≤ A ∧
              (1/(M : ℝ))/2 ≤ stateEnergy gs (qHeightJetSegment P zs sigma p) ∧
              ((((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))*(1/(M : ℝ)))/2)/A^2 ≤
                qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p) ∧
              (((kappa/2)/2)*((1/(M : ℝ))/2))/A^2 ≤
                (qFirstCoefficient gs 4 (qHeightJetSegment P zs sigma p)/2)^2+
                  qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p)) := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let nu := (boundedClassSpeed kappa M)^2/(2*(M : ℝ))
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hnu : 0 < nu := boundedClassShearHxxFloor_pos hkappa hM
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hq1 : |q0| ≤ 1 := hq0.trans (by norm_num)
  have ha : 0 < L*r/16 := div_pos (mul_pos hL hr) (by norm_num)
  obtain ⟨C,hC,hPjets⟩ := exists_actual_taylor_finite_jets_at_radius
    hgStar hV hSV M hG hd hkappa hM hq0 hr hrhalf hLr hrsmall N 3
  obtain ⟨epsilon,A,hepsilon,hA,htransfer⟩ := exists_uniform_Q_closed_strip_margins
    (16*G) 1 Z C (mul_nonneg (by norm_num) hG) (by norm_num) hZ hC
      hd hnu hminv hminv (half_pos hkappa)
  obtain ⟨tauRef,htauRef,hfloor⟩ := exists_bounded_patch_reference_initial_floor
    G kappa d q0 M hG hkappa hd hM hq0
  refine ⟨C,A,hC,hA,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  have hlarge : ∀ᶠ tau : ℕ in atTop, 2*delta*(Z+C)/epsilon ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hPjets delta hdelt hdhalf,hwidth,hlarge,eventually_ge_atTop tauRef,
    actual_sheared_metric_finite_reference_closeness hgStar hV hSV hq1 ha 2 N hN hepsilon delta]
    with tau hPtau hw htlarge htRef hclose
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let gt := metricInShearCoordinates g q0
  let zs := heightInShearCoordinates z q0
  let a := -delta/(tau : ℝ)
  let b := delta/(tau : ℝ)
  let I := Ioo (-(L*r)) (L*r)
  let P := taylorApproximation gs a (heightCauchyValue zs a) (heightCauchyVelocity zs a) N
  let S := closedRectangle (-(L*r/2)) (L*r/2) a b
  have hSP : S = pulseStrip (L*r/2) delta (tau : ℝ) := by
    simp only [S,pulseStrip,a,b,neg_div]
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbnonneg : 0 ≤ b := div_nonneg hdelt.le htpos.le
  have hab : a ≤ b := by
    dsimp only [a,b]
    rw [neg_div]
    exact neg_le_self hbnonneg
  have hbr : b ≤ r := by
    have he : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    dsimp only [b]
    rw [he]
    linarith [hw.2]
  have haabs : |a| ≤ r := by
    dsimp only [a]
    rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htpos]
    exact hbr
  have hLrpos : 0 < L*r := mul_pos hL hr
  have hhr : r ≤ 1/20 := by
    have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
    have hh : r ≤ L*r := by nlinarith
    exact hh.trans hLr
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r := by
    have hx : |p 0| ≤ L*r/2 := abs_le.mpr hp.1
    have ht : |p 1| ≤ b := abs_le.mpr
      ⟨by simpa only [a,b,neg_div] using hp.2.1,hp.2.2⟩
    exact ⟨hx.trans (by linarith),ht.trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hbox : S ⊆ D := by
    intro p hp
    refine ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,?_⟩
    exact ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
  have hpoint (p : Coord) (hp : p ∈ S) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · exact (hcoordinates p hp).2.trans (hhr.trans (by norm_num))
  have hgtUs : SmoothPositiveOn gt Us := metricInShearCoordinates_smoothPositive hg q0
  have hgsVs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hgtD : SmoothPositiveOn gt D :=
    ⟨fun i j => (hgtUs.1 i j).mono (fun _ hp => hp.1.1),fun p hp => hgtUs.2 p hp.1.1⟩
  have hgsD : SmoothPositiveOn gs D :=
    ⟨fun i j => (hgsVs.1 i j).mono (fun _ hp => hp.1.2),fun p hp => hgsVs.2 p hp.1.2⟩
  have hzsUs : ContDiffOn ℝ ∞ zs Us := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD := hzsUs.mono (show D ⊆ Us from fun _ hp => hp.1.1)
  obtain ⟨hP,_hPfull,hPBpulse⟩ := hPtau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hPB : CoordinateBound P S 3 C := by rw [hSP]; exact hPBpulse
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hzB : CoordinateBound zs S 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have htwo (g1 : MetricField) (U1 : Set Coord) (hg1 : SmoothPositiveOn g1 U1)
      (hU1 : IsOpen U1) (hSU1 : modelSquare ⊆ U1)
      (hB1 : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => g1 q i j) p‖ ≤ G)
      (i j : Fin 2) (k : ℕ) (hk : k ≤ 2) (p : Coord) (hp : p ∈ S) :
      ‖iteratedFDeriv ℝ k (fun q => metricInShearCoordinates g1 q0 q i j) p‖ ≤ 16*G := by
    apply (sheared_metric_full_jet_bound hg1.1 hU1 hq1 hG (hSU1 (hpS p hp)) k
      (fun l m => hB1 l m k hk _ (hpS p hp)) i j).trans
    have he : (2 : ℝ)^k ≤ 4 := by
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk).trans (by norm_num)
    nlinarith
  have hg2 := htwo g U hg hU hSU (fun i j k hk => hgB i j k (by omega))
  have hgs2 := htwo gStar V hgStar hV hSV hgStarB
  have hdetT (p : Coord) (hp : p ∈ S) : d ≤ |(gt p).det| := by
    rw [metricDet_in_shear_coordinates]
    exact hdet _ (hpS p hp)
  have hdetR (p : Coord) (hp : p ∈ S) : d ≤ |(gs p).det| := by
    rw [metricDet_in_shear_coordinates]
    exact (hdStar _ (hpS p hp)).trans (le_abs_self _)
  have hmetric (i j : Fin 2) (k : ℕ) (hk : k ≤ 2) (p : Coord) (hp : p ∈ S) :
      ‖iteratedFDeriv ℝ k (fun q => gs q i j-gt q i j) p‖ ≤ epsilon :=
    hclose.2.2 g U hg hU hSU happ i j k hk p (hpS p hp)
  have hduration : (Z+C)*(b-a) ≤ epsilon := by
    have hh := (div_le_iff₀ hepsilon).mp htlarge
    have he : (Z+C)*(b-a)=(2*delta*(Z+C))/(tau : ℝ) := by dsimp only [a,b]; ring
    rw [he]
    apply (div_le_iff₀ htpos).mpr
    nlinarith
  have hcutS (x : ℝ) (hx : x ∈ I) : inverseShearCoordinates q0 ![x,a] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,haabs⟩
  have hcutU (x : ℝ) (hx : x ∈ I) : (![x,a] : Coord) ∈ Us := hSU (hcutS x hx)
  have h0 := heightCauchyValue_contDiffOn hzsUs a hcutU
  have h1 := heightCauchyVelocity_contDiffOn hzsUs hUs a hcutU
  have hden := hfloor g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelt htRef hbr happ
  have hxx0 : ∀ x ∈ I, covHessian gs (linearCauchy a (heightCauchyValue zs a)
      (heightCauchyVelocity zs a)) ![x,a] 0 0 ≠ 0 := by
    intro x hx hzero
    have hh := hden x hx
    rw [hzero,abs_zero] at hh
    have hc : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by
      have he : (boundedClassSpeed kappa M)^2/(4*(M : ℝ))=nu/2 := by dsimp only [nu]; ring
      rw [he]
      exact half_pos hnu
    linarith
  have hjet0 := (taylorApproximation_properties hgsVs hVs isOpen_Ioo h0 h1 a
    (fun x hx => hSV (hcutS x hx)) hxx0 N).2.1
  have hinitial (x : ℝ) (hx : x ∈ Icc (-(L*r/2)) (L*r/2)) :
      qSolutionJet P (boxPoint x a)=qSolutionJet zs (boxPoint x a) := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have he : boxPoint x a = (![x,a] : Coord) := by
      ext i
      fin_cases i <;> simp [boxPoint]
    rw [he]
    exact (hjet0 x hxI).trans (linearCauchy_height_initial_state hzsUs hUs (-(L*r)) (L*r) a hcutU hxI)
  have hresult := htransfer gt gs zs P D hgtD hgsD hD hzsD hPD
    (-(L*r/2)) (L*r/2) a b hab hbox hpoint hg2 hgs2 hzB hPB hdetT hdetR hmetric hduration hinitial
    (fun p hp => (hgeom p hp).2.1) (fun p hp => (hgeom p hp).2.2.1)
    (fun p hp => (hgeom p hp).2.2.2.1) (fun p hp => (hgeom p hp).2.2.2.2.1)
    (fun p hp => (hgeom p hp).2.2.2.2.2.1) (fun p hp => (hgeom p hp).2.2.2.2.2.2)
  refine ⟨hP,hPBpulse,?_⟩
  intro p hp sigma hsigma
  have hpS' : p ∈ S := by rw [hSP]; exact hp
  have hm := (hresult (p 0) hpS'.1 (p 1) hpS'.2).1 sigma hsigma
  have he : boxPoint (p 0) (p 1)=p := by ext i; fin_cases i <;> simp [boxPoint]
  have hhalf : nu/2=(boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by dsimp only [nu]; ring
  simpa only [he,hhalf] using hm

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.exists_actual_reference_segment_at_radius := @OAI.SmoothLocal.Perturbation.exists_actual_reference_segment_at_radius
