-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.exists_actual_upper_off_pulse_cauchy_bounds_at_radius
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:12:31.956265+00:00
-- url     : https://prove2.me/submissions/c39b1661-0973-408c-8eb8-b70f5305a3a9

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Flow_exists_C8_one_flow_physical_cap_estimates
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_bounded_patch_cauchy_bound
import Theorems.Thm_OAI_SmoothLocal_Pulse_exists_actual_finite_lower_cut_bound_at_radius

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model
open SmoothLocal.Geometry

theorem modelProfile_even : Function.Even modelProfile := by
  intro y
  simp [modelProfile]

end SmoothLocal.Model

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

theorem matrix_pullback_bilinear (G R : Matrix (Fin 2) (Fin 2) ℝ) (v w : Coord) :
    (R *ᵥ v) ⬝ᵥ (G *ᵥ (R *ᵥ w)) = v ⬝ᵥ ((Rᵀ * G * R) *ᵥ w) := by
  calc
    _ = (G *ᵥ (R *ᵥ w)) ⬝ᵥ (R *ᵥ v) := dotProduct_comm _ _
    _ = v ⬝ᵥ (Rᵀ *ᵥ (G *ᵥ (R *ᵥ w))) :=
      (Matrix.dotProduct_transpose_mulVec R v (G *ᵥ (R *ᵥ w))).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

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
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def affineInverseCoordinates (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (p : Coord) : Coord := R⁻¹ *ᵥ (p - b)

theorem affineInverseCoordinates_contDiff (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affineInverseCoordinates b R) :=
  (matrixContinuousLinear R⁻¹).contDiff.comp (contDiff_id.sub contDiff_const)

theorem affineInverseCoordinates_affineCoordinates (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (q : Coord) :
    affineInverseCoordinates b R (affineCoordinates b R q) = q := by
  have hSR := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  simp only [affineInverseCoordinates, affineCoordinates, add_sub_cancel_left, Matrix.mulVec_mulVec, hSR, Matrix.one_mulVec]

theorem affineCoordinates_affineInverseCoordinates (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (p : Coord) :
    affineCoordinates b R (affineInverseCoordinates b R p) = p := by
  have hRS := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  simp only [affineInverseCoordinates, affineCoordinates, Matrix.mulVec_mulVec, hRS, Matrix.one_mulVec, add_sub_cancel]

def affineCoordinateHomeomorph (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : IsUnit R) : Coord ≃ₜ Coord where
  toFun := affineCoordinates b R
  invFun := affineInverseCoordinates b R
  left_inv := affineInverseCoordinates_affineCoordinates b R hR
  right_inv := affineCoordinates_affineInverseCoordinates b R hR
  continuous_toFun := (affineCoordinates_contDiff b R).continuous
  continuous_invFun := (affineInverseCoordinates_contDiff b R).continuous

def affinePushforwardMetric (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : MetricField := fun p =>
  R⁻¹ᵀ * η (affineInverseCoordinates b R p) * R⁻¹

theorem affinePullback_pushforward (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    affinePullbackMetric (affinePushforwardMetric η b R) b R = η := by
  have hSR := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hT : Rᵀ * R⁻¹ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hSR, Matrix.transpose_one]
  funext q
  simp only [affinePullbackMetric, affinePushforwardMetric,
    affineInverseCoordinates_affineCoordinates b R hR]
  calc
    _ = (Rᵀ * R⁻¹ᵀ) * η q * (R⁻¹ * R) := by simp only [Matrix.mul_assoc]
    _ = η q := by rw [hT, hSR, Matrix.one_mul, Matrix.mul_one]

theorem affinePullbackMetric_add (g η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) :
    affinePullbackMetric (g + η) b R =
      affinePullbackMetric g b R + affinePullbackMetric η b R := by
  funext p
  simp only [affinePullbackMetric, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]

theorem affinePushforwardMetric_eq_zero_iff (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (p : Coord) :
    affinePushforwardMetric η b R p = 0 ↔ η (affineInverseCoordinates b R p) = 0 := by
  constructor
  · intro hp
    have h := congrFun (affinePullback_pushforward η b R hR)
      (affineInverseCoordinates b R p)
    simp only [affinePullbackMetric, affineCoordinates_affineInverseCoordinates b R hR,
      hp, Matrix.mul_zero, Matrix.zero_mul] at h
    exact h.symm
  · intro hp
    simp only [affinePushforwardMetric, hp, Matrix.mul_zero, Matrix.zero_mul]

theorem affinePushforwardMetric_support (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    Function.support (affinePushforwardMetric η b R) =
      affineCoordinates b R '' Function.support η := by
  ext p
  constructor
  · intro hp
    refine ⟨affineInverseCoordinates b R p, ?_,
      affineCoordinates_affineInverseCoordinates b R hR p⟩
    change η (affineInverseCoordinates b R p) ≠ 0
    intro hη
    exact hp ((affinePushforwardMetric_eq_zero_iff η b R hR p).mpr hη)
  · rintro ⟨q, hq, rfl⟩
    change affinePushforwardMetric η b R (affineCoordinates b R q) ≠ 0
    intro hη
    have hzero := (affinePushforwardMetric_eq_zero_iff η b R hR _).mp hη
    rw [affineInverseCoordinates_affineCoordinates b R hR] at hzero
    exact hq hzero

theorem affinePushforwardMetric_tsupport (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    tsupport (affinePushforwardMetric η b R) = affineCoordinates b R '' tsupport η := by
  rw [tsupport, affinePushforwardMetric_support η b R hR]
  exact ((affineCoordinateHomeomorph b R hR).image_closure (Function.support η)).symm

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

def bilinearMatrix (B : Coord →L[ℝ] Coord →L[ℝ] ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a k => B (Pi.single a 1) (Pi.single k 1)

theorem bilinear_matrix_congruence (B : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    B (R *ᵥ Pi.single i 1) (R *ᵥ Pi.single j 1) =
      (Rᵀ * bilinearMatrix B * R) i j := by
  rw [matrix_column_basis_expansion R i, matrix_column_basis_expansion R j]
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, bilinearMatrix]
  ring

theorem second_coordPartial_affine_comp {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q =
      fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)
        (R *ᵥ Pi.single i 1) (R *ᵥ Pi.single j 1) := by
  have hV := isOpen_affine_preimage hU b R
  have heq : coordPartial j (z ∘ affineCoordinates b R) =ᶠ[𝓝 q]
      (fun p => fderiv ℝ z (affineCoordinates b R p) (R *ᵥ Pi.single j 1)) := by
    filter_upwards [hV.mem_nhds hq] with p hp
    exact fderiv_affine_comp_apply b R p (Pi.single j 1)
      (((hz _ hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ z) U := hz.fderiv_of_isOpen hU (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ z) (affineCoordinates b R q) :=
    (((hs _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
  have hdc : DifferentiableAt ℝ
      (fun p => fderiv ℝ z (affineCoordinates b R p)) q :=
    hd.comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have heval : coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q =
      fderiv ℝ (fun p => fderiv ℝ z (affineCoordinates b R p)) q
        (Pi.single i 1) (R *ᵥ Pi.single j 1) := by
    change fderiv ℝ (coordPartial j (z ∘ affineCoordinates b R)) q (Pi.single i 1) = _
    rw [heq.fderiv_eq, fderiv_clm_apply hdc
      (differentiableAt_const (c := R *ᵥ Pi.single j (1 : ℝ)))]
    simp
  rw [heval]
  exact congrArg (fun L : Coord →L[ℝ] ℝ => L (R *ᵥ Pi.single j 1))
    (fderiv_affine_comp_apply b R q (Pi.single i 1) hd)

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
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def ordinaryCoordinateHessian (z : Coord → ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => coordPartial i (coordPartial j z) p

def connectionHessianCorrection (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  ∑ k, christoffel g k i j p * coordPartial k z p

theorem covHessian_eq_ordinary_sub_correction (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    covHessian g z p = ordinaryCoordinateHessian z p - connectionHessianCorrection g z p := rfl

theorem ordinaryCoordinateHessian_affine_comp {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) :
    ordinaryCoordinateHessian (z ∘ affineCoordinates b R) q =
      Rᵀ * ordinaryCoordinateHessian z (affineCoordinates b R q) * R := by
  have hB : ordinaryCoordinateHessian z (affineCoordinates b R q) =
      bilinearMatrix (fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)) := by
    ext i j
    exact second_coordPartial_eq_fderiv hz hU hq i j
  rw [hB]
  ext i j
  change coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q = _
  rw [second_coordPartial_affine_comp hz hU b R q hq i j]
  exact bilinear_matrix_congruence (fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)) R i j

theorem connectionHessianCorrection_affine_comp
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    connectionHessianCorrection (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      Rᵀ * connectionHessianCorrection g z (affineCoordinates b R q) * R := by
  have hdz : DifferentiableAt ℝ z (affineCoordinates b R q) :=
    (((hz _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
  have hchain (k : Fin 2) : coordPartial k (z ∘ affineCoordinates b R) q =
      ∑ a, R a k * coordPartial a z (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q hdz k
  ext i j
  change (∑ k, christoffel (affinePullbackMetric g b R) k i j q *
    coordPartial k (z ∘ affineCoordinates b R) q) = _
  simp only [hchain]
  calc
    _ = ∑ a, coordPartial a z (affineCoordinates b R q) *
        (∑ k, R a k * christoffel (affinePullbackMetric g b R) k i j q) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ a, coordPartial a z (affineCoordinates b R q) *
        (∑ c, ∑ d, R c i * R d j * christoffel g a c d (affineCoordinates b R q)) := by
      simp_rw [christoffel_affinePullback_push hg hU b R hR q hq]
    _ = _ := by
      simp only [connectionHessianCorrection, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two]
      ring

theorem covHessian_affinePullback
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    covHessian (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      Rᵀ * covHessian g z (affineCoordinates b R q) * R := by
  rw [covHessian_eq_ordinary_sub_correction, covHessian_eq_ordinary_sub_correction,
    ordinaryCoordinateHessian_affine_comp hz hU b R q hq,
    connectionHessianCorrection_affine_comp hg hz hU b R hR q hq]
  simp only [Matrix.mul_sub, Matrix.sub_mul]

def coordinateCovector (z : Coord → ℝ) (p : Coord) : Coord := fun i => coordPartial i z p

theorem coordinateCovector_affine_comp {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    coordinateCovector (z ∘ affineCoordinates b R) q =
      Rᵀ *ᵥ coordinateCovector z (affineCoordinates b R q) := by
  ext i
  exact coordPartial_affine_comp b R q hz i

theorem covectorNormSq_eq_dotProduct (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    covectorNormSq g z p = coordinateCovector z p ⬝ᵥ
      (inverseMetric g p *ᵥ coordinateCovector z p) := by
  simp only [covectorNormSq, coordinateCovector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem inverseMetric_affinePullback (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) :
    inverseMetric (affinePullbackMetric g b R) q =
      R⁻¹ * inverseMetric g (affineCoordinates b R q) * R⁻¹ᵀ := by
  simp only [inverseMetric, affinePullbackMetric, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem covectorNormSq_affinePullback {g : MetricField} {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    covectorNormSq (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      covectorNormSq g z (affineCoordinates b R q) := by
  have hRS := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hT : R⁻¹ᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  let v := coordinateCovector z (affineCoordinates b R q)
  have hvec : R⁻¹ᵀ *ᵥ (Rᵀ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  have hquad := matrix_pullback_bilinear (inverseMetric g (affineCoordinates b R q))
    R⁻¹ᵀ (Rᵀ *ᵥ v) (Rᵀ *ᵥ v)
  simp only [hvec, Matrix.transpose_transpose] at hquad
  rw [covectorNormSq_eq_dotProduct, covectorNormSq_eq_dotProduct,
    coordinateCovector_affine_comp b R q hz, inverseMetric_affinePullback]
  exact hquad.symm

theorem heightEnergy_affinePullback {g : MetricField} {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    heightEnergy (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      R.det ^ 2 * heightEnergy g z (affineCoordinates b R q) := by
  rw [heightEnergy, covectorNormSq_affinePullback b R hR q hz]
  simp only [affinePullbackMetric, Matrix.det_mul, Matrix.det_transpose, heightEnergy]
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
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

theorem perturbationTensor_tsupport_subset (η : SymmetricPerturbation) :
    tsupport (perturbationTensor η) ⊆ patchBox := η.val.tsupport_subset

theorem perturbedMetric_zero (g0 : MetricField) : perturbedMetric g0 0 = g0 := by
  funext p
  change g0 p + 0 = g0 p
  exact add_zero _

theorem zero_mem_metricPatchSet {g0 : MetricField} {kappa : ℝ}
    (hg : ∀ p ∈ modelSquare, (g0 p).PosDef)
    (hK : ∀ p ∈ centralBox, gaussianCurvature g0 p < -kappa / 2) :
    (0 : SymmetricPerturbation) ∈ metricPatchSet g0 kappa := by
  change (∀ p ∈ modelSquare, (perturbedMetric g0 0 p).PosDef) ∧ _
  rw [perturbedMetric_zero]
  exact ⟨hg, hK⟩

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
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

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
open Set Function Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Model

def reflectionMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,-1]

def reflectPoint (p : Coord) : Coord := fun i => if i = 0 then p 0 else -p 1

@[simp] theorem reflectPoint_zero (p : Coord) : reflectPoint p 0 = p 0 := by
  simp [reflectPoint]

@[simp] theorem reflectPoint_one (p : Coord) : reflectPoint p 1 = -p 1 := by
  simp [reflectPoint]

@[simp] theorem reflectPoint_twice (p : Coord) : reflectPoint (reflectPoint p) = p := by
  ext i
  fin_cases i <;> simp

theorem reflectPoint_eq_affine : reflectPoint = affineCoordinates 0 reflectionMatrix := by
  funext p
  ext i
  fin_cases i <;> simp [reflectPoint,affineCoordinates,reflectionMatrix,
    dotProduct,Fin.sum_univ_two]

theorem reflectionMatrix_square : reflectionMatrix * reflectionMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflectionMatrix,Matrix.mul_apply,Fin.sum_univ_two]

@[simp] theorem reflectionMatrix_det : reflectionMatrix.det = -1 := by
  norm_num [reflectionMatrix,Matrix.det_fin_two]

theorem reflectionMatrix_isUnit : IsUnit reflectionMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.mpr
  rw [reflectionMatrix_det]
  norm_num

@[simp] theorem reflectionMatrix_inv : reflectionMatrix⁻¹ = reflectionMatrix :=
  Matrix.inv_eq_left_inv reflectionMatrix_square

theorem reflectPoint_contDiff : ContDiff ℝ ∞ reflectPoint := by
  rw [reflectPoint_eq_affine]
  exact affineCoordinates_contDiff 0 reflectionMatrix

def reflectionIsometry : Coord ≃ₗᵢ[ℝ] Coord where
  toFun := reflectPoint
  invFun := reflectPoint
  left_inv := reflectPoint_twice
  right_inv := reflectPoint_twice
  map_add' p q := by
    ext i
    fin_cases i <;> simp [reflectPoint,Pi.add_apply,add_comm]
  map_smul' a p := by
    ext i
    fin_cases i <;> simp [reflectPoint,Pi.smul_apply,smul_eq_mul]
  norm_map' p := by
    change ‖reflectPoint p‖ = ‖p‖
    rw [Pi.norm_def,Pi.norm_def]
    congr 1
    apply Finset.sup_congr rfl
    intro index _
    fin_cases index <;> simp

def reflectedScalar {V : Type*} (f : Coord → V) : Coord → V := f ∘ reflectPoint

def reflectedMetric (g : MetricField) : MetricField :=
  affinePullbackMetric g 0 reflectionMatrix

theorem reflectedScalar_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (reflectedScalar f) (reflectPoint ⁻¹' U) :=
  hf.comp reflectPoint_contDiff.contDiffOn (fun _ hp => hp)

theorem reflectedDomain_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (reflectPoint ⁻¹' U) := hU.preimage reflectPoint_contDiff.continuous

theorem reflectedMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    SmoothPositiveOn (reflectedMetric g) (reflectPoint ⁻¹' U) := by
  simpa only [reflectedMetric,reflectPoint_eq_affine] using
    affinePullbackMetric_smoothPositive hg 0 reflectionMatrix
      (Matrix.mulVec_injective_of_isUnit reflectionMatrix_isUnit)

theorem reflectedMetric_add (g eta : MetricField) :
    reflectedMetric (g+eta) = reflectedMetric g + reflectedMetric eta :=
  affinePullbackMetric_add g eta 0 reflectionMatrix

theorem reflectedMetric_entry (g : MetricField) (p : Coord) (i j : Fin 2) :
    reflectedMetric g p i j =
      if i=j then g (reflectPoint p) i j else -g (reflectPoint p) i j := by
  rw [reflectPoint_eq_affine]
  fin_cases i <;> fin_cases j <;>
    simp [reflectedMetric,affinePullbackMetric,reflectionMatrix,Matrix.mul_apply,
      Matrix.transpose_apply,Fin.sum_univ_two]

theorem reflectedMetric_det (g : MetricField) (p : Coord) :
    (reflectedMetric g p).det = (g (reflectPoint p)).det := by
  simpa only [reflectedMetric,reflectPoint_eq_affine,reflectionMatrix_det,
    neg_one_sq,one_mul] using det_affinePullbackMetric g 0 reflectionMatrix p

theorem reflectedMetric_curvature {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : reflectPoint p ∈ U) :
    gaussianCurvature (reflectedMetric g) p = gaussianCurvature g (reflectPoint p) := by
  simpa only [reflectedMetric,reflectPoint_eq_affine] using
    gaussianCurvature_affinePullback hg hU 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hp)

theorem reflectedMetric_hessian {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    covHessian (reflectedMetric g) (reflectedScalar z) p =
      reflectionMatrixᵀ * covHessian g z (reflectPoint p) * reflectionMatrix := by
  simpa only [reflectedMetric,reflectedScalar,reflectPoint_eq_affine] using
    covHessian_affinePullback hg hz hU 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hp)

theorem reflectedMetric_hessian_entry {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) (i j : Fin 2) :
    covHessian (reflectedMetric g) (reflectedScalar z) p i j =
      if i=j then covHessian g z (reflectPoint p) i j
      else -covHessian g z (reflectPoint p) i j := by
  rw [reflectedMetric_hessian hg hz hU hp]
  fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]

theorem reflectedMetric_hessian_det {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    (covHessian (reflectedMetric g) (reflectedScalar z) p).det =
      (covHessian g z (reflectPoint p)).det := by
  rw [reflectedMetric_hessian hg hz hU hp]
  simp [Matrix.det_mul,Matrix.det_transpose]

theorem reflectedMetric_energy {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    heightEnergy (reflectedMetric g) (reflectedScalar z) p = heightEnergy g z (reflectPoint p) := by
  have hd := (hz.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simpa only [reflectedMetric,reflectedScalar,reflectPoint_eq_affine,reflectionMatrix_det,
    neg_one_sq,one_mul] using
    heightEnergy_affinePullback (g := g) 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hd)

theorem reflectedMetric_quotient {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    hessianQuotient (reflectedMetric g) (reflectedScalar z) p =
      -hessianQuotient g z (reflectPoint p) := by
  simp only [hessianQuotient,reflectedMetric_hessian_entry hg hz hU hp,
    show (0 : Fin 2) ≠ 1 by decide,ite_false,ite_true,neg_div]

theorem reflectPoint_mem_symmetricSquare (r : ℝ) (p : Coord) :
    reflectPoint p ∈ Icc (fun _ : Fin 2 => -r) (fun _ => r) ↔
      p ∈ Icc (fun _ : Fin 2 => -r) (fun _ => r) := by
  simp only [mem_Icc,Pi.le_def,Fin.forall_fin_two,reflectPoint_zero,reflectPoint_one]
  constructor <;> rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ <;> constructor <;> constructor <;> linarith

theorem reflectPoint_mem_modelSquare (p : Coord) :
    reflectPoint p ∈ modelSquare ↔ p ∈ modelSquare := reflectPoint_mem_symmetricSquare 3 p

theorem reflectedDomain_contains_modelSquare {U : Set Coord} (hS : modelSquare ⊆ U) :
    modelSquare ⊆ reflectPoint ⁻¹' U := by
  intro p hp
  exact hS ((reflectPoint_mem_modelSquare p).mpr hp)

theorem modelCurvature_reflect (kappa : ℝ) (p : Coord) :
    modelCurvature kappa (reflectPoint p) = modelCurvature kappa p := by
  simp only [modelCurvature,reflectPoint_zero,reflectPoint_one]
  rw [modelProfile_even (p 1)]

theorem reflectedMetric_model {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    (hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∀ p ∈ reflectPoint ⁻¹' U,
      gaussianCurvature (reflectedMetric g0) p = modelCurvature kappa p := by
  intro p hp
  rw [reflectedMetric_curvature hg0 hU hp,hmodel _ hp,modelCurvature_reflect]

theorem reflectedMetric_eq_pushforward (g : MetricField) :
    reflectedMetric g = affinePushforwardMetric g 0 reflectionMatrix := by
  funext p
  simp only [reflectedMetric,affinePullbackMetric,affinePushforwardMetric,
    affineInverseCoordinates,affineCoordinates,reflectionMatrix_inv,sub_zero,zero_add]

theorem reflectedMetric_tsupport (g : MetricField) :
    tsupport (reflectedMetric g) = reflectPoint '' tsupport g := by
  rw [reflectedMetric_eq_pushforward,reflectPoint_eq_affine]
  exact affinePushforwardMetric_tsupport g 0 reflectionMatrix reflectionMatrix_isUnit

theorem reflectedMetric_support_patch {eta : MetricField} (h : tsupport eta ⊆ patchBox) :
    tsupport (reflectedMetric eta) ⊆ patchBox := by
  rw [reflectedMetric_tsupport]
  rintro p ⟨q,hq,rfl⟩
  exact (reflectPoint_mem_symmetricSquare (1/10) q).mpr (h hq)

theorem reflectedScalar_jet_norm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) (p : Coord) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (reflectedScalar f) p‖ =
      ‖iteratedFDeriv ℝ k f (reflectPoint p)‖ :=
  reflectionIsometry.norm_iteratedFDeriv_comp_right f p k

theorem reflectedMetric_entry_jet_norm (g : MetricField) (p : Coord)
    (i j : Fin 2) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j) p‖ =
      ‖iteratedFDeriv ℝ k (fun q => g q i j) (reflectPoint p)‖ := by
  have he : (fun q => reflectedMetric g q i j) =
      if i=j then reflectedScalar (fun q => g q i j)
      else -reflectedScalar (fun q => g q i j) := by
    funext q
    rw [reflectedMetric_entry]
    split_ifs <;> rfl
  rw [he]
  split_ifs
  · exact reflectedScalar_jet_norm _ p k
  · rw [iteratedFDeriv_neg_apply,norm_neg]
    exact reflectedScalar_jet_norm _ p k

theorem reflectedScalar_C8 {z : Coord → ℝ} {Z : ℝ}
    (hZ : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) :
    ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k (reflectedScalar z) p‖ ≤ Z := by
  intro k hk p hp
  rw [reflectedScalar_jet_norm]
  exact hZ k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)

theorem reflectedMetric_C8 {g : MetricField} {G : ℝ}
    (hG : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) :
    ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j) p‖ ≤ G := by
  intro i j k hk p hp
  rw [reflectedMetric_entry_jet_norm]
  exact hG i j k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)

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
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection

theorem axisBump_even (a t : ℝ) : axisBump a (-t) = axisBump a t := by
  simp only [axisBump, neg_sq]

theorem inverseShear_reflect (q0 : ℝ) (p : Coord) :
    inverseShearCoordinates q0 (reflectPoint p) =
      reflectPoint (inverseShearCoordinates (-q0) p) := by
  ext i
  fin_cases i
  · change p 0 = p 0
    rfl
  · change -p 1-q0*p 0 = -(p 1-(-q0)*p 0)
    ring

theorem shear_reflect (q0 : ℝ) (p : Coord) :
    shearCoordinates q0 (reflectPoint p) =
      reflectPoint (shearCoordinates (-q0) p) := by
  ext i
  fin_cases i
  · change p 0 = p 0
    rfl
  · change -p 1+q0*p 0 = -(p 1+(-q0)*p 0)
    ring

theorem pulseScalar_reflect (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    pulseScalar a N delta tau (reflectPoint p) = pulseScalar a N delta tau p := by
  simp only [pulseScalar, reflectPoint_zero, reflectPoint_one, mul_neg, neg_div,
    temporalCutoff, axisBump_even]

theorem reflectedMetric_pulseTensor (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    reflectedMetric (pulseTensor q0 a N delta tau) = pulseTensor (-q0) a N delta tau := by
  funext p
  ext i j
  rw [reflectedMetric_entry]
  simp only [pulseTensor, shear_reflect, pulseScalar_reflect]
  fin_cases i <;> fin_cases j <;> simp [thetaCovector]

theorem reflectedMetric_testMetric (g : MetricField) (q0 a : ℝ) (N : ℕ)
    (delta tau : ℝ) :
    reflectedMetric (testMetric g q0 a N delta tau) =
      testMetric (reflectedMetric g) (-q0) a N delta tau := by
  rw [testMetric, reflectedMetric_add, reflectedMetric_pulseTensor]
  rfl

theorem reflectedMetric_sub (g h : MetricField) :
    reflectedMetric (g-h) = reflectedMetric g-reflectedMetric h := by
  funext p
  ext i j
  simp only [reflectedMetric_entry, Pi.sub_apply, Matrix.sub_apply]
  split_ifs <;> ring

theorem height_shear_reflection (z : Coord → ℝ) (q0 : ℝ) :
    heightInShearCoordinates (reflectedScalar z) (-q0) =
      reflectedScalar (heightInShearCoordinates z q0) := by
  funext p
  change z (reflectPoint (inverseShearCoordinates (-q0) p)) =
    z (inverseShearCoordinates q0 (reflectPoint p))
  rw [inverseShear_reflect]

theorem reflected_pulse_approximation_jet_norm
    (gTau gStar : MetricField) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (i j : Fin 2) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => reflectedMetric gTau q i j-
      testMetric (reflectedMetric gStar) (-q0) a N delta tau q i j) p‖ =
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) (reflectPoint p)‖ := by
  have hfun : (fun q => reflectedMetric gTau q i j-
      testMetric (reflectedMetric gStar) (-q0) a N delta tau q i j) =
      (fun q => reflectedMetric (gTau-testMetric gStar q0 a N delta tau) q i j) := by
    funext q
    simp only [← reflectedMetric_testMetric,reflectedMetric_sub,Pi.sub_apply,Matrix.sub_apply]
  rw [hfun]
  exact reflectedMetric_entry_jet_norm _ p i j k

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.Flow.Reflection

theorem PatchAdmissibleHeight.reflected {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) :
    PatchAdmissibleHeight (reflectedMetric g) (reflectedScalar z) := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := h
  have hmem {p : Coord} (hp : p ∈ modelSquare) : reflectPoint p ∈ U :=
    hSU ((reflectPoint_mem_modelSquare p).mpr hp)
  refine ⟨reflectPoint ⁻¹' U, reflectedDomain_isOpen hU,
    reflectedDomain_contains_modelSquare hSU, reflectedMetric_smoothPositive hg,
    reflectedScalar_contDiffOn hz, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [reflectedMetric_hessian_det hg hz hU (hmem hp),
      reflectedMetric_curvature hg hU (hmem hp), reflectedMetric_energy hz hU (hmem hp)]
    exact hD _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_energy hz hU (hmem hp)]
    exact hE _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_hessian_entry hg hz hU (hmem hp)]
    simpa only [ite_true] using hyy _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_quotient hg hz hU (hmem hp),abs_neg]
    exact hq _ ((reflectPoint_mem_modelSquare p).mpr hp)

theorem BoundedAdmissibleHeight.reflected {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (h : BoundedAdmissibleHeight g M z) :
    BoundedAdmissibleHeight (reflectedMetric g) M (reflectedScalar z) := by
  obtain ⟨hM,ha,hB,hyy,hE⟩ := h
  have har := ha.reflected
  obtain ⟨U,hU,hSU,hg,hz,hD,hpos,hne,hq⟩ := ha
  refine ⟨hM,har,reflectedScalar_C8 hB,?_,?_⟩
  · intro p hp
    have hpr := (reflectPoint_mem_modelSquare p).mpr hp
    rw [reflectedMetric_hessian_entry hg hz hU (hSU hpr)]
    simpa only [ite_true] using hyy _ hpr
  · intro p hp
    have hpr := (reflectPoint_mem_modelSquare p).mpr hp
    rw [reflectedMetric_energy hz hU (hSU hpr)]
    exact hE _ hpr

theorem bounded_class_reflected_center {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (h : BoundedAdmissibleHeight g M z) (q0 : ℝ) :
    |hessianQuotient (reflectedMetric g) (reflectedScalar z) 0-(-q0)| =
      |hessianQuotient g z 0-q0| := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := h.2.1
  have hzero : (0 : Coord) ∈ modelSquare := by constructor <;> intro i <;> norm_num
  have hrzero : reflectPoint (0 : Coord) = 0 := by ext i; fin_cases i <;> simp
  have hzeroU : reflectPoint (0 : Coord) ∈ U := by
    simpa only [hrzero] using hSU hzero
  rw [reflectedMetric_quotient hg hz hU (p := 0) hzeroU,hrzero]
  have he : -hessianQuotient g z 0-(-q0) = -(hessianQuotient g z 0-q0) := by ring
  rw [he,abs_neg]

end SmoothLocal.Geometry

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection

theorem reflected_actual_metric_zero_patch {g0 : MetricField} {kappa : ℝ}
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z) :
    (0 : SymmetricPerturbation) ∈
      metricPatchSet (reflectedMetric (perturbedMetric g0 eta.val)) kappa := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := hclass.2.1
  apply zero_mem_metricPatchSet
  · intro p hp
    exact (reflectedMetric_smoothPositive hg).2 p
      (hSU ((reflectPoint_mem_modelSquare p).mpr hp))
  · intro p hp
    have hpr : reflectPoint p ∈ centralBox :=
      (reflectPoint_mem_symmetricSquare (1/5) p).mpr hp
    rw [reflectedMetric_curvature hg hU (hSU (centralBox_subset_modelSquare hpr))]
    exact eta.property.2 _ hpr

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
open scoped ContDiff Topology

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection SmoothLocal.Pulse

theorem reflectPoint_initialPoint (x a : ℝ) :
    reflectPoint (![x,a] : Coord) = ![x,-a] := by
  ext i
  fin_cases i <;> simp

theorem coordPartial_one_reflectedScalar (f : Coord → ℝ) (p : Coord) :
    coordPartial 1 (reflectedScalar f) p = -coordPartial 1 f (reflectPoint p) := by
  have he : fderiv ℝ (f ∘ reflectPoint) p =
      (fderiv ℝ f (reflectPoint p)).comp
        (reflectionIsometry.toContinuousLinearEquiv : Coord →L[ℝ] Coord) :=
    reflectionIsometry.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := p)
  change fderiv ℝ (f ∘ reflectPoint) p (Pi.single 1 (1 : ℝ)) =
    -fderiv ℝ f (reflectPoint p) (Pi.single 1 (1 : ℝ))
  rw [he, ContinuousLinearMap.comp_apply]
  have hb : reflectionIsometry.toContinuousLinearEquiv (Pi.single 1 (1 : ℝ)) =
      -(Pi.single 1 (1 : ℝ) : Coord) := by
    ext i
    fin_cases i <;> simp [reflectionIsometry,reflectPoint]
  change (fderiv ℝ f (reflectPoint p)) (reflectionIsometry (Pi.single 1 1)) =
    -(fderiv ℝ f (reflectPoint p)) (Pi.single 1 1)
  change reflectionIsometry (Pi.single 1 (1 : ℝ)) = -(Pi.single 1 (1 : ℝ) : Coord) at hb
  rw [hb,map_neg]

theorem heightCauchyValue_reflected (z : Coord → ℝ) (a : ℝ) :
    heightCauchyValue (reflectedScalar z) a = heightCauchyValue z (-a) := by
  funext x
  change z (reflectPoint ![x,a]) = z ![x,-a]
  rw [reflectPoint_initialPoint]

theorem heightCauchyVelocity_reflected (z : Coord → ℝ) (a : ℝ) :
    heightCauchyVelocity (reflectedScalar z) a = -heightCauchyVelocity z (-a) := by
  funext x
  change coordPartial 1 (reflectedScalar z) ![x,a] = -coordPartial 1 z ![x,-a]
  rw [coordPartial_one_reflectedScalar,reflectPoint_initialPoint]

theorem reflected_Cauchy_jet_norms (z : Coord → ℝ) (a x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (heightCauchyValue (reflectedScalar z) a) x‖ =
      ‖iteratedFDeriv ℝ n (heightCauchyValue z (-a)) x‖ ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity (reflectedScalar z) a) x‖ =
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity z (-a)) x‖ := by
  simp [heightCauchyValue_reflected,heightCauchyVelocity_reflected,
    iteratedFDeriv_neg_apply]

theorem sheared_reflected_Cauchy_jet_norms (z : Coord → ℝ) (q0 a x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (heightCauchyValue
      (heightInShearCoordinates (reflectedScalar z) (-q0)) a) x‖ =
        ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0) (-a)) x‖ ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity
      (heightInShearCoordinates (reflectedScalar z) (-q0)) a) x‖ =
        ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0) (-a)) x‖ := by
  rw [height_shear_reflection]
  exact reflected_Cauchy_jet_norms _ a x n

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
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation
  SmoothLocal.Model

theorem reflected_capInductionHeight {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} {Z c e0 : ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) (hh : CapInductionHeight g U Z c e0 z) :
    CapInductionHeight (reflectedMetric g) (reflectPoint ⁻¹' U) Z c e0 (reflectedScalar z) := by
  have hmem {p : Coord} (hp : p ∈ modelSquare) : reflectPoint p ∈ U :=
    hSU ((reflectPoint_mem_modelSquare p).mpr hp)
  refine ⟨reflectedScalar_contDiffOn hh.smooth, reflectedScalar_C8 hh.lowJet, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [reflectedMetric_hessian_entry hg hh.smooth hU (hmem hp)]
    simp only [ite_true]
    exact hh.denominator _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_energy hh.smooth hU (hmem hp)]
    exact hh.energy _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_quotient hg hh.smooth hU (hmem hp), abs_neg]
    exact hh.quotient _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_hessian_det hg hh.smooth hU (hmem hp),
      reflectedMetric_curvature hg hU (hmem hp), reflectedMetric_energy hh.smooth hU (hmem hp)]
    exact hh.darboux _ ((reflectPoint_mem_modelSquare p).mpr hp)

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
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection SmoothLocal.Model

theorem exists_actual_reflected_capInductionFlow
    {g0 : MetricField} {kappa G Z d c e0 : ℝ} (eta : metricPatchSet g0 kappa)
    {U : Set Coord} {z : Coord → ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hg : SmoothPositiveOn (perturbedMetric g0 eta.val) U)
    (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hh : CapInductionHeight (perturbedMetric g0 eta.val) U Z c e0 z)
    (hk : 0 < kappa) (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ (W : Set Coord) (Y : ℝ → ℝ → ℝ),
      CapInductionFlow (reflectedMetric (perturbedMetric g0 eta.val)) (reflectPoint ⁻¹' U)
        G Z d c e0 kappa (reflectedScalar z) Y W := by
  have hsum : reflectedMetric g0+reflectedMetric (perturbationTensor eta.val) =
      reflectedMetric (perturbedMetric g0 eta.val) :=
    (reflectedMetric_add g0 (perturbationTensor eta.val)).symm
  have hgR : SmoothPositiveOn
      (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) (reflectPoint ⁻¹' U) := by
    rw [hsum]
    exact reflectedMetric_smoothPositive hg
  have hhR : CapInductionHeight
      (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val))
      (reflectPoint ⁻¹' U) Z c e0 (reflectedScalar z) := by
    rw [hsum]
    exact reflected_capInductionHeight hg hU hSU hh
  have hBR : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q =>
        (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) q i j) p‖ ≤ G := by
    rw [hsum]
    exact reflectedMetric_C8 hgB
  have hdetR : ∀ p ∈ modelSquare,
      d ≤ |((reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) p).det| := by
    intro p hp
    rw [hsum,reflectedMetric_det]
    exact hdet _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hcentralR : ∀ p ∈ centralBox,
      gaussianCurvature (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) p < -kappa/2 := by
    intro p hp
    have hpr : reflectPoint p ∈ centralBox :=
      (reflectPoint_mem_symmetricSquare (1/5) p).mpr hp
    rw [hsum,reflectedMetric_curvature hg hU (hSU (centralBox_subset_modelSquare hpr))]
    exact eta.property.2 _ hpr
  obtain ⟨W,Y,hflow⟩ := exists_capInductionFlow hgR (reflectedDomain_isOpen hU)
    (reflectedDomain_contains_modelSquare hSU) hG hZ hd hc he0 hBR hdetR hhR hk
    (reflectedMetric_model hg0 hU hbackground)
    (reflectedMetric_support_patch (perturbationTensor_tsupport_subset eta.val)) hcentralR
  exact ⟨W,Y,by simpa only [hsum] using hflow⟩

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
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.Flow.Reflection SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Taylor
open SmoothLocal.Model

theorem exists_actual_upper_off_pulse_cauchy_bounds_at_radius
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
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U : Set Coord) (z : Coord → ℝ),
          SmoothPositiveOn g0 U → SmoothPositiveOn (perturbedMetric g0 eta.val) U →
          IsOpen U → modelSquare ⊆ U →
          (∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 8 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
            ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
              (delta/(tau : ℝ))) x‖ ≤ B ∧
            ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
              (delta/(tau : ℝ))) x‖ ≤ B := by
  have hqneg : |-q0| ≤ (1 : ℝ)/20 := by simpa only [abs_neg] using hq0
  obtain ⟨B,hB,hcauchy⟩ := exists_actual_off_pulse_cauchy_bounds_at_radius
    (q0 := -q0) (reflectedMetric_smoothPositive hgStar) (reflectedDomain_isOpen hV)
    (reflectedDomain_contains_modelSquare hSV) M hG hd hkappa hM hqneg hr hrhalf hLr hrsmall K
  refine ⟨B,hB,?_⟩
  intro N delta hdelt
  filter_upwards [hcauchy N delta hdelt] with tau hcauchyTau
  intro g0 eta U z hg0 hg hU hSU hbackground hh hclass hgB hdet hcenter happ x hx n hn
  let g := perturbedMetric g0 eta.val
  let gr := reflectedMetric g
  let zr := reflectedScalar z
  let UR := reflectPoint ⁻¹' U
  let etaR : metricPatchSet gr kappa := ⟨0,reflected_actual_metric_zero_patch eta hclass⟩
  have heR : perturbedMetric gr etaR.val = gr := perturbedMetric_zero gr
  have hgR : SmoothPositiveOn gr UR := reflectedMetric_smoothPositive hg
  have hhR : CapInductionHeight gr UR (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) zr :=
    reflected_capInductionHeight hg hU hSU hh
  have hcR : BoundedAdmissibleHeight gr M zr := hclass.reflected
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨WR,YR,hfR⟩ := exists_actual_reflected_capInductionFlow eta hg0 hg hU hSU
    hG (Nat.cast_nonneg M) hd (one_div_pos.mpr hMR) (one_div_pos.mpr hMR)
    hgB hdet hh hkappa hbackground
  have hg4R : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => gr a i j) p‖ ≤ G := by
    intro i j k hk p hp
    change ‖iteratedFDeriv ℝ k (fun a => reflectedMetric g a i j) p‖ ≤ G
    rw [reflectedMetric_entry_jet_norm]
    exact hgB i j k (by omega) _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hdetR : ∀ p ∈ modelSquare, d ≤ |(gr p).det| := by
    intro p hp
    change d ≤ |(reflectedMetric g p).det|
    rw [reflectedMetric_det]
    exact hdet _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hcenterR : |hessianQuotient gr zr 0-(-q0)| ≤ 1/(100*boundedClassWidth kappa M) := by
    change |hessianQuotient (reflectedMetric g) (reflectedScalar z) 0-(-q0)| ≤ _
    rw [bounded_class_reflected_center hclass q0]
    exact hcenter
  have happR : ∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gr q i j-
        testMetric (reflectedMetric gStar) (-q0) (boundedClassWidth kappa M*r/16)
          N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau := by
    intro i j k hk p hp
    change ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j-
      testMetric (reflectedMetric gStar) (-q0) (boundedClassWidth kappa M*r/16)
        N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau
    rw [reflected_pulse_approximation_jet_norm]
    exact happ i j k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hbound := hcauchyTau gr etaR UR WR zr YR
    (by simpa only [heR] using hgR) (reflectedDomain_isOpen hU)
    (by simpa only [heR] using hhR) (by simpa only [heR] using hfR)
    (by simpa only [heR] using hcR) (by simpa only [heR] using hg4R)
    (by simpa only [heR] using hdetR) (by simpa only [heR] using hcenterR)
    (by simpa only [heR] using happR) x hx n hn
  have he := sheared_reflected_Cauchy_jet_norms z q0 (-delta/(tau : ℝ)) x n
  change (‖iteratedFDeriv ℝ n (heightCauchyValue
      (heightInShearCoordinates (reflectedScalar z) (-q0)) (-delta/(tau : ℝ))) x‖ ≤ B ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity
      (heightInShearCoordinates (reflectedScalar z) (-q0)) (-delta/(tau : ℝ))) x‖ ≤ B) at hbound
  rw [he.1,he.2] at hbound
  simpa only [neg_div,neg_neg] using hbound

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.exists_actual_upper_off_pulse_cauchy_bounds_at_radius := @OAI.SmoothLocal.Perturbation.exists_actual_upper_off_pulse_cauchy_bounds_at_radius
