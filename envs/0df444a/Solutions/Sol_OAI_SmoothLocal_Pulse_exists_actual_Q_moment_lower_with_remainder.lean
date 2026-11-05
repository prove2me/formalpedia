-- Prove2me | solution 1 for OAI.SmoothLocal.Pulse.exists_actual_Q_moment_lower_with_remainder
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:39:22.731025+00:00
-- url     : https://prove2.me/submissions/8ef72603-38c7-4c2f-834a-921b63704eeb

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

theorem forcingCoefficient_contDiffOn {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U)
    (hxx : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (forcingCoefficient g z) S := by
  apply (contDiffOn_const.sub ((covectorNormSq_contDiffOn hg hU hz).mono hSU)).div
    (contDiffOn_const.mul ((covHessian_contDiffOn hg hU hz 0 0).mono hSU))
  intro p hp
  exact mul_ne_zero (by norm_num) (hxx p hp)

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

theorem forcingCoefficient_one_sign {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hS : IsPreconnected S)
    (hE : ∀ p ∈ S, 0 < heightEnergy g z p)
    (hxx : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0) :
    ∀ p ∈ S, ∀ q ∈ S, 0 < forcingCoefficient g z p * forcingCoefficient g z q := by
  have hcont := (forcingCoefficient_contDiffOn hg hz hU hSU hxx).continuousOn
  have hne (p : Coord) (hp : p ∈ S) : forcingCoefficient g z p ≠ 0 := by
    rw [forcingCoefficient_eq_energy hg z (hSU hp)]
    exact div_ne_zero (hE p hp).ne'
      (mul_ne_zero (mul_ne_zero (by norm_num) (metricDet_ne_zero hg (hSU hp))) (hxx p hp))
  intro p hp q hq
  rcases lt_or_gt_of_ne (hne p hp) with hpneg | hppos
  · have hqneg : forcingCoefficient g z q < 0 := by
      by_contra hn
      obtain ⟨b, hb, heq⟩ := hS.intermediate_value₂ hp hq hcont continuousOn_const
        hpneg.le (le_of_not_gt hn)
      exact hne b hb heq
    exact mul_pos_of_neg_of_neg hpneg hqneg
  · have hqpos : 0 < forcingCoefficient g z q := by
      by_contra hn
      obtain ⟨b, hb, heq⟩ := hS.intermediate_value₂ hq hp hcont continuousOn_const
        (le_of_not_gt hn) hppos.le
      exact hne b hb heq
    exact mul_pos hppos hqpos

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

theorem closedRectangle_eq_Icc (l r b t : ℝ) :
    closedRectangle l r b t = Icc (![l,b]) (![r,t]) := by
  ext p
  change (p 0 ∈ Icc l r ∧ p 1 ∈ Icc b t) ↔
    (![l,b] ≤ p ∧ p ≤ ![r,t])
  constructor
  · intro hp
    constructor <;> intro i <;> fin_cases i
    · exact hp.1.1
    · exact hp.2.1
    · exact hp.1.2
    · exact hp.2.2
  · intro hp
    exact ⟨⟨hp.1 0,hp.2 0⟩,⟨hp.1 1,hp.2 1⟩⟩

theorem closedRectangle_isPreconnected (l r b t : ℝ) :
    IsPreconnected (closedRectangle l r b t) := by
  rw [closedRectangle_eq_Icc]
  exact (convex_Icc (![l,b] : Coord) (![r,t])).isPreconnected

def forcingFloor (e D C : ℝ) : ℝ := e/(2*max D 1*max C 1)

theorem forcingFloor_pos {e : ℝ} (he : 0 < e) (D C : ℝ) : 0 < forcingFloor e D C := by
  unfold forcingFloor
  have hD : 0 < max D 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hC : 0 < max C 1 := zero_lt_one.trans_le (le_max_right _ _)
  positivity

theorem forcingCoefficient_floor_of_reference_margins
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U)
    {e c D C : ℝ} (he : 0 < e) (hc : 0 < c)
    (hE : e ≤ heightEnergy g z p) (hdet : (g p).det ≤ D)
    (hxx : c ≤ |covHessian g z p 0 0|) (hxxup : |covHessian g z p 0 0| ≤ C) :
    forcingFloor e D C ≤ |forcingCoefficient g z p| := by
  exact (forcingCoefficient_bounds hg hp he (hg.2 p hp).det_pos hc hE le_rfl le_rfl
    (hdet.trans (le_max_left _ _)) hxx (hxxup.trans (le_max_left _ _))).2.1

theorem actual_forcingCoefficient_signed_floor
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hS : IsPreconnected S)
    {p0 : Coord} (hp0 : p0 ∈ S) {e c D C : ℝ} (he : 0 < e) (hc : 0 < c)
    (hE : ∀ p ∈ S, e ≤ heightEnergy g z p)
    (hdet : ∀ p ∈ S, (g p).det ≤ D)
    (hxx : ∀ p ∈ S, c ≤ |covHessian g z p 0 0|)
    (hxxup : ∀ p ∈ S, |covHessian g z p 0 0| ≤ C) :
    ∃ sigma : ℝ, |sigma| = 1 ∧ ∀ p ∈ S,
      sigma*forcingCoefficient g z p = |forcingCoefficient g z p| ∧
      forcingFloor e D C ≤ sigma*forcingCoefficient g z p := by
  have hxxne : ∀ p ∈ S, covHessian g z p 0 0 ≠ 0 := by
    intro p hp hz0
    have hh := hxx p hp
    rw [hz0,abs_zero] at hh
    linarith
  have hsign := forcingCoefficient_one_sign hg hz hU hSU hS
    (fun p hp => he.trans_le (hE p hp)) hxxne
  have hfloor (p : Coord) (hp : p ∈ S) :=
    forcingCoefficient_floor_of_reference_margins hg (hSU hp) he hc
      (hE p hp) (hdet p hp) (hxx p hp) (hxxup p hp)
  have hanchor : forcingCoefficient g z p0 ≠ 0 :=
    abs_pos.mp ((forcingFloor_pos he D C).trans_le (hfloor p0 hp0))
  rcases lt_or_gt_of_ne hanchor with hneg | hpos
  · refine ⟨-1,by norm_num,?_⟩
    intro p hp
    have hpneg : forcingCoefficient g z p < 0 := by
      by_contra hn
      have hn0 : 0 ≤ forcingCoefficient g z p := le_of_not_gt hn
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg hneg.le hn0
      linarith [hsign p0 hp0 p hp]
    constructor
    · rw [abs_of_neg hpneg]
      ring
    · simpa only [neg_one_mul,abs_of_neg hpneg] using hfloor p hp
  · refine ⟨1,by norm_num,?_⟩
    intro p hp
    have hppos : 0 < forcingCoefficient g z p := by
      by_contra hn
      have hn0 : forcingCoefficient g z p ≤ 0 := le_of_not_gt hn
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hpos.le hn0
      linarith [hsign p0 hp0 p hp]
    constructor
    · rw [one_mul,abs_of_pos hppos]
    · simpa only [one_mul,abs_of_pos hppos] using hfloor p hp

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

theorem temporalCutoff_integral_pos : 0 < ∫ t : ℝ, temporalCutoff t :=
  axisBump_integral_pos (by norm_num)

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
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def thetaPulseMetric (g : MetricField) (f : Coord → ℝ) : MetricField :=
  fun p => g p + !![0,0;0,f p]

def thetaPulseFirstJet (f : Coord → ℝ) (p : Coord) : MetricFirstJet :=
  fun d i j => if i=1 ∧ j=1 then coordPartial d f p else 0

def thetaPulseLowerDifference (g : MetricField) (f : Coord → ℝ) (p : Coord) : ℝ :=
  curvatureLowerJet (g p + !![0,0;0,f p])
    (metricFirstJet g p + thetaPulseFirstJet f p) -
      curvatureLowerJet (g p) (metricFirstJet g p)

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

theorem secondCoordPartial_add {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => f q+h q)) p =
      coordPartial i (coordPartial j f) p + coordPartial i (coordPartial j h) p := by
  have he : coordPartial j (fun q => f q+h q) =ᶠ[𝓝 p]
      (fun q => coordPartial j f q+coordPartial j h q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact HessianCalculus.coordPartial_add_at
      ((hf.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
      ((hh.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)) j
  rw [coordPartial_eq_of_eventuallyEq he i]
  exact HessianCalculus.coordPartial_add_at
    (((partial_contDiffOn hf hU j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    (((partial_contDiffOn hh hU j).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) i

theorem thetaPulseLowerDifference_eq {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    thetaPulseLowerDifference g f p =
      curvatureLowerTerm (thetaPulseMetric g f) p-curvatureLowerTerm g p := by
  simp only [curvatureLowerTerm,metricFirstJet_thetaPulseMetric hg hf hU hp,
    thetaPulseMetric,thetaPulseLowerDifference]

theorem thetaPulse_curvature_density {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hplus : SmoothPositiveOn (thetaPulseMetric g f) U)
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (thetaPulseMetric g f) p*(thetaPulseMetric g f p).det -
      gaussianCurvature g p*(g p).det =
        -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 f) p + thetaPulseLowerDifference g f p := by
  have h00 : (fun q => thetaPulseMetric g f q 0 0) = (fun q => g q 0 0) := by
    funext q
    simp [thetaPulseMetric_entry]
  have h01 : (fun q => thetaPulseMetric g f q 0 1) = (fun q => g q 0 1) := by
    funext q
    simp [thetaPulseMetric_entry]
  have h11 : (fun q => thetaPulseMetric g f q 1 1) = (fun q => g q 1 1+f q) := by
    funext q
    simp [thetaPulseMetric_entry]
  have hnew := gaussianCurvature_density_principal_part hplus hU hp
  rw [h00,h01,h11,secondCoordPartial_add (hg.1 1 1) hf hU hp 0 0] at hnew
  have hold := gaussianCurvature_density_principal_part hg hU hp
  rw [hnew,hold,thetaPulseLowerDifference_eq hg hf hU hp]
  ring

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

theorem actual_pulse_curvature_density
    {gStar : MetricField} {U : Set Coord} (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (hg : SmoothPositiveOn gStar U)
    (htest : SmoothPositiveOn (testMetric gStar q0 a N delta tau) U)
    (hU : IsOpen U) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    gaussianCurvature (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p) *
        (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det -
      gaussianCurvature gStar (inverseShearCoordinates q0 p) *
        (gStar (inverseShearCoordinates q0 p)).det =
      -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p +
        thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p := by
  let R := inverseShearMatrix q0
  let V := affineCoordinates 0 R ⁻¹' U
  have hR : IsUnit R := inverseShearMatrix_isUnit q0
  have hV : IsOpen V := hU.preimage (affineCoordinates_contDiff 0 R).continuous
  have hpV : p ∈ V := by
    simpa only [V,R,Set.mem_preimage,←inverseShearCoordinates_eq_affine] using hp
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V :=
    affinePullbackMetric_smoothPositive hg 0 R (Matrix.mulVec_injective_of_isUnit hR)
  have htV : SmoothPositiveOn
      (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) V :=
    affinePullbackMetric_smoothPositive htest 0 R (Matrix.mulVec_injective_of_isUnit hR)
  have htTheta : SmoothPositiveOn
      (thetaPulseMetric (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau)) V := by
    rw [←metricInShearCoordinates_test]
    exact htV
  have hformula := thetaPulse_curvature_density hgV htTheta
    (pulseScalar_contDiff a N delta tau).contDiffOn hV hpV
  rw [←metricInShearCoordinates_test] at hformula
  have hpa : affineCoordinates 0 R p ∈ U := hpV
  have hKg := gaussianCurvature_affinePullback hg hU 0 R hR p hpa
  have hKt := gaussianCurvature_affinePullback htest hU 0 R hR p hpa
  change gaussianCurvature (affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 R) p *
      (affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 R p).det -
      gaussianCurvature (affinePullbackMetric gStar 0 R) p *
        (affinePullbackMetric gStar 0 R p).det = _ at hformula
  rw [hKt,hKg,det_affinePullbackMetric,det_affinePullbackMetric] at hformula
  simpa only [R,inverseShearMatrix_det,one_pow,one_mul,
    ←inverseShearCoordinates_eq_affine] using hformula

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

theorem compact_weight_cos_integral_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {tau : ℝ} (htau : 0 < tau) :
    |∫ x : ℝ, f x*Real.cos (tau*x)| ≤ (∫ x : ℝ, |deriv f x|)/tau := by
  let v : ℝ → ℝ := fun x => Real.sin (tau*x)/tau
  have hc : Continuous (fun x : ℝ => Real.cos (tau*x)) := by fun_prop
  have hvcont : Continuous v := by dsimp only [v]; fun_prop
  have hdcont : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hdcompact : HasCompactSupport (deriv f) := hcompact.deriv
  have hfc : Integrable (fun x : ℝ => f x*Real.cos (tau*x)) :=
    (hf.continuous.mul hc).integrable_of_hasCompactSupport hcompact.mul_right
  have hdfv : Integrable (fun x : ℝ => deriv f x*v x) :=
    (hdcont.mul hvcont).integrable_of_hasCompactSupport hdcompact.mul_right
  have hfv : Integrable (fun x : ℝ => f x*v x) :=
    (hf.continuous.mul hvcont).integrable_of_hasCompactSupport hcompact.mul_right
  have hv (x : ℝ) : HasDerivAt v (Real.cos (tau*x)) x := by
    have h := ((Real.hasDerivAt_sin (tau*x)).comp x
      ((hasDerivAt_id x).const_mul tau)).div_const tau
    simp only [Function.comp_def] at h
    convert h using 1 <;> try with_reducible_and_instances rfl
    first | rfl | field_simp [htau.ne']
  have hibp : (∫ x : ℝ, f x*Real.cos (tau*x)) = -∫ x : ℝ, deriv f x*v x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
      (fun x _ => hv x) hfc hdfv hfv
  have hdint : Integrable (fun x : ℝ => |deriv f x|) :=
    hdcont.abs.integrable_of_hasCompactSupport hdcompact.abs
  have hnorm : ∀ x : ℝ, ‖deriv f x*v x‖ ≤ |deriv f x| / tau := by
    intro x
    simp only [Real.norm_eq_abs,abs_mul,v,abs_div,abs_of_pos htau]
    calc
      _ ≤ |deriv f x| * (1/tau) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) htau.le) (abs_nonneg _)
      _ = _ := by ring
  rw [hibp,abs_neg]
  have h := norm_integral_le_of_norm_le (hdint.div_const tau) (Eventually.of_forall hnorm)
  simpa only [Real.norm_eq_abs,integral_div] using h

theorem compact_weight_cos_integral_tendsto_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, f x*Real.cos (tau*x)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ tau : ℝ in atTop,
      ‖∫ x : ℝ, f x*Real.cos (tau*x)‖ ≤ (∫ x : ℝ, |deriv f x|)/tau := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau htau
    simpa only [Real.norm_eq_abs] using compact_weight_cos_integral_le hf hcompact htau
  have hzero : Tendsto (fun tau : ℝ => (∫ x : ℝ, |deriv f x|)/tau) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0)).const_mul
        (∫ x : ℝ, |deriv f x|)
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbound hzero

theorem compact_weight_cos_sq_integral_eq {f : ℝ → ℝ}
    (hf : Continuous f) (hcompact : HasCompactSupport f) (tau : ℝ) :
    (∫ x : ℝ, f x*Real.cos (tau*x)^2) =
      (1/2 : ℝ)*(∫ x : ℝ, f x)+
        (1/2 : ℝ)*(∫ x : ℝ, f x*Real.cos ((2*tau)*x)) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hcompact
  have hci : Integrable (fun x : ℝ => f x*Real.cos ((2*tau)*x)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hcompact.mul_right
  have heq : (fun x : ℝ => f x*Real.cos (tau*x)^2) =
      fun x => (1/2 : ℝ)*f x+(1/2 : ℝ)*(f x*Real.cos ((2*tau)*x)) := by
    funext x
    have hc : Real.cos ((2*tau)*x) = 2*Real.cos (tau*x)^2-1 := by
      rw [mul_assoc,Real.cos_two_mul]
    rw [hc]
    ring
  rw [heq,integral_add (hfi.const_mul (1/2)) (hci.const_mul (1/2)),
    integral_const_mul,integral_const_mul]

theorem compact_weight_cos_sq_integral_tendsto {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, f x*Real.cos (tau*x)^2) atTop
      (𝓝 ((1/2 : ℝ)*(∫ x : ℝ, f x))) := by
  have hfreq : Tendsto (fun tau : ℝ => 2*tau) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hzero := (compact_weight_cos_integral_tendsto_zero hf hcompact).comp hfreq
  have hlimit := (hzero.const_mul (1/2 : ℝ)).const_add ((1/2 : ℝ)*(∫ x : ℝ, f x))
  simpa only [compact_weight_cos_sq_integral_eq hf.continuous hcompact,
    Function.comp_def,mul_zero,add_zero] using hlimit

def spatialCutoffSquare (a x : ℝ) : ℝ := axisBump a x^2

theorem spatialCutoffSquare_contDiff (a : ℝ) : ContDiff ℝ ∞ (spatialCutoffSquare a) :=
  (axisBump_contDiff a).pow 2

theorem spatialCutoffSquare_hasCompactSupport {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (spatialCutoffSquare a) := by
  change HasCompactSupport (fun x => axisBump a x ^ 2)
  simpa only [pow_two,Pi.mul_def] using
    (axisBump_hasCompactSupport ha).mul_right (f' := axisBump a)

theorem spatialCutoffSquare_integral_pos {a : ℝ} (ha : 0 < a) :
    0 < ∫ x : ℝ, spatialCutoffSquare a x :=
  (spatialCutoffSquare_contDiff a).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (spatialCutoffSquare_hasCompactSupport ha) (fun _ => sq_nonneg _)
      (sq_pos_of_pos (axisBump_pos_zero ha)).ne'

theorem spatialCutoff_cos_sq_moment_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2) atTop
      (𝓝 ((1/2 : ℝ)*(∫ x : ℝ, axisBump a x^2))) :=
  compact_weight_cos_sq_integral_tendsto (spatialCutoffSquare_contDiff a)
    (spatialCutoffSquare_hasCompactSupport ha)

theorem spatialCutoff_cos_sq_moment_eventually_lower {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ tau : ℝ in atTop,
      c ≤ ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2 := by
  let I : ℝ := ∫ x : ℝ, axisBump a x^2
  have hI : 0 < I := spatialCutoffSquare_integral_pos ha
  refine ⟨I/4,div_pos hI (by norm_num),?_⟩
  have hgap : I/4 < (1/2 : ℝ)*I := by linarith
  have h := (spatialCutoff_cos_sq_moment_tendsto ha).eventually (eventually_gt_nhds hgap)
  exact h.mono (fun _ ht => ht.le)

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

theorem curvatureFirstDomain_isOpen : IsOpen curvatureFirstDomain :=
  isOpen_ne_fun curvatureFirstDet_contDiff.continuous continuous_const

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

theorem curvatureFirstTube_fderiv_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ curvatureFirstTube M d,
      ‖fderiv ℝ curvatureFirstFunction a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ curvatureFirstFunction) curvatureFirstDomain :=
    (curvatureFirstFunction_contDiffOn.fderiv_of_isOpen (m := 0)
      curvatureFirstDomain_isOpen (by simp)).continuousOn
  obtain ⟨C,hC⟩ := (curvatureFirstTube_isCompact M d).exists_bound_of_continuousOn
    (hcont.mono (curvatureFirstTube_subset_domain M hd))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

theorem theta_first_segment_det (a : CurvatureFirstInput) (f : Coord → ℝ) (p : Coord)
    (t : ℝ) :
    (Matrix.of ((1-t) • a + t • (a+thetaCurvatureFirstIncrement f p)).1).det =
      (1-t)*(Matrix.of a.1).det+t*(Matrix.of (a+thetaCurvatureFirstIncrement f p).1).det := by
  simp only [Matrix.det_fin_two,thetaCurvatureFirstIncrement,Prod.fst_add,Prod.smul_fst,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.of_apply]
  ring

theorem theta_first_segment_subset_tube (a : CurvatureFirstInput) (f : Coord → ℝ) (p : Coord)
    {M d : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖a+thetaCurvatureFirstIncrement f p‖ ≤ M)
    (hda : d ≤ (Matrix.of a.1).det)
    (hdb : d ≤ (Matrix.of (a+thetaCurvatureFirstIncrement f p).1).det) :
    segment ℝ a (a+thetaCurvatureFirstIncrement f p) ⊆ curvatureFirstTube M d := by
  intro x hx
  have hball : x ∈ Metric.closedBall (0 : CurvatureFirstInput) M :=
    (convex_closedBall (0 : CurvatureFirstInput) M).segment_subset
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using ha)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hb) hx
  refine ⟨hball,?_⟩
  rw [segment_eq_image] at hx
  obtain ⟨t,ht,rfl⟩ := hx
  change d ≤ (Matrix.of ((1-t) • a + t • (a+thetaCurvatureFirstIncrement f p)).1).det
  rw [theta_first_segment_det]
  have h0 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hda)
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr hdb)
  nlinarith

theorem thetaPulseLowerDifference_eq_firstFunction (g : MetricField) (f : Coord → ℝ) (p : Coord) :
    thetaPulseLowerDifference g f p =
      curvatureFirstFunction (actualCurvatureFirstInput g p+thetaCurvatureFirstIncrement f p)-
        curvatureFirstFunction (actualCurvatureFirstInput g p) := rfl

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

theorem exists_uniform_thetaPulseLowerDifference_bound (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (f : Coord → ℝ) (p : Coord),
      ‖actualCurvatureFirstInput g p‖ ≤ B → d ≤ (g p).det →
      ‖thetaCurvatureFirstIncrement f p‖ ≤ 1 → |g p 0 0| * |f p| ≤ d/2 →
      |thetaPulseLowerDifference g f p| ≤ C*‖thetaCurvatureFirstIncrement f p‖ := by
  obtain ⟨C,hC,hbound⟩ := curvatureFirstTube_fderiv_bound (B+1) (half_pos hd)
  refine ⟨C,hC,?_⟩
  intro g f p hg hdet hincr hsmall
  let a := actualCurvatureFirstInput g p
  let b := a+thetaCurvatureFirstIncrement f p
  have ha : ‖a‖ ≤ B+1 := hg.trans (by linarith)
  have hb : ‖b‖ ≤ B+1 := (norm_add_le _ _).trans (add_le_add hg hincr)
  have hda : d/2 ≤ (Matrix.of a.1).det := (by linarith : d/2 ≤ d).trans hdet
  have hdetEq : (Matrix.of b.1).det = (g p).det+g p 0 0*f p := by
    simp only [b,a,actualCurvatureFirstInput,thetaCurvatureFirstIncrement,
      Matrix.det_fin_two,Prod.fst_add,Pi.add_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.of_apply]
    ring
  have hdb : d/2 ≤ (Matrix.of b.1).det := by
    rw [hdetEq]
    have hprod : -(d/2) ≤ g p 0 0*f p := by
      have h := neg_abs_le (g p 0 0*f p)
      rw [abs_mul] at h
      linarith
    linarith
  have htube := theta_first_segment_subset_tube a f p ha hb hda hdb
  have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ curvatureFirstFunction x := by
    intro x hx
    exact (curvatureFirstFunction_contDiffOn.contDiffAt
      (curvatureFirstDomain_isOpen.mem_nhds
        (curvatureFirstTube_subset_domain (B+1) (half_pos hd) (htube hx)))).differentiableAt (by simp)
  have h := (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
    (fun x hx => hbound x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  simpa only [b,a,thetaPulseLowerDifference_eq_firstFunction,Real.norm_eq_abs,
    add_sub_cancel_left] using h

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

theorem coordPartial_xi_eq_line_deriv {f : Coord → ℝ}
    (hf : Differentiable ℝ f) (p : Coord) :
    coordPartial 0 f p = deriv (fun x => f (coordinatePoint x (p 1))) (p 0) := by
  have h := (hf (coordinatePoint (p 0) (p 1))).hasFDerivAt.comp_hasDerivAt
    (p 0) (point_hasDerivAt_t (p 0) (p 1))
  simpa only [point_eta,coordPartial,Function.comp_def] using h.deriv.symm

theorem pulseLine_hasDerivAt (a : ℝ) (N : ℕ) (delta tau x y : ℝ) :
    HasDerivAt (fun u => pulseScalar a N delta tau (coordinatePoint u y))
      ((1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x))) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by simp) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := (((hχ.const_mul (1/tau^N)).mul_const
    (temporalCutoff (tau*y/delta))).mul hc)
  simp only [Function.comp_def, Pi.mul_def, mul_one] at h
  convert h using 1 <;>
    (first | rfl | (funext u; simp [pulseScalar, coordinatePoint]) | ring)

theorem pulseScalar_xi (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    coordPartial 0 (pulseScalar a N delta tau) p =
      (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (axisBump a) (p 0)*Real.cos (tau*p 0)-
          tau*axisBump a (p 0)*Real.sin (tau*p 0)) := by
  rw [coordPartial_xi_eq_line_deriv ((pulseScalar_contDiff a N delta tau).differentiable (by simp))]
  exact (pulseLine_hasDerivAt a N delta tau (p 0) (p 1)).deriv

theorem pulseXiLine_hasDerivAt (a : ℝ) (N : ℕ) (delta tau x y : ℝ) :
    HasDerivAt
      (fun u => (1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (axisBump a) u*Real.cos (tau*u)-tau*axisBump a u*Real.sin (tau*u)))
      ((1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (deriv (axisBump a)) x*Real.cos (tau*x)-
          2*tau*deriv (axisBump a) x*Real.sin (tau*x)-
            tau^2*axisBump a x*Real.cos (tau*x))) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by simp) x).hasDerivAt
  have hχ' := (((contDiff_infty_iff_deriv.mp (axisBump_contDiff a)).2).differentiable
    (by simp) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have hs := (Real.hasDerivAt_sin (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := (((hχ'.mul hc).sub ((hχ.const_mul tau).mul hs)).const_mul
    ((1/tau^N)*temporalCutoff (tau*y/delta)))
  simp only [Function.comp_def, Pi.mul_def, Pi.sub_def, mul_one] at h
  convert h using 1 <;> try with_reducible_and_instances rfl
  first | rfl | ring

theorem pulseScalar_xixi (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p =
      (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)-
          2*tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
            tau^2*axisBump a (p 0)*Real.cos (tau*p 0)) := by
  have hf : ContDiff ℝ ∞ (coordPartial 0 (pulseScalar a N delta tau)) :=
    contDiffOn_univ.mp (partial_contDiffOn
      (pulseScalar_contDiff a N delta tau).contDiffOn isOpen_univ 0)
  rw [coordPartial_xi_eq_line_deriv (hf.differentiable (by simp))]
  have he : (fun x => coordPartial 0 (pulseScalar a N delta tau) (coordinatePoint x (p 1))) =
      (fun x => (1/tau^N)*temporalCutoff (tau*p 1/delta)*
        (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x))) := by
    funext x
    rw [pulseScalar_xi]
    simp [coordinatePoint]
  rw [he]
  exact (pulseXiLine_hasDerivAt a N delta tau (p 0) (p 1)).deriv

def pulsePrincipalLeading (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (tau^2/(2*tau^N))*axisBump a (p 0)*temporalCutoff (tau*p 1/delta)*Real.cos (tau*p 0)

def pulsePrincipalRemainder (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (1/tau^N)*temporalCutoff (tau*p 1/delta)*
    (tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
      (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0))

theorem pulse_principal_exact (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) :
    -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p =
      pulsePrincipalLeading a N delta tau p + pulsePrincipalRemainder a N delta tau p := by
  rw [pulseScalar_xixi]
  unfold pulsePrincipalLeading pulsePrincipalRemainder
  ring

theorem pulsePrincipalRemainderBound_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ pulsePrincipalRemainderBound a ha := by
  exact mul_nonneg (axisBumpDerivativeBound_pos (by norm_num) 0).le
    (add_nonneg (axisBumpDerivativeBound_pos ha 1).le (axisBumpDerivativeBound_pos ha 2).le)

theorem pulse_principal_remainder_le {a : ℝ} (ha : 0 < a) (N : ℕ)
    (delta : ℝ) {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    |pulsePrincipalRemainder a N delta tau p| ≤
      pulsePrincipalRemainderBound a ha * tau/tau^N := by
  let A1 := axisBumpDerivativeBound a ha 1
  let A2 := axisBumpDerivativeBound a ha 2
  let P0 := axisBumpDerivativeBound (1/2) (by norm_num) 0
  have hA1 : 0 ≤ A1 := (axisBumpDerivativeBound_pos ha 1).le
  have hA2 : 0 ≤ A2 := (axisBumpDerivativeBound_pos ha 2).le
  have hP0 : 0 ≤ P0 := (axisBumpDerivativeBound_pos (by norm_num) 0).le
  have ht0 : 0 < tau := zero_lt_one.trans_le ht
  have hq : 0 ≤ (1/tau^N) := div_nonneg zero_le_one (pow_nonneg ht0.le N)
  have hχ1 : |deriv (axisBump a) (p 0)| ≤ A1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_one,Real.norm_eq_abs]
      using axisBump_derivative_le ha 1 (p 0)
  have hχ2 : |deriv (deriv (axisBump a)) (p 0)| ≤ A2 := by
    simpa only [A2,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      show 2=1+1 by omega,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,Real.norm_eq_abs]
      using axisBump_derivative_le ha 2 (p 0)
  have hφ : |temporalCutoff (tau*p 1/delta)| ≤ P0 := by
    simpa only [P0,temporalCutoff,norm_iteratedFDeriv_zero,Real.norm_eq_abs]
      using axisBump_derivative_le (by norm_num : (0 : ℝ)<1/2) 0 (tau*p 1/delta)
  have hinner : |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
      (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| ≤ tau*(A1+A2) := by
    calc
      _ ≤ |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)|+
          |(1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| := abs_sub _ _
      _ = tau*|deriv (axisBump a) (p 0)| *|Real.sin (tau*p 0)|+
          (1/2 : ℝ)*|deriv (deriv (axisBump a)) (p 0)| *|Real.cos (tau*p 0)| := by
        simp only [abs_mul,abs_of_pos ht0]
        norm_num
      _ ≤ tau*A1*1+(1/2 : ℝ)*A2*1 := by
        exact add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left hχ1 ht0.le) (Real.abs_sin_le_one _)
            (abs_nonneg _) (mul_nonneg ht0.le hA1))
          (mul_le_mul (mul_le_mul_of_nonneg_left hχ2 (by norm_num)) (Real.abs_cos_le_one _)
            (abs_nonneg _) (mul_nonneg (by norm_num) hA2))
      _ ≤ tau*(A1+A2) := by nlinarith [mul_le_mul_of_nonneg_right ht hA2]
  calc
    _ = (1/tau^N)*|temporalCutoff (tau*p 1/delta)| *
        |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
          (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| := by
      simp only [pulsePrincipalRemainder,abs_mul,abs_of_nonneg hq]
    _ ≤ ((1/tau^N)*P0)*(tau*(A1+A2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hφ hq) hinner (abs_nonneg _)
        (mul_nonneg hq hP0)
    _ = pulsePrincipalRemainderBound a ha*tau/tau^N := by
      dsimp only [A1,A2,P0,pulsePrincipalRemainderBound]
      ring

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

def pulseMomentWeight (a delta tau : ℝ) (q : ℝ × ℝ) : ℝ :=
  temporalCutoff (tau*q.1/delta)*(axisBump a q.2^2*Real.cos (tau*q.2)^2)

theorem pulsePairRectangle_isCompact (a delta tau : ℝ) :
    IsCompact (pulsePairRectangle a delta tau) := isCompact_Icc.prod isCompact_Icc

theorem pulsePairPoint_continuous : Continuous pulsePairPoint := by
  unfold pulsePairPoint boxPoint
  fun_prop

theorem pulsePairPoint_mem {a delta tau : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ pulsePairRectangle a delta tau) : pulsePairPoint q ∈ pulseStrip a delta tau :=
  boxPoint_mem hq.2 hq.1

theorem pulseStrip_zero_mem {a delta tau : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ delta) (ht : 0 < tau) :
    boxPoint 0 0 ∈ pulseStrip a delta tau := by
  apply boxPoint_mem <;> constructor <;> linarith [div_nonneg hd ht.le]

theorem pulseMomentWeight_continuous (a delta tau : ℝ) :
    Continuous (pulseMomentWeight a delta tau) := by
  unfold pulseMomentWeight temporalCutoff
  exact (((axisBump_contDiff (1/2)).continuous.comp (by fun_prop)).mul
    ((((axisBump_contDiff a).continuous.comp continuous_snd).pow 2).mul (by fun_prop)))

theorem pulseMomentWeight_nonneg (a delta tau : ℝ) (q : ℝ × ℝ) :
    0 ≤ pulseMomentWeight a delta tau q :=
  mul_nonneg (axisBump_nonneg _ _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem pulseTest_continuous (a tau : ℝ) : Continuous (pulseTest a tau) :=
  (axisBump_contDiff a).continuous.mul (by fun_prop)

theorem spatial_moment_Icc_eq {a : ℝ} (ha : 0 < a) (tau : ℝ) :
    (∫ x in Icc (-a) a, axisBump a x^2*Real.cos (tau*x)^2) =
      ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2 := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : axisBump a x = 0 := by
    by_contra hn
    have h := abs_lt.mp (axisBump_support_bound ha hn)
    exact hx ⟨h.1.le,h.2.le⟩
  simp only [hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul]

theorem temporal_pulse_integral {delta tau : ℝ} (hd : 0 < delta) (ht : 0 < tau) :
    (∫ theta in Icc (-(delta/tau)) (delta/tau), temporalCutoff (tau*theta/delta)) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta) := by
  have hglobal : (∫ theta : ℝ, temporalCutoff (tau*theta/delta)) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta) := by
    have heq : (fun theta : ℝ => temporalCutoff (tau*theta/delta)) =
        fun theta => temporalCutoff ((tau/delta)*theta) := by
      funext theta
      congr 1
      ring
    rw [heq,Measure.integral_comp_mul_left]
    simp only [inv_div,abs_of_pos (div_pos hd ht),smul_eq_mul]
  rw [←hglobal]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro theta htheta
  by_contra hn
  have h := axisBump_support_bound (by norm_num : (0 : ℝ) < 1/2) hn
  rw [abs_div,abs_mul,abs_of_pos ht,abs_of_pos hd] at h
  have hmul : tau*|theta| < delta/2 := by
    have hh := (div_lt_iff₀ hd).mp h
    linarith
  have htheta' : |theta| ≤ delta/tau := (le_div_iff₀ ht).mpr (by nlinarith)
  exact htheta (abs_le.mp htheta')

theorem pulseMomentWeight_integral {a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) :
    (∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta)*
        (∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2) := by
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl]
  unfold pulseMomentWeight
  rw [setIntegral_prod_mul (fun theta : ℝ => temporalCutoff (tau*theta/delta))
    (fun x : ℝ => axisBump a x^2*Real.cos (tau*x)^2)
    (Icc (-(delta/tau)) (delta/tau)) (Icc (-a) a),
    temporal_pulse_integral hd ht,spatial_moment_Icc_eq ha tau]

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

theorem scalarPulseFirstJetBudget_tendsto_zero {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hN : 1 < N) (delta : ℝ) :
    Tendsto (scalarPulseFirstJetBudget a ha N delta) atTop (𝓝 0) := by
  have hn : N-1 ≠ 0 := by omega
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).pow (N-1)
  have h : Tendsto (fun t : ℝ => scalarPulseFirstJetBound a ha delta*(t⁻¹)^(N-1)) atTop (𝓝 0) := by
    simpa only [zero_pow hn,mul_zero] using hi.const_mul (scalarPulseFirstJetBound a ha delta)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hN' : N = 1+(N-1) := by omega
  have hr : t/t^N = (t⁻¹)^(N-1) := by
    conv_lhs => rw [hN',pow_add,pow_one]
    rw [inv_pow]
    field_simp [ht.ne']
  simp only [scalarPulseFirstJetBudget,mul_div_assoc,hr]

theorem exists_uniform_actual_pulse_lower_bound (B : ℝ) {d : ℝ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, ∃ T : ℝ, 1 ≤ T ∧
      ∀ tau : ℝ, T ≤ tau → ∀ (g : MetricField) (p : Coord),
        ‖actualCurvatureFirstInput g p‖ ≤ B → d ≤ (g p).det →
        |thetaPulseLowerDifference g (pulseScalar a N delta tau) p| ≤
          C*scalarPulseFirstJetBudget a ha N delta tau := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_thetaPulseLowerDifference_bound B hd
  refine ⟨C,hC,?_⟩
  intro delta
  let beta := max B 0+1
  have hbeta : 0 < beta := by dsimp only [beta]; linarith [le_max_right B 0]
  let e := min 1 (d/(2*beta))
  have he : 0 < e := lt_min zero_lt_one (div_pos hd (mul_pos (by norm_num) hbeta))
  have hev : ∀ᶠ tau : ℝ in atTop, scalarPulseFirstJetBudget a ha N delta tau < e :=
    (scalarPulseFirstJetBudget_tendsto_zero ha N hN delta).eventually (eventually_lt_nhds he)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hev
  refine ⟨max T 1,le_max_right _ _,?_⟩
  intro tau ht g p hg hdet
  have ht1 : 1 ≤ tau := (le_max_right _ _).trans ht
  have htT : T ≤ tau := (le_max_left _ _).trans ht
  have hsmall1 : scalarPulseFirstJetBudget a ha N delta tau ≤ 1 :=
    (hT tau htT).le.trans (min_le_left _ _)
  have hsmallD : scalarPulseFirstJetBudget a ha N delta tau ≤ d/(2*beta) :=
    (hT tau htT).le.trans (min_le_right _ _)
  have hg00 : |g p 0 0| ≤ beta := by
    have h0 : |g p 0 0| ≤ ‖actualCurvatureFirstInput g p‖ := by
      simpa only [Real.norm_eq_abs] using
        ((norm_le_pi_norm (g p 0) 0).trans (norm_le_pi_norm (g p) 0)).trans
          (norm_fst_le (actualCurvatureFirstInput g p))
    exact (h0.trans hg).trans (by dsimp only [beta]; linarith [le_max_left B 0])
  have hproduct : |g p 0 0| * |pulseScalar a N delta tau p| ≤ d/2 := by
    calc
      _ ≤ beta*scalarPulseFirstJetBudget a ha N delta tau :=
        mul_le_mul hg00 (pulseScalar_first_jet_bounds ha N delta ht1 p).1
          (abs_nonneg _) hbeta.le
      _ ≤ beta*(d/(2*beta)) := mul_le_mul_of_nonneg_left hsmallD hbeta.le
      _ = d/2 := by field_simp [hbeta.ne']
  have hinc := thetaPulse_first_increment_bound ha N delta ht1 p
  exact (hbound g (pulseScalar a N delta tau) p hg hdet (hinc.trans hsmall1) hproduct).trans
    (mul_le_mul_of_nonneg_left hinc hC)

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

theorem actual_leading_weighted_moment_eq (g : MetricField) (z : Coord → ℝ)
    (a delta : ℝ) (N : ℕ) {tau : ℝ} (ht : 0 < tau) :
    pulseWeightedMoment a delta tau
      (fun p => 2*forcingCoefficient g z p*pulsePrincipalLeading a N delta tau p) =
      (tau^2/tau^N)*(∫ q in pulsePairRectangle a delta tau,
        forcingCoefficient g z (pulsePairPoint q)*pulseMomentWeight a delta tau q
          ∂volume.prod volume) := by
  have heq (q : ℝ × ℝ) :
      (2*forcingCoefficient g z (pulsePairPoint q)*
        pulsePrincipalLeading a N delta tau (pulsePairPoint q))*pulseTest a tau q.2 =
      (tau^2/tau^N)*(forcingCoefficient g z (pulsePairPoint q)*pulseMomentWeight a delta tau q) := by
    have h0 : pulsePairPoint q 0 = q.2 := by simp [pulsePairPoint,boxPoint]
    have h1 : pulsePairPoint q 1 = q.1 := by simp [pulsePairPoint,boxPoint]
    unfold pulsePrincipalLeading pulseTest pulseMomentWeight
    rw [h0,h1]
    field_simp [ht.ne']
  unfold pulseWeightedMoment
  simp_rw [heq]
  rw [integral_const_mul]

theorem signed_coefficient_weighted_integral_lower
    {a delta tau sigma d0 : ℝ} {D : Coord → ℝ}
    (hD : ContinuousOn D (pulseStrip a delta tau)) (hsigma : |sigma| = 1)
    (hfloor : ∀ p ∈ pulseStrip a delta tau, d0 ≤ sigma*D p) :
    d0*(∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) ≤
      |∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume| := by
  have hDw : ContinuousOn
      (fun q => D (pulsePairPoint q)*pulseMomentWeight a delta tau q)
      (pulsePairRectangle a delta tau) :=
    (hD.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).mul
      (pulseMomentWeight_continuous a delta tau).continuousOn
  have hDi : IntegrableOn
      (fun q => D (pulsePairPoint q)*pulseMomentWeight a delta tau q)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    hDw.integrableOn_compact (pulsePairRectangle_isCompact a delta tau)
  have hwi : IntegrableOn (pulseMomentWeight a delta tau)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    (pulseMomentWeight_continuous a delta tau).continuousOn.integrableOn_compact
    (pulsePairRectangle_isCompact a delta tau)
  have hmono : d0*(∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) ≤ sigma*(∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume) := by
    have h := integral_mono_ae (hwi.const_mul d0) (hDi.const_mul sigma) (by
      filter_upwards [ae_restrict_mem (pulsePairRectangle_isCompact a delta tau).measurableSet] with q hq
      have hp := mul_le_mul_of_nonneg_right (hfloor _ (pulsePairPoint_mem hq))
        (pulseMomentWeight_nonneg a delta tau q)
      simpa only [mul_assoc] using hp)
    simpa only [integral_const_mul] using h
  apply hmono.trans
  calc
    _ ≤ |sigma*(∫ q in pulsePairRectangle a delta tau,
        D (pulsePairPoint q)*pulseMomentWeight a delta tau q ∂volume.prod volume)| := le_abs_self _
    _ = _ := by rw [abs_mul,hsigma,one_mul]

theorem exists_actual_leading_forcing_moment_lower {a e c : ℝ}
    (ha : 0 < a) (he : 0 < e) (hc : 0 < c) (D C : ℝ) (N : ℕ) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ tau : ℝ in atTop,
      ∀ delta : ℝ, 0 < delta → ∀ (g : MetricField) (z : Coord → ℝ) (U : Set Coord),
        SmoothPositiveOn g U → ContDiffOn ℝ ∞ z U → IsOpen U →
        pulseStrip a delta tau ⊆ U →
        (∀ p ∈ pulseStrip a delta tau, e ≤ heightEnergy g z p) →
        (∀ p ∈ pulseStrip a delta tau, (g p).det ≤ D) →
        (∀ p ∈ pulseStrip a delta tau, c ≤ |covHessian g z p 0 0|) →
        (∀ p ∈ pulseStrip a delta tau, |covHessian g z p 0 0| ≤ C) →
        c3*delta*tau/tau^N ≤
          |pulseWeightedMoment a delta tau
            (fun p => 2*forcingCoefficient g z p*pulsePrincipalLeading a N delta tau p)| := by
  obtain ⟨cs,hcs,hspatial⟩ := spatialCutoff_cos_sq_moment_eventually_lower ha
  let c3 := forcingFloor e D C*(∫ theta : ℝ, temporalCutoff theta)*cs
  have hc3 : 0 < c3 := mul_pos
    (mul_pos (forcingFloor_pos he D C) temporalCutoff_integral_pos) hcs
  refine ⟨c3,hc3,?_⟩
  filter_upwards [hspatial,eventually_gt_atTop (0 : ℝ)] with tau hspatialTau ht
  intro delta hd g z U hg hz hU hSU hE hdet hxx hxxup
  obtain ⟨sigma,hsigma,hsigned⟩ := actual_forcingCoefficient_signed_floor hg hz hU hSU
    (closedRectangle_isPreconnected (-a) a (-(delta/tau)) (delta/tau))
    (pulseStrip_zero_mem ha.le hd.le ht) he hc hE hdet hxx hxxup
  have hxxne : ∀ p ∈ pulseStrip a delta tau, covHessian g z p 0 0 ≠ 0 := by
    intro p hp hz0
    have h := hxx p hp
    rw [hz0,abs_zero] at h
    linarith
  have hcont := (forcingCoefficient_contDiffOn hg hz hU hSU hxxne).continuousOn
  have hmoment := signed_coefficient_weighted_integral_lower hcont hsigma
    (fun p hp => (hsigned p hp).2)
  rw [pulseMomentWeight_integral ha hd ht] at hmoment
  have hscale : 0 ≤ tau^2/tau^N := div_nonneg (sq_nonneg tau) (pow_nonneg ht.le N)
  rw [actual_leading_weighted_moment_eq g z a delta N ht,abs_mul,abs_of_nonneg hscale]
  calc
    c3*delta*tau/tau^N = (tau^2/tau^N)*
      (forcingFloor e D C*((delta/tau)*(∫ theta : ℝ, temporalCutoff theta)*cs)) := by
        dsimp only [c3]
        field_simp [ht.ne']
    _ ≤ (tau^2/tau^N)*(forcingFloor e D C*((delta/tau)*
        (∫ theta : ℝ, temporalCutoff theta)*
          (∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      apply mul_le_mul_of_nonneg_left _ (forcingFloor_pos he D C).le
      exact mul_le_mul_of_nonneg_left hspatialTau
        (mul_nonneg (div_nonneg hd.le ht.le) temporalCutoff_integral_pos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hmoment hscale

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

def curvatureDensityJetError (g h : MetricField) (p : Coord) : ℝ :=
  (coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
    coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p) -
  ((coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
      coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p) +
    (coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
      coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p))/2 +
  curvatureLowerTerm g p-curvatureLowerTerm h p

theorem curvatureDensityJetError_eq {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    curvatureDensityJetError g h p = curvatureDensity g p-curvatureDensity h p := by
  unfold curvatureDensity curvatureDensityJetError
  rw [gaussianCurvature_density_principal_part hg hU hp,
    gaussianCurvature_density_principal_part hh hU hp]
  ring

theorem curvatureDensityJetError_le (g h : MetricField) (p : Coord) {e : ℝ}
    (hxy : |coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
      coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p| ≤ e)
    (hxx : |coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
      coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p| ≤ e)
    (hyy : |coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
      coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p| ≤ e) :
    |curvatureDensityJetError g h p| ≤ 2*e+|curvatureLowerTerm g p-curvatureLowerTerm h p| := by
  let x := coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
    coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p
  let y := coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
    coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p
  let z := coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
    coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p
  have hmain : |x-(y+z)/2| ≤ 2*e := by
    calc
      _ ≤ |x|+|(y+z)/2| := abs_sub _ _
      _ = |x|+|y+z|/2 := by rw [abs_div]; norm_num
      _ ≤ e+(e+e)/2 := add_le_add hxy
        (div_le_div_of_nonneg_right ((abs_add_le y z).trans (add_le_add hxx hyy)) (by norm_num))
      _ = 2*e := by ring
  have heq : curvatureDensityJetError g h p =
      (x-(y+z)/2)+(curvatureLowerTerm g p-curvatureLowerTerm h p) := by
    dsimp only [curvatureDensityJetError,x,y,z]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmain le_rfl)

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

theorem pulseTest_abs_le (a tau x : ℝ) : |pulseTest a tau x| ≤ axisBump a x := by
  unfold pulseTest
  rw [abs_mul,abs_of_nonneg (axisBump_nonneg a x)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (axisBump_nonneg a x)

theorem axisBump_Icc_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in Icc (-a) a, axisBump a x) = ∫ x : ℝ, axisBump a x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra hn
  have h := abs_lt.mp (axisBump_support_bound ha hn)
  exact hx ⟨h.1.le,h.2.le⟩

theorem pulse_spatial_mass_integral {a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau) :
    (∫ q in pulsePairRectangle a delta tau, axisBump a q.2 ∂volume.prod volume) =
      (2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  have hw : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hh := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun _ : ℝ => (1 : ℝ)) (axisBump a) (Icc (-(delta/tau)) (delta/tau)) (Icc (-a) a)
  simp only [one_mul] at hh
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl,hh,
    setIntegral_const,Real.volume_real_Icc_of_le hw,smul_eq_mul,mul_one,axisBump_Icc_integral ha]
  ring

theorem pulseWeightedMoment_bound {a delta tau B : ℝ} {f : Coord → ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau) (hB : 0 ≤ B)
    (hf : ∀ p ∈ pulseStrip a delta tau, |f p| ≤ B) :
    |pulseWeightedMoment a delta tau f| ≤
      B*(2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  have hmajor : IntegrableOn (fun q : ℝ × ℝ => B*axisBump a q.2)
      (pulsePairRectangle a delta tau) (volume.prod volume) :=
    ((continuous_const.mul ((axisBump_contDiff a).continuous.comp continuous_snd)).continuousOn).integrableOn_compact
      (pulsePairRectangle_isCompact a delta tau)
  have hpoint : ∀ᵐ q ∂(volume.prod volume).restrict (pulsePairRectangle a delta tau),
      ‖f (pulsePairPoint q)*pulseTest a tau q.2‖ ≤ B*axisBump a q.2 := by
    filter_upwards [ae_restrict_mem (pulsePairRectangle_isCompact a delta tau).measurableSet] with q hq
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hf _ (pulsePairPoint_mem hq)) (pulseTest_abs_le a tau q.2)
      (abs_nonneg _) hB
  have h := norm_integral_le_of_norm_le hmajor hpoint
  simp only [Real.norm_eq_abs,integral_const_mul] at h
  rw [pulse_spatial_mass_integral ha hd ht] at h
  simpa only [pulseWeightedMoment,mul_assoc] using h

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

theorem first_jet_close_segment_subset_tube (a b : CurvatureFirstInput) {B d : ℝ}
    (ha : ‖a‖ ≤ B) (hdet : d ≤ (Matrix.of a.1).det) (hdist : ‖b-a‖ ≤ 1)
    (hsmall : (4*max B 0+2)*‖b-a‖ ≤ d/2) :
    segment ℝ a b ⊆ curvatureFirstTube (max B 0+1) (d/2) := by
  intro x hx
  have hxa : ‖x-a‖ ≤ ‖b-a‖ := by
    have hball : x ∈ Metric.closedBall a ‖b-a‖ :=
      (convex_closedBall a ‖b-a‖).segment_subset
        (by simp) (Metric.mem_closedBall.mpr (dist_eq_norm b a).le) hx
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hball
  have hxnorm : ‖x‖ ≤ max B 0+1 := by
    calc
      _ = ‖(x-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-a‖+‖a‖ := norm_add_le _ _
      _ ≤ 1+max B 0 := add_le_add (hxa.trans hdist) (ha.trans (le_max_left _ _))
      _ = _ := by ring
  have hmatrixD : ‖x.1-a.1‖ ≤ ‖b-a‖ :=
    (show ‖x.1-a.1‖ ≤ ‖x-a‖ from norm_fst_le (x-a)).trans hxa
  have hmatrixA : ‖a.1‖ ≤ max B 0 := (norm_fst_le a).trans (ha.trans (le_max_left _ _))
  have hdetdiff := det_sub_le_small_first_distance (Matrix.of a.1) (Matrix.of x.1) (le_max_right B 0)
    (norm_nonneg _) hdist hmatrixA hmatrixD
  have hxdet : d/2 ≤ (Matrix.of x.1).det := by
    have hneg := neg_abs_le ((Matrix.of x.1).det-(Matrix.of a.1).det)
    linarith [hdetdiff.trans hsmall]
  exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxnorm,hxdet⟩

theorem exists_uniform_curvature_first_comparison (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : CurvatureFirstInput,
      ‖a‖ ≤ B → d ≤ (Matrix.of a.1).det → ‖b-a‖ ≤ 1 →
      (4*max B 0+2)*‖b-a‖ ≤ d/2 →
      |curvatureFirstFunction b-curvatureFirstFunction a| ≤ C*‖b-a‖ := by
  obtain ⟨C,hC,hbound⟩ := curvatureFirstTube_fderiv_bound (max B 0+1) (half_pos hd)
  refine ⟨C,hC,?_⟩
  intro a b ha hdet hdist hsmall
  have htube := first_jet_close_segment_subset_tube a b ha hdet hdist hsmall
  have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ curvatureFirstFunction x := by
    intro x hx
    exact (curvatureFirstFunction_contDiffOn.contDiffAt (curvatureFirstDomain_isOpen.mem_nhds
      (curvatureFirstTube_subset_domain (max B 0+1) (half_pos hd) (htube hx)))).differentiableAt (by simp)
  simpa only [Real.norm_eq_abs] using
    (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
      (fun x hx => hbound x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)

theorem exists_uniform_curvature_density_comparison (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g h : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn h U → IsOpen U →
      ∀ p ∈ U, ∀ e : ℝ,
        ‖actualCurvatureFirstInput h p‖ ≤ B → d ≤ (h p).det →
        ‖actualCurvatureFirstInput g p-actualCurvatureFirstInput h p‖ ≤ e →
        e ≤ 1 → (4*max B 0+2)*e ≤ d/2 →
        (∀ i j k l : Fin 2,
          |coordPartial i (coordPartial j (fun q => g q k l)) p-
            coordPartial i (coordPartial j (fun q => h q k l)) p| ≤ e) →
        |curvatureDensity g p-curvatureDensity h p| ≤ C*e := by
  obtain ⟨C0,hC0,hbound⟩ := exists_uniform_curvature_first_comparison B hd
  refine ⟨2+C0,by linarith,?_⟩
  intro g h U hg hh hU p hp e hjet hdet hdist he1 hsmall hsecond
  have hscale : 0 ≤ 4*max B 0+2 := by linarith [le_max_right B 0]
  have hfirst := hbound (actualCurvatureFirstInput h p) (actualCurvatureFirstInput g p)
    hjet hdet (hdist.trans he1) ((mul_le_mul_of_nonneg_left hdist hscale).trans hsmall)
  have hL : |curvatureLowerTerm g p-curvatureLowerTerm h p| ≤ C0*e :=
    hfirst.trans (mul_le_mul_of_nonneg_left hdist hC0)
  rw [←curvatureDensityJetError_eq hg hh hU hp]
  exact ((curvatureDensityJetError_le g h p (hsecond 0 1 0 1) (hsecond 0 0 1 1)
    (hsecond 1 1 0 0)).trans (add_le_add le_rfl hL)).trans_eq (by ring)

end SmoothLocal.Pulse

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

def qMetricFirstLower (g : MetricField) (w : DarbouxState) : ℝ :=
  stateConnection g 1 1 w+(stateMixed g w)^2/stateQDenominator g w

def qMetricFirstError (gTau gStar : MetricField) (w : DarbouxState) : ℝ :=
  curvatureDensity gTau (statePoint w)*(qMetricDensityFactor gTau w-qMetricDensityFactor gStar w)+
    (qMetricFirstLower gTau w-qMetricFirstLower gStar w)

theorem sixVariableQ_density_split {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (hxx : stateQDenominator g w ≠ 0) :
    sixVariableQ g w = qMetricFirstLower g w+
      curvatureDensity g (statePoint w)*qMetricDensityFactor g w := by
  have hraw : sixVariableQ g w = stateConnection g 1 1 w+
      ((stateMixed g w)^2+gaussianCurvature g (statePoint w)*stateEnergy g w)/
        stateQDenominator g w := by
    rw [sixVariableQ_explicit hg hU hw]
    rfl
  rw [hraw]
  unfold qMetricFirstLower qMetricDensityFactor curvatureDensity
  have hdet := metricDet_ne_zero hg hw
  field_simp [hdet,hxx]
  ring

theorem sixVariableQ_metric_density_difference
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) {w : DarbouxState} (hw : statePoint w ∈ U)
    (hxxTau : stateQDenominator gTau w ≠ 0) (hxxStar : stateQDenominator gStar w ≠ 0) :
    sixVariableQ gTau w-sixVariableQ gStar w =
      (curvatureDensity gTau (statePoint w)-curvatureDensity gStar (statePoint w))*
        qMetricDensityFactor gStar w+qMetricFirstError gTau gStar w := by
  rw [sixVariableQ_density_split hgTau hU hw hxxTau,
    sixVariableQ_density_split hgStar hU hw hxxStar]
  unfold qMetricFirstError
  ring

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

theorem actual_Q_metric_forcing_decomposition
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxxTau : covHessian gTau z p 0 0 ≠ 0) (hxxStar : covHessian gStar z p 0 0 ≠ 0) :
    sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p) =
      2*forcingCoefficient gStar z p*(curvatureDensity gTau p-curvatureDensity gStar p)+
        qMetricFirstError gTau gStar (qSolutionJet z p) := by
  rw [sixVariableQ_metric_density_difference hgTau hgStar hU
    (by simpa only [statePoint_qSolutionJet] using hp)
    (by simpa only [stateQDenominator_qSolutionJet] using hxxTau)
    (by simpa only [stateQDenominator_qSolutionJet] using hxxStar),
    statePoint_qSolutionJet,qMetricDensityFactor_at_height hgStar z hp hxxStar]
  ring

theorem actual_Q_metric_forcing_leading_identity
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxxTau : covHessian gTau z p 0 0 ≠ 0) (hxxStar : covHessian gStar z p 0 0 ≠ 0)
    (leading : ℝ) :
    (sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p))-
        2*forcingCoefficient gStar z p*leading =
      2*forcingCoefficient gStar z p*((curvatureDensity gTau p-curvatureDensity gStar p)-leading)+
        qMetricFirstError gTau gStar (qSolutionJet z p) := by
  rw [actual_Q_metric_forcing_decomposition hgTau hgStar hU z hp hxxTau hxxStar]
  ring

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

theorem exists_test_density_global_bound (B : ℝ) {d : ℝ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
      ∀ tau : ℝ, T ≤ tau → ∀ (gStar : MetricField) (q0 : ℝ) (U : Set Coord),
        SmoothPositiveOn gStar U → SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
        IsOpen U → ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
          ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B →
          d ≤ (metricInShearCoordinates gStar q0 p).det →
          |(curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
              curvatureDensity gStar (inverseShearCoordinates q0 p))-
            pulsePrincipalLeading a N delta tau p| ≤
            testDensityErrorCoefficient C a ha delta*tau/tau^N := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_actual_pulse_lower_bound B hd ha N hN
  refine ⟨C,hC,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hsmall⟩ := hbound delta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar q0 U hg htest hU p hpU hjet hdet
  have ht1 : 1 ≤ tau := hT.trans ht
  have hL := hsmall tau ht (metricInShearCoordinates gStar q0) p hjet hdet
  have hR := pulse_principal_remainder_le ha N delta ht1 p
  have heq := actual_pulse_curvature_density q0 a N delta tau hg htest hU hpU
  rw [pulse_principal_exact] at heq
  have hdensity :
      (curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-pulsePrincipalLeading a N delta tau p =
        pulsePrincipalRemainder a N delta tau p+
          thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p := by
    dsimp only [curvatureDensity]
    linarith only [heq]
  rw [hdensity]
  calc
    _ ≤ |pulsePrincipalRemainder a N delta tau p|+
        |thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p| :=
      abs_add_le _ _
    _ ≤ pulsePrincipalRemainderBound a ha*tau/tau^N+
        C*scalarPulseFirstJetBudget a ha N delta tau := add_le_add hR hL
    _ = _ := by unfold testDensityErrorCoefficient scalarPulseFirstJetBudget; ring

theorem exists_actual_density_global_bound (B Bcompare : ℝ) {d dcompare : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ Ctest Ccompare : ℝ, 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
            ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B →
            d ≤ (metricInShearCoordinates gStar q0 p).det →
            ∀ epsilon : ℝ,
              ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                (inverseShearCoordinates q0 p)‖ ≤ Bcompare →
              dcompare ≤ (testMetric gStar q0 a N delta tau
                (inverseShearCoordinates q0 p)).det →
              ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
                actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                  (inverseShearCoordinates q0 p)‖ ≤ epsilon →
              epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
              (∀ i j k l : Fin 2,
                |coordPartial i (coordPartial j (fun q => gTau q k l))
                    (inverseShearCoordinates q0 p)-
                  coordPartial i (coordPartial j
                    (fun q => testMetric gStar q0 a N delta tau q k l))
                    (inverseShearCoordinates q0 p)| ≤ epsilon) →
              |(curvatureDensity gTau (inverseShearCoordinates q0 p)-
                  curvatureDensity gStar (inverseShearCoordinates q0 p))-
                pulsePrincipalLeading a N delta tau p| ≤
                testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+
                  Ccompare*epsilon := by
  obtain ⟨Ct,hCt,htest⟩ := exists_test_density_global_bound B hd ha N hN
  obtain ⟨Cc,hCc,hcompare⟩ := exists_uniform_curvature_density_comparison Bcompare hdcompare
  refine ⟨Ct,Cc,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hglobal⟩ := htest delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU hjet hdet
    epsilon hjetTest hdetTest hdistance he1 hesmall hsecond
  have hpulse := hglobal tau ht gStar q0 U hgStar hgTest hU p hpU hjet hdet
  have hmetric := hcompare gTau (testMetric gStar q0 a N delta tau) U
    hgTau hgTest hU (inverseShearCoordinates q0 p) hpU epsilon
    hjetTest hdetTest hdistance he1 hesmall hsecond
  have heq :
      (curvatureDensity gTau (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-
          pulsePrincipalLeading a N delta tau p =
      ((curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-
          pulsePrincipalLeading a N delta tau p)+
      (curvatureDensity gTau (inverseShearCoordinates q0 p)-
        curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hpulse hmetric)

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
def qFirstMixed (a : QFirstInput) : ℝ := a.2 4-qFirstConnection a 0 1
def qFirstEnergy (a : QFirstInput) : ℝ :=
  qFirstDet a-(a.1.1 1 1*(stateGradient a.2 0)^2-
    (a.1.1 0 1+a.1.1 1 0)*stateGradient a.2 0*stateGradient a.2 1+
      a.1.1 0 0*(stateGradient a.2 1)^2)
def qFirstDensityFactor (a : QFirstInput) : ℝ :=
  qFirstEnergy a/(qFirstDet a*qFirstXX a)
def qFirstLower (a : QFirstInput) : ℝ :=
  qFirstConnection a 1 1+(qFirstMixed a)^2/qFirstXX a

theorem qFirstXX_bundle (g : MetricField) (w : DarbouxState) :
    qFirstXX (qFirstBundle g w) = stateQDenominator g w := rfl
theorem qFirstDensityFactor_bundle (g : MetricField) (w : DarbouxState) :
    qFirstDensityFactor (qFirstBundle g w) = qMetricDensityFactor g w := rfl
theorem qFirstLower_bundle (g : MetricField) (w : DarbouxState) :
    qFirstLower (qFirstBundle g w) = qMetricFirstLower g w := rfl

theorem qFirstBundle_distance (g h : MetricField) (w : DarbouxState) :
    ‖qFirstBundle g w-qFirstBundle h w‖ =
      ‖actualCurvatureFirstInput g (statePoint w)-actualCurvatureFirstInput h (statePoint w)‖ := by
  simp [qFirstBundle,Prod.norm_def]

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

theorem qFirstDomain_isOpen : IsOpen qFirstDomain :=
  qFirstXX_contDiffOn.continuousOn.isOpen_inter_preimage qFirstBase_isOpen
    isClosed_singleton.isOpen_compl

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

theorem qFirstLower_contDiffOn : ContDiffOn ℝ ∞ qFirstLower qFirstDomain := by
  intro a ha
  have hΓ := qFirstConnection_contDiffAt ha.1
  have hx := qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds ha.1)
  have hm : ContDiffAt ℝ ∞ qFirstMixed a :=
    (show ContDiffAt ℝ ∞ (fun b : QFirstInput => b.2 4) a by fun_prop).sub (hΓ 0 1)
  exact ((hΓ 1 1).add ((hm.pow 2).div hx ha.2)).contDiffWithinAt

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

theorem qFirstXX_fderiv_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ qFirstBaseTube M d, ‖fderiv ℝ qFirstXX a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ qFirstXX) qFirstBase :=
    (qFirstXX_contDiffOn.fderiv_of_isOpen (m := 0) qFirstBase_isOpen (by simp)).continuousOn
  obtain ⟨C,hC⟩ := (qFirstBaseTube_isCompact M d).exists_bound_of_continuousOn
    (hcont.mono (qFirstBaseTube_subset_base M hd))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

theorem qFirstTube_fderiv_bound (f : QFirstInput → ℝ)
    (hf : ContDiffOn ℝ ∞ f qFirstDomain) (M : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ qFirstTube M d c, ‖fderiv ℝ f a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ f) qFirstDomain :=
    (hf.fderiv_of_isOpen (m := 0) qFirstDomain_isOpen (by simp)).continuousOn
  obtain ⟨C,hC⟩ := (qFirstTube_isCompact M hd c).exists_bound_of_continuousOn
    (hcont.mono (qFirstTube_subset_domain M hd hc))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

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
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem qFirst_segment_distance_le (a b : QFirstInput) {x : QFirstInput}
    (hx : x ∈ segment ℝ a b) : ‖x-a‖ ≤ ‖b-a‖ := by
  have hball : x ∈ Metric.closedBall a ‖b-a‖ :=
    (convex_closedBall a ‖b-a‖).segment_subset
      (by simp) (by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl]) hx
  simpa only [Metric.mem_closedBall,dist_eq_norm] using hball

theorem qFirst_close_segment_subset_baseTube (a b : QFirstInput) {B d : ℝ}
    (ha : ‖a‖ ≤ B) (hdet : d ≤ qFirstDet a) (hdist : ‖b-a‖ ≤ 1)
    (hsmall : (4*max B 0+2)*‖b-a‖ ≤ d/2) :
    segment ℝ a b ⊆ qFirstBaseTube (max B 0+1) (d/2) := by
  intro x hx
  have hxa := qFirst_segment_distance_le a b hx
  have hxnorm : ‖x‖ ≤ max B 0+1 := by
    calc
      _ = ‖(x-a)+a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-a‖+‖a‖ := norm_add_le _ _
      _ ≤ 1+max B 0 := add_le_add (hxa.trans hdist) (ha.trans (le_max_left _ _))
      _ = _ := by ring
  have hmatrixD : ‖x.1.1-a.1.1‖ ≤ ‖b-a‖ :=
    (show ‖x.1.1-a.1.1‖ ≤ ‖x-a‖ from
      (norm_fst_le (x-a).1).trans (norm_fst_le (x-a))).trans hxa
  have hmatrixA : ‖a.1.1‖ ≤ max B 0 :=
    ((norm_fst_le a.1).trans (norm_fst_le a)).trans (ha.trans (le_max_left _ _))
  have hdetdiff := det_sub_le_small_first_distance (Matrix.of a.1.1) (Matrix.of x.1.1)
    (le_max_right B 0) (norm_nonneg _) hdist hmatrixA hmatrixD
  have hxdet : d/2 ≤ qFirstDet x := by
    have hneg := neg_abs_le (qFirstDet x-qFirstDet a)
    change |qFirstDet x-qFirstDet a| ≤ (4*max B 0+2)*‖b-a‖ at hdetdiff
    linarith [hdetdiff.trans hsmall]
  exact ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hxnorm,hxdet⟩

theorem exists_uniform_qFirst_comparison (B : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ H F L : ℝ, 0 ≤ H ∧ 0 ≤ F ∧ 0 ≤ L ∧
      ∀ a b : QFirstInput, ‖a‖ ≤ B → d ≤ qFirstDet a → c ≤ |qFirstXX a| →
        ‖b-a‖ ≤ 1 → (4*max B 0+2)*‖b-a‖ ≤ d/2 → H*‖b-a‖ ≤ c/2 →
        (∀ x ∈ segment ℝ a b, c/2 ≤ |qFirstXX x|) ∧
        |qFirstDensityFactor b-qFirstDensityFactor a| ≤ F*‖b-a‖ ∧
        |qFirstLower b-qFirstLower a| ≤ L*‖b-a‖ := by
  obtain ⟨H,hH,hHb⟩ := qFirstXX_fderiv_bound (max B 0+1) (half_pos hd)
  obtain ⟨F,hF,hFb⟩ := qFirstTube_fderiv_bound qFirstDensityFactor
    qFirstDensityFactor_contDiffOn (max B 0+1) (half_pos hd) (half_pos hc)
  obtain ⟨L,hL,hLb⟩ := qFirstTube_fderiv_bound qFirstLower
    qFirstLower_contDiffOn (max B 0+1) (half_pos hd) (half_pos hc)
  refine ⟨H,F,L,hH,hF,hL,?_⟩
  intro a b ha hdet hxx hdist hsmall hxxsmall
  have hbase := qFirst_close_segment_subset_baseTube a b ha hdet hdist hsmall
  have hXXdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ qFirstXX x := by
    intro x hx
    exact (qFirstXX_contDiffOn.contDiffAt (qFirstBase_isOpen.mem_nhds
      (qFirstBaseTube_subset_base (max B 0+1) (half_pos hd) (hbase hx)))).differentiableAt (by simp)
  have hfloor : ∀ x ∈ segment ℝ a b, c/2 ≤ |qFirstXX x| := by
    intro x hx
    have herr : |qFirstXX x-qFirstXX a| ≤ H*‖x-a‖ := by
      simpa only [Real.norm_eq_abs] using
        (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hXXdiff
          (fun y hy => hHb y (hbase hy)) (left_mem_segment ℝ a b) hx
    have hsmall' : |qFirstXX x-qFirstXX a| ≤ c/2 :=
      herr.trans ((mul_le_mul_of_nonneg_left (qFirst_segment_distance_le a b hx) hH).trans hxxsmall)
    have htriangle : |qFirstXX a| ≤ |qFirstXX x|+|qFirstXX x-qFirstXX a| := by
      calc
        _ = |qFirstXX x-(qFirstXX x-qFirstXX a)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith
  have htube : segment ℝ a b ⊆ qFirstTube (max B 0+1) (d/2) (c/2) :=
    fun x hx => ⟨hbase hx,hfloor x hx⟩
  have hcompare (f : QFirstInput → ℝ) (hf : ContDiffOn ℝ ∞ f qFirstDomain)
      (C : ℝ) (hCb : ∀ x ∈ qFirstTube (max B 0+1) (d/2) (c/2), ‖fderiv ℝ f x‖ ≤ C) :
      |f b-f a| ≤ C*‖b-a‖ := by
    have hdiff : ∀ x ∈ segment ℝ a b, DifferentiableAt ℝ f x := by
      intro x hx
      exact (hf.contDiffAt (qFirstDomain_isOpen.mem_nhds
        (qFirstTube_subset_domain (max B 0+1) (half_pos hd) (half_pos hc)
          (htube hx)))).differentiableAt (by simp)
    simpa only [Real.norm_eq_abs] using
      (convex_segment a b).norm_image_sub_le_of_norm_fderiv_le hdiff
        (fun x hx => hCb x (htube hx)) (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  exact ⟨hfloor,hcompare _ qFirstDensityFactor_contDiffOn F hFb,
    hcompare _ qFirstLower_contDiffOn L hLb⟩

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

theorem exists_uniform_qMetricFirstError_bound (B D : ℝ) {d c : ℝ}
    (hD : 0 ≤ D) (hd : 0 < d) (hc : 0 < c) :
    ∃ H C : ℝ, 0 ≤ H ∧ 0 ≤ C ∧
      ∀ (gTau gStar : MetricField) (w : DarbouxState) (epsilon : ℝ),
        ‖qFirstBundle gStar w‖ ≤ B → d ≤ (gStar (statePoint w)).det →
        c ≤ |stateQDenominator gStar w| →
        ‖actualCurvatureFirstInput gTau (statePoint w)-
          actualCurvatureFirstInput gStar (statePoint w)‖ ≤ epsilon →
        epsilon ≤ 1 → (4*max B 0+2)*epsilon ≤ d/2 → H*epsilon ≤ c/2 →
        |curvatureDensity gTau (statePoint w)| ≤ D →
        c/2 ≤ |stateQDenominator gTau w| ∧
        |qMetricFirstError gTau gStar w| ≤ C*epsilon := by
  obtain ⟨H,F,L,hH,hF,hL,hcompare⟩ := exists_uniform_qFirst_comparison B hd hc
  refine ⟨H,D*F+L,hH,add_nonneg (mul_nonneg hD hF) hL,?_⟩
  intro gTau gStar w epsilon hB hdet hxx hdist he1 hsmall hxxsmall hdensity
  have hscale : 0 ≤ 4*max B 0+2 := by linarith [le_max_right B 0]
  have hb : ‖qFirstBundle gTau w-qFirstBundle gStar w‖ ≤ epsilon := by
    simpa only [qFirstBundle_distance] using hdist
  obtain ⟨hfloor,hfactor,hlower⟩ := hcompare (qFirstBundle gStar w) (qFirstBundle gTau w)
    hB hdet hxx (hb.trans he1)
    ((mul_le_mul_of_nonneg_left hb hscale).trans hsmall)
    ((mul_le_mul_of_nonneg_left hb hH).trans hxxsmall)
  have hxxTau : c/2 ≤ |stateQDenominator gTau w| := by
    simpa only [qFirstXX_bundle] using
      hfloor (qFirstBundle gTau w) (right_mem_segment ℝ _ _)
  have hfactorBase : |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w| ≤
      F*‖qFirstBundle gTau w-qFirstBundle gStar w‖ := by
    simpa only [qFirstDensityFactor_bundle] using hfactor
  have hlowerBase : |qMetricFirstLower gTau w-qMetricFirstLower gStar w| ≤
      L*‖qFirstBundle gTau w-qFirstBundle gStar w‖ := by
    simpa only [qFirstLower_bundle] using hlower
  have hfactor' : |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w| ≤ F*epsilon :=
    hfactorBase.trans (mul_le_mul_of_nonneg_left hb hF)
  have hlower' : |qMetricFirstLower gTau w-qMetricFirstLower gStar w| ≤ L*epsilon :=
    hlowerBase.trans (mul_le_mul_of_nonneg_left hb hL)
  refine ⟨hxxTau,?_⟩
  unfold qMetricFirstError
  calc
    _ ≤ |curvatureDensity gTau (statePoint w)| *
          |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w|+
        |qMetricFirstLower gTau w-qMetricFirstLower gStar w| := by
      simpa only [abs_mul] using abs_add_le
        (curvatureDensity gTau (statePoint w)*(qMetricDensityFactor gTau w-qMetricDensityFactor gStar w))
        (qMetricFirstLower gTau w-qMetricFirstLower gStar w)
    _ ≤ D*(F*epsilon)+L*epsilon := add_le_add
      (mul_le_mul hdensity hfactor' (abs_nonneg _) hD) hlower'
    _ = _ := by ring

theorem exists_actual_Q_forcing_error_bound (B D A : ℝ) {d c : ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hd : 0 < d) (hc : 0 < c) :
    ∃ H C : ℝ, 0 ≤ H ∧ 0 ≤ C ∧
      ∀ (gTau gStar : MetricField) (U : Set Coord),
        SmoothPositiveOn gTau U → SmoothPositiveOn gStar U → IsOpen U →
        ∀ (z : Coord → ℝ) (p : Coord), p ∈ U → ∀ epsilon leading : ℝ,
          ‖qFirstBundle gStar (qSolutionJet z p)‖ ≤ B → d ≤ (gStar p).det →
          c ≤ |covHessian gStar z p 0 0| →
          ‖actualCurvatureFirstInput gTau p-actualCurvatureFirstInput gStar p‖ ≤ epsilon →
          epsilon ≤ 1 → (4*max B 0+2)*epsilon ≤ d/2 → H*epsilon ≤ c/2 →
          |curvatureDensity gTau p| ≤ D → |forcingCoefficient gStar z p| ≤ A →
          |(sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p))-
              2*forcingCoefficient gStar z p*leading| ≤
            2*A*|(curvatureDensity gTau p-curvatureDensity gStar p)-leading|+C*epsilon := by
  obtain ⟨H,C,hH,hC,herror⟩ := exists_uniform_qMetricFirstError_bound B D hD hd hc
  refine ⟨H,C,hH,hC,?_⟩
  intro gTau gStar U hgTau hgStar hU z p hp epsilon leading hB hdet hxx hdist
    he1 hsmall hxxsmall hdensity hforce
  obtain ⟨hfloor,herr⟩ := herror gTau gStar (qSolutionJet z p) epsilon hB
    (by simpa only [statePoint_qSolutionJet] using hdet)
    (by simpa only [stateQDenominator_qSolutionJet] using hxx)
    (by simpa only [statePoint_qSolutionJet] using hdist) he1 hsmall hxxsmall
    (by simpa only [statePoint_qSolutionJet] using hdensity)
  have hxxStar : covHessian gStar z p 0 0 ≠ 0 := by
    intro hz
    rw [hz,abs_zero] at hxx
    linarith
  have hxxTau : covHessian gTau z p 0 0 ≠ 0 := by
    rw [stateQDenominator_qSolutionJet] at hfloor
    intro hz
    rw [hz,abs_zero] at hfloor
    linarith
  rw [actual_Q_metric_forcing_leading_identity hgTau hgStar hU z hp hxxTau hxxStar]
  have hfactor : |2*forcingCoefficient gStar z p| ≤ 2*A := by
    simpa only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_left hforce (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ |2*forcingCoefficient gStar z p| *
        |(curvatureDensity gTau p-curvatureDensity gStar p)-leading|+
        |qMetricFirstError gTau gStar (qSolutionJet z p)| := by
      simpa only [abs_mul] using abs_add_le
        (2*forcingCoefficient gStar z p*((curvatureDensity gTau p-curvatureDensity gStar p)-leading))
        (qMetricFirstError gTau gStar (qSolutionJet z p))
    _ ≤ _ := add_le_add
      (mul_le_mul hfactor le_rfl (abs_nonneg _) (mul_nonneg (by norm_num) hA)) herr

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

theorem curvatureDensity_in_shear_coordinates {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (q0 : ℝ) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) :
    curvatureDensity (metricInShearCoordinates g q0) p =
      curvatureDensity g (inverseShearCoordinates q0 p) := by
  have hpa : affineCoordinates 0 (inverseShearMatrix q0) p ∈ U := by
    simpa only [←inverseShearCoordinates_eq_affine] using hp
  unfold curvatureDensity metricInShearCoordinates
  rw [gaussianCurvature_affinePullback hg hU 0 (inverseShearMatrix q0)
    (inverseShearMatrix_isUnit q0) p hpa,det_affinePullbackMetric]
  simp only [inverseShearMatrix_det,one_pow,one_mul,←inverseShearCoordinates_eq_affine]

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

theorem exists_actual_Q_pulse_forcing_bound_global (B Bcompare BQ D A : ℝ)
    {d dcompare c : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ H Cfirst Ctest Ccompare : ℝ,
      0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          let gs := metricInShearCoordinates gStar q0
          let gt := metricInShearCoordinates gTau q0
          let zs := heightInShearCoordinates z q0
          ∀ epsilon epsilonQ : ℝ,
            ‖actualCurvatureFirstInput gs p‖ ≤ B → d ≤ (gs p).det →
            ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
              (inverseShearCoordinates q0 p)‖ ≤ Bcompare →
            dcompare ≤ (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det →
            ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
              actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                (inverseShearCoordinates q0 p)‖ ≤ epsilon →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            (∀ i j k l : Fin 2,
              |coordPartial i (coordPartial j (fun q => gTau q k l)) (inverseShearCoordinates q0 p)-
                coordPartial i (coordPartial j (fun q => testMetric gStar q0 a N delta tau q k l))
                  (inverseShearCoordinates q0 p)| ≤ epsilon) →
            ‖qFirstBundle gs (qSolutionJet zs p)‖ ≤ BQ →
            c ≤ |covHessian gs zs p 0 0| →
            ‖actualCurvatureFirstInput gt p-actualCurvatureFirstInput gs p‖ ≤ epsilonQ →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            |curvatureDensity gTau (inverseShearCoordinates q0 p)| ≤ D →
            |forcingCoefficient gs zs p| ≤ A →
            |(sixVariableQ gt (qSolutionJet zs p)-sixVariableQ gs (qSolutionJet zs p))-
                2*forcingCoefficient gs zs p*pulsePrincipalLeading a N delta tau p| ≤
              2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*epsilon)+
                Cfirst*epsilonQ := by
  obtain ⟨H,Cfirst,hH,hCfirst,hQ⟩ := exists_actual_Q_forcing_error_bound BQ D A hD hA hd hc
  obtain ⟨Ctest,Ccompare,hCt,hCc,hDensity⟩ :=
    exists_actual_density_global_bound B Bcompare hd hdcompare ha N hN
  refine ⟨H,Cfirst,Ctest,Ccompare,hH,hCfirst,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hDensityT⟩ := hDensity delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU z hz
  dsimp only
  intro epsilon epsilonQ hB hdet hBcompare hdetcompare hdist he1 hsmall hsecond
    hBQ hxx hdistQ heQ1 hsmallQ hxxsmall hdensity hforce
  have hactualDensity := hDensityT tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU
    hB hdet epsilon hBcompare hdetcompare hdist he1 hsmall hsecond
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hpV : p ∈ V := hpU
  have hgSV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hgTV : SmoothPositiveOn (metricInShearCoordinates gTau q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgTau 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hdensityQ : |curvatureDensity (metricInShearCoordinates gTau q0) p| ≤ D := by
    rw [curvatureDensity_in_shear_coordinates hgTau hU q0 hpU]
    exact hdensity
  have hQactual := hQ (metricInShearCoordinates gTau q0) (metricInShearCoordinates gStar q0)
    V hgTV hgSV hV (heightInShearCoordinates z q0) p hpV epsilonQ
    (pulsePrincipalLeading a N delta tau p) hBQ hdet hxx hdistQ heQ1 hsmallQ hxxsmall
    hdensityQ hforce
  rw [curvatureDensity_in_shear_coordinates hgTau hU q0 hpU,
    curvatureDensity_in_shear_coordinates hgStar hU q0 hpU] at hQactual
  exact hQactual.trans (add_le_add
    (mul_le_mul_of_nonneg_left hactualDensity (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)) le_rfl)

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

def actualShearedQLeading (gStar : MetricField) (z : Coord → ℝ)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  2*forcingCoefficient (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p*
    pulsePrincipalLeading a N delta tau p

theorem qForcingRemainderBudget_nonneg {A Cfirst Ctest Ccompare a : ℝ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare)
    (N : ℕ) (delta : ℝ) {tau epsilon epsilonQ : ℝ}
    (ht : 0 ≤ tau) (he : 0 ≤ epsilon) (heQ : 0 ≤ epsilonQ) :
    0 ≤ qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ := by
  have hCd : 0 ≤ testDensityErrorCoefficient Ctest a ha delta :=
    add_nonneg (pulsePrincipalRemainderBound_nonneg a ha)
      (mul_nonneg hCt (scalarPulseFirstJetBound_nonneg ha delta))
  unfold qForcingRemainderBudget
  positivity

theorem exists_actual_Q_weighted_remainder_bound (B Bcompare BQ D A : ℝ)
    {d dcompare c : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ H Cfirst Ctest Ccompare : ℝ,
      0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, 0 ≤ epsilon → 0 ≤ epsilonQ →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            (∀ p ∈ pulseStrip a delta tau,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p) →
            |pulseWeightedMoment a delta tau (fun p => actualShearedQForcing gStar gTau z q0 p-
              actualShearedQLeading gStar z q0 a N delta tau p)| ≤
              qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
                (2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  obtain ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,hglobal⟩ :=
    exists_actual_Q_pulse_forcing_bound_global B Bcompare BQ D A hd hdcompare hc hD hA ha N hN
  refine ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hglobalT⟩ := hglobal delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ he heQ
    he1 hesmall heQ1 heQsmall hxxsmall hpoint
  have htpos : 0 < tau := zero_lt_one.trans_le (hT.trans ht)
  apply pulseWeightedMoment_bound ha hdelta.le htpos
    (qForcingRemainderBudget_nonneg ha hA hCf hCt hCc N delta htpos.le he heQ)
  intro p hp
  have h := hpoint p hp
  exact hglobalT tau ht gStar gTau q0 U hgStar hgTest hgTau hU p h.point_mem z hz epsilon epsilonQ
    h.referenceFirst h.referenceDet h.testFirst h.testDet h.approximationFirst he1 hesmall
    h.approximationSecond h.referenceState h.referenceXX h.baseFirstDistance heQ1 heQsmall hxxsmall
    h.actualDensity h.referenceCoefficient

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

theorem pulsePrincipalLeading_contDiff (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulsePrincipalLeading a N delta tau) := by
  unfold pulsePrincipalLeading temporalCutoff
  exact ((contDiff_const.mul ((axisBump_contDiff a).comp (contDiff_apply ℝ ℝ 0))).mul
    ((axisBump_contDiff (1/2)).comp
      ((contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const delta))).mul
      (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0)))

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

theorem actualShearedQLeading_contDiffOn {gStar : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn gStar U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (hSU : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ U)
    (hxx : ∀ p ∈ S, covHessian (metricInShearCoordinates gStar q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (actualShearedQLeading gStar z q0 a N delta tau) S := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : S ⊆ V := fun p hp => hSU p hp
  exact (contDiffOn_const.mul (forcingCoefficient_contDiffOn hgV hzV hV hSV hxx)).mul
    (pulsePrincipalLeading_contDiff a N delta tau).contDiffOn

theorem exists_actual_Q_moment_lower_with_remainder
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
            c3*delta*tau/tau^N-
                qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
                  (2*delta/tau)*(∫ x : ℝ, axisBump a x) ≤
              |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| := by
  obtain ⟨c3,hc3,hLead⟩ := exists_actual_leading_forcing_moment_lower ha he hc Dref Cref N
  obtain ⟨Tlead,hTlead⟩ := eventually_atTop.mp hLead
  obtain ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,hError⟩ :=
    exists_actual_Q_weighted_remainder_bound B Bcompare BQ D A hd hdcompare hc hD hA ha N hN
  refine ⟨c3,H,Cfirst,Ctest,Ccompare,hc3,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨Terror,hTerror,hErrorT⟩ := hError delta hdelta
  refine ⟨max Terror Tlead,hTerror.trans (le_max_left _ _),?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ heps hepsQ
    heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint hxxTau hE hdetup hxxup
  have htE : Terror ≤ tau := (le_max_left _ _).trans ht
  have htL : Tlead ≤ tau := (le_max_right _ _).trans ht
  have hSU : ∀ p ∈ pulseStrip a delta tau, inverseShearCoordinates q0 p ∈ U :=
    fun p hp => (hpoint p hp).point_mem
  have hxxStar : ∀ p ∈ pulseStrip a delta tau,
      covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    intro p hp hz0
    have hm := (hpoint p hp).referenceXX
    rw [hz0,abs_zero] at hm
    linarith
  have hFc : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau) :=
    ((sheared_Q_on_height_contDiffOn hgTau hz hU q0 hSU hxxTau).sub
      (sheared_Q_on_height_contDiffOn hgStar hz hU q0 hSU hxxStar)).continuousOn
  have hLc := (actualShearedQLeading_contDiffOn hgStar hz hU q0 a N delta tau hSU hxxStar).continuousOn
  have herr := hErrorT tau htE gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ
    heps hepsQ heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint
  rw [pulseWeightedMoment_sub hFc hLc] at herr
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : pulseStrip a delta tau ⊆ V := fun p hp => hSU p hp
  have hlead := hTlead tau htL delta hdelta (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) V hgV hzV hV hSV hE hdetup
    (fun p hp => (hpoint p hp).referenceXX) hxxup
  change c3*delta*tau/tau^N ≤ |pulseWeightedMoment a delta tau
    (actualShearedQLeading gStar z q0 a N delta tau)| at hlead
  have htriangle : |pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau)| ≤
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)|+
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
        pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau)| := by
    calc
      _ = |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
        (pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
          pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau))| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  linarith

end SmoothLocal.Pulse

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Pulse.exists_actual_Q_moment_lower_with_remainder := @OAI.SmoothLocal.Pulse.exists_actual_Q_moment_lower_with_remainder
