-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.actual_central_sheared_solution_margins
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:49:04.662116+00:00
-- url     : https://prove2.me/submissions/d4dfe66a-18d2-4a60-88dc-4d3e7f19eb7f

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

namespace SmoothLocal.Pulse

theorem shear_time_factor_bound {v b a : ℝ} (hv : 0 < v)
    (hb : |b| ≤ v / 2) (ha : a ≤ -(v ^ 2)) :
    v ^ 2 / 2 ≤ -(b ^ 2 + a) := by
  have hb2 : b ^ 2 ≤ (v / 2) ^ 2 := by
    have ht := (sq_le_sq₀ (abs_nonneg b) (by positivity : 0 ≤ v / 2)).mpr hb
    simpa only [sq_abs] using ht
  nlinarith [sq_nonneg v]

theorem shear_principal_speed {v b a : ℝ} (hv : 0 < v)
    (hb : |b| ≤ v / 2) (ha : a ≤ -(v ^ 2)) :
    0 < -1 / (b ^ 2 + a) ∧
      |2 * b / (b ^ 2 + a)| + Real.sqrt (-1 / (b ^ 2 + a)) ≤ 4 / v := by
  let d := -(b ^ 2 + a)
  have hd0 : v ^ 2 / 2 ≤ d := shear_time_factor_bound hv hb ha
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  have hd : 0 < d := (half_pos hv2).trans_le hd0
  have hS : -1 / (b ^ 2 + a) = 1 / d := by
    dsimp only [d]
    rw [div_neg, neg_div]
  have hP : |2 * b / (b ^ 2 + a)| = 2 * |b| / d := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_neg (show b ^ 2 + a < 0 from neg_pos.mp hd)]
  have hp : 2 * |b| / d ≤ 2 / v := by
    apply (div_le_div_iff₀ hd hv).mpr
    have hh := mul_le_mul_of_nonneg_right hb hv.le
    nlinarith
  have hs : 1 / d ≤ (2 / v) ^ 2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ hd hv2).mpr
    nlinarith
  have hsqrt : Real.sqrt (1 / d) ≤ 2 / v :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hs⟩
  rw [hS, hP]
  refine ⟨one_div_pos.mpr hd, ?_⟩
  calc
    _ ≤ 2 / v + 2 / v := add_le_add hp hsqrt
    _ = 4 / v := by ring

theorem shear_width_smallness {v b : ℝ} (hv : 0 < v)
    (hb : |b| ≤ 1 / (10 * (100 * (1 + v⁻¹)))) :
    |b| ≤ v / 2 ∧ 4 / v < (100 * (1 + v⁻¹)) / 4 := by
  have hwidth : 0 < 100 * (1 + v⁻¹) := by positivity
  have hsmall : 1 / (10 * (100 * (1 + v⁻¹))) ≤ v / 1000 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hwidth)).mpr
    have he : v / 1000 * (10 * (100 * (1 + v⁻¹))) = v + 1 := by
      field_simp [hv.ne']
      ring
    rw [he]
    linarith
  refine ⟨(hb.trans hsmall).trans (by linarith), ?_⟩
  apply (div_lt_iff₀ hv).mpr
  have he : (100 * (1 + v⁻¹)) / 4 * v = 25 * (v + 1) := by
    field_simp [hv.ne']
    ring
  rw [he]
  linarith

theorem negative_curvature_factor {K E h kappa e M v : ℝ}
    (hkappa : 0 < kappa) (he : 0 < e) (hh : h ≠ 0)
    (hK : K ≤ -kappa / 2) (hE : e ≤ E) (hH : |h| ≤ M)
    (hv : v ^ 2 ≤ kappa * e / (2 * M ^ 2)) :
    K * (E / h ^ 2) ≤ -(v ^ 2) := by
  have hE0 : 0 < E := he.trans_le hE
  have hK0 : 0 < -K := by linarith
  have hM0 : 0 < M := (abs_pos.mpr hh).trans_le hH
  have hden : h ^ 2 ≤ M ^ 2 := by
    have ht := (sq_le_sq₀ (abs_nonneg h) hM0.le).mpr hH
    simpa only [sq_abs] using ht
  have hnum : kappa * e / 2 ≤ -K * E := by
    have ht := mul_le_mul (show kappa / 2 ≤ -K by linarith) hE he.le hK0.le
    nlinarith
  have hdiv : (kappa * e / 2) / M ^ 2 ≤ (-K * E) / h ^ 2 :=
    div_le_div₀ (mul_nonneg hK0.le hE0.le) hnum (sq_pos_of_ne_zero hh) hden
  have heq : kappa * e / (2 * M ^ 2) = (kappa * e / 2) / M ^ 2 := by ring
  rw [heq] at hv
  have ht := hv.trans hdiv
  have heq2 : K * (E / h ^ 2) = -((-K * E) / h ^ 2) := by ring
  rw [heq2]
  linarith

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

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

theorem q_mixed_coefficient_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    qFirstCoefficient g 4 (qSolutionJet z p) =
      2 * (covHessian g z p 0 1 / covHessian g z p 0 0) := by
  unfold qFirstCoefficient
  rw [sixVariableQ_mixed_axis hg hU (qSolutionJet_mem_domain hp hxx),
    stateQDenominator_qSolutionJet]
  unfold stateMixed
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  rfl

theorem q_xx_coefficient_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    qFirstCoefficient g 5 (qSolutionJet z p) =
      -(covHessian g z p 1 1 / covHessian g z p 0 0) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold qFirstCoefficient
  rw [sixVariableQ_xx_axis hg hU (qSolutionJet_mem_domain hp hxx),
    stateQDenominator_qSolutionJet]
  simp only [stateMixed, stateEnergy, statePoint_qSolutionJet, stateGradient_qSolutionJet]
  change -((jetMixed g p (coordPartial 0 (coordPartial 1 z) p)
    (fun i => coordPartial i z p) / covHessian g z p 0 0) ^ 2 +
      gaussianCurvature g p * jetEnergy g p (fun i => coordPartial i z p) /
        (covHessian g z p 0 0) ^ 2) = _
  rw [jetMixed_at_height, jetEnergy_at_height hg hp z]
  field_simp [hxx]
  nlinarith [hdet]

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

theorem covHessian_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      (inverseShearMatrix q0)ᵀ * covHessian g z (inverseShearCoordinates q0 p) *
        inverseShearMatrix q0 := by
  simpa only [metricInShearCoordinates, heightInShearCoordinates,
    inverseShearCoordinates_eq_affine] using
    covHessian_affinePullback hg hz hU 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p (by simpa only [← inverseShearCoordinates_eq_affine] using hp)

theorem covHessian_shear_entries {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    let H := covHessian g z (inverseShearCoordinates q0 p)
    let S := covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p
    S 1 1 = H 1 1 ∧ S 0 1 = H 0 1 - q0 * H 1 1 ∧
      S 0 0 = H 0 0 - 2 * q0 * H 0 1 + q0 ^ 2 * H 1 1 := by
  dsimp only
  rw [covHessian_in_shear_coordinates hg hz hU q0 hp]
  simp only [inverseShearMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [covHessian_symm hg hU hz hp 1 0]
  constructor
  · ring
  constructor <;> ring

theorem heightEnergy_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    heightEnergy (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      heightEnergy g z (inverseShearCoordinates q0 p) := by
  have hd := (hz.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  simpa only [metricInShearCoordinates, heightInShearCoordinates,
    ← inverseShearCoordinates_eq_affine, inverseShearMatrix_det, one_pow, one_mul] using
    heightEnergy_affinePullback (g := g) 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p
      (by simpa only [← inverseShearCoordinates_eq_affine] using hd)

theorem hessianQuotient_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0) :
    hessianQuotient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p =
      hessianQuotient g z (inverseShearCoordinates q0 p) - q0 := by
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  unfold hessianQuotient
  rw [h01, h11]
  field_simp [hyy]

theorem sheared_Hxx_factor {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      ((hessianQuotient g z (inverseShearCoordinates q0 p) - q0)^2 +
        gaussianCurvature g (inverseShearCoordinates q0 p) *
          darbouxG g z (inverseShearCoordinates q0 p)) *
            covHessian g z (inverseShearCoordinates q0 p) 1 1 := by
  have hratio := hessian_time_ratio hg hU hz hp hyy hD
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  rw [h00]
  have hf : covHessian g z (inverseShearCoordinates q0 p) 0 0 =
      ((hessianQuotient g z (inverseShearCoordinates q0 p))^2 +
        gaussianCurvature g (inverseShearCoordinates q0 p) *
          darbouxG g z (inverseShearCoordinates q0 p)) *
            covHessian g z (inverseShearCoordinates q0 p) 1 1 := by
    rw [hratio, div_mul_cancel₀ _ hyy]
  rw [hf]
  unfold hessianQuotient
  field_simp [hyy]
  ring

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

theorem gaussianCurvature_in_shear_coordinates {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (q0 : ℝ) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) :
    gaussianCurvature (metricInShearCoordinates g q0) p =
      gaussianCurvature g (inverseShearCoordinates q0 p) := by
  simpa only [metricInShearCoordinates, ← inverseShearCoordinates_eq_affine] using
    gaussianCurvature_affinePullback hg hU 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p
      (by simpa only [← inverseShearCoordinates_eq_affine] using hp)

theorem darboux_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    (covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p).det =
      gaussianCurvature (metricInShearCoordinates g q0) p *
        heightEnergy (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p := by
  rw [covHessian_in_shear_coordinates hg hz hU q0 hp,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, inverseShearMatrix_det,
    one_mul, mul_one, hD, gaussianCurvature_in_shear_coordinates hg hU q0 hp,
    heightEnergy_in_shear_coordinates hz hU q0 hp]

def shearTimeFactor (g : MetricField) (z : Coord → ℝ) (q0 : ℝ) (p : Coord) : ℝ :=
  (hessianQuotient g z (inverseShearCoordinates q0 p) - q0) ^ 2 +
    gaussianCurvature g (inverseShearCoordinates q0 p) *
      darbouxG g z (inverseShearCoordinates q0 p)

theorem sheared_principal_coefficients {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p))
    (hd : shearTimeFactor g z q0 p ≠ 0) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 ∧
    qFirstCoefficient (metricInShearCoordinates g q0) 4
        (qSolutionJet (heightInShearCoordinates z q0) p) =
      2 * (hessianQuotient g z (inverseShearCoordinates q0 p) - q0) /
        shearTimeFactor g z q0 p ∧
    qFirstCoefficient (metricInShearCoordinates g q0) 5
        (qSolutionJet (heightInShearCoordinates z q0) p) = -1 / shearTimeFactor g z q0 p := by
  have hgS := metricInShearCoordinates_smoothPositive hg q0
  have hzS := heightInShearCoordinates_contDiffOn hz q0
  have hUS := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hfac : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      shearTimeFactor g z q0 p * covHessian g z (inverseShearCoordinates q0 p) 1 1 :=
    sheared_Hxx_factor hg hz hU q0 hp hyy hD
  have hxx : covHessian (metricInShearCoordinates g q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero hd hyy
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  refine ⟨hxx, ?_, ?_⟩
  · rw [q_mixed_coefficient_at_height hgS hUS hp hxx, h01, hfac]
    unfold hessianQuotient
    field_simp [hd, hyy]
  · rw [q_xx_coefficient_at_height hgS hUS hzS hp hxx
      (darboux_in_shear_coordinates hg hz hU q0 hp hD), h11, hfac]
    field_simp [hd, hyy]

theorem actual_shear_hyperbolicity {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) {q0 kappa e M v : ℝ} {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (hkappa : 0 < kappa) (he : 0 < e)
    (hv : 0 < v) (hvBound : v ^ 2 ≤ kappa * e / (2 * M ^ 2))
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hH : |covHessian g z (inverseShearCoordinates q0 p) 1 1| ≤ M)
    (hE : e ≤ heightEnergy g z (inverseShearCoordinates q0 p))
    (hK : gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * (100 * (1 + v⁻¹))))
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    v ^ 2 / 2 ≤ -shearTimeFactor g z q0 p ∧
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 ∧
    0 < qFirstCoefficient (metricInShearCoordinates g q0) 5
      (qSolutionJet (heightInShearCoordinates z q0) p) ∧
    |qFirstCoefficient (metricInShearCoordinates g q0) 4
      (qSolutionJet (heightInShearCoordinates z q0) p)| +
        Real.sqrt (qFirstCoefficient (metricInShearCoordinates g q0) 5
          (qSolutionJet (heightInShearCoordinates z q0) p)) < (100 * (1 + v⁻¹)) / 4 := by
  have ha : gaussianCurvature g (inverseShearCoordinates q0 p) *
      darbouxG g z (inverseShearCoordinates q0 p) ≤ -(v ^ 2) :=
    negative_curvature_factor hkappa he hyy hK hE hH hvBound
  obtain ⟨hb, hspeed⟩ := shear_width_smallness hv hq
  have hfactor := shear_time_factor_bound hv hb ha
  have hdneg : shearTimeFactor g z q0 p < 0 := by
    have hv2 : 0 < v ^ 2 / 2 := half_pos (sq_pos_of_pos hv)
    change v ^ 2 / 2 ≤ -shearTimeFactor g z q0 p at hfactor
    linarith
  obtain ⟨hxx, hP, hS⟩ := sheared_principal_coefficients hg hz hU q0 hp hyy hD hdneg.ne
  obtain ⟨hSpos, hchar⟩ := shear_principal_speed hv hb ha
  refine ⟨hfactor, hxx, ?_, ?_⟩
  · rw [hS]
    exact hSpos
  · rw [hP, hS]
    exact hchar.trans_lt hspeed

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
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation

theorem boundedClassSpeed_sq {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    (boundedClassSpeed kappa M) ^ 2 = kappa / (2 * (M : ℝ) ^ 3) := by
  have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have he : ((M : ℝ) ^ (-(3 : ℝ) / 2)) ^ (2 : ℕ) = ((M : ℝ) ^ (3 : ℕ))⁻¹ := by
    rw [← Real.rpow_mul_natCast hMp.le]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  unfold boundedClassSpeed
  rw [mul_pow, Real.sq_sqrt (by positivity), he]
  ring

theorem boundedClassSpeed_sq_energy {kappa : ℝ} (hkappa : 0 < kappa)
    {M : ℕ} (hM : 0 < M) :
    (boundedClassSpeed kappa M) ^ 2 =
      kappa * (1 / (M : ℝ)) / (2 * (M : ℝ) ^ 2) := by
  rw [boundedClassSpeed_sq hkappa hM]
  field_simp

theorem bounded_class_shear_estimates {g : MetricField} {z : Coord → ℝ}
    {M : ℕ} (h : BoundedAdmissibleHeight g M z) {kappa q0 : ℝ}
    (hkappa : 0 < kappa) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ modelSquare)
    (hK : gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M)) :
    (boundedClassSpeed kappa M) ^ 2 / 2 ≤ -shearTimeFactor g z q0 p ∧
    (boundedClassSpeed kappa M) ^ 2 / (2 * (M : ℝ)) ≤
      |covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0| ∧
    0 < qFirstCoefficient (metricInShearCoordinates g q0) 5
      (qSolutionJet (heightInShearCoordinates z q0) p) ∧
    |qFirstCoefficient (metricInShearCoordinates g q0) 4
      (qSolutionJet (heightInShearCoordinates z q0) p)| +
        Real.sqrt (qFirstCoefficient (metricInShearCoordinates g q0) 5
          (qSolutionJet (heightInShearCoordinates z q0) p)) < boundedClassWidth kappa M / 4 := by
  obtain ⟨hM, hadm, hjet, hHb, hEb⟩ := h
  obtain ⟨U, hU, hSU, hg, hz, hD, hE, hyy, hsmall⟩ := hadm
  have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hv := boundedClassSpeed_pos hkappa hM
  obtain ⟨hd, hxx, hS, hchar⟩ := actual_shear_hyperbolicity hg hz hU (hSU hp)
    hkappa (one_div_pos.mpr hMp) hv (boundedClassSpeed_sq_energy hkappa hM).le
    (hyy _ hp) (hHb _ hp).2 (hEb _ hp) hK hq (hD _ hp)
  have hdneg : shearTimeFactor g z q0 p < 0 := by
    have hv2 : 0 < (boundedClassSpeed kappa M) ^ 2 / 2 := half_pos (sq_pos_of_pos hv)
    linarith
  have hfac : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      shearTimeFactor g z q0 p * covHessian g z (inverseShearCoordinates q0 p) 1 1 :=
    sheared_Hxx_factor hg hz hU q0 (hSU hp) (hyy _ hp) (hD _ hp)
  refine ⟨hd, ?_, hS, hchar⟩
  calc
    _ = ((boundedClassSpeed kappa M) ^ 2 / 2) * (1 / (M : ℝ)) := by ring
    _ ≤ (-shearTimeFactor g z q0 p) * |covHessian g z (inverseShearCoordinates q0 p) 1 1| :=
      mul_le_mul hd (hHb _ hp).1 (one_div_nonneg.mpr hMp.le) (neg_pos.mpr hdneg).le
    _ = _ := by rw [hfac, abs_mul, abs_of_neg hdneg]

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

theorem scalar_fderiv_coordinate_bound {q : Coord → ℝ} {p v : Coord} {M : ℝ}
    (_hM : 0 ≤ M) (hpartial : ∀ i : Fin 2, |coordPartial i q p| ≤ M) :
    |fderiv ℝ q p v| ≤ M*(|v 0|+|v 1|) := by
  have he : v = (v 0) • Pi.single 0 (1 : ℝ) + (v 1) • Pi.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [he, map_add, map_smul, map_smul]
  change |v 0 * coordPartial 0 q p + v 1 * coordPartial 1 q p| ≤ _
  calc
    _ ≤ |v 0 * coordPartial 0 q p| + |v 1 * coordPartial 1 q p| := abs_add_le _ _
    _ = |v 0| * |coordPartial 0 q p|+|v 1| * |coordPartial 1 q p| := by rw [abs_mul,abs_mul]
    _ ≤ |v 0| * M+|v 1| * M := add_le_add
      (mul_le_mul_of_nonneg_left (hpartial 0) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hpartial 1) (abs_nonneg _))
    _ = _ := by ring

theorem quotient_change_from_origin
    {q : Coord → ℝ} {U : Set Coord} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (hM : 0 ≤ M)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    {p : Coord} (hp : p ∈ modelSquare) : |q p-q 0| ≤ M*(|p 0|+|p 1|) := by
  have hz : (0 : Coord) ∈ modelSquare := by constructor <;> intro i <;> norm_num
  have hconv : Convex ℝ modelSquare := convex_Icc _ _
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • p ∈ modelSquare := by
    have h := hconv hp hz ht.1 (sub_nonneg.mpr ht.2) (by ring)
    simpa only [smul_zero, add_zero] using h
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => q (s • p)) (fderiv ℝ q (t • p) p) t := by
    have hdq := ((hq.contDiffAt (hU.mem_nhds (hSU (hseg t ht)))).differentiableAt (by simp)).hasFDerivAt
    have hdp : HasDerivAt (fun s : ℝ => s • p) p t := by
      have ht := (hasDerivAt_id t).smul_const p
      change HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) t at ht
      rw [one_smul] at ht
      exact ht
    exact hdq.comp_hasDerivAt t hdp
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv (fun s : ℝ => q (s • p)) t‖ ≤ M*(|p 0|+|p 1|) := by
    rw [(hder t ht).deriv, Real.norm_eq_abs]
    exact scalar_fderiv_coordinate_bound hM (hpartial (t • p) (hseg t ht))
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hder t ht).differentiableAt) hb
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  simpa only [zero_smul, one_smul, sub_zero, norm_one, mul_one, Real.norm_eq_abs] using h

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
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

def boundedClassQuotientBudget (G d : ℝ) (M : ℕ) : ℝ :=
  heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ))

theorem boundedClassQuotientBudget_nonneg {G d : ℝ} {M : ℕ}
    (hG : 0 ≤ G) (hd : 0 < d) (hM : 0 < M) : 0 ≤ boundedClassQuotientBudget G d M :=
  heightQuotientJetBound_nonneg hG (Nat.cast_nonneg M) hd
    (one_div_pos.mpr (Nat.cast_pos.mpr hM))

theorem bounded_class_quotient_change_from_origin
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun r => g r i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    {p : Coord} (hp : p ∈ modelSquare) :
    |hessianQuotient g z p - hessianQuotient g z 0| ≤
      boundedClassQuotientBudget G d M * (|p 0| + |p 1|) := by
  obtain ⟨hM, hadm, hjet, hHb, _⟩ := h
  obtain ⟨U, hU, hSU, hg, hz, _, _, _, _⟩ := hadm
  have hgCoord : ∀ i j, CoordinateBound (fun p => g p i j) modelSquare 4 G := by
    intro i j ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU ds (hSU hp)).trans
      (hgB i j ds.length hds p hp)
  have hzCoord : CoordinateBound z modelSquare 5 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  obtain ⟨V, hV, hSV, _, _, hqV, hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG (Nat.cast_nonneg M) hd
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hgCoord hzCoord hdet (fun p hp => (hHb p hp).1)
  apply quotient_change_from_origin hqV hV hSV (boundedClassQuotientBudget_nonneg hG hd hM) ?_ hp
  intro p hp i
  exact hqB [i] (by norm_num) p hp

theorem inverseShear_coordinate_sum_le {q0 L r : ℝ} {p : Coord}
    (_hr : 0 ≤ r) (hx : |p 0| ≤ L * r) (hy : |p 1| ≤ r) :
    |inverseShearCoordinates q0 p 0| + |inverseShearCoordinates q0 p 1| ≤
      r * (1 + (1 + |q0|) * L) := by
  change |p 0| + |p 1 - q0 * p 0| ≤ _
  calc
    _ ≤ |p 0| + (|p 1| + |q0 * p 0|) := add_le_add le_rfl (abs_sub _ _)
    _ ≤ L * r + (r + |q0| * (L * r)) := by
      rw [abs_mul]
      exact add_le_add hx (add_le_add hy (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
    _ = _ := by ring

end SmoothLocal.Perturbation

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

theorem bounded_class_slab_quotient_small_of_cap_radius
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    {G d kappa q0 r : ℝ} (hG : 0 ≤ G) (hd : 0 < d) (hr : 0 ≤ r)
    (hq0 : |q0| ≤ 1 / 20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
      (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤ 9 / (100 * boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => g a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hcenter : |hessianQuotient g z 0 - q0| ≤ 1 / (100 * boundedClassWidth kappa M))
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ modelSquare)
    (hx : |p 0| ≤ boundedClassWidth kappa M * r) (hy : |p 1| ≤ r) :
    |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M) := by
  let L := boundedClassWidth kappa M
  let Q := boundedClassQuotientBudget G d M
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hQ : 0 ≤ Q := boundedClassQuotientBudget_nonneg hG hd h.1
  have hLr : 0 ≤ L * r := mul_nonneg hL.le hr
  have hdist := inverseShear_coordinate_sum_le (q0 := q0) hr hx hy
  have hdist' : |inverseShearCoordinates q0 p 0| + |inverseShearCoordinates q0 p 1| ≤
      r + 107 * (L * r) / 100 := by
    apply hdist.trans
    have hh := mul_le_mul_of_nonneg_right hq0 hLr
    nlinarith
  have hchange := bounded_class_quotient_change_from_origin h hG hd hgB hdet hp
  have hchange' : |hessianQuotient g z (inverseShearCoordinates q0 p) - hessianQuotient g z 0| ≤
      9 / (100 * L) := hchange.trans ((mul_le_mul_of_nonneg_left hdist' hQ).trans hrsmall)
  calc
    _ ≤ |hessianQuotient g z (inverseShearCoordinates q0 p) - hessianQuotient g z 0| +
        |hessianQuotient g z 0 - q0| := abs_sub_le _ _ _
    _ ≤ 9 / (100 * L) + 1 / (100 * L) := add_le_add hchange' hcenter
    _ = _ := by
      change 9 / (100 * L) + 1 / (100 * L) = 1 / (10 * L)
      field_simp [hL.ne']
      ring

end SmoothLocal.Perturbation

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

end SmoothLocal.Perturbation

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

theorem actual_central_sheared_solution_margins
    {g0 : MetricField} {kappa q0 r G d : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z)
    (hG : 0 ≤ G) (hd : 0 < d) (hkappa : 0 < kappa) (hr : 0 ≤ r)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hcenter : |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
      1/(100*boundedClassWidth kappa M))
    {p : Coord} (hx : |p 0| ≤ boundedClassWidth kappa M*r) (ht : |p 1| ≤ r) :
    let g := metricInShearCoordinates (perturbedMetric g0 eta.val) q0
    let zs := heightInShearCoordinates z q0
    inverseShearCoordinates q0 p ∈ modelSquare ∧
      (boundedClassSpeed kappa M)^2/(2*(M : ℝ)) ≤ |covHessian g zs p 0 0| ∧
      1/(M : ℝ) ≤ |covHessian g zs p 1 1| ∧
      1/(M : ℝ) ≤ heightEnergy g zs p ∧
      gaussianCurvature g p ≤ -(kappa/2) ∧
      (covHessian g zs p).det = gaussianCurvature g p*heightEnergy g zs p ∧
      (hessianQuotient g zs p)^2+gaussianCurvature g p*darbouxG g zs p < 0 := by
  dsimp only
  have hpC := inverseShear_slab_mem_centralBox
    ((by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M))
    hr hLr hq0 hx ht
  have hpS := centralBox_subset_modelSquare hpC
  have hq := bounded_class_slab_quotient_small_of_cap_radius hclass hG hd hr hq0 hrsmall
    hgB hdet hcenter hpS hx ht
  have hK : gaussianCurvature (perturbedMetric g0 eta.val) (inverseShearCoordinates q0 p) ≤ -kappa/2 :=
    (eta.property.2 _ hpC).le
  have hgeom := bounded_class_shear_estimates hclass hkappa hpS hK hq
  obtain ⟨hM,hadm,_,hHb,hEb⟩ := hclass
  obtain ⟨U,hU,hSU,hg,hz,hD,_,hyy,_⟩ := hadm
  have hpU := hSU hpS
  have h11 := (covHessian_shear_entries hg hz hU q0 hpU).1
  have hEnergy := heightEnergy_in_shear_coordinates (g := perturbedMetric g0 eta.val) hz hU q0 hpU
  have hCurvature := gaussianCurvature_in_shear_coordinates hg hU q0 hpU
  have hqShear := hessianQuotient_in_shear_coordinates hg hz hU q0 hpU (hyy _ hpS)
  have htimeeq :
      (hessianQuotient (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (heightInShearCoordinates z q0) p)^2+
        gaussianCurvature (metricInShearCoordinates (perturbedMetric g0 eta.val) q0) p*
          darbouxG (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
            (heightInShearCoordinates z q0) p =
        shearTimeFactor (perturbedMetric g0 eta.val) z q0 p := by
    unfold shearTimeFactor darbouxG
    rw [hqShear,hCurvature,hEnergy,h11]
  have htime : shearTimeFactor (perturbedMetric g0 eta.val) z q0 p < 0 := by
    have hv2 := half_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    linarith [hgeom.1]
  refine ⟨hpS,hgeom.2.1,?_,?_,?_,darboux_in_shear_coordinates hg hz hU q0 hpU (hD _ hpS),?_⟩
  · rw [h11]
    exact (hHb _ hpS).1
  · rw [hEnergy]
    exact hEb _ hpS
  · rw [hCurvature]
    simpa only [neg_div] using hK
  · rw [htimeeq]
    exact htime

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.actual_central_sheared_solution_margins := @OAI.SmoothLocal.Perturbation.actual_central_sheared_solution_margins
