-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.exists_actual_taylor_finite_jets_at_radius
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:15:53.096195+00:00
-- url     : https://prove2.me/submissions/d309a077-2cc7-4c57-8fba-2ac055d0b434

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Taylor_taylorApproximation_properties
import Theorems.Thm_OAI_SmoothLocal_Taylor_linearCauchy_height_initial_state
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_bounded_patch_cauchy_bound
import Theorems.Thm_OAI_SmoothLocal_Pulse_exists_bounded_patch_reference_initial_floor
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
open Function Set
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Taylor

theorem normalizedTimePower_contDiff (a : ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (normalizedTimePower a m) := by
  unfold normalizedTimePower
  fun_prop

theorem normalizedTimePower_hasDerivAt (a t : ℝ) (m : ℕ) :
    HasDerivAt (normalizedTimePower a (m + 1)) (normalizedTimePower a m t) t := by
  have h := (((hasDerivAt_id t).sub_const a).pow (m + 1)).div_const ((m + 1).factorial : ℝ)
  change HasDerivAt (normalizedTimePower a (m + 1))
    ((m + 1 : ℕ) * (t - a)^(m + 1 - 1) * 1 / ((m + 1).factorial : ℝ)) t at h
  simp only [Nat.add_sub_cancel, mul_one] at h
  have he : (m + 1 : ℕ) * (t - a)^m / ((m + 1).factorial : ℝ) = normalizedTimePower a m t := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, normalizedTimePower]
    have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hm, hm1]
  rw [he] at h
  exact h

theorem normalizedTimePower_deriv (a : ℝ) (m : ℕ) :
    deriv (normalizedTimePower a (m + 1)) = normalizedTimePower a m := by
  funext t
  exact (normalizedTimePower_hasDerivAt a t m).deriv

section Composition
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end Composition
end SmoothLocal.Taylor

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
open scoped ContDiff Topology BigOperators Matrix
open Set Filter

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def stateBaseCompact (S : Set Coord) (M : ℝ) : Set DarbouxState :=
  (statePoint ⁻¹' S) ∩ Icc (fun _ => -M) (fun _ => M)

theorem stateBaseCompact_isCompact {S : Set Coord} (hS : IsCompact S) (M : ℝ) :
    IsCompact (stateBaseCompact S M) :=
  isCompact_Icc.inter_left (hS.isClosed.preimage statePoint_contDiff.continuous)

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
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem spatialStrip_isOpen {I : Set ℝ} (hI : IsOpen I) : IsOpen (spatialStrip I) :=
  hI.preimage (continuous_apply 0)

theorem separatedProduct_contDiffOn {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (separatedProduct C f) (spatialStrip I) :=
  (hC.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).mul
    (hf.comp (contDiff_apply ℝ ℝ 1)).contDiffOn

theorem taylorCorrection_contDiffOn {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (taylorCorrection C a n) (spatialStrip I) :=
  separatedProduct_contDiffOn hC _ (normalizedTimePower_contDiff a (n + 2))

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

def comparisonDomain (g : MetricField) (U : Set Coord) (P : Coord → ℝ)
    (I : Set ℝ) : Set Coord :=
  spatialStrip I ∩ qSolutionJet P ⁻¹' darbouxQStateDomain g U

theorem comparisonDomain_isOpen {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) :
    IsOpen (comparisonDomain g U P I) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact inter_mem ((spatialStrip_isOpen hI).mem_nhds hp.1)
    (((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
      ((spatialStrip_isOpen hI).mem_nhds hp.1)).continuousAt.preimage_mem_nhds
        ((darbouxQStateDomain_isOpen hg hU).mem_nhds hp.2))

theorem mem_comparisonDomain {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} {p : Coord}
    (hpI : p ∈ spatialStrip I) (hpU : p ∈ U) (hxx : covHessian g P p 0 0 ≠ 0) :
    p ∈ comparisonDomain g U P I :=
  ⟨hpI, qSolutionJet_mem_domain hpU hxx⟩

theorem qResidual_contDiffOn {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) :
    ContDiffOn ℝ ∞ (qResidual g P) (comparisonDomain g U P I) := by
  have hs := spatialStrip_isOpen hI
  exact ((partial_contDiffOn (partial_contDiffOn hP hs 1) hs 1).mono
    (fun _ hp => hp.1)).sub
      ((sixVariableQ_contDiffOn hg hU).comp
        ((qSolutionJet_contDiffOn hs hP).mono (fun _ hp => hp.1)) (fun _ hp => hp.2))

theorem initialPoint_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (fun x => (![x, a] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const

theorem nextTaylorCoefficient_contDiffOn {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g P ![x, a] 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (nextTaylorCoefficient g a P n) I :=
  ((verticalJet_contDiffOn (comparisonDomain_isOpen hg hU hI hP)
    (qResidual_contDiffOn hg hU hI hP) n).comp (initialPoint_contDiff a).contDiffOn
      (fun x hx => mem_comparisonDomain hx (hcut x hx) (hxx x hx))).neg

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
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem coordinateProjection_norm_le (i : Fin 2) :
    ‖(ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖p i‖ ≤ 1 * ‖p‖
  rw [one_mul]
  exact norm_le_pi_norm p i

theorem coordinateProjection_positive_jet_bound (i : Fin 2) (p : Coord)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun q : Coord => q i) p‖ ≤ 1 := by
  let L : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h := L.norm_iteratedFDeriv_comp_left
    (f := fun q : Coord => q) (x := p) contDiffAt_id (n := n) (WithTop.coe_le_coe.mpr le_top)
  have hL : ‖L‖ ≤ 1 := coordinateProjection_norm_le i
  exact h.trans ((mul_le_mul hL (norm_iteratedFDeriv_id_pos p hn)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem qSolutionJet_positive_fullJet_bound {P : Coord → ℝ} {V : Set Coord}
    (hP : ContDiffOn ℝ ∞ P V) (hV : IsOpen V) {p : Coord} (hp : p ∈ V)
    {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hB : ∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (qSolutionJet P) p‖ ≤ max 1 B := by
  apply norm_iteratedFDeriv_pi_le
    ((qSolutionJet_contDiffOn hV hP).contDiffAt (hV.mem_nhds hp)) n
    (zero_le_one.trans (le_max_left _ _))
  intro i
  fin_cases i
  · exact (coordinateProjection_positive_jet_bound 0 p hn).trans (le_max_left _ _)
  · exact (coordinateProjection_positive_jet_bound 1 p hn).trans (le_max_left _ _)
  · exact ((norm_iteratedFDeriv_coordPartial_le hP hV hp 0 n).trans
      (hB (n + 1) (by omega))).trans (le_max_right _ _)
  · exact ((norm_iteratedFDeriv_coordPartial_le hP hV hp 1 n).trans
      (hB (n + 1) (by omega))).trans (le_max_right _ _)
  · exact (((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP hV 1) hV hp 0 n).trans
      (norm_iteratedFDeriv_coordPartial_le hP hV hp 1 (n + 1))).trans
        (hB (n + 1 + 1) (by omega))).trans (le_max_right _ _)
  · exact (((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP hV 0) hV hp 0 n).trans
      (norm_iteratedFDeriv_coordPartial_le hP hV hp 0 (n + 1))).trans
        (hB (n + 1 + 1) (by omega))).trans (le_max_right _ _)

theorem qCompactTube_finite_Q_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ N, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ n (sixVariableQ g) w‖ ≤ C := by
  classical
  have hh : ∀ j : Fin (N + 1), ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ j.val (sixVariableQ g) w‖ ≤ C :=
    fun j => qCompactTube_derivative_bound hg hU hS hSU M hc
      (sixVariableQ_contDiffOn hg hU) j.val
  choose A hA using hh
  refine ⟨∑ j : Fin (N + 1), |A j|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro n hn w hw
  let j : Fin (N + 1) := ⟨n, by omega⟩
  exact (hA j w hw).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

theorem qSolutionJet_mem_qCompactTube {g : MetricField} {P : Coord → ℝ}
    {S : Set Coord} {p : Coord} (hp : p ∈ S) {M c : ℝ}
    (_hM : 0 ≤ M) (hstate : ‖qSolutionJet P p‖ ≤ M)
    (hden : c ≤ |covHessian g P p 0 0|) :
    qSolutionJet P p ∈ qCompactTube g S M c := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change statePoint (qSolutionJet P p) ∈ S
    rw [statePoint_qSolutionJet]
    exact hp
  · constructor <;> intro i
    · exact (abs_le.mp ((norm_le_pi_norm (qSolutionJet P p) i).trans hstate)).1
    · exact (abs_le.mp ((norm_le_pi_norm (qSolutionJet P p) i).trans hstate)).2
  · change c ≤ |stateQDenominator g (qSolutionJet P p)|
    rw [stateQDenominator_qSolutionJet]
    exact hden

theorem Q_height_composition_fullJet_bound {g : MetricField} {U S : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {p : Coord} (hpI : p ∈ spatialStrip I) (hpS : p ∈ S) (hSU : S ⊆ U)
    {M c B C : ℝ} (hM : 0 ≤ M) (hc : 0 < c) (hstate : ‖qSolutionJet P p‖ ≤ M)
    (hden : c ≤ |covHessian g P p 0 0|) (n : ℕ)
    (hB : ∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B)
    (hC : ∀ j ≤ n, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ j (sixVariableQ g) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun q => sixVariableQ g (qSolutionJet P q)) p‖ ≤
      (n.factorial : ℝ) * C * (max 1 B)^n := by
  have hxx : covHessian g P p 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  have hpD := mem_comparisonDomain hpI (hSU hpS) hxx
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hQ := sixVariableQ_contDiffOn hg hU
  have hQD := darbouxQStateDomain_isOpen hg hU
  have hinput := (qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).mono
    (show comparisonDomain g U P I ⊆ spatialStrip I from inter_subset_left)
  have hmap : MapsTo (qSolutionJet P) (comparisonDomain g U P I) (darbouxQStateDomain g U) :=
    fun _ hq => hq.2
  have houter : ∀ j, j ≤ n →
      ‖iteratedFDerivWithin ℝ j (sixVariableQ g) (darbouxQStateDomain g U) (qSolutionJet P p)‖ ≤ C := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hQD (hmap hpD)]
    exact hC j hj _ (qSolutionJet_mem_qCompactTube hpS hM hstate hden)
  have hinner : ∀ j, 1 ≤ j → j ≤ n →
      ‖iteratedFDerivWithin ℝ j (qSolutionJet P) (comparisonDomain g U P I) p‖ ≤ (max 1 B)^j := by
    intro j hj hjn
    rw [iteratedFDerivWithin_of_isOpen j hD hpD]
    exact (qSolutionJet_positive_fullJet_bound hP (spatialStrip_isOpen hI) hpI hj
      (fun k hk => hB k (by omega))).trans (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le hQ hinput
    (WithTop.coe_le_coe.mpr le_top) hQD.uniqueDiffOn hD.uniqueDiffOn hmap hpD houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hD hpD] at hcomp
  exact hcomp

theorem exists_uniform_qResidual_fullJet_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ p : Coord, p ∈ spatialStrip I → p ∈ S →
      ‖qSolutionJet P p‖ ≤ M → c ≤ |covHessian g P p 0 0| →
      ∀ (n : ℕ), n ≤ N → ∀ B : ℝ,
      (∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j P p‖ ≤ B) →
      ‖iteratedFDeriv ℝ n (qResidual g P) p‖ ≤
        B + (n.factorial : ℝ) * C * (max 1 B)^n := by
  obtain ⟨C, hC, hCQ⟩ := qCompactTube_finite_Q_bound hg hU hS hSU M hc N
  refine ⟨C, hC, ?_⟩
  intro P I hI hP p hpI hpS hstate hden n hn B hB
  have hxx : covHessian g P p 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  have htt := (partial_contDiffOn (partial_contDiffOn hP (spatialStrip_isOpen hI) 1)
    (spatialStrip_isOpen hI) 1).contDiffAt ((spatialStrip_isOpen hI).mem_nhds hpI)
  have hQc := (sixVariableQ_contDiffAt_solutionJet hg hU (hSU hpS) hxx).comp p
    ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
      ((spatialStrip_isOpen hI).mem_nhds hpI))
  have hsecond : ‖iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 P)) p‖ ≤ B :=
    ((norm_iteratedFDeriv_coordPartial_le (partial_contDiffOn hP (spatialStrip_isOpen hI) 1)
      (spatialStrip_isOpen hI) hpI 1 n).trans
        (norm_iteratedFDeriv_coordPartial_le hP (spatialStrip_isOpen hI) hpI 1 (n + 1))).trans
          (hB (n + 1 + 1) (by omega))
  have hQbound := Q_height_composition_fullJet_bound hg hU hI hP hpI hpS hSU hM hc
    hstate hden n hB (fun j hj => hCQ j (hj.trans hn))
  change ‖iteratedFDeriv ℝ n (coordPartial 1 (coordPartial 1 P) -
    (sixVariableQ g ∘ qSolutionJet P)) p‖ ≤ _
  rw [iteratedFDeriv_sub_apply (htt.of_le (WithTop.coe_le_coe.mpr le_top))
    (hQc.of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_sub_le _ _).trans (add_le_add hsecond hQbound)

end SmoothLocal.Taylor

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
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def initialAxisCLM : ℝ →L[ℝ] Coord :=
  ContinuousLinearMap.pi (fun i => if i = 0 then ContinuousLinearMap.id ℝ ℝ else 0)

theorem initialAxisCLM_eq (x : ℝ) : initialAxisCLM x = (![x, 0] : Coord) := by
  ext i
  fin_cases i <;> simp [initialAxisCLM]

theorem initialAxisCLM_norm_le : ‖initialAxisCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, initialAxisCLM_eq]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · exact le_rfl
  · simp

theorem initialAxis_add (x a : ℝ) : initialAxisCLM x + (![0, a] : Coord) = ![x, a] := by
  rw [initialAxisCLM_eq]
  ext i
  fin_cases i <;> simp

theorem norm_initial_slice_jet_le {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) (a x : ℝ)
    (hp : (![x, a] : Coord) ∈ V) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f ![y, a]) x‖ ≤ ‖iteratedFDeriv ℝ k f ![x, a]‖ := by
  let shift : Coord → Coord := fun p => p + ![0, a]
  have hshift : ContDiff ℝ ∞ shift := contDiff_id.add contDiff_const
  have hpre : IsOpen (shift ⁻¹' V) := hV.preimage hshift.continuous
  have hfs : ContDiffOn ℝ ∞ (f ∘ shift) (shift ⁻¹' V) :=
    hf.comp hshift.contDiffOn (fun _ hp => hp)
  have hpoint : initialAxisCLM x ∈ shift ⁻¹' V := by
    change initialAxisCLM x + ![0, a] ∈ V
    rw [initialAxis_add]
    exact hp
  have hb := norm_iteratedFDeriv_comp_contraction initialAxisCLM hfs hpre
    initialAxisCLM_norm_le hpoint k
  have he : (f ∘ shift) ∘ initialAxisCLM = (fun y => f ![y, a]) := by
    funext y
    change f (initialAxisCLM y + ![0, a]) = f ![y, a]
    rw [initialAxis_add]
  rw [he] at hb
  change ‖iteratedFDeriv ℝ k (fun y => f ![y, a]) x‖ ≤
    ‖iteratedFDeriv ℝ k (fun p => f (p + ![0, a])) (initialAxisCLM x)‖ at hb
  rw [iteratedFDeriv_comp_add_right, initialAxis_add] at hb
  exact hb

theorem norm_verticalJet_fullJet_le {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) {p : Coord} (hp : p ∈ V)
    (n k : ℕ) :
    ‖iteratedFDeriv ℝ k (verticalJet f n) p‖ ≤ ‖iteratedFDeriv ℝ (k + n) f p‖ := by
  induction n generalizing k with
  | zero => simpa only [verticalJet, Nat.add_zero] using le_rfl
  | succ n hn =>
    have hb := (norm_iteratedFDeriv_coordPartial_le (verticalJet_contDiffOn hV hf n)
      hV hp 1 k).trans (hn (k + 1))
    have he : k + 1 + n = k + (n + 1) := by omega
    rw [he] at hb
    exact hb

theorem nextTaylorCoefficient_fullJet_le {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (a x : ℝ) (hx : x ∈ I) (hpU : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) (n k : ℕ) :
    ‖iteratedFDeriv ℝ k (nextTaylorCoefficient g a P n) x‖ ≤
      ‖iteratedFDeriv ℝ (k + n) (qResidual g P) ![x, a]‖ := by
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hR := qResidual_contDiffOn hg hU hI hP
  have hp := mem_comparisonDomain hx hpU hxx
  change ‖iteratedFDeriv ℝ k (-(fun y => verticalJet (qResidual g P) n ![y, a])) x‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact (norm_initial_slice_jet_le (verticalJet_contDiffOn hD hR n) hD a x hp k).trans
    (norm_verticalJet_fullJet_le hR hD hp n k)

theorem exists_uniform_nextTaylorCoefficient_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a x : ℝ, x ∈ I → (![x, a] : Coord) ∈ S →
      ‖qSolutionJet P ![x, a]‖ ≤ M → c ≤ |covHessian g P ![x, a] 0 0| →
      ∀ n k : ℕ, k + n ≤ N → ∀ B : ℝ,
      (∀ j ≤ k + n + 2, ‖iteratedFDeriv ℝ j P ![x, a]‖ ≤ B) →
      ‖iteratedFDeriv ℝ k (nextTaylorCoefficient g a P n) x‖ ≤
        B + ((k + n).factorial : ℝ) * C * (max 1 B)^(k + n) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_qResidual_fullJet_bound hg hU hS hSU M hM hc N
  refine ⟨C, hC, ?_⟩
  intro P I hI hP a x hx hpS hstate hden n k hkn B hB
  have hxx : covHessian g P ![x, a] 0 0 ≠ 0 := by
    intro h
    rw [h, abs_zero] at hden
    linarith
  exact (nextTaylorCoefficient_fullJet_le hg hU hI hP a x hx (hSU hpS) hxx n k).trans
    (hbound P I hI hP ![x, a] hx hpS hstate hden (k + n) hkn B hB)

end SmoothLocal.Taylor

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
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem normalizedTimePower_abs_le_one (a t : ℝ) (m : ℕ) (ht : |t - a| ≤ 1) :
    |normalizedTimePower a m t| ≤ 1 := by
  have hpow : |t - a|^m ≤ (1 : ℝ) := pow_le_one₀ (abs_nonneg _) ht
  have hfact : (1 : ℝ) ≤ (m.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ m.factorial from Nat.factorial_pos m)
  rw [normalizedTimePower, abs_div, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg m.factorial : (0 : ℝ) ≤ (m.factorial : ℝ))]
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hfact)).mpr (by simpa using hpow.trans hfact)

theorem normalizedTimePower_zero (a : ℝ) : normalizedTimePower a 0 = fun _ => (1 : ℝ) := by
  funext t
  simp [normalizedTimePower]

theorem normalizedTimePower_iteratedDeriv_abs_le_one (a t : ℝ) (m k : ℕ)
    (ht : |t - a| ≤ 1) : |iteratedDeriv k (normalizedTimePower a m) t| ≤ 1 := by
  induction k generalizing m with
  | zero => exact normalizedTimePower_abs_le_one a t m ht
  | succ k hk =>
    cases m with
    | zero =>
      rw [normalizedTimePower_zero]
      simp [iteratedDeriv_const]
    | succ m =>
      rw [iteratedDeriv_succ', normalizedTimePower_deriv]
      exact hk m

theorem normalizedTimePower_fullJet_le_one (a t : ℝ) (m k : ℕ)
    (ht : |t - a| ≤ 1) : ‖iteratedFDeriv ℝ k (normalizedTimePower a m) t‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact normalizedTimePower_iteratedDeriv_abs_le_one a t m k ht

theorem product_fullJet_bound {f h : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hh : ContDiffOn ℝ ∞ h V) (hV : IsOpen V)
    {p : Coord} (hp : p ∈ V) (k : ℕ) {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hfB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f p‖ ≤ A)
    (hhB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j h p‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun q => f q * h q) p‖ ≤ (2 : ℝ)^k * A * B := by
  have hm := norm_iteratedFDerivWithin_mul_le hf hh hV.uniqueDiffOn hp
    (n := k) (WithTop.coe_le_coe.mpr le_top)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hV hp] at hm
  have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ)^k := by
    exact_mod_cast Nat.sum_range_choose k
  apply hm.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfB j hjk) (Nat.cast_nonneg _))
        (hhB (k - j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ)^k * A * B := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]

theorem spatialCoefficient_fullJet_le {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) {p : Coord} (hp : p 0 ∈ I) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : Coord => C (q 0)) p‖ ≤ ‖iteratedFDeriv ℝ k C (p 0)‖ := by
  have hh := norm_iteratedFDeriv_comp_contraction
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ) (f := C) hC hI
    (coordinateProjection_norm_le 0) (p := p) hp k
  change ‖iteratedFDeriv ℝ k (fun q : Coord => C (q 0)) p‖ ≤
    ‖iteratedFDeriv ℝ k C (p 0)‖ at hh
  exact hh

theorem timeMonomial_fullJet_le_one (a : ℝ) (m : ℕ) {p : Coord}
    (hp : |p 1 - a| ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : Coord => normalizedTimePower a m (q 1)) p‖ ≤ 1 := by
  have hh := norm_iteratedFDeriv_comp_contraction
    (ContinuousLinearMap.proj 1 : Coord →L[ℝ] ℝ) (f := normalizedTimePower a m)
    (normalizedTimePower_contDiff a m).contDiffOn isOpen_univ (coordinateProjection_norm_le 1)
      (p := p) (mem_univ (p 1)) k
  change ‖iteratedFDeriv ℝ k (fun q : Coord => normalizedTimePower a m (q 1)) p‖ ≤
    ‖iteratedFDeriv ℝ k (normalizedTimePower a m) (p 1)‖ at hh
  exact hh.trans (normalizedTimePower_fullJet_le_one a (p 1) m k hp)

theorem separatedTimePower_fullJet_bound {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (m k : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) (ht : |p 1 - a| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hCB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j C (p 0)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (separatedProduct C (normalizedTimePower a m)) p‖ ≤ (2 : ℝ)^k * B := by
  have hc : ContDiffOn ℝ ∞ (fun q : Coord => C (q 0)) (spatialStrip I) :=
    hC.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)
  have ht' : ContDiffOn ℝ ∞ (fun q : Coord => normalizedTimePower a m (q 1)) (spatialStrip I) :=
    ((normalizedTimePower_contDiff a m).comp (contDiff_apply ℝ ℝ 1)).contDiffOn
  have hb := product_fullJet_bound hc ht' (spatialStrip_isOpen hI) hp k hB zero_le_one
    (fun j hj => (spatialCoefficient_fullJet_le hC hI hp j).trans (hCB j hj))
    (fun order _ => timeMonomial_fullJet_le_one a m ht order)
  change ‖iteratedFDeriv ℝ k (separatedProduct C (normalizedTimePower a m)) p‖ ≤
    (2 : ℝ)^k * B * 1 at hb
  rw [mul_one] at hb
  exact hb

theorem linearCauchy_fullJet_bound {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I) (hI : IsOpen I)
    (a : ℝ) (k : ℕ) {p : Coord} (hp : p ∈ spatialStrip I) (ht : |p 1 - a| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (h0B : ∀ j ≤ k, ‖iteratedFDeriv ℝ j u0 (p 0)‖ ≤ B)
    (h1B : ∀ j ≤ k, ‖iteratedFDeriv ℝ j u1 (p 0)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (linearCauchy a u0 u1) p‖ ≤ (1 + (2 : ℝ)^k) * B := by
  have hf0 : ContDiffOn ℝ ∞ (fun q : Coord => u0 (q 0)) (spatialStrip I) :=
    h0.comp (contDiffOn_apply ℝ ℝ 0 _) (fun _ hp => hp)
  have hf1 := separatedProduct_contDiffOn h1 _ (normalizedTimePower_contDiff a 1)
  have he : linearCauchy a u0 u1 = (fun q => u0 (q 0)) +
      separatedProduct u1 (normalizedTimePower a 1) := by
    funext q
    simp [linearCauchy, separatedProduct, normalizedTimePower]
  rw [he, iteratedFDeriv_add_apply
    ((hf0.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hf1.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))]
  have hval := (norm_add_le _ _).trans (add_le_add
    ((spatialCoefficient_fullJet_le h0 hI hp k).trans (h0B k le_rfl))
    (separatedTimePower_fullJet_bound h1 hI a 1 k hp ht hB h1B))
  convert hval using 1 <;> try with_reducible_and_instances rfl
  first | rfl | ring

end SmoothLocal.Taylor

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def taylorInitialRequest (N k : ℕ) : ℕ := k + N * (N + 3)

theorem taylorInitialRequest_step (n k : ℕ) :
    taylorInitialRequest n (k + n + 2) ≤ taylorInitialRequest (n + 1) k := by
  unfold taylorInitialRequest
  nlinarith

theorem uniform_taylorApproximation_jets
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) :
    ∀ N k : ℕ, ∃ R : ℝ, 0 ≤ R ∧
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ) (a : ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, a] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy a u0 u1) ![x, a]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy a u0 u1) ![x, a] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N k, ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N k, ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      ∀ j ≤ k, ∀ p : Coord, p 0 ∈ J → |p 1 - a| ≤ 1 →
        ‖iteratedFDeriv ℝ j (taylorApproximation g a u0 u1 N) p‖ ≤ R := by
  classical
  intro N
  induction N with
  | zero =>
    intro k
    refine ⟨(1 + (2 : ℝ)^k) * B, mul_nonneg (by positivity) hB, ?_⟩
    intro u0 u1 I J a hI hJI h0 h1 _ _ _ h0B h1B j hj p hp ht
    have hpb := linearCauchy_fullJet_bound h0 h1 hI a j (hJI hp) ht hB
      (fun i hi => h0B (p 0) hp i (by simpa only [taylorInitialRequest, zero_mul, Nat.add_zero] using hi.trans hj))
      (fun i hi => h1B (p 0) hp i (by simpa only [taylorInitialRequest, zero_mul, Nat.add_zero] using hi.trans hj))
    exact hpb.trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)) hB)
  | succ n ih =>
    intro k
    obtain ⟨R0, hR0, hprevious⟩ := ih (k + n + 2)
    obtain ⟨C, hC, hcoefficient⟩ := exists_uniform_nextTaylorCoefficient_bound
      hg hU hS hSU M hM hc (k + n)
    let RC : ℝ := ∑ i : Fin (k + 1),
      (R0 + ((i.val + n).factorial : ℝ) * C * (max 1 R0)^(i.val + n))
    have hRC : 0 ≤ RC := Finset.sum_nonneg (fun i _ => by positivity)
    refine ⟨R0 + (2 : ℝ)^k * RC, add_nonneg hR0 (mul_nonneg (by positivity) hRC), ?_⟩
    intro u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B j hj p hp ht
    have hcutU : ∀ x ∈ I, (![x, a] : Coord) ∈ U := fun x hx => hSU (hcut x hx)
    have hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0 := by
      intro x hx hh
      have hd := hden x hx
      rw [hh, abs_zero] at hd
      linarith
    obtain ⟨hP, hjet, _⟩ := taylorApproximation_properties hg hU hI h0 h1 a hcutU hxx n
    have hstateN : ∀ x ∈ I, ‖qSolutionJet (taylorApproximation g a u0 u1 n) ![x, a]‖ ≤ M := by
      intro x hx
      rw [hjet x hx]
      exact hstate x hx
    have hdenN : ∀ x ∈ I,
        c ≤ |covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0| := by
      intro x hx
      rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
      exact hden x hx
    have hxxN : ∀ x ∈ I,
        covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0 ≠ 0 := by
      intro x hx hh
      have hd := hdenN x hx
      rw [hh, abs_zero] at hd
      linarith
    have hprev := hprevious u0 u1 I J a hI hJI h0 h1 hcut hstate hden
      (fun x hx i hi => h0B x hx i (hi.trans (taylorInitialRequest_step n k)))
      (fun x hx i hi => h1B x hx i (hi.trans (taylorInitialRequest_step n k)))
    have hCoeff : ContDiffOn ℝ ∞
        (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) I :=
      nextTaylorCoefficient_contDiffOn hg hU hI hP a n hcutU hxxN
    have hCoeffB : ∀ x ∈ J, ∀ i ≤ k,
        ‖iteratedFDeriv ℝ i (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) x‖ ≤ RC := by
      intro x hx i hi
      have hb := hcoefficient (taylorApproximation g a u0 u1 n) I hI hP a x (hJI hx)
        (hcut x (hJI hx)) (hstateN x (hJI hx)) (hdenN x (hJI hx)) n i (by omega) R0
        (fun l hl => hprev l (by omega) ![x, a] hx (by simp))
      let fi : Fin (k + 1) := ⟨i, by omega⟩
      have hsingle : R0 + ((fi.val + n).factorial : ℝ) * C * (max 1 R0)^(fi.val + n) ≤ RC :=
        Finset.single_le_sum
          (f := fun l : Fin (k + 1) => R0 + ((l.val + n).factorial : ℝ) * C * (max 1 R0)^(l.val + n))
          (fun l _ => by positivity) (Finset.mem_univ fi)
      exact hb.trans hsingle
    have hcorr := separatedTimePower_fullJet_bound hCoeff hI a (n + 2) j (hJI hp) ht hRC
      (fun i hi => hCoeffB (p 0) hp i (hi.trans hj))
    have hprevp := hprev j (by omega) p hp ht
    have hcorrsmooth := taylorCorrection_contDiffOn hCoeff a n
    change ‖iteratedFDeriv ℝ j
      (taylorApproximation g a u0 u1 n +
        taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n) p‖ ≤ _
    rw [iteratedFDeriv_add_apply
      ((hP.contDiffAt ((spatialStrip_isOpen hI).mem_nhds (hJI hp))).of_le (WithTop.coe_le_coe.mpr le_top))
      ((hcorrsmooth.contDiffAt ((spatialStrip_isOpen hI).mem_nhds (hJI hp))).of_le
        (WithTop.coe_le_coe.mpr le_top))]
    exact (norm_add_le _ _).trans (add_le_add hprevp (hcorr.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hRC)))

end SmoothLocal.Taylor

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
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Pulse SmoothLocal.Flow

def initialShearedStateBudget (Z q0 : ℝ) : ℝ :=
  max 1 ((2*(1+|q0|))^2*Z)

theorem initialShearedStateBudget_nonneg (Z q0 : ℝ) : 0 ≤ initialShearedStateBudget Z q0 :=
  zero_le_one.trans (le_max_left _ _)

theorem actual_initial_sheared_state_bound
    {z : Coord → ℝ} {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (hSU : modelSquare ⊆ U) {Z : ℝ} (hZ : 0 ≤ Z)
    (hjet : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (q0 left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, inverseShearCoordinates q0 ![x,a] ∈ modelSquare)
    {x : ℝ} (hx : x ∈ Ioo left right) (hpB : ‖(![x,a] : Coord)‖ ≤ 1) :
    ‖qSolutionJet (linearCauchy a (heightCauchyValue (heightInShearCoordinates z q0) a)
      (heightCauchyVelocity (heightInShearCoordinates z q0) a)) ![x,a]‖ ≤
        initialShearedStateBudget Z q0 := by
  have hz2 : CoordinateBound z modelSquare 2 Z := by
    apply coordinateBound_of_frechet_bounds hz hU hSU
    intro k hk p hp
    exact hjet k (by omega) p hp
  have hzs := heightInShearCoordinates_contDiffOn hz q0
  have hV := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  rw [linearCauchy_height_initial_state hzs hV left right a
    (fun x hx => hSU (hcut x hx)) hx]
  have hb := SmoothLocal.Pulse.CoordinateBound.inverse_shear hz2 hz hU hSU hZ q0
  apply qSolutionJet_norm_bound_of_words (by norm_num) hpB
  intro ds hds
  exact hb ds hds _ (hcut x hx)

end SmoothLocal.Taylor

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
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_taylor_finite_jets_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
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
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let P := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ j ≤ K, ∀ p : Coord, |p 0| ≤ boundedClassWidth kappa M*r/2 →
              |p 1| ≤ delta/(tau : ℝ) → ‖iteratedFDeriv ℝ j P p‖ ≤ C) ∧
            CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) K C := by
  let L := boundedClassWidth kappa M
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let S := shearedModelSquare q0
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hgs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  have hS : IsCompact S := shearedModelSquare_isCompact q0
  have hSVs : S ⊆ Vs := shearedModelSquare_subset_domain hSV q0
  obtain ⟨tauRef,htauRef,hfloor⟩ := exists_bounded_patch_reference_initial_floor
    G kappa d q0 M hG hkappa hd hM hq0
  obtain ⟨B,hB,hCauchyK⟩ := exists_actual_off_pulse_cauchy_bounds_at_radius
    hgStar hV hSV M hG hd hkappa hM hq0 hr hrhalf hLr hrsmall (taylorInitialRequest N K)
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hc : 0 < c := div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  obtain ⟨C,hC,hpoly⟩ := uniform_taylorApproximation_jets hgs hVs hS hSVs
    (initialShearedStateBudget (M : ℝ) q0) (initialShearedStateBudget_nonneg _ _) hc B hB N K
  refine ⟨C,hC,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hCauchyK N delta hdelt,hwidth,eventually_ge_atTop tauRef] with tau hCauchyTau hwidthTau htauR
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let a := -delta/(tau : ℝ)
  let zs := heightInShearCoordinates z q0
  let I := Ioo (-(L*r)) (L*r)
  let J := Icc (-(L*r/2)) (L*r/2)
  have htau1 : 1 ≤ tau := htauRef.trans htauR
  have htauPos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau1)
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have habs : |a| ≤ r := by
    dsimp only [a]
    rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htauPos]
    exact hdw
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hcutS (x : ℝ) (hx : x ∈ I) : inverseShearCoordinates q0 ![x,a] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,habs⟩
  have hcutU (x : ℝ) (hx : x ∈ I) : (![x,a] : Coord) ∈ inverseShearCoordinates q0 ⁻¹' U :=
    hSU (hcutS x hx)
  have hzs : ContDiffOn ℝ ∞ zs (inverseShearCoordinates q0 ⁻¹' U) :=
    heightInShearCoordinates_contDiffOn hh.smooth q0
  have hUs := shearedModelDomain_isOpen hU q0
  have hI : IsOpen I := isOpen_Ioo
  have hJI : J ⊆ I := by
    intro x hx
    exact ⟨by linarith [hx.1,mul_pos hL hr],by linarith [hx.2,mul_pos hL hr]⟩
  have hstate (x : ℝ) (hx : x ∈ I) :
      ‖qSolutionJet (linearCauchy a (heightCauchyValue zs a) (heightCauchyVelocity zs a)) ![x,a]‖ ≤
        initialShearedStateBudget (M : ℝ) q0 := by
    apply actual_initial_sheared_state_bound hh.smooth hU hSU (Nat.cast_nonneg M) hh.lowJet
      q0 (-(L*r)) (L*r) a hcutS hx
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change ‖x‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact (abs_le.mpr ⟨hx.1.le,hx.2.le⟩).trans (hLr.trans (by norm_num))
    · change ‖a‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact habs.trans (by linarith)
  have hden := hfloor g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelt htauR hdw happ
  have hBactual := hCauchyTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have h0 := heightCauchyValue_contDiffOn hzs a hcutU
  have h1 := heightCauchyVelocity_contDiffOn hzs hUs a hcutU
  let P := taylorApproximation gs a (heightCauchyValue zs a) (heightCauchyVelocity zs a) N
  have hxx : ∀ x ∈ I, covHessian gs
      (linearCauchy a (heightCauchyValue zs a) (heightCauchyVelocity zs a)) ![x,a] 0 0 ≠ 0 := by
    intro x hx hzero
    have hl := hden x hx
    rw [hzero,abs_zero] at hl
    linarith
  have hP : ContDiffOn ℝ ∞ P (spatialStrip I) :=
    (taylorApproximation_properties hgs hVs hI h0 h1 a
      (fun x hx => hSVs (hcutS x hx)) hxx N).1
  have hb := hpoly (heightCauchyValue zs a) (heightCauchyVelocity zs a) I J a hI hJI h0 h1
    (fun x hx => hcutS x hx) hstate hden
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).1)
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).2)
  have hfull (j : ℕ) (hj : j ≤ K) (p : Coord) (hx : |p 0| ≤ L*r/2)
      (ht : |p 1| ≤ delta/(tau : ℝ)) : ‖iteratedFDeriv ℝ j P p‖ ≤ C := by
    apply hb j hj p (abs_le.mp hx)
    have hdelta : delta/(tau : ℝ) ≤ 1/2 :=
      (div_le_self hdelt.le hwidthTau.1).trans hdhalf
    have hpa : |p 1-a| ≤ |p 1|+|a| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (p 1) 0 a
    have haeq : |a| = delta/(tau : ℝ) := by
      dsimp [a]
      rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htauPos]
    rw [haeq] at hpa
    linarith
  refine ⟨hP,hfull,?_⟩
  apply coordinateBound_of_frechet_bounds hP (spatialStrip_isOpen hI)
  · intro p hp
    exact hJI hp.1
  · intro j hj p hp
    apply hfull j hj p (abs_le.mpr hp.1)
    simpa only [neg_div] using (abs_le.mpr hp.2)

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.exists_actual_taylor_finite_jets_at_radius := @OAI.SmoothLocal.Perturbation.exists_actual_taylor_finite_jets_at_radius
