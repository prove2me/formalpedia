-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.exists_actual_uniform_comparison_gradient
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:19:53.974194+00:00
-- url     : https://prove2.me/submissions/74574230-bc8b-4396-9a70-f68b453530ab

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Taylor_taylorApproximation_properties
import Theorems.Thm_OAI_SmoothLocal_Taylor_linearCauchy_height_initial_state
import Theorems.Thm_OAI_SmoothLocal_HighEquation_exists_actual_comparison_energy
import Theorems.Thm_OAI_SmoothLocal_Perturbation_actual_central_sheared_solution_margins
import Theorems.Thm_OAI_SmoothLocal_Pulse_exists_bounded_patch_reference_initial_floor
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_off_pulse_cauchy_bounds
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_reference_segment_at_radius
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_actual_class_comparison_source_bound_at_radius

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

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

variable {U : Set Coord}

end SmoothLocal.Weighted

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

theorem verticalPoint_contDiff (x : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => (![x, y] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

end SmoothLocal.HighEquation

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

theorem pulsePairPoint_mem {a delta tau : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ pulsePairRectangle a delta tau) : pulsePairPoint q ∈ pulseStrip a delta tau :=
  boxPoint_mem hq.2 hq.1

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
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

variable {P S bTheta bXi v R : Coord → ℝ} {radius lo hi xl xr theta0 speed theta : ℝ}

theorem point_mem_shrinkingSlab {xl xr a b speed x t : ℝ}
    (ht : t ∈ Icc a b)
    (hx : x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t)) :
    coordinatePoint x t ∈ shrinkingSlab xl xr a b speed := by
  simpa [shrinkingSlab, coordinatePoint] using And.intro ht hx

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem scalar_gradient_le_energy {s0 S a b : ℝ} (hs0 : 0 < s0) (hS : s0 ≤ S) :
    a ^ 2 + b ^ 2 ≤ (2 * (1 + 1 / s0)) * ((a ^ 2 + S * b ^ 2) / 2) := by
  have hspos : 0 ≤ S := hs0.le.trans hS
  have hsb : b ^ 2 ≤ (S * b ^ 2) / s0 := (le_div_iff₀ hs0).2
    (by nlinarith [mul_le_mul_of_nonneg_right hS (sq_nonneg b)])
  have hsb' : b ^ 2 ≤ (1 / s0) * (S * b ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using hsb
  have hi : 0 ≤ 1 / s0 := by positivity
  nlinarith [mul_nonneg hi (sq_nonneg a), mul_nonneg hspos (sq_nonneg b)]

end SmoothLocal.Hyperbolic

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

theorem point_eta (p : Coord) : (![p 0, p 1] : Coord) = p := by
  ext i
  fin_cases i <;> rfl

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

theorem comparisonDomain_denominator {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} {p : Coord}
    (hp : p ∈ comparisonDomain g U P I) :
    p ∈ U ∧ covHessian g P p 0 0 ≠ 0 := by
  exact ⟨by simpa only [statePoint_qSolutionJet] using hp.2.1,
    by simpa only [stateQDenominator_qSolutionJet] using hp.2.2⟩

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
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem linearCauchy_contDiffOn {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I) (a : ℝ) :
    ContDiffOn ℝ ∞ (linearCauchy a u0 u1) (spatialStrip I) :=
  (h0.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).add
    ((h1.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).mul
      ((contDiffOn_apply ℝ ℝ 1 (spatialStrip I)).sub contDiffOn_const))

theorem linearCauchy_value (a x : ℝ) (u0 u1 : ℝ → ℝ) :
    linearCauchy a u0 u1 ![x, a] = u0 x := by simp [linearCauchy]

theorem linearCauchy_velocity {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (linearCauchy a u0 u1) p = u1 (p 0) := by
  have hlin := linearCauchy_contDiffOn h0 h1 a
  have hd : HasFDerivAt (linearCauchy a u0 u1)
      (fderiv ℝ (linearCauchy a u0 u1) p) (![p 0, p 1] : Coord) := by
    simpa only [point_eta] using
      ((hlin.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hc := hd.comp_hasDerivAt (p 1) (verticalPoint_hasDerivAt (p 0) (p 1))
  have he : (fun t => linearCauchy a u0 u1 ![p 0, t]) =
      (fun t => u0 (p 0) + u1 (p 0) * (t - a)) := rfl
  change HasDerivAt (fun t => linearCauchy a u0 u1 ![p 0, t])
    (coordPartial 1 (linearCauchy a u0 u1) p) (p 1) at hc
  rw [he] at hc
  have hf := ((hasDerivAt_id (p 1)).sub_const a).const_mul (u1 (p 0))
  have hf' := hf.const_add (u0 (p 0))
  simpa only [mul_one] using hc.unique hf'

theorem taylorApproximation_value (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ) :
    taylorApproximation g a u0 u1 N ![x, a] = u0 x := by
  induction N with
  | zero => exact linearCauchy_value a x u0 u1
  | succ n hn =>
    simp only [taylorApproximation, hn, taylorCorrection, separatedProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp [normalizedTimePower]

def comparisonTimePolynomial (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x : ℝ) : ℕ → Polynomial ℝ
  | 0 => Polynomial.C (u0 x) + Polynomial.C (u1 x) * (Polynomial.X - Polynomial.C a)
  | n + 1 => comparisonTimePolynomial g a u0 u1 x n +
      Polynomial.C (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n x /
        ((n + 2).factorial : ℝ)) * (Polynomial.X - Polynomial.C a)^(n + 2)

theorem comparisonTimePolynomial_eval (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x t : ℝ) (N : ℕ) :
    (comparisonTimePolynomial g a u0 u1 x N).eval t =
      taylorApproximation g a u0 u1 N ![x, t] := by
  induction N with
  | zero => simp [comparisonTimePolynomial, taylorApproximation, linearCauchy]
  | succ n hn =>
    simp only [comparisonTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      hn, taylorApproximation, taylorCorrection, separatedProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, normalizedTimePower]
    ring

theorem comparisonTimePolynomial_natDegree (g : MetricField) (a : ℝ) (u0 u1 : ℝ → ℝ)
    (x : ℝ) (N : ℕ) :
    (comparisonTimePolynomial g a u0 u1 x N).natDegree ≤ N + 1 := by
  induction N with
  | zero =>
    unfold comparisonTimePolynomial
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_sub_C_le a)
  | succ n hn =>
    change (comparisonTimePolynomial g a u0 u1 x n + _).natDegree ≤ n + 1 + 1
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact hn.trans (by omega)
    · apply (Polynomial.natDegree_C_mul_le _ _).trans
      have hp : ((Polynomial.X - Polynomial.C a : Polynomial ℝ)^(n + 2)).natDegree ≤ n + 2 := by
        simpa only [mul_one] using
          (Polynomial.natDegree_pow_le_of_le (n + 2) (Polynomial.natDegree_X_sub_C_le a))
      exact hp.trans (by omega)

theorem finiteTaylorComparison {g : MetricField} {U : Set Coord}
    {u0 u1 : ℝ → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0) (N : ℕ) :
    let z0 := taylorApproximation g a u0 u1 N
    ContDiffOn ℝ ∞ z0 (spatialStrip I) ∧
    (∀ x ∈ I, z0 ![x, a] = u0 x ∧ coordPartial 1 z0 ![x, a] = u1 x) ∧
    (∀ x, ∃ p : Polynomial ℝ, p.natDegree ≤ N + 1 ∧
      ∀ t, p.eval t = z0 ![x, t]) ∧
    (∃ V : Set Coord, IsOpen V ∧ V ⊆ U ∩ spatialStrip I ∧
      (∀ x ∈ I, (![x, a] : Coord) ∈ V) ∧
      (∀ p ∈ V, covHessian g z0 p 0 0 ≠ 0) ∧
      ContDiffOn ℝ ∞ (qResidual g z0) V) ∧
    (∀ x ∈ I, ∀ k < N, iteratedDeriv k (fun t => qResidual g z0 ![x, t]) a = 0) := by
  dsimp only
  obtain ⟨hP, hjet, hzero⟩ := taylorApproximation_properties hg hU hI h0 h1 a hcut hxx N
  have hxxN : ∀ x ∈ I,
      covHessian g (taylorApproximation g a u0 u1 N) ![x, a] 0 0 ≠ 0 := by
    intro x hx
    rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
    exact hxx x hx
  refine ⟨hP, ?_, ?_, ?_, hzero⟩
  · intro x hx
    refine ⟨taylorApproximation_value g a x u0 u1 N, ?_⟩
    have hv := congrArg (fun w : DarbouxState => w 3) (hjet x hx)
    change coordPartial 1 (taylorApproximation g a u0 u1 N) ![x, a] =
      coordPartial 1 (linearCauchy a u0 u1) ![x, a] at hv
    exact hv.trans (linearCauchy_velocity hI h0 h1 a hx)
  · intro x
    exact ⟨comparisonTimePolynomial g a u0 u1 x N,
      comparisonTimePolynomial_natDegree g a u0 u1 x N,
      fun t => comparisonTimePolynomial_eval g a u0 u1 x t N⟩
  · refine ⟨comparisonDomain g U (taylorApproximation g a u0 u1 N) I,
      comparisonDomain_isOpen hg hU hI hP, ?_, ?_, ?_, qResidual_contDiffOn hg hU hI hP⟩
    · intro p hp
      exact ⟨(comparisonDomain_denominator hp).1, hp.1⟩
    · intro x hx
      exact mem_comparisonDomain hx (hcut x hx) (hxxN x hx)
    · intro p hp
      exact (comparisonDomain_denominator hp).2

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
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

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

end SmoothLocal.HighEquation

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
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qSolutionJet_norm_bound {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    {R Z : ℝ} (hR : 0 ≤ R) (_hZ : 0 ≤ Z) (hpB : ‖p‖ ≤ R)
    (hzB : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) :
    ‖qSolutionJet z p‖ ≤ max R Z := by
  have hw (ds : List (Fin 2)) (hds : ds.length ≤ 2) :
      |iteratedCoordPartial ds z p| ≤ Z :=
    (norm_iteratedCoordPartial_le_jet hz hU ds hp).trans (hzB ds.length hds)
  have hcoord (i : Fin 2) : |p i| ≤ R := (norm_le_pi_norm p i).trans hpB
  apply (pi_norm_le_iff_of_nonneg (hR.trans (le_max_left _ _))).mpr
  intro i
  fin_cases i
  · exact (hcoord 0).trans (le_max_left _ _)
  · exact (hcoord 1).trans (le_max_left _ _)
  · exact (hw [0] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [1] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [0, 1] (by norm_num)).trans (le_max_right _ _)
  · exact (hw [0, 0] (by norm_num)).trans (le_max_right _ _)

end SmoothLocal.HighEquation

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

theorem stateBaseCompact_mem_of_norm {w : DarbouxState} {S : Set Coord} {M : ℝ}
    (hp : statePoint w ∈ S) (hw : ‖w‖ ≤ M) : w ∈ stateBaseCompact S M := by
  refine ⟨hp, ?_⟩
  constructor <;> intro i
  · exact (abs_le.mp ((norm_le_pi_norm w i).trans hw)).1
  · exact (abs_le.mp ((norm_le_pi_norm w i).trans hw)).2

theorem stateQDenominator_uniform_fderiv_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w ∈ stateBaseCompact S M, ‖fderiv ℝ (stateQDenominator g) w‖ ≤ L := by
  have hf := (stateQDenominator_contDiffOn hg hU).continuousOn_fderiv_of_isOpen
    (stateBaseDomain_isOpen hU) (by simp)
  obtain ⟨L, hL⟩ := (stateBaseCompact_isCompact hS M).exists_bound_of_continuousOn
    (hf.mono (fun _ hw => hSU hw.1))
  exact ⟨max L 0, le_max_right _ _, fun w hw => (hL w hw).trans (le_max_left _ _)⟩

theorem qHessian_time_hasDerivAt {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {x t : ℝ} (hx : x ∈ I) (hp : (![x, t] : Coord) ∈ U) :
    HasDerivAt (fun s => covHessian g P ![x, s] 0 0)
      (fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, t])
        (fderiv ℝ (qSolutionJet P) ![x, t] (Pi.single 1 1))) t := by
  have hf : DifferentiableAt ℝ (qSolutionJet P) ![x, t] :=
    ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hx)).differentiableAt (by simp)
  have hd := ((stateQDenominator_contDiffOn hg hU).contDiffAt
    ((stateBaseDomain_isOpen hU).mem_nhds
      (show qSolutionJet P ![x, t] ∈ stateBaseDomain U by
        change statePoint (qSolutionJet P ![x, t]) ∈ U
        rw [statePoint_qSolutionJet]
        exact hp))).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt t
    (hf.hasFDerivAt.comp_hasDerivAt t (verticalPoint_hasDerivAt x t))
  change HasDerivAt (fun s => stateQDenominator g (qSolutionJet P ![x, s]))
    (fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, t])
      (fderiv ℝ (qSolutionJet P) ![x, t] (Pi.single 1 1))) t at hc
  simp_rw [stateQDenominator_qSolutionJet] at hc
  exact hc

theorem exists_uniform_Hxx_time_variation {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a t x : ℝ, a ≤ t → x ∈ I →
      (∀ s ∈ Icc a t, (![x, s] : Coord) ∈ S) →
      (∀ s ∈ Icc a t, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j P ![x, s]‖ ≤ R) →
      |covHessian g P ![x, t] 0 0 - covHessian g P ![x, a] 0 0| ≤ L * |t - a| := by
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (fun p : Coord => p) S)
  let A0 := max A 0
  have hA0 : 0 ≤ A0 := le_max_right _ _
  have hpoint : ∀ p ∈ S, ‖p‖ ≤ A0 := fun p hp => (hA p hp).trans (le_max_left _ _)
  obtain ⟨L, hL, hder⟩ := stateQDenominator_uniform_fderiv_bound hg hU hS hSU (max A0 R)
  refine ⟨L * max 1 R, mul_nonneg hL (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro P I hI hP a t x hat hx hseg hPB
  have hd (s : ℝ) (hs : s ∈ Icc a t) := qHessian_time_hasDerivAt hg hU hI hP hx (hSU (hseg s hs))
  have hbound (s : ℝ) (hs : s ∈ Icc a t) :
      ‖deriv (fun v => covHessian g P ![x, v] 0 0) s‖ ≤ L * max 1 R := by
    rw [(hd s hs).deriv]
    have hstate := qSolutionJet_norm_bound hP (spatialStrip_isOpen hI) hx hA0 hR
      (hpoint _ (hseg s hs)) (fun j hj => hPB s hs j (by omega))
    have houter := hder (qSolutionJet P ![x, s])
      (stateBaseCompact_mem_of_norm (by simpa only [statePoint_qSolutionJet] using hseg s hs) hstate)
    have hinner : ‖fderiv ℝ (qSolutionJet P) ![x, s]‖ ≤ max 1 R := by
      simpa only [norm_iteratedFDeriv_one] using
        qSolutionJet_positive_fullJet_bound hP (spatialStrip_isOpen hI) hx
          (show 1 ≤ (1 : ℕ) by omega) (fun j hj => hPB s hs j hj)
    have hv : ‖fderiv ℝ (qSolutionJet P) ![x, s] (Pi.single 1 1)‖ ≤ max 1 R := by
      have hv0 : ‖fderiv ℝ (qSolutionJet P) ![x, s] (Pi.single 1 1)‖ ≤
          ‖fderiv ℝ (qSolutionJet P) ![x, s]‖ * ‖(Pi.single 1 1 : Coord)‖ :=
        (fderiv ℝ (qSolutionJet P) ![x, s]).le_opNorm (Pi.single 1 1)
      rw [Pi.norm_single, norm_one, mul_one] at hv0
      exact hv0.trans hinner
    exact ((fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, s])).le_opNorm _).trans
      (mul_le_mul houter hv (norm_nonneg _) hL)
  have hv := (convex_Icc a t).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hd s hs).differentiableAt) hbound
    (show a ∈ Icc a t from ⟨le_rfl, hat⟩) (show t ∈ Icc a t from ⟨hat, le_rfl⟩)
  simpa only [Real.norm_eq_abs] using hv

theorem exists_uniform_Hxx_strip_width {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R : ℝ) (hR : 0 ≤ R) {c : ℝ} (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a t x : ℝ,
      a ≤ t → t - a ≤ epsilon → x ∈ I →
      (∀ s ∈ Icc a t, (![x, s] : Coord) ∈ S) →
      (∀ s ∈ Icc a t, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j P ![x, s]‖ ≤ R) →
      c ≤ |covHessian g P ![x, a] 0 0| → c / 2 ≤ |covHessian g P ![x, t] 0 0| := by
  obtain ⟨L, hL, hvar⟩ := exists_uniform_Hxx_time_variation hg hU hS hSU R hR
  let epsilon := min 1 (c / (2 * (L + 1)))
  have he : 0 < epsilon := lt_min zero_lt_one (div_pos hc (by positivity))
  have hsmall : L * epsilon ≤ c / 2 := by
    have heupper : epsilon ≤ c / (2 * (L + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (L + 1))).mp heupper
    nlinarith [he.le]
  refine ⟨epsilon, he, min_le_left _ _, ?_⟩
  intro P I hI hP a t x hat htime hx hseg hPB hden
  have hv := hvar P I hI hP a t x hat hx hseg hPB
  rw [abs_of_nonneg (sub_nonneg.mpr hat)] at hv
  have hv' := hv.trans ((mul_le_mul_of_nonneg_left htime hL).trans hsmall)
  rw [abs_sub_comm] at hv'
  have htri : |covHessian g P ![x, a] 0 0| ≤
      |covHessian g P ![x, a] 0 0 - covHessian g P ![x, t] 0 0| +
        |covHessian g P ![x, t] 0 0| := by
    simpa only [sub_add_cancel] using abs_add_le
      (covHessian g P ![x, a] 0 0 - covHessian g P ![x, t] 0 0)
      (covHessian g P ![x, t] 0 0)
  linarith

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
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem iteratedDerivWithin_Icc_eq_of_contDiffAt {f : ℝ → ℝ} {a b t : ℝ}
    (hab : a < b) (hf : ContDiffAt ℝ ∞ f t) (ht : t ∈ Icc a b) (k : ℕ) :
    iteratedDerivWithin k f (Icc a b) t = iteratedDeriv k f t := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hab)
      (hf.of_le (WithTop.coe_le_coe.mpr le_top)) ht]

theorem zero_jets_remainder_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ f t) (N : ℕ)
    (hzero : ∀ k < N, iteratedDeriv k f a = 0) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc a b, |iteratedDeriv N f t| ≤ C)
    {t : ℝ} (ht : t ∈ Icc a b) : |f t| ≤ C * (t - a)^N := by
  cases N with
  | zero => simpa only [iteratedDeriv_zero, pow_zero, mul_one] using hbound t ht
  | succ n =>
    rcases eq_or_lt_of_le hab with hab | hab
    · subst b
      have hta : t = a := le_antisymm ht.2 ht.1
      subst t
      have hfa : f a = 0 := hzero 0 (by omega)
      simp [hfa]
    have hwithin (j : ℕ) (s : ℝ) (hs : s ∈ Icc a b) :
        iteratedDerivWithin j f (Icc a b) s = iteratedDeriv j f s :=
      iteratedDerivWithin_Icc_eq_of_contDiffAt hab (hf s hs) hs j
    have hTaylor : taylorWithinEval f n (Icc a b) a t = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hwithin j a ⟨le_rfl, hab.le⟩, hzero j (Finset.mem_range.mp hj)]
      simp
    have hdiff : ContDiffOn ℝ (n + 1) f (Icc a b) :=
      fun s hs => ((hf s hs).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
    have hrem := taylor_mean_remainder_bound hab.le hdiff ht
      (fun s hs => by rw [hwithin (n + 1) s hs, Real.norm_eq_abs]; exact hbound s hs)
    rw [hTaylor, sub_zero, Real.norm_eq_abs] at hrem
    apply hrem.trans
    have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast (show 1 ≤ n.factorial from Nat.factorial_pos n)
    exact div_le_self (mul_nonneg hC (pow_nonneg (sub_nonneg.mpr ht.1) _)) hfac

theorem qResidual_time_jet_le_fullJet {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (x t : ℝ) (hx : x ∈ I) (hpU : (![x, t] : Coord) ∈ U)
    (hxx : covHessian g P ![x, t] 0 0 ≠ 0) (N : ℕ) :
    |iteratedDeriv N (fun s => qResidual g P ![x, s]) t| ≤
      ‖iteratedFDeriv ℝ N (qResidual g P) ![x, t]‖ := by
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hR := qResidual_contDiffOn hg hU hI hP
  have hp := mem_comparisonDomain hx hpU hxx
  rw [verticalJet_slice hD hR x N t hp]
  have hb := norm_verticalJet_fullJet_le hR hD hp N 0
  rw [Nat.zero_add, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
  exact hb

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
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def taylorStripJetOrder (N : ℕ) : ℕ := max 3 (N + 2)

theorem uniform_taylor_strip
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    ∃ epsilon R C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 ≤ R ∧ 0 ≤ C ∧
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ) (a : ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, a] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy a u0 u1) ![x, a]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy a u0 u1) ![x, a] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      ∀ b : ℝ, a ≤ b → b - a ≤ epsilon →
      (∀ x ∈ J, ∀ t ∈ Icc a b, (![x, t] : Coord) ∈ S) →
      let z0 := taylorApproximation g a u0 u1 N
      (∀ x ∈ J, ∀ t ∈ Icc a b, ∀ j ≤ taylorStripJetOrder N,
        ‖iteratedFDeriv ℝ j z0 ![x, t]‖ ≤ R) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b, c / 2 ≤ |covHessian g z0 ![x, t] 0 0|) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b,
        |iteratedDeriv N (fun s => qResidual g z0 ![x, s]) t| ≤ C) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b, |qResidual g z0 ![x, t]| ≤ C * (t - a)^N) := by
  obtain ⟨R, hR, hpoly⟩ := uniform_taylorApproximation_jets hg hU hS hSU M hM hc B hB
    N (taylorStripJetOrder N)
  obtain ⟨epsilon, he, he1, hwidth⟩ := exists_uniform_Hxx_strip_width hg hU hS hSU R hR hc
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (fun p : Coord => p) S)
  let A0 := max A 0
  have hA0 : 0 ≤ A0 := le_max_right _ _
  have hpoint : ∀ p ∈ S, ‖p‖ ≤ A0 := fun p hp => (hA p hp).trans (le_max_left _ _)
  obtain ⟨C0, hC0, hresidual⟩ := exists_uniform_qResidual_fullJet_bound hg hU hS hSU
    (max A0 R) (hA0.trans (le_max_left _ _)) (half_pos hc) N
  let C := R + (N.factorial : ℝ) * C0 * (max 1 R)^N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨epsilon, R, C, he, he1, hR, hC, ?_⟩
  intro u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B b hab hba hstrip
  dsimp only
  have hxx0 : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0 := by
    intro x hx hh
    have hd := hden x hx
    rw [hh, abs_zero] at hd
    linarith
  obtain ⟨hP, hjet, hzero⟩ := taylorApproximation_properties hg hU hI h0 h1 a
    (fun x hx => hSU (hcut x hx)) hxx0 N
  have hfull := hpoly u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B
  have htime (t : ℝ) (ht : t ∈ Icc a b) : |t - a| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    exact (sub_le_sub_right ht.2 a).trans (hba.trans he1)
  have hfull' : ∀ x ∈ J, ∀ t ∈ Icc a b, ∀ j ≤ taylorStripJetOrder N,
      ‖iteratedFDeriv ℝ j (taylorApproximation g a u0 u1 N) ![x, t]‖ ≤ R := by
    intro x hx t ht j hj
    exact hfull j hj ![x, t] hx (htime t ht)
  have hden0 : ∀ x ∈ I,
      c ≤ |covHessian g (taylorApproximation g a u0 u1 N) ![x, a] 0 0| := by
    intro x hx
    rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
    exact hden x hx
  have hdenAll : ∀ x ∈ J, ∀ t ∈ Icc a b,
      c / 2 ≤ |covHessian g (taylorApproximation g a u0 u1 N) ![x, t] 0 0| := by
    intro x hx t ht
    apply hwidth (taylorApproximation g a u0 u1 N) I hI hP a t x ht.1
      ((sub_le_sub_right ht.2 a).trans hba) (hJI hx)
    · intro s hs
      exact hstrip x hx s ⟨hs.1, hs.2.trans ht.2⟩
    · intro s hs j hj
      exact hfull' x hx s ⟨hs.1, hs.2.trans ht.2⟩ j
        (hj.trans (le_max_left _ _))
    · exact hden0 x (hJI hx)
  have hne : ∀ x ∈ J, ∀ t ∈ Icc a b,
      covHessian g (taylorApproximation g a u0 u1 N) ![x, t] 0 0 ≠ 0 := by
    intro x hx t ht hh
    have hd := hdenAll x hx t ht
    rw [hh, abs_zero] at hd
    linarith
  have hstateAll : ∀ x ∈ J, ∀ t ∈ Icc a b,
      ‖qSolutionJet (taylorApproximation g a u0 u1 N) ![x, t]‖ ≤ max A0 R := by
    intro x hx t ht
    apply qSolutionJet_norm_bound hP (spatialStrip_isOpen hI) (hJI hx) hA0 hR
      (hpoint _ (hstrip x hx t ht))
    intro j hj
    exact hfull' x hx t ht j (hj.trans (by unfold taylorStripJetOrder; omega))
  have hresBound : ∀ x ∈ J, ∀ t ∈ Icc a b,
      ‖iteratedFDeriv ℝ N (qResidual g (taylorApproximation g a u0 u1 N)) ![x, t]‖ ≤ C := by
    intro x hx t ht
    exact hresidual (taylorApproximation g a u0 u1 N) I hI hP ![x, t] (hJI hx)
      (hstrip x hx t ht) (hstateAll x hx t ht) (hdenAll x hx t ht) N le_rfl R
      (fun j hj => hfull' x hx t ht j (hj.trans (le_max_right _ _)))
  have htimeBound : ∀ x ∈ J, ∀ t ∈ Icc a b,
      |iteratedDeriv N (fun s => qResidual g (taylorApproximation g a u0 u1 N) ![x, s]) t| ≤ C := by
    intro x hx t ht
    exact (qResidual_time_jet_le_fullJet hg hU hI hP x t (hJI hx)
      (hSU (hstrip x hx t ht)) (hne x hx t ht) N).trans (hresBound x hx t ht)
  refine ⟨hfull', hdenAll, htimeBound, ?_⟩
  intro x hx t ht
  apply zero_jets_remainder_bound hab ?_ N (hzero x (hJI hx)) hC
    (htimeBound x hx) ht
  intro s hs
  exact ((qResidual_contDiffOn hg hU hI hP).contDiffAt
    ((comparisonDomain_isOpen hg hU hI hP).mem_nhds
      (mem_comparisonDomain (hJI hx) (hSU (hstrip x hx s hs)) (hne x hx s hs)))).comp s
        (verticalPoint_contDiff x).contDiffAt

end SmoothLocal.Taylor

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
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem taylorApproximation_initial_time_hasDerivAt
    (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ) :
    HasDerivAt (fun t => taylorApproximation g a u0 u1 N ![x,t]) (u1 x) a := by
  induction N with
  | zero =>
    have h := (((hasDerivAt_id a).sub_const a).const_mul (u1 x)).const_add (u0 x)
    change HasDerivAt (fun t => u0 x+u1 x*(t-a)) (u1 x) a
    simpa only [mul_one, id_eq] using h
  | succ n ih =>
    let C := nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n x
    have hc : HasDerivAt (fun t => C*normalizedTimePower a (n+2) t) 0 a := by
      have h := (normalizedTimePower_hasDerivAt a a (n+1)).const_mul C
      simpa only [normalizedTimePower,sub_self,zero_pow (by omega : n+1 ≠ 0),zero_div,mul_zero] using h
    have h := ih.fun_add hc
    change HasDerivAt (fun t => taylorApproximation g a u0 u1 n ![x,t]+
      C*normalizedTimePower a (n+2) t) (u1 x) a
    simpa only [add_zero] using h

theorem taylorApproximation_initial_velocity_of_differentiable
    (g : MetricField) (a x : ℝ) (u0 u1 : ℝ → ℝ) (N : ℕ)
    (hP : DifferentiableAt ℝ (taylorApproximation g a u0 u1 N) ![x,a]) :
    coordPartial 1 (taylorApproximation g a u0 u1 N) ![x,a] = u1 x := by
  have h := hP.hasFDerivAt.comp_hasDerivAt a (verticalPoint_hasDerivAt x a)
  exact h.unique (taylorApproximation_initial_time_hasDerivAt g a x u0 u1 N)

theorem actual_taylor_Cauchy_of_smooth
    (g : MetricField) (z : Coord → ℝ) (a : ℝ) (N : ℕ) {I : Set ℝ}
    (hI : IsOpen I)
    (hP : ContDiffOn ℝ ∞ (taylorApproximation g a (heightCauchyValue z a)
      (heightCauchyVelocity z a) N) (spatialStrip I)) :
    ∀ x ∈ I,
      taylorApproximation g a (heightCauchyValue z a) (heightCauchyVelocity z a) N ![x,a] = z ![x,a] ∧
      coordPartial 1 (taylorApproximation g a (heightCauchyValue z a) (heightCauchyVelocity z a) N) ![x,a] =
        coordPartial 1 z ![x,a] := by
  intro x hx
  refine ⟨taylorApproximation_value g a x _ _ N,?_⟩
  exact taylorApproximation_initial_velocity_of_differentiable g a x _ _ N
    ((hP.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hx)).differentiableAt (by simp))

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

theorem exists_pulse_width_threshold {epsilon delta : ℝ} (he : 0 < epsilon)
    (_hd : 0 < delta) :
    ∃ tau0 : ℕ, 0 < tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      0 < tau ∧ 2 * delta / (tau : ℝ) ≤ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * delta / epsilon)
  refine ⟨max 1 n, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro tau htau
  have ht : 0 < tau := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans htau)
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr ht
  have hnreal : (n : ℝ) ≤ (tau : ℝ) := by exact_mod_cast (le_max_right 1 n).trans htau
  have hn' : 2 * delta < (n : ℝ) * epsilon := (div_lt_iff₀ he).mp hn
  refine ⟨ht, (div_le_iff₀ htr).mpr ?_⟩
  nlinarith

theorem pulse_time_power_bound {delta C t : ℝ} {tau N : ℕ}
    (_hd : 0 < delta) (hdhalf : delta ≤ 1 / 2) (htau : 0 < tau) (hC : 0 ≤ C)
    (ht : t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ))) :
    C * (t - (-delta / (tau : ℝ)))^N ≤ C / (tau : ℝ)^N := by
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr htau
  have hleft : 0 ≤ t - (-delta / (tau : ℝ)) := sub_nonneg.mpr ht.1
  have hright : t - (-delta / (tau : ℝ)) ≤ 1 / (tau : ℝ) := by
    have hw : t - (-delta / (tau : ℝ)) ≤ 2 * delta / (tau : ℝ) := by
      have hs := sub_le_sub_right ht.2 (-delta / (tau : ℝ))
      convert hs using 1 <;> first | rfl | ring
    exact hw.trans ((div_le_div_iff_of_pos_right htr).mpr (by linarith))
  have hp := pow_le_pow_left₀ hleft hright N
  have hm := mul_le_mul_of_nonneg_left hp hC
  simpa only [div_pow, one_pow, mul_one_div] using hm

theorem uniform_taylor_pulse
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 2 →
      ∃ tau0 : ℕ, 0 < tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, -delta / (tau : ℝ)] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      (∀ x ∈ J, ∀ t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ)),
        (![x, t] : Coord) ∈ S) →
      let z0 := taylorApproximation g (-delta / (tau : ℝ)) u0 u1 N
      ContDiffOn ℝ ∞ z0 (spatialStrip I) ∧
      (∀ x ∈ I, z0 ![x, -delta / (tau : ℝ)] = u0 x ∧
        coordPartial 1 z0 ![x, -delta / (tau : ℝ)] = u1 x) ∧
      (∀ x, ∃ p : Polynomial ℝ, p.natDegree ≤ N + 1 ∧ ∀ t, p.eval t = z0 ![x, t]) ∧
      (∀ x ∈ J, ∀ t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ)),
        c / 2 ≤ |covHessian g z0 ![x, t] 0 0| ∧
        |qResidual g z0 ![x, t]| ≤ C / (tau : ℝ)^N) := by
  obtain ⟨epsilon, _, C, he, _, _, hC, hstrip⟩ := uniform_taylor_strip
    hg hU hS hSU M hM hc B hB N
  refine ⟨C, hC, ?_⟩
  intro delta hd hdhalf
  obtain ⟨tau0, htau0, hwidth⟩ := exists_pulse_width_threshold he hd
  refine ⟨tau0, htau0, ?_⟩
  intro tau htau u0 u1 I J hI hJI h0 h1 hcut hstate hden h0B h1B hregion
  obtain ⟨htaupos, hthin⟩ := hwidth tau htau
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr htaupos
  have hab : -delta / (tau : ℝ) ≤ delta / (tau : ℝ) := by
    exact div_le_div_of_nonneg_right (by linarith) htr.le
  have hwidth' : delta / (tau : ℝ) - (-delta / (tau : ℝ)) ≤ epsilon := by
    convert hthin using 1 <;> first | rfl | ring
  have hdata := hstrip u0 u1 I J (-delta / (tau : ℝ)) hI hJI h0 h1 hcut hstate hden
    h0B h1B (delta / (tau : ℝ)) hab hwidth' hregion
  have hxx : ∀ x ∈ I,
      covHessian g (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)] 0 0 ≠ 0 := by
    intro x hx hh
    have hd' := hden x hx
    rw [hh, abs_zero] at hd'
    linarith
  obtain ⟨hP, hinitial, hdegree, _, _⟩ := finiteTaylorComparison hg hU hI h0 h1
    (-delta / (tau : ℝ)) (fun x hx => hSU (hcut x hx)) hxx N
  refine ⟨hP, hinitial, hdegree, ?_⟩
  intro x hx t ht
  exact ⟨hdata.2.1 x hx t ht, (hdata.2.2.2 x hx t ht).trans
    (pulse_time_power_bound hd hdhalf htaupos hC ht)⟩

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
open Set MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

theorem movingSourceNorm_le_of_pointwise_bound
    {f : Coord → ℝ} {xl xr a b speed t F : ℝ}
    (hspeed : 0 ≤ speed) (ht : t ∈ Icc a b)
    (horder : inwardLeft xl a speed t ≤ inwardRight xr a speed t)
    (hF : 0 ≤ F)
    (hbound : ∀ p ∈ shrinkingSlab xl xr a b speed, |f p| ≤ F) :
    movingSourceNorm xl xr a speed f t ≤ F*Real.sqrt (xr-xl) := by
  let l := inwardLeft xl a speed t
  let r := inwardRight xr a speed t
  have hlen : r-l ≤ xr-xl := by
    have hi : 0 ≤ speed*(t-a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
    dsimp [l,r,inwardLeft,inwardRight]
    linarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := l) (b := r) (C := F^2) (f := fun x => f (coordinatePoint x t)^2) (by
      intro x hx
      have hx0 : x ∈ Ioc l r := by
        rw [uIoc_of_le (show l ≤ r from horder)] at hx
        exact hx
      have hb := hbound _ (point_mem_shrinkingSlab ht ⟨hx0.1.le,hx0.2⟩)
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hF).mpr hb)
  have hsquare : (∫ x in l..r, f (coordinatePoint x t)^2) ≤ F^2*(xr-xl) := by
    apply (le_abs_self _).trans
    apply hi.trans
    rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    exact mul_le_mul_of_nonneg_left hlen (sq_nonneg F)
  have hsqrt := Real.sqrt_le_sqrt hsquare
  simpa only [movingSourceNorm,movingIntervalIntegral,l,r,
    Real.sqrt_mul (sq_nonneg F),Real.sqrt_sq hF] using hsqrt

theorem integrated_movingSourceNorm_le_of_pointwise_bound
    {f : Coord → ℝ} {xl xr a b speed F : ℝ}
    (hab : a ≤ b) (hspeed : 0 ≤ speed) (hF : 0 ≤ F)
    (horder : ∀ t ∈ Icc a b, inwardLeft xl a speed t ≤ inwardRight xr a speed t)
    (hbound : ∀ p ∈ shrinkingSlab xl xr a b speed, |f p| ≤ F) :
    (∫ t in a..b, movingSourceNorm xl xr a speed f t) ≤
      F*Real.sqrt (xr-xl)*(b-a) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := F*Real.sqrt (xr-xl))
    (f := movingSourceNorm xl xr a speed f) (by
      intro t ht
      have ht0 : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using ht
      have ht1 : t ∈ Icc a b := ⟨ht0.1.le,ht0.2⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ movingSourceNorm xl xr a speed f t from Real.sqrt_nonneg _)]
      exact movingSourceNorm_le_of_pointwise_bound hspeed ht1 (horder t ht1) hF hbound)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using hi)

end SmoothLocal.Hyperbolic

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

theorem pulseRectangle_mem_shearedModelSquare
    {q0 L r delta tau x t : ℝ} (hL : 0 < L) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hwidth : delta/tau ≤ r) (hx : |x| ≤ L*r/2)
    (ht : t ∈ Icc (-delta/tau) (delta/tau)) :
    (![x,t] : Coord) ∈ shearedModelSquare q0 := by
  apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
  constructor
  · exact hx.trans (by nlinarith [mul_pos hL hr])
  · exact (abs_le.mpr ⟨by simpa only [neg_div] using ht.1, ht.2⟩).trans hwidth

end SmoothLocal.Pulse

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

theorem fixed_slice_gradient_le_moving_energy
    {S v : Coord → ℝ} {V : Set Coord} {xl xr a speed t pulseRadius s0 : ℝ}
    (hV : IsOpen V) (hS : ContinuousOn S V) (hv : ContDiffOn ℝ ∞ v V)
    (hs0 : 0 < s0) (hpulse : 0 ≤ pulseRadius)
    (hleft : inwardLeft xl a speed t ≤ -pulseRadius)
    (hright : pulseRadius ≤ inwardRight xr a speed t)
    (hmem : ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
      coordinatePoint x t ∈ V)
    (hfloor : ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
      s0 ≤ S (coordinatePoint x t)) (i : Fin 2) :
    Real.sqrt (∫ x in Icc (-pulseRadius) pulseRadius, (coordPartial i v (boxPoint x t))^2) ≤
      Real.sqrt (2*(1+1/s0))*Real.sqrt (movingEnergy xl xr a speed S v t) := by
  let l := inwardLeft xl a speed t
  let r := inwardRight xr a speed t
  let K := 2*(1+1/s0)
  have hlr : l ≤ r := hleft.trans ((by linarith : -pulseRadius ≤ pulseRadius).trans hright)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpointContinuous : Continuous (fun x : ℝ => coordinatePoint x t) := by
    unfold coordinatePoint
    fun_prop
  have hvi : ContinuousOn (fun x => coordPartial i v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV i).continuousOn.comp hpointContinuous.continuousOn hmem
  have hvt : ContinuousOn (fun x => coordPartial 1 v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV 1).continuousOn.comp hpointContinuous.continuousOn hmem
  have hvx : ContinuousOn (fun x => coordPartial 0 v (coordinatePoint x t)) (Icc l r) :=
    (partial_contDiffOn hv hV 0).continuousOn.comp hpointContinuous.continuousOn hmem
  have hSc : ContinuousOn (fun x => S (coordinatePoint x t)) (Icc l r) :=
    hS.comp hpointContinuous.continuousOn hmem
  have he : ContinuousOn (fun x => energyDensity S v (coordinatePoint x t)) (Icc l r) :=
    ((hvt.pow 2).add (hSc.mul (hvx.pow 2))).div_const 2
  have hsmall : (∫ x in -pulseRadius..pulseRadius, (coordPartial i v (coordinatePoint x t))^2) ≤
      ∫ x in l..r, (coordPartial i v (coordinatePoint x t))^2 :=
    intervalIntegral.integral_mono_interval hleft (by linarith) hright
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      ((hvi.pow 2).intervalIntegrable_of_Icc hlr)
  have henergy : (∫ x in l..r, (coordPartial i v (coordinatePoint x t))^2) ≤
      K*movingEnergy xl xr a speed S v t := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hlr
      ((hvi.pow 2).intervalIntegrable_of_Icc hlr)
      ((continuousOn_const.mul he).intervalIntegrable_of_Icc hlr) (fun x hx => by
        have hscalar := scalar_gradient_le_energy hs0 (hfloor x hx)
          (a := coordPartial 1 v (coordinatePoint x t)) (b := coordPartial 0 v (coordinatePoint x t))
        have hi : (coordPartial i v (coordinatePoint x t))^2 ≤
            (coordPartial 1 v (coordinatePoint x t))^2+(coordPartial 0 v (coordinatePoint x t))^2 := by
          fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith [sq_nonneg (coordPartial 0 v (coordinatePoint x t)),
            sq_nonneg (coordPartial 1 v (coordinatePoint x t))]
        exact hi.trans hscalar)
    dsimp only [Pi.pow_apply,Pi.mul_apply] at hmono
    simpa only [intervalIntegral.integral_const_mul,movingEnergy,movingIntervalIntegral,l,r,K] using hmono
  have hroot := Real.sqrt_le_sqrt (hsmall.trans henergy)
  rw [Real.sqrt_mul hK] at hroot
  have hpoint : (fun x => coordPartial i v (coordinatePoint x t)^2) =
      (fun x => coordPartial i v (boxPoint x t)^2) := by
    funext x
    have he : coordinatePoint x t=boxPoint x t := by ext j; fin_cases j <;> simp [coordinatePoint,boxPoint]
    rw [he]
  simpa only [intervalIntegral.integral_of_le (by linarith : -pulseRadius ≤ pulseRadius),
    ← integral_Icc_eq_integral_Ioc,hpoint,K] using hroot

end SmoothLocal.Hyperbolic

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem comparison_exponential_le_fixed {Lambda delta tau : ℝ}
    (ht : 0 < tau) (hlarge : Lambda*(2*delta) ≤ tau) :
    Real.exp (Lambda*(2*delta/tau)) ≤ Real.exp 1 := by
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc]
  exact (div_le_one ht).mpr hlarge

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_comparison_gradient
    {gRef : MetricField} {U S : Set Coord}
    (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c s0 : ℝ} (hc : 0 < c) (hs0 : 0 < s0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : MetricField) (P z : Coord → ℝ) (V : Set Coord)
      (boxRadius width pulseRadius a b F : ℝ),
      IsOpen V → V ⊆ U → SmoothPositiveOn g V →
      ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V →
      0 < width → width < boxRadius → a ≤ b →
      closedRectangle (-boxRadius) boxRadius a b ⊆ V →
      closedRectangle (-boxRadius) boxRadius a b ⊆ S →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ‖p‖ ≤ R) →
      CoordinateBound P (closedRectangle (-boxRadius) boxRadius a b) 3 Z0 →
      CoordinateBound z (closedRectangle (-boxRadius) boxRadius a b) 3 Z →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator gRef (qHeightJetSegment P z sigma p)| ∧
          s0 ≤ qFirstCoefficient gRef 5 (qHeightJetSegment P z sigma p)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius, P (boxPoint x a)=z (boxPoint x a)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius,
        coordPartial 1 P (boxPoint x a)=coordPartial 1 z (boxPoint x a)) →
      0 < pulseRadius → 0 ≤ F →
      comparisonEnergySpeed C*(b-a) ≤ width-pulseRadius →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, |metricComparisonSource g gRef P z p| ≤ F) →
      ∀ t ∈ Icc a b, ∀ i : Fin 2,
        Real.sqrt (∫ x in Icc (-pulseRadius) pulseRadius,
          (coordPartial i (comparisonDifference P z) (boxPoint x t))^2) ≤
          Real.sqrt (2*(1+1/s0))*
            (Real.exp (comparisonEnergyRate C Z0 Z s0*(b-a))*F*Real.sqrt (2*width)*(b-a)) := by
  obtain ⟨C,hC,henergy⟩ := exists_actual_comparison_energy hgRef hU hS hSU R Z0 Z hR hc hs0
  refine ⟨C,hC,?_⟩
  intro g P z V boxRadius width pulseRadius a b F hV hVU hg hP hz hw hwR hab
    hboxV hboxS hpB hPZ hzZ hD hxx hmargin hvalue hvelocity hpulse hF hwidth hsource
  let T := closedRectangle (-boxRadius) boxRadius a b
  let speed := comparisonEnergySpeed C
  let rate := comparisonEnergyRate C Z0 Z s0
  have hs : 0 ≤ speed := add_nonneg (zero_le_one.trans hC) (Real.sqrt_nonneg _)
  have hr : 0 ≤ rate := by unfold rate comparisonEnergyRate; positivity
  have hlength : 2*speed*(b-a)<2*width := by linarith
  have hgRefV := hgRef.mono hVU
  have hseg : ∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef V := by
    intro p hp sigma hsigma
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hboxV hp,
      abs_pos.mp (hc.trans_le (hmargin p hp sigma hsigma).1)⟩
  obtain ⟨W,hW,hTW,hWV,_,hWsmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRefV hV hP hz (closedRectangle_compact _ _ _ _) hboxV hseg
  have hSlabT {t : ℝ} (ht : t ∈ Icc a b) : shrinkingSlab (-width) width a t speed ⊆ T := by
    intro p hp
    change p 1 ∈ Icc a t ∧ p 0 ∈ Icc (-width+speed*(p 1-a)) (width-speed*(p 1-a)) at hp
    have hinc : 0 ≤ speed*(p 1-a) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
    exact ⟨⟨by linarith [hp.2.1],
      by linarith [hp.2.2]⟩,⟨hp.1.1,hp.1.2.trans ht.2⟩⟩
  intro t ht i
  have hTT : closedRectangle (-boxRadius) boxRadius a t ⊆ T :=
    fun p hp => ⟨hp.1,⟨hp.2.1,hp.2.2.trans ht.2⟩⟩
  have hlengtht : 2*speed*(t-a)<2*width := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs)
    exact hm.trans_lt hlength
  have hEt := henergy g P z V boxRadius width a t hV hVU hg hP hz hw hwR ht.1
    (hTT.trans hboxV) (hTT.trans hboxS) (fun p hp => hpB p (hTT hp))
    (fun ds hds p hp => hPZ ds hds p (hTT hp)) (fun ds hds p hp => hzZ ds hds p (hTT hp))
    (fun p hp => hD p (hTT hp)) (fun p hp => hxx p (hTT hp))
    (fun p hp sigma hsigma => hmargin p (hTT hp) sigma hsigma) hvalue hvelocity hlengtht
  have horder (s : ℝ) (hsat : s ∈ Icc a t) :
      inwardLeft (-width) a speed s ≤ inwardRight width a speed s := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hsat.2 a) hs
    dsimp [inwardLeft,inwardRight]
    linarith
  have hI := integrated_movingSourceNorm_le_of_pointwise_bound ht.1 hs hF horder
    (fun p hp => hsource p (hSlabT ht hp))
  have hE : Real.sqrt (movingEnergy (-width) width a speed (comparisonCoefficient gRef P z 5)
      (comparisonDifference P z) t) ≤ Real.exp (rate*(b-a))*F*Real.sqrt (2*width)*(b-a) := by
    have hI' : (∫ s in a..t, movingSourceNorm (-width) width a speed
        (metricComparisonSource g gRef P z) s) ≤ F*Real.sqrt (2*width)*(t-a) := by
      simpa only [sub_neg_eq_add,←two_mul] using hI
    have h0 := hEt.trans (mul_le_mul_of_nonneg_left hI' (Real.exp_pos _).le)
    have hexp : Real.exp (rate*(t-a)) ≤ Real.exp (rate*(b-a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hr)
    have htime : F*Real.sqrt (2*width)*(t-a) ≤ F*Real.sqrt (2*width)*(b-a) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (mul_nonneg hF (Real.sqrt_nonneg _))
    have hprod := mul_le_mul hexp htime
      (mul_nonneg (mul_nonneg hF (Real.sqrt_nonneg _)) (sub_nonneg.mpr ht.1)) (Real.exp_pos _).le
    apply h0.trans
    convert hprod using 1 <;> try with_reducible_and_instances rfl
    first | rfl | ring
  have hcover : inwardLeft (-width) a speed t ≤ -pulseRadius ∧
      pulseRadius ≤ inwardRight width a speed t := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hs
    dsimp [inwardLeft,inwardRight]
    constructor <;> linarith
  have hgrad := fixed_slice_gradient_le_moving_energy hW (hWsmooth 5).continuousOn
    ((hz.mono hWV).sub (hP.mono hWV)) hs0 hpulse.le hcover.1 hcover.2
    (fun x hx => hTW (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx)))
    (fun x hx => averagedQCoefficient_lower hgRefV hV
      (hseg _ (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx))) 5
      (fun sigma hsigma => (hmargin _ (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx)) sigma hsigma).2)) i
  exact hgrad.trans (mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg _))

end SmoothLocal.HighEquation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem pulseStrip_subset_comparisonSlab
    {a delta tau speed : ℝ} (_ha : 0 ≤ a) (_hd : 0 ≤ delta) (_ht : 0 < tau)
    (hs : 0 ≤ speed) (htravel : speed*(2*delta/tau) ≤ 3*a) :
    pulseStrip a delta tau ⊆ shrinkingSlab (-(4*a)) (4*a) (-(delta/tau)) (delta/tau) speed := by
  intro p hp
  have hpT : p 1 ∈ Icc (-(delta/tau)) (delta/tau) := hp.2
  have hm : speed*(p 1-(-(delta/tau))) ≤ speed*(2*delta/tau) := by
    apply mul_le_mul_of_nonneg_left _ hs
    calc
      _ ≤ delta/tau+delta/tau := by linarith [hpT.2]
      _ = _ := by ring
  refine ⟨hpT,?_⟩
  change -(4*a)+speed*(p 1-(-(delta/tau))) ≤ p 0 ∧
    p 0 ≤ 4*a-speed*(p 1-(-(delta/tau)))
  constructor <;> linarith [hp.1.1,hp.1.2]

theorem comparisonSlab_subset_dataStrip
    {a delta tau speed : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ speed) :
    shrinkingSlab (-(4*a)) (4*a) (-(delta/tau)) (delta/tau) speed ⊆
      pulseStrip (8*a) delta tau := by
  intro p hp
  have hinc : 0 ≤ speed*(p 1-(-(delta/tau))) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
  refine ⟨?_,hp.1⟩
  change -(8*a) ≤ p 0 ∧ p 0 ≤ 8*a
  change p 1 ∈ Icc (-(delta/tau)) (delta/tau) ∧
    (-(4*a)+speed*(p 1-(-(delta/tau))) ≤ p 0 ∧
      p 0 ≤ 4*a-speed*(p 1-(-(delta/tau)))) at hp
  constructor <;> linarith [hp.2.1,hp.2.2]

theorem comparison_pulse_travel_bound
    {a delta tau speed : ℝ} (ha : 0 < a) (ht : 0 < tau)
    (hlarge : 2*speed*delta/(3*a) ≤ tau) : speed*(2*delta/tau) ≤ 3*a := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ ht).mpr
  convert (div_le_iff₀ (by positivity : 0 < 3*a)).mp hlarge using 1 <;> ring

theorem comparison_pulse_geometry_eventually
    {a speed : ℝ} (ha : 0 < a) (hs : 0 ≤ speed) (delta : ℝ) (hd : 0 ≤ delta) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
      speed*(2*delta/(tau : ℝ)) ≤ 3*a ∧
      pulseStrip a delta (tau : ℝ) ⊆
        shrinkingSlab (-(4*a)) (4*a) (-(delta/(tau : ℝ))) (delta/(tau : ℝ)) speed ∧
      shrinkingSlab (-(4*a)) (4*a) (-(delta/(tau : ℝ))) (delta/(tau : ℝ)) speed ⊆
        pulseStrip (8*a) delta (tau : ℝ) := by
  have hlarge : ∀ᶠ tau : ℕ in atTop, max 1 (2*speed*delta/(3*a)) ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hlarge] with tau htau
  have ht1 : 1 ≤ (tau : ℝ) := (le_max_left _ _).trans htau
  have ht : (0 : ℝ) < tau := zero_lt_one.trans_le ht1
  have htravel := comparison_pulse_travel_bound ha ht ((le_max_right _ _).trans htau)
  exact ⟨ht1,htravel,pulseStrip_subset_comparisonSlab ha.le hd ht hs htravel,
    comparisonSlab_subset_dataStrip ha.le hs⟩

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
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_uniform_taylor_pulse
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
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
            let z0 := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ z0 (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              z0 ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 z0 ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ P : Polynomial ℝ, P.natDegree ≤ N+1 ∧ ∀ t, P.eval t = z0 ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs z0 ![x,t] 0 0| ∧
                |qResidual gs z0 ![x,t]| ≤ C/(tau : ℝ)^N) := by
  let L := boundedClassWidth kappa M
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let S := shearedModelSquare q0
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hgs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  have hS : IsCompact S := shearedModelSquare_isCompact q0
  have hSVs : S ⊆ Vs := shearedModelSquare_subset_domain hSV q0
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hCauchy⟩ :=
    exists_actual_off_pulse_cauchy_bounds hgStar hV hSV M hG hd hkappa hM hq0
  obtain ⟨tauRef,htauRef,hfloor⟩ := exists_bounded_patch_reference_initial_floor
    G kappa d q0 M hG hkappa hd hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N
  let K := taylorInitialRequest N (taylorStripJetOrder N)
  obtain ⟨B,hB,hCauchyK⟩ := hCauchy K
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hc : 0 < c := div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  obtain ⟨C,hC,hTaylor⟩ := uniform_taylor_pulse hgs hVs hS hSVs
    (initialShearedStateBudget (M : ℝ) q0) (initialShearedStateBudget_nonneg _ _) hc B hB N
  refine ⟨C,hC,?_⟩
  intro delta hdelt hdhalf
  obtain ⟨tauTaylor,_,hpoly⟩ := hTaylor delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hCauchyK N delta hdelt,hwidth,
    eventually_ge_atTop (max tauTaylor tauRef)] with tau hCauchyTau hwidthTau htau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let a := -delta/(tau : ℝ)
  let zs := heightInShearCoordinates z q0
  let I := Ioo (-(L*r)) (L*r)
  let J := Icc (-(L*r/2)) (L*r/2)
  have htauT : tauTaylor ≤ tau := (le_max_left _ _).trans htau
  have htauR : tauRef ≤ tau := (le_max_right _ _).trans htau
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
  have hregion (x : ℝ) (hx : x ∈ J) (t : ℝ)
      (ht : t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ))) : (![x,t] : Coord) ∈ S :=
    pulseRectangle_mem_shearedModelSquare hL hr hrhalf hLr hq0 hdw (abs_le.mpr hx) ht
  have hresult := hpoly tau htauT (heightCauchyValue zs a) (heightCauchyVelocity zs a) I J hI hJI h0 h1
    (fun x hx => hcutS x hx) hstate hden
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).1)
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).2) hregion
  refine ⟨hresult.1,hresult.2.1,hresult.2.2.1,?_⟩
  intro x hx t ht
  have hh := hresult.2.2.2 x (abs_le.mp hx) t ht
  have he : c/2 = (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) := by dsimp [c]; ring
  exact ⟨he ▸ hh.1,hh.2⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_uniform_taylor_comparison_and_moment
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
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
            let z0 := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ z0 (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              z0 ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 z0 ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ P : Polynomial ℝ, P.natDegree ≤ N+1 ∧ ∀ t, P.eval t = z0 ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs z0 ![x,t] 0 0| ∧
                |qResidual gs z0 ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs z0)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs z0)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_taylor_pulse hgStar hV hSV M hG hd hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N
  obtain ⟨C,hC,hN⟩ := hTaylor N
  refine ⟨C,hC,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hN delta hdelt hdhalf,hwidth] with tau htaylor hwidthTau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have ht := htaylor g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ)))
    (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have ha : 0 < a := div_pos (mul_pos hL hr) (by norm_num)
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le hwidthTau.1
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have hP : ContDiffOn ℝ ∞ P (spatialStrip I) := ht.1
  have hpoint (p : Coord) (hp : p ∈ pulseStrip a delta (tau : ℝ)) :
      (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P p 0 0| ∧
      |qResidual gs P p| ≤ C/(tau : ℝ)^N := by
    have hx : |p 0| ≤ L*r/2 := (abs_le.mpr hp.1).trans (by dsimp [a]; nlinarith [mul_pos hL hr])
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    simpa only [he] using ht.2.2.2 (p 0) hx (p 1) htime
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs := shearedModelDomain_isOpen hV q0
  have hc : 0 < (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
      (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  have hsub : pulseStrip a delta (tau : ℝ) ⊆
      comparisonDomain gs (inverseShearCoordinates q0 ⁻¹' V) P I := by
    intro p hp
    have hx : |p 0| ≤ L*r/2 := (abs_le.mpr hp.1).trans (by dsimp [a]; nlinarith [mul_pos hL hr])
    have hpI : p ∈ spatialStrip I := by
      exact ⟨by linarith [(abs_le.mp hx).1,mul_pos hL hr],
        by linarith [(abs_le.mp hx).2,mul_pos hL hr]⟩
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    have hpS : p ∈ shearedModelSquare q0 := by
      simpa only [he] using pulseRectangle_mem_shearedModelSquare hL hr hrhalf hLr hq0 hdw hx htime
    exact mem_comparisonDomain hpI (shearedModelSquare_subset_domain hSV q0 hpS)
      (abs_pos.mp (hc.trans_le (hpoint p hp).1))
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,
    (qResidual_contDiffOn hgs hVs isOpen_Ioo hP).continuousOn.mono hsub,?_⟩
  apply (pulseWeightedMoment_bound ha hdelt.le htr (div_nonneg hC (pow_nonneg htr.le N))
    (fun p hp => (hpoint p hp).2)).trans_eq
  rw [pow_succ]
  field_simp [htr.ne']
  ring

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_comparison_gradient_from_source
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
    ∃ Cgradient : ℝ, 0 ≤ Cgradient ∧
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
          ∀ F : ℝ, 0 ≤ F →
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤ F) →
            ∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*F*delta/(tau : ℝ) := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let nu := (boundedClassSpeed kappa M)^2/(2*(M : ℝ))
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hLrpos : 0 < L*r := mul_pos hL hr
  have hnu : 0 < nu := boundedClassShearHxxFloor_pos hkappa hM
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  obtain ⟨CP,A,_,hA,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  let s0 := ((nu*(1/(M : ℝ)))/2)/A^2
  have hs0 : 0 < s0 := div_pos (half_pos (mul_pos hnu hminv))
    (sq_pos_of_pos (zero_lt_one.trans_le hA))
  have hgs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  obtain ⟨CE,hCE,hgradient⟩ := exists_actual_comparison_gradient hgs hVs
    (shearedModelSquare_isCompact q0) (shearedModelSquare_subset_domain hSV q0)
    1 CP Z (by norm_num) (half_pos hnu) hs0
  let speed := comparisonEnergySpeed CE
  let rate := comparisonEnergyRate CE CP Z s0
  let Cgradient := 2*Real.exp 1*Real.sqrt (2*(1+1/s0))*Real.sqrt (2*(L*r/4))
  have hs : 0 ≤ speed := add_nonneg (zero_le_one.trans hCE) (Real.sqrt_nonneg _)
  have hCg : 0 ≤ Cgradient := by dsimp [Cgradient]; positivity
  refine ⟨Cgradient,hCg,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  have hlarge : ∀ᶠ tau : ℕ in atTop, rate*(2*delta) ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  have hpulse : 0 < L*r/16 := div_pos hLrpos (by norm_num : (0 : ℝ) < 16)
  filter_upwards [hsegment delta hdelt hdhalf,hwidth,hlarge,
    comparison_pulse_geometry_eventually hpulse hs delta hdelt.le]
    with tau hsegTau hw hrateTau htravel
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gt := metricInShearCoordinates g q0
  let zs := heightInShearCoordinates z q0
  let a := -delta/(tau : ℝ)
  let b := delta/(tau : ℝ)
  let I := Ioo (-(L*r)) (L*r)
  let P := taylorApproximation gs a (heightCauchyValue zs a) (heightCauchyVelocity zs a) N
  let T := closedRectangle (-(L*r/2)) (L*r/2) a b
  have hTP : T = pulseStrip (L*r/2) delta (tau : ℝ) := by
    simp only [T,pulseStrip,a,b,neg_div]
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbnonneg : 0 ≤ b := div_nonneg hdelt.le htpos.le
  have hab : a ≤ b := by dsimp only [a,b]; simp only [neg_div]; linarith
  have hbr : b ≤ r := by
    have he : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    dsimp only [b]
    rw [he]
    linarith [hw.2]
  have hcoordinates (p : Coord) (hp : p ∈ T) : |p 0| ≤ L*r ∧ |p 1| ≤ r := by
    have hx : |p 0| ≤ L*r/2 := abs_le.mpr hp.1
    have ht : |p 1| ≤ b := abs_le.mpr
      ⟨by simpa only [a,b,neg_div] using hp.2.1,hp.2.2⟩
    exact ⟨hx.trans (by linarith),ht.trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ T) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hbox : T ⊆ D := by
    intro p hp
    exact ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,
      ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩⟩
  have hpoint (p : Coord) (hp : p ∈ T) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change |p 0| ≤ 1
      exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · change |p 1| ≤ 1
      exact (hcoordinates p hp).2.trans (by linarith)
  have hgt : SmoothPositiveOn gt D :=
    (metricInShearCoordinates_smoothPositive hg q0).mono (fun p hp => hp.1.1)
  have hzsUs : ContDiffOn ℝ ∞ zs Us := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD : ContDiffOn ℝ ∞ zs D := hzsUs.mono (fun p hp => hp.1.1)
  obtain ⟨hP,hPB,hsegActual⟩ := hsegTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hzB : CoordinateBound zs T 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have hPB' : CoordinateBound P T 3 CP := by rw [hTP]; exact hPB
  have hCauchy := actual_taylor_Cauchy_of_smooth gs zs a N isOpen_Ioo hP
  have hpointEq (x t : ℝ) : boxPoint x t=(![x,t] : Coord) := by
    ext i
    fin_cases i
    · change x*1+t*0=x
      ring
    · change x*0+t*1=t
      ring
  have hvalue (x : ℝ) (hx : x ∈ Ioo (-(L*r/2)) (L*r/2)) :
      P (boxPoint x a)=zs (boxPoint x a) := by
    rw [hpointEq]
    exact (hCauchy x ⟨by linarith [hx.1],by linarith [hx.2]⟩).1
  have hvelocity (x : ℝ) (hx : x ∈ Ioo (-(L*r/2)) (L*r/2)) :
      coordPartial 1 P (boxPoint x a)=coordPartial 1 zs (boxPoint x a) := by
    rw [hpointEq]
    exact (hCauchy x ⟨by linarith [hx.1],by linarith [hx.2]⟩).2
  have hmargin (p : Coord) (hp : p ∈ T) (sigma : ℝ) (hsigma : sigma ∈ Icc (0 : ℝ) 1) :
      nu/2 ≤ |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ∧
        s0 ≤ qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p) := by
    have hm := hsegActual p (by simpa only [hTP] using hp) sigma hsigma
    have he : nu/2=(boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by dsimp [nu]; ring
    exact ⟨by simpa only [he] using hm.1,hm.2.2.2.1⟩
  have htravel' : speed*(b-a) ≤ L*r/4-L*r/16 := by
    have he : b-a=2*delta/(tau : ℝ) := by dsimp [a,b]; ring
    rw [he]
    calc
      speed*(2*delta/(tau : ℝ)) ≤ 3*(L*r/16) := htravel.2.1
      _ = L*r/4-L*r/16 := by ring
  dsimp only
  intro F hF hsource theta htheta i
  have hsourceMetric (p : Coord) (hp : p ∈ T) :
      |metricComparisonSource gt gs P zs p| ≤ F := by
    change |actualComparisonSource gStar g z q0 P p| ≤ F
    exact hsource p (by simpa only [hTP] using hp)
  have hgrad := hgradient gt P zs D (L*r/2) (L*r/4) (L*r/16) a b F
    hD (fun p hp => hp.1.2) hgt hPD hzsD (by positivity) (by linarith) hab
    hbox (fun p hp => hpS p hp) hpoint hPB' hzB
    (fun p hp => (hgeom p hp).2.2.2.2.2.1)
    (fun p hp => abs_pos.mp (hnu.trans_le (hgeom p hp).2.1))
    hmargin hvalue hvelocity (by positivity) hF htravel'
    hsourceMetric theta
    (by simpa only [a,b,neg_div] using htheta) i
  have he : b-a=2*delta/(tau : ℝ) := by dsimp [a,b]; ring
  rw [he] at hgrad
  have hexp := comparison_exponential_le_fixed htpos hrateTau
  have hbound := mul_le_mul_of_nonneg_right hexp hF
  have hbound := mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg (2*(L*r/4)))
  have hduration : 0 ≤ 2*delta/(tau : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdelt.le) htpos.le
  have hbound := mul_le_mul_of_nonneg_right hbound hduration
  have hbound := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg (2*(1+1/s0)))
  apply hgrad.trans
  convert hbound using 1 <;> try with_reducible_and_instances rfl
  dsimp [Cgradient]
  ring

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

theorem exists_actual_uniform_comparison_gradient
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
      ∀ N : ℕ, 2 < N → ∃ Cres Csource Cgradient : ℝ,
        0 ≤ Cres ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧
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
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ Q : Polynomial ℝ, Q.natDegree ≤ N+1 ∧ ∀ t, Q.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ Cres/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*Cres*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_taylor_comparison_and_moment hgStar hV hSV M hG hd hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N hN
  obtain ⟨Cres,hCres,hTaylorN⟩ := hTaylor N
  obtain ⟨Csource,hCsource,hsource⟩ := exists_actual_class_comparison_source_bound_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN Cres hCres
  obtain ⟨CE,hCE,hgradient⟩ := exists_actual_class_comparison_gradient_from_source
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  refine ⟨Cres,Csource,CE*Csource,hCres,hCsource,mul_nonneg hCE hCsource.le,?_⟩
  intro delta hdelt hdhalf
  filter_upwards [hTaylorN delta hdelt hdhalf,hsource delta hdelt hdhalf,hgradient delta hdelt hdhalf]
    with tau htaylor hsourceTau hgradientTau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let L := boundedClassWidth kappa M
  let zs := heightInShearCoordinates z q0
  let gs := metricInShearCoordinates gStar q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ)))
    (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  have ht := htaylor g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hres (p : Coord) (hp : p ∈ pulseStrip (L*r/2) delta (tau : ℝ)) :
      |qResidual gs P p| ≤ Cres/(tau : ℝ)^N := by
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    simpa only [he] using (ht.2.2.2.1 (p 0) (abs_le.mpr hp.1) (p 1) htime).2
  have hs := hsourceTau.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ P hres
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2.1,ht.2.2.2.2.2,hs,?_⟩
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast hsourceTau.1)
  have hF : 0 ≤ Csource*(tau : ℝ)^2/(tau : ℝ)^N := by positivity
  intro theta htheta i
  have hgrad := hgradientTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
    (Csource*(tau : ℝ)^2/(tau : ℝ)^N) hF hs theta htheta i
  apply hgrad.trans_eq
  field_simp [htpos.ne']

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.exists_actual_uniform_comparison_gradient := @OAI.SmoothLocal.Perturbation.exists_actual_uniform_comparison_gradient
