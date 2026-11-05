-- Prove2me | solution 1 for OAI.SmoothLocal.Taylor.taylorApproximation_properties
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:36:35.154725+00:00
-- url     : https://prove2.me/submissions/4bc4280c-9162-4a02-b5d0-f59a5a793b0d

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

theorem normalizedTimePower_iteratedDeriv_at_center (a : ℝ) (m k : ℕ) :
    iteratedDeriv k (normalizedTimePower a m) a = if k = m then 1 else 0 := by
  change iteratedDeriv k (fun t : ℝ => (t - a)^m / (m.factorial : ℝ)) a = _
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_comp_sub_const (f := fun t : ℝ => t^m)]
  change iteratedDeriv k (fun t : ℝ => t^m) (a - a) / (m.factorial : ℝ) = _
  rw [sub_self, iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m) : (m.factorial : ℝ) ≠ 0)
  · simpa only [Nat.cast_zero] using (zero_div (m.factorial : ℝ))

theorem coefficient_timePower_jet (a C : ℝ) (m k : ℕ) :
    iteratedDeriv k (fun t => C * normalizedTimePower a m t) a =
      if k = m then C else 0 := by
  rw [iteratedDeriv_const_mul_field, normalizedTimePower_iteratedDeriv_at_center]
  split_ifs <;> simp

section Composition
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedDeriv_comp_eq_of_jets {Q : E → F} {f g : ℝ → E} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ ∞ f a) (hg : ContDiffAt ℝ ∞ g a)
    (hQ : ContDiffAt ℝ ∞ Q (f a))
    (hjets : ∀ j ≤ n, iteratedDeriv j f a = iteratedDeriv j g a) :
    iteratedDeriv n (Q ∘ f) a = iteratedDeriv n (Q ∘ g) a := by
  have hvalue : f a = g a := by simpa only [iteratedDeriv_zero] using hjets 0 (Nat.zero_le n)
  have hQg : ContDiffAt ℝ ∞ Q (g a) := by rw [← hvalue]; exact hQ
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hQ hf (WithTop.coe_le_coe.mpr le_top),
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition hQg hg (WithTop.coe_le_coe.mpr le_top)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hvalue]
  congr 1
  funext j
  exact hjets (c.partSize j) (c.partSize_le j)

theorem iteratedDeriv_add_eq_of_zero_jets {f h : ℝ → E} {a : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ ∞ f a) (hh : ContDiffAt ℝ ∞ h a)
    (hzero : ∀ j ≤ n, iteratedDeriv j h a = 0) :
    ∀ j ≤ n, iteratedDeriv j (fun t => f t + h t) a = iteratedDeriv j f a := by
  intro j hj
  rw [iteratedDeriv_fun_add (hf.of_le (WithTop.coe_le_coe.mpr le_top))
    (hh.of_le (WithTop.coe_le_coe.mpr le_top)), hzero j hj, add_zero]

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

theorem iteratedDeriv_state_eval {f : ℝ → DarbouxState} {y : ℝ}
    (hf : ContDiffAt ℝ ∞ f y) (n : ℕ) (i : Fin 6) :
    (iteratedDeriv n f y) i = iteratedDeriv n (fun t => f t i) y := by
  let L : DarbouxState →L[ℝ] ℝ := ContinuousLinearMap.proj i
  symm
  change iteratedFDeriv ℝ n (L ∘ f) y (fun _ => 1) = L (iteratedDeriv n f y)
  rw [L.iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)]
  rfl

end SmoothLocal.HighEquation

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

theorem initialPoint_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => (![y, t] : Coord)) (Pi.single 0 (1 : ℝ)) x := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hasDerivAt_id x using 1 <;> rfl
  · simpa using hasDerivAt_const x t

theorem point_eta (p : Coord) : (![p 0, p 1] : Coord) = p := by
  ext i
  fin_cases i <;> rfl

theorem separatedProduct_partial_x {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (separatedProduct C f) p = deriv C (p 0) * f (p 1) := by
  have hd := (((separatedProduct_contDiffOn hC f hf).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (separatedProduct C f) (fderiv ℝ (separatedProduct C f) p)
      (![p 0, p 1] : Coord) := by simpa only [point_eta] using hd
  have hcurve := hd'.comp_hasDerivAt (p 0) (initialPoint_hasDerivAt (p 0) (p 1))
  have hCderiv := ((hC.contDiffAt (hI.mem_nhds hp)).differentiableAt (by simp)).hasDerivAt
  have hformula := hCderiv.mul_const (f (p 1))
  have heq : (fun y => separatedProduct C f ![y, p 1]) = (fun y => C y * f (p 1)) := rfl
  change HasDerivAt (fun y => separatedProduct C f ![y, p 1])
    (coordPartial 0 (separatedProduct C f) p) (p 0) at hcurve
  rw [heq] at hcurve
  exact hcurve.unique hformula

theorem separatedProduct_partial_t {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (separatedProduct C f) p = C (p 0) * deriv f (p 1) := by
  have hd := (((separatedProduct_contDiffOn hC f hf).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (separatedProduct C f) (fderiv ℝ (separatedProduct C f) p)
      (![p 0, p 1] : Coord) := by simpa only [point_eta] using hd
  have hcurve := hd'.comp_hasDerivAt (p 1) (verticalPoint_hasDerivAt (p 0) (p 1))
  have hformula := (hf.differentiable (by simp) (p 1)).hasDerivAt.const_mul (C (p 0))
  have heq : (fun y => separatedProduct C f ![p 0, y]) = (fun y => C (p 0) * f y) := rfl
  change HasDerivAt (fun y => separatedProduct C f ![p 0, y])
    (coordPartial 1 (separatedProduct C f) p) (p 1) at hcurve
  rw [heq] at hcurve
  exact hcurve.unique hformula

theorem taylorCorrection_contDiffOn {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (taylorCorrection C a n) (spatialStrip I) :=
  separatedProduct_contDiffOn hC _ (normalizedTimePower_contDiff a (n + 2))

theorem taylorCorrection_partial_x {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (taylorCorrection C a n) p =
      separatedProduct (deriv C) (normalizedTimePower a (n + 2)) p :=
  separatedProduct_partial_x hC hI _ (normalizedTimePower_contDiff a (n + 2)) hp

theorem taylorCorrection_partial_t {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (taylorCorrection C a n) p =
      separatedProduct C (normalizedTimePower a (n + 1)) p := by
  rw [taylorCorrection, separatedProduct_partial_t hC hI _
    (normalizedTimePower_contDiff a (n + 2)) hp]
  rw [show n + 2 = (n + 1) + 1 by omega, normalizedTimePower_deriv]
  rfl

theorem taylorCorrection_partial_xx {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (coordPartial 0 (taylorCorrection C a n)) p =
      separatedProduct (deriv (deriv C)) (normalizedTimePower a (n + 2)) p := by
  have heq : coordPartial 0 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct (deriv C) (normalizedTimePower a (n + 2)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_x hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 0]
  exact separatedProduct_partial_x (hC.deriv_of_isOpen hI (by simp)) hI _
    (normalizedTimePower_contDiff a (n + 2)) hp

theorem taylorCorrection_partial_xt {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (coordPartial 1 (taylorCorrection C a n)) p =
      separatedProduct (deriv C) (normalizedTimePower a (n + 1)) p := by
  have heq : coordPartial 1 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct C (normalizedTimePower a (n + 1)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_t hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 0]
  exact separatedProduct_partial_x hC hI _ (normalizedTimePower_contDiff a (n + 1)) hp

theorem taylorCorrection_partial_tt {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (coordPartial 1 (taylorCorrection C a n)) p =
      separatedProduct C (normalizedTimePower a n) p := by
  have heq : coordPartial 1 (taylorCorrection C a n) =ᶠ[𝓝 p]
      separatedProduct C (normalizedTimePower a (n + 1)) := by
    filter_upwards [(spatialStrip_isOpen hI).mem_nhds hp] with q hq
    exact taylorCorrection_partial_t hC hI a n hq
  rw [coordPartial_eq_of_eventuallyEq heq 1,
    separatedProduct_partial_t hC hI _ (normalizedTimePower_contDiff a (n + 1)) hp,
    normalizedTimePower_deriv]
  rfl

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
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem secondCoordPartial_add {P R : Coord → ℝ} {V : Set Coord}
    (hV : IsOpen V) (hP : ContDiffOn ℝ ∞ P V) (hR : ContDiffOn ℝ ∞ R V)
    {p : Coord} (hp : p ∈ V) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => P q + R q)) p =
      coordPartial i (coordPartial j P) p + coordPartial i (coordPartial j R) p := by
  have he : coordPartial j (fun q => P q + R q) =ᶠ[𝓝 p]
      (fun q => coordPartial j P q + coordPartial j R q) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact HessianCalculus.coordPartial_add_at
      ((hP.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp))
      ((hR.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)) j
  rw [coordPartial_eq_of_eventuallyEq he i]
  exact HessianCalculus.coordPartial_add_at
    (((partial_contDiffOn hP hV j).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp))
    (((partial_contDiffOn hR hV j).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)) i

def correctionState (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (p : Coord) : DarbouxState :=
  ![0, 0,
    deriv C (p 0) * normalizedTimePower a (n + 2) (p 1),
    C (p 0) * normalizedTimePower a (n + 1) (p 1),
    deriv C (p 0) * normalizedTimePower a (n + 1) (p 1),
    deriv (deriv C) (p 0) * normalizedTimePower a (n + 2) (p 1)]

theorem correctionState_slice_contDiff (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun t => correctionState C a n ![x, t]) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · change ContDiff ℝ ∞ (fun t => deriv C x * normalizedTimePower a (n + 2) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 2))
  · change ContDiff ℝ ∞ (fun t => C x * normalizedTimePower a (n + 1) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 1))
  · change ContDiff ℝ ∞ (fun t => deriv C x * normalizedTimePower a (n + 1) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 1))
  · change ContDiff ℝ ∞ (fun t => deriv (deriv C) x * normalizedTimePower a (n + 2) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 2))

theorem correctionState_time_jets_zero (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ)
    (k : ℕ) (hk : k ≤ n) :
    iteratedDeriv k (fun t => correctionState C a n ![x, t]) a = 0 := by
  ext i
  rw [iteratedDeriv_state_eval (correctionState_slice_contDiff C a n x).contDiffAt k i]
  fin_cases i
  · exact iteratedDeriv_fun_const_zero
  · exact iteratedDeriv_fun_const_zero
  · change iteratedDeriv k (fun t => deriv C x * normalizedTimePower a (n + 2) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => C x * normalizedTimePower a (n + 1) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => deriv C x * normalizedTimePower a (n + 1) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => deriv (deriv C) x * normalizedTimePower a (n + 2) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]

theorem qSolutionJet_add_taylorCorrection {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    qSolutionJet (fun q => P q + taylorCorrection C a n q) p =
      qSolutionJet P p + correctionState C a n p := by
  have hV := spatialStrip_isOpen hI
  have hR := taylorCorrection_contDiffOn hC a n
  have hdP := (hP.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hdR := (hR.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  ext i
  fin_cases i
  · exact (add_zero (p 0)).symm
  · exact (add_zero (p 1)).symm
  · change coordPartial 0 (fun q => P q + taylorCorrection C a n q) p = _
    rw [HessianCalculus.coordPartial_add_at hdP hdR 0,
      taylorCorrection_partial_x hC hI a n hp]
    rfl
  · change coordPartial 1 (fun q => P q + taylorCorrection C a n q) p = _
    rw [HessianCalculus.coordPartial_add_at hdP hdR 1,
      taylorCorrection_partial_t hC hI a n hp]
    rfl
  · change coordPartial 0 (coordPartial 1 (fun q => P q + taylorCorrection C a n q)) p = _
    rw [secondCoordPartial_add hV hP hR hp 0 1,
      taylorCorrection_partial_xt hC hI a n hp]
    rfl
  · change coordPartial 0 (coordPartial 0 (fun q => P q + taylorCorrection C a n q)) p = _
    rw [secondCoordPartial_add hV hP hR hp 0 0,
      taylorCorrection_partial_xx hC hI a n hp]
    rfl

theorem qSolutionJet_time_slice_contDiffAt {P : Coord → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {x : ℝ} (hx : x ∈ I) (a : ℝ) :
    ContDiffAt ℝ ∞ (fun t => qSolutionJet P ![x, t]) a :=
  ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt

theorem qSolutionJet_taylorCorrection_time_jets
    {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ I) :
    ∀ k ≤ n,
      iteratedDeriv k (fun t => qSolutionJet
        (fun q => P q + taylorCorrection C a n q) ![x, t]) a =
      iteratedDeriv k (fun t => qSolutionJet P ![x, t]) a := by
  have he : (fun t => qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t]) =
      (fun t => qSolutionJet P ![x, t] + correctionState C a n ![x, t]) := by
    funext t
    exact qSolutionJet_add_taylorCorrection hI hP hC a n hx
  rw [he]
  exact iteratedDeriv_add_eq_of_zero_jets
    (qSolutionJet_time_slice_contDiffAt hI hP hx a)
    (correctionState_slice_contDiff C a n x).contDiffAt
    (fun k hk => correctionState_time_jets_zero C a n x k hk)

theorem sixVariableQ_taylorCorrection_time_jets
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ I)
    (hp : (![x, a] : Coord) ∈ U) (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    ∀ k ≤ n,
      iteratedDeriv k (fun t => sixVariableQ g (qSolutionJet
        (fun q => P q + taylorCorrection C a n q) ![x, t])) a =
      iteratedDeriv k (fun t => sixVariableQ g (qSolutionJet P ![x, t])) a := by
  intro k hk
  have hnew := hP.add (taylorCorrection_contDiffOn hC a n)
  have hj := qSolutionJet_taylorCorrection_time_jets hI hP hC a n hx
  have hvalue : qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a] =
      qSolutionJet P ![x, a] := by simpa only [iteratedDeriv_zero] using hj 0 (by omega)
  have hQ := sixVariableQ_contDiffAt_solutionJet hg hU hp hxx
  rw [← hvalue] at hQ
  exact iteratedDeriv_comp_eq_of_jets (Q := sixVariableQ g)
    (qSolutionJet_time_slice_contDiffAt hI hnew hx a)
    (qSolutionJet_time_slice_contDiffAt hI hP hx a) hQ
    (fun j hjk => hj j (hjk.trans hk))

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

theorem nextTaylorCoefficient_eq_residual_jet {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ I) (hp : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    nextTaylorCoefficient g a P n x =
      -iteratedDeriv n (fun t => qResidual g P ![x, t]) a := by
  exact congrArg Neg.neg (verticalJet_slice (comparisonDomain_isOpen hg hU hI hP)
    (qResidual_contDiffOn hg hU hI hP) x n a (mem_comparisonDomain hx hp hxx)).symm

theorem qResidual_taylorCorrection_time_jet
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n k : ℕ) (hk : k ≤ n)
    {x : ℝ} (hx : x ∈ I) (hp : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    iteratedDeriv k (fun t => qResidual g
      (fun q => P q + taylorCorrection C a n q) ![x, t]) a =
      iteratedDeriv k (fun t => qResidual g P ![x, t]) a +
        if k = n then C x else 0 := by
  have hV := spatialStrip_isOpen hI
  have hR := taylorCorrection_contDiffOn hC a n
  have hnew := hP.add hR
  have htt : ContDiffAt ℝ ∞ (fun t => coordPartial 1 (coordPartial 1 P) ![x, t]) a :=
    ((partial_contDiffOn (partial_contDiffOn hP hV 1) hV 1).contDiffAt
      (hV.mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt
  have httnew : ContDiffAt ℝ ∞ (fun t => coordPartial 1 (coordPartial 1
      (fun q => P q + taylorCorrection C a n q)) ![x, t]) a :=
    ((partial_contDiffOn (partial_contDiffOn hnew hV 1) hV 1).contDiffAt
      (hV.mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt
  have hQouter := sixVariableQ_contDiffAt_solutionJet hg hU hp hxx
  have hQ : ContDiffAt ℝ ∞ (fun t => sixVariableQ g (qSolutionJet P ![x, t])) a :=
    ContDiffAt.comp (g := sixVariableQ g) (f := fun t => qSolutionJet P ![x, t])
      a hQouter (qSolutionJet_time_slice_contDiffAt hI hP hx a)
  have hstate : qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a] =
      qSolutionJet P ![x, a] := by
    simpa only [iteratedDeriv_zero] using
      qSolutionJet_taylorCorrection_time_jets hI hP hC a n hx 0 (Nat.zero_le n)
  have hQouterNew : ContDiffAt ℝ ∞ (sixVariableQ g)
      (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a]) := by
    rw [hstate]
    exact hQouter
  have hQnew : ContDiffAt ℝ ∞ (fun t => sixVariableQ g
      (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])) a :=
    ContDiffAt.comp (g := sixVariableQ g)
      (f := fun t => qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])
      a hQouterNew (qSolutionJet_time_slice_contDiffAt hI hnew hx a)
  have he : (fun t => coordPartial 1 (coordPartial 1
      (fun q => P q + taylorCorrection C a n q)) ![x, t]) =
      (fun t => coordPartial 1 (coordPartial 1 P) ![x, t] +
        C x * normalizedTimePower a n t) := by
    funext t
    rw [secondCoordPartial_add hV hP hR (p := ![x, t]) hx 1 1,
      taylorCorrection_partial_tt hC hI a n (p := ![x, t]) hx]
    rfl
  have hmon : ContDiffAt ℝ ∞ (fun t => C x * normalizedTimePower a n t) a :=
    (contDiff_const.mul (normalizedTimePower_contDiff a n)).contDiffAt
  change iteratedDeriv k (fun t =>
    coordPartial 1 (coordPartial 1 (fun q => P q + taylorCorrection C a n q)) ![x, t] -
      sixVariableQ g (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])) a =
    iteratedDeriv k (fun t => coordPartial 1 (coordPartial 1 P) ![x, t] -
      sixVariableQ g (qSolutionJet P ![x, t])) a + _
  rw [iteratedDeriv_fun_sub (httnew.of_le (WithTop.coe_le_coe.mpr le_top))
      (hQnew.of_le (WithTop.coe_le_coe.mpr le_top)),
    iteratedDeriv_fun_sub (htt.of_le (WithTop.coe_le_coe.mpr le_top))
      (hQ.of_le (WithTop.coe_le_coe.mpr le_top)),
    sixVariableQ_taylorCorrection_time_jets hg hU hI hP hC a n hx hp hxx k hk,
    he, iteratedDeriv_fun_add (htt.of_le (WithTop.coe_le_coe.mpr le_top))
      (hmon.of_le (WithTop.coe_le_coe.mpr le_top)), coefficient_timePower_jet]
  ring

theorem nextTaylorCoefficient_cancels
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g P ![x, a] 0 0 ≠ 0)
    (hzero : ∀ x ∈ I, ∀ k < n, iteratedDeriv k (fun t => qResidual g P ![x, t]) a = 0) :
    ∀ x ∈ I, ∀ k < n + 1,
      iteratedDeriv k (fun t => qResidual g
        (fun q => P q + taylorCorrection (nextTaylorCoefficient g a P n) a n q) ![x, t]) a = 0 := by
  intro x hx k hk
  rw [qResidual_taylorCorrection_time_jet hg hU hI hP
    (nextTaylorCoefficient_contDiffOn hg hU hI hP a n hcut hxx)
    a n k (by omega) hx (hcut x hx) (hxx x hx)]
  by_cases hkn : k = n
  · subst k
    rw [ite_eq_left rfl, nextTaylorCoefficient_eq_residual_jet hg hU hI hP a n
      hx (hcut x hx) (hxx x hx)]
    ring
  · rw [ite_eq_right hkn, hzero x hx k (by omega), zero_add]

end SmoothLocal.Taylor

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

theorem taylorApproximation_properties {g : MetricField} {U : Set Coord}
    {u0 u1 : ℝ → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0) :
    ∀ N,
      ContDiffOn ℝ ∞ (taylorApproximation g a u0 u1 N) (spatialStrip I) ∧
      (∀ x ∈ I, qSolutionJet (taylorApproximation g a u0 u1 N) ![x, a] =
        qSolutionJet (linearCauchy a u0 u1) ![x, a]) ∧
      (∀ x ∈ I, ∀ k < N,
        iteratedDeriv k (fun t => qResidual g (taylorApproximation g a u0 u1 N) ![x, t]) a = 0) := by
  intro N
  induction N with
  | zero =>
    refine ⟨linearCauchy_contDiffOn h0 h1 a, fun _ _ => rfl, ?_⟩
    intro _ _ k hk
    omega
  | succ n hn =>
    have hxxn : ∀ x ∈ I,
        covHessian g (taylorApproximation g a u0 u1 n) ![x, a] 0 0 ≠ 0 := by
      intro x hx
      rw [← stateQDenominator_qSolutionJet, hn.2.1 x hx, stateQDenominator_qSolutionJet]
      exact hxx x hx
    have hC := nextTaylorCoefficient_contDiffOn hg hU hI hn.1 a n hcut hxxn
    refine ⟨hn.1.add (taylorCorrection_contDiffOn hC a n), ?_, ?_⟩
    · intro x hx
      have hj := qSolutionJet_taylorCorrection_time_jets hI hn.1 hC a n hx 0 (Nat.zero_le n)
      change qSolutionJet (fun p => taylorApproximation g a u0 u1 n p +
        taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p)
        ![x, a] = _
      have hj0 : qSolutionJet (fun p => taylorApproximation g a u0 u1 n p +
          taylorCorrection (nextTaylorCoefficient g a (taylorApproximation g a u0 u1 n) n) a n p)
          ![x, a] = qSolutionJet (taylorApproximation g a u0 u1 n) ![x, a] := by
        simpa only [iteratedDeriv_zero] using hj
      exact hj0.trans (hn.2.1 x hx)
    · exact nextTaylorCoefficient_cancels hg hU hI hn.1 a n hcut hxxn hn.2.2

end SmoothLocal.Taylor

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Taylor.taylorApproximation_properties := @OAI.SmoothLocal.Taylor.taylorApproximation_properties
