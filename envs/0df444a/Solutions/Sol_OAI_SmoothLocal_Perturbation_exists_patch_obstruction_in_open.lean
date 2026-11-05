-- Prove2me | solution 1 for OAI.SmoothLocal.Perturbation.exists_patch_obstruction_in_open
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:03:07.35391+00:00
-- url     : https://prove2.me/submissions/fe199751-761a-4afb-80df-8f4442ea959d

import Mathlib
import Definitions.Def_IsometricImmersion
import Definitions.Def_SmoothLocalIsometricSupport
import Theorems.Thm_OAI_SmoothLocal_Perturbation_exists_original_pulse_exclusion

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

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

theorem heightEnergy_contDiffOn {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (heightEnergy g z) U :=
  (metricDet_contDiffOn hg).mul (contDiffOn_const.sub (covectorNormSq_contDiffOn hg hU hz))

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

theorem metricMatrix_inverse_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t) (hdet : (G t).det ≠ 0)
    (i j : Fin 2) : ContinuousAt (fun s => (G s)⁻¹ i j) t := by
  have hdetc : ContinuousAt (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hi := hdetc.inv₀ hdet
  have ha : ContinuousAt (fun s => (G s).adjugate i j) t := by
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using hG 1 1
    · convert (hG 0 1).neg using 1
      funext s
      simp [Matrix.adjugate_fin_two]
    · convert (hG 1 0).neg using 1
      funext s
      simp [Matrix.adjugate_fin_two]
    · simpa [Matrix.adjugate_fin_two] using hG 0 0
  have hh : ContinuousAt (fun s => (G s).det⁻¹ * (G s).adjugate i j) t := hi.mul ha
  simpa [Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hh

theorem inverseDerivativeJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (d i j : Fin 2) :
    ContinuousAt (fun s => inverseDerivativeJet (G s) (D s) d i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  simp only [inverseDerivativeJet, Fin.sum_univ_two]
  fun_prop

theorem christoffelJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hdet : (G t).det ≠ 0) (k i j : Fin 2) :
    ContinuousAt (fun s => christoffelJet (G s) (D s) k i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  simp only [christoffelJet, Fin.sum_univ_two]
  fun_prop

theorem christoffelDerivativeJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (d k i j : Fin 2) :
    ContinuousAt (fun s => christoffelDerivativeJet (G s) (D s) (DD s) d k i j) t := by
  have hi := metricMatrix_inverse_continuousAt hG hdet
  have hdi := inverseDerivativeJet_continuousAt hG hD hdet
  simp only [christoffelDerivativeJet, Fin.sum_univ_two]
  fun_prop

theorem riemannJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) (l k i j : Fin 2) :
    ContinuousAt (fun s => riemannJet (G s) (D s) (DD s) l k i j) t := by
  have hΓ := christoffelJet_continuousAt hG hD hdet
  have hDΓ := christoffelDerivativeJet_continuousAt hG hD hDD hdet
  simp only [riemannJet, Fin.sum_univ_two]
  fun_prop

theorem curvatureJet_continuousAt
    (hG : ∀ i j, ContinuousAt (fun s => G s i j) t)
    (hD : ∀ d i j, ContinuousAt (fun s => D s d i j) t)
    (hDD : ∀ d e i j, ContinuousAt (fun s => DD s d e i j) t)
    (hdet : (G t).det ≠ 0) :
    ContinuousAt (fun s => curvatureJet (G s) (D s) (DD s)) t := by
  have hR := riemannJet_continuousAt hG hD hDD hdet
  have hn : ContinuousAt (fun s => ∑ l, G s 0 l * riemannJet (G s) (D s) (DD s) l 1 0 1) t := by
    simp only [Fin.sum_univ_two]
    fun_prop
  have hd : ContinuousAt (fun s => (G s).det) t := by
    simp only [Matrix.det_fin_two]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  exact hn.div hd hdet

end Continuity
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

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

theorem supportedTensor_eval_continuous (p : Coord) (i j : Fin 2) :
    Continuous (fun η : SupportedTensor => η p i j) := by
  have hjet : Continuous (fun η : SupportedTensor =>
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0 η p) :=
    (continuous_eval_const p).comp (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ 0).continuous
  have hval : Continuous (fun η : SupportedTensor => η p) := by
    have h := (continuousMultilinearCurryFin0 ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ)).continuous.comp hjet
    simp only [Function.comp_def, ContDiffMapSupportedIn.structureMapCLM_zero_apply,
      continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.uncurry0_apply] at h
    exact h
  exact (continuous_apply j).comp ((continuous_apply i).comp hval)

theorem symmetricSupportedSubmodule_isClosed :
    IsClosed (symmetricSupportedSubmodule : Set SupportedTensor) := by
  change IsClosed {η : SupportedTensor | ∀ p i j, η p i j = η p j i}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun p => isClosed_iInter (fun i => isClosed_iInter (fun j =>
    isClosed_eq (supportedTensor_eval_continuous p i j) (supportedTensor_eval_continuous p j i))))

theorem perturbationTensor_symmetric (η : SymmetricPerturbation) (p : Coord) (i j : Fin 2) :
    perturbationTensor η p i j = perturbationTensor η p j i := η.property p i j

theorem perturbationTensor_contDiff (η : SymmetricPerturbation) :
    ContDiff ℝ ∞ (perturbationTensor η) := η.val.contDiff

theorem perturbationTensor_coeff_contDiff (η : SymmetricPerturbation) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p => perturbationTensor η p i j) :=
  (contDiff_apply ℝ ℝ j).comp
    ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (perturbationTensor_contDiff η))

theorem perturbationTensor_zero_off_patch (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∉ patchBox) : perturbationTensor η p = 0 := η.val.zero_on_compl hp

def perturbationSeminorm (k : ℕ) (η : SymmetricPerturbation) : ℝ :=
  ContDiffMapSupportedIn.seminorm ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact k η.val

theorem perturbationSeminorm_continuous (k : ℕ) : Continuous (perturbationSeminorm k) :=
  ((ContDiffMapSupportedIn.withSeminorms ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ)
    ⊤ patchCompact).continuous_seminorm k).comp continuous_subtype_val

theorem perturbation_derivative_norm_le (η : SymmetricPerturbation) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (perturbationTensor η) p‖ ≤ perturbationSeminorm k η :=
  ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ

theorem supportedTensor_iteratedFDeriv_eval_continuous (k : ℕ) :
    Continuous (fun a : SupportedTensor × Coord => iteratedFDeriv ℝ k a.1 a.2) := by
  have h := ((ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k).continuous.comp
    (continuous_fst : Continuous (Prod.fst : SupportedTensor × Coord → SupportedTensor))).eval
      continuous_snd
  simpa only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply] using h

theorem patchBox_subset_modelSquare : patchBox ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

theorem perturbedMetric_smoothPositiveOn {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (η : SymmetricPerturbation)
    (hpos : ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef) :
    SmoothPositiveOn (perturbedMetric g0 η) U := by
  constructor
  · intro i j
    exact (hg0.1 i j).add (perturbationTensor_coeff_contDiff η i j).contDiffOn
  · intro p hp
    by_cases hP : p ∈ patchBox
    · exact hpos p (patchBox_subset_modelSquare hP)
    · simpa only [perturbedMetric, Pi.add_apply, perturbationTensor_zero_off_patch η hP,
        add_zero] using hg0.2 p hp

end SmoothLocal.Perturbation

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

def perturbationSeminormFamily : ℕ → Seminorm ℝ SymmetricPerturbation := fun k =>
  (ContDiffMapSupportedIn.seminorm ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact k).comp
    symmetricSupportedSubmodule.subtype

theorem symmetricPerturbation_withSeminorms : WithSeminorms perturbationSeminormFamily :=
  Topology.IsInducing.withSeminorms
    (ContDiffMapSupportedIn.withSeminorms ℝ Coord (Matrix (Fin 2) (Fin 2) ℝ) ⊤ patchCompact)
    (f := symmetricSupportedSubmodule.subtype) .subtypeVal

theorem exists_finite_seminorm_neighborhood {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O) :
    ∃ (s : Finset ℕ) (epsilon : ℝ), 0 < epsilon ∧
      ∀ ρ : SymmetricPerturbation,
        (∀ k ∈ s, perturbationSeminorm k ρ < epsilon) → η + ρ ∈ O := by
  obtain ⟨s, epsilon, heps, hsub⟩ :=
    (symmetricPerturbation_withSeminorms.mem_nhds_iff η O).mp (hO.mem_nhds hη)
  refine ⟨s, epsilon, heps, ?_⟩
  intro ρ hρ
  apply hsub
  rw [Seminorm.mem_ball]
  simpa only [add_sub_cancel_left] using
    Seminorm.finset_sup_apply_lt heps
      (show ∀ k ∈ s, perturbationSeminormFamily k ρ < epsilon from hρ)

theorem exists_ordered_seminorm_neighborhood {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O) :
    ∃ (N : ℕ) (epsilon : ℝ), 10 < N ∧ 0 < epsilon ∧
      ∀ ρ : SymmetricPerturbation,
        (∀ k < N, perturbationSeminorm k ρ < epsilon) → η + ρ ∈ O := by
  obtain ⟨s, epsilon, heps, hsub⟩ := exists_finite_seminorm_neighborhood hO hη
  let N : ℕ := max 11 (s.sup id + 1)
  have hN : 10 < N :=
    lt_of_lt_of_le (by norm_num : 10 < (11 : ℕ)) (le_max_left _ _)
  refine ⟨N, epsilon, hN, heps, ?_⟩
  intro ρ hρ
  apply hsub ρ
  intro k hk
  have hkSup : k ≤ s.sup id := by
    simpa only [id_eq] using (Finset.le_sup (f := id) hk)
  exact hρ k (lt_of_lt_of_le (Nat.lt_succ_of_le hkSup) (le_max_right _ _))

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

theorem inverse_shear (q0 : ℝ) (p : Coord) :
    inverseShearCoordinates q0 (shearCoordinates q0 p) = p := by
  ext i
  fin_cases i <;> simp [shearCoordinates, inverseShearCoordinates]

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

theorem pulseOriginalBox_subset_patchBox {q0 a delta tau : ℝ}
    (ha : a ≤ 1 / 10) (hy : delta / (2 * tau) + |q0| * a ≤ 1 / 10) :
    pulseOriginalBox q0 a delta tau ⊆ patchBox := by
  rintro p ⟨u, hu, rfl⟩
  have hu0 : |u 0| ≤ a := abs_le.mpr ⟨hu.1 0, hu.2 0⟩
  have hu1 : |u 1| ≤ delta / (2 * tau) := abs_le.mpr ⟨hu.1 1, hu.2 1⟩
  have h0 : |inverseShearCoordinates q0 u 0| ≤ 1 / 10 := hu0.trans ha
  have h1 : |inverseShearCoordinates q0 u 1| ≤ 1 / 10 := by
    change |u 1 - q0 * u 0| ≤ _
    calc
      _ ≤ |u 1| + |q0 * u 0| := abs_sub _ _
      _ = |u 1| + |q0| * |u 0| := by rw [abs_mul]
      _ ≤ delta / (2 * tau) + |q0| * a :=
        add_le_add hu1 (mul_le_mul_of_nonneg_left hu0 (abs_nonneg q0))
      _ ≤ _ := hy
  constructor <;> intro i <;> fin_cases i
  · exact (abs_le.mp h0).1
  · exact (abs_le.mp h1).1
  · exact (abs_le.mp h0).2
  · exact (abs_le.mp h1).2

def supportedPulse (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau)
    (hax : a ≤ 1 / 10) (hay : delta / (2 * tau) + |q0| * a ≤ 1 / 10) :
    SymmetricPerturbation := by
  let f : SupportedTensor := ⟨pulseTensor q0 a N delta tau,
    pulseTensor_contDiff q0 a N delta tau, by
      intro p hp
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => hp (pulseOriginalBox_subset_patchBox hax hay
        (pulseTensor_tsupport_subset ha hd ht N h))⟩
  exact ⟨f, pulseTensor_symmetric q0 a N delta tau⟩

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

theorem supportedTensor_coeff_iteratedFDeriv (η : SupportedTensor) (k : ℕ)
    (p : Coord) (v : Fin k → Coord) (i j : Fin 2) :
    iteratedFDeriv ℝ k (fun q => η q i j) p v = (iteratedFDeriv ℝ k η p v) i j := by
  change iteratedFDeriv ℝ k (metricCoefficientCLM i j ∘ η) p v =
    metricCoefficientCLM i j (iteratedFDeriv ℝ k η p v)
  have he := (metricCoefficientCLM i j).iteratedFDeriv_comp_left (x := p) (i := k)
    η.contDiff.contDiffAt (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k))
  exact congrArg (fun L : Coord [×k]→L[ℝ] ℝ => L v) he

theorem supportedTensor_coordPartial_eq_jet (η : SupportedTensor)
    (p : Coord) (d i j : Fin 2) :
    coordPartial d (fun q => η q i j) p =
      (iteratedFDeriv ℝ 1 η p (fun _ => Pi.single d 1)) i j := by
  rw [← supportedTensor_coeff_iteratedFDeriv]
  simp only [iteratedFDeriv_one_apply, coordPartial]

theorem supportedTensor_second_coordPartial_eq_jet (η : SupportedTensor)
    (p : Coord) (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => η q i j)) p =
      (iteratedFDeriv ℝ 2 η p ![Pi.single d 1, Pi.single e 1]) i j := by
  have hs : ContDiff ℝ ∞ (fun q => η q i j) :=
    (metricCoefficientCLM i j).contDiff.comp η.contDiff
  rw [← supportedTensor_coeff_iteratedFDeriv, iteratedFDeriv_two_apply,
    second_coordPartial_eq_fderiv hs.contDiffOn isOpen_univ (mem_univ p)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem supportedTensor_coeff_eval_joint_continuous (i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord => a.1 a.2 i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_eval)

theorem supportedTensor_coordPartial_joint_continuous (d i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord =>
      coordPartial d (fun q => a.1 q i j) a.2) := by
  have hc := (supportedTensor_iteratedFDeriv_eval_continuous 1).eval
    (continuous_const (y := ((fun _ : Fin 1 => Pi.single d (1 : ℝ)) : Fin 1 → Coord)))
  have he := (continuous_apply j).comp ((continuous_apply i).comp hc)
  simp only [supportedTensor_coordPartial_eq_jet]
  exact he

theorem supportedTensor_second_coordPartial_joint_continuous (d e i j : Fin 2) :
    Continuous (fun a : SupportedTensor × Coord =>
      coordPartial d (coordPartial e (fun q => a.1 q i j)) a.2) := by
  have hc := (supportedTensor_iteratedFDeriv_eval_continuous 2).eval
    (continuous_const (y := (![Pi.single d 1, Pi.single e 1] : Fin 2 → Coord)))
  have he := (continuous_apply j).comp ((continuous_apply i).comp hc)
  simp only [supportedTensor_second_coordPartial_eq_jet]
  exact he

theorem perturbationTensor_coeff_eval_joint_continuous (i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord => perturbationTensor a.1 a.2 i j) :=
  (supportedTensor_coeff_eval_joint_continuous i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbationTensor_coordPartial_joint_continuous (d i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (fun q => perturbationTensor a.1 q i j) a.2) :=
  (supportedTensor_coordPartial_joint_continuous d i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbationTensor_second_coordPartial_joint_continuous (d e i j : Fin 2) :
    Continuous (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (coordPartial e (fun q => perturbationTensor a.1 q i j)) a.2) :=
  (supportedTensor_second_coordPartial_joint_continuous d e i j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem perturbedMetric_coordPartial {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) (d i j : Fin 2) :
    coordPartial d (fun q => perturbedMetric g0 η q i j) p =
      coordPartial d (fun q => g0 q i j) p +
        coordPartial d (fun q => perturbationTensor η q i j) p := by
  apply HessianCalculus.coordPartial_add_at
  · exact (((hg0.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  · exact (perturbationTensor_coeff_contDiff η i j).differentiable (by simp) p

theorem perturbedMetric_second_coordPartial {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) (d e i j : Fin 2) :
    coordPartial d (coordPartial e (fun q => perturbedMetric g0 η q i j)) p =
      coordPartial d (coordPartial e (fun q => g0 q i j)) p +
        coordPartial d (coordPartial e (fun q => perturbationTensor η q i j)) p := by
  have heq : coordPartial e (fun q => perturbedMetric g0 η q i j) =ᶠ[𝓝 p]
      (fun q => coordPartial e (fun q => g0 q i j) q +
        coordPartial e (fun q => perturbationTensor η q i j) q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact perturbedMetric_coordPartial hg0 hU η hq e i j
  change fderiv ℝ _ p (Pi.single d 1) = _
  rw [heq.fderiv_eq]
  apply HessianCalculus.coordPartial_add_at
  · exact (((partial_contDiffOn (hg0.1 i j) hU e) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  · exact (((partial_contDiffOn (perturbationTensor_coeff_contDiff η i j).contDiffOn
      isOpen_univ e) p (mem_univ p)).contDiffAt (by simp)).differentiableAt (by simp)

section JointMetric
variable {g0 : MetricField} {U : Set Coord}
variable (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
variable {η : SymmetricPerturbation} {p : Coord} (hp : p ∈ U)
include hg0 hU hp

theorem perturbedMetric_coeff_joint_continuousAt (i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord => perturbedMetric g0 a.1 a.2 i j)
      (η, p) := by
  have hbg := (((hg0.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).continuousAt
  exact (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_coeff_eval_joint_continuous i j).continuousAt

theorem perturbedMetric_coordPartial_joint_continuousAt (d i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (fun q => perturbedMetric g0 a.1 q i j) a.2) (η, p) := by
  have hbg := (((partial_contDiffOn (hg0.1 i j) hU d) p hp).contDiffAt
    (hU.mem_nhds hp)).continuousAt
  have hc := (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_coordPartial_joint_continuous d i j).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with a ha
  exact perturbedMetric_coordPartial hg0 hU a.1 ha d i j

theorem perturbedMetric_second_coordPartial_joint_continuousAt (d e i j : Fin 2) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord =>
      coordPartial d (coordPartial e (fun q => perturbedMetric g0 a.1 q i j)) a.2) (η, p) := by
  have hbg := (((partial_contDiffOn (partial_contDiffOn (hg0.1 i j) hU e) hU d)
    p hp).contDiffAt (hU.mem_nhds hp)).continuousAt
  have hc := (hbg.comp (x := (η, p)) continuous_snd.continuousAt).add
    (perturbationTensor_second_coordPartial_joint_continuous d e i j).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with a ha
  exact perturbedMetric_second_coordPartial hg0 hU a.1 ha d e i j

end JointMetric

def perturbedCurvatureJet (g0 : MetricField) (η : SymmetricPerturbation) (p : Coord) : ℝ :=
  curvatureJet (perturbedMetric g0 η p)
    (fun d i j => coordPartial d (fun q => perturbedMetric g0 η q i j) p)
    (fun d e i j => coordPartial d (coordPartial e (fun q => perturbedMetric g0 η q i j)) p)

theorem perturbedCurvatureJet_joint_continuousAt {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) {η : SymmetricPerturbation}
    {p : Coord} (hp : p ∈ U) (hdet : (perturbedMetric g0 η p).det ≠ 0) :
    ContinuousAt (fun a : SymmetricPerturbation × Coord => perturbedCurvatureJet g0 a.1 a.2)
      (η, p) :=
  curvatureJet_continuousAt (perturbedMetric_coeff_joint_continuousAt hg0 hU hp)
    (perturbedMetric_coordPartial_joint_continuousAt hg0 hU hp)
    (perturbedMetric_second_coordPartial_joint_continuousAt hg0 hU hp) hdet

theorem gaussianCurvature_perturbedMetric_eq_jet {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (η : SymmetricPerturbation)
    (hpos : ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef)
    {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (perturbedMetric g0 η) p = perturbedCurvatureJet g0 η p :=
  gaussianCurvature_eq_curvatureJet (perturbedMetric_smoothPositiveOn hg0 η hpos) hU hp

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace
open scoped BoundedContinuousFunction

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

abbrev SupportedJetProduct (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  Π k : ℕ, Coord →ᵇ (Coord [×k]→L[ℝ] V)

def supportedJetMap (K : Compacts Coord) :
    ContDiffMapSupportedIn Coord V ⊤ K →L[ℝ] SupportedJetProduct V :=
  ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤)

omit [CompleteSpace V] in
theorem supportedJetMap_isUniformEmbedding (K : Compacts Coord) :
    IsUniformEmbedding (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V) :=
  ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM (𝕜 := ℝ) (n := ⊤)

set_option synthInstance.maxHeartbeats 400000 in
omit [CompleteSpace V] in
theorem supportedJetMap_isClosed_range (K : Compacts Coord) :
    IsClosed (Set.range (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu ht
  choose f hf using hu
  have hfconv : Tendsto (fun n => supportedJetMap K (f n)) atTop (𝓝 v) := by
    simpa only [hf] using ht
  have hconv (k : ℕ) : TendstoUniformly
      (fun n => iteratedFDeriv ℝ k (f n)) (v k) atTop := by
    have hcoord := ((continuous_apply k).tendsto v).comp hfconv
    change Tendsto (fun n => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (f n))
      atTop (𝓝 (v k)) at hcoord
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hcoord
    simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using h
  let C (k : ℕ) :=
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Coord) V
  have hderivative (k : ℕ) (x : Coord) :
      HasFDerivAt (fun y => v k y) (C k (v (k + 1) x)) x := by
    have hnext : TendstoUniformly
        (fun n => C k ∘ iteratedFDeriv ℝ (k + 1) (f n)) (C k ∘ v (k + 1)) atTop :=
      (C k).isometry.uniformContinuous.comp_tendstoUniformly (hconv (k + 1))
    have hfn (n : ℕ) (y : Coord) : HasFDerivAt (iteratedFDeriv ℝ k (f n))
        (C k (iteratedFDeriv ℝ (k + 1) (f n) y)) y := by
      have hs : ContDiff ℝ ∞ (f n) := (f n).contDiff
      have hd := ((hs.contDiffAt (x := y)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).hasFDerivAt
      simpa only [fderiv_iteratedFDeriv, Function.comp_apply, C] using hd
    exact hasFDerivAt_of_tendstoUniformly hnext hfn (fun y => (hconv k).tendsto_at y) x
  let C0 := continuousMultilinearCurryFin0 ℝ Coord V
  let g : Coord → V := fun x => C0 (v 0 x)
  have hjet : ∀ k : ℕ, iteratedFDeriv ℝ k g = (v k : Coord → Coord [×k]→L[ℝ] V) := by
    intro k
    induction k with
    | zero =>
        funext x
        change C0.symm (C0 (v 0 x)) = v 0 x
        exact C0.symm_apply_apply _
    | succ k ih =>
        rw [iteratedFDeriv_succ_eq_comp_left, ih]
        funext x
        change (C k).symm (fderiv ℝ (fun y => v k y) x) = v (k + 1) x
        rw [(hderivative k x).fderiv]
        exact (C k).symm_apply_apply _
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_continuous_differentiable.mpr
    constructor
    · intro k _
      rw [hjet k]
      exact (v k).continuous
    · intro k _
      rw [hjet k]
      exact fun x => (hderivative k x).differentiableAt
  have hzero : EqOn g 0 (K : Set Coord)ᶜ := by
    intro x hx
    have hlim := (hconv 0).tendsto_at x
    have hconst : Tendsto (fun n => iteratedFDeriv ℝ 0 (f n) x) atTop (𝓝 0) := by
      have hz (n : ℕ) : iteratedFDeriv ℝ 0 (f n) x = 0 :=
        (f n).iteratedFDeriv_zero_on_compl hx
      simpa only [hz] using (tendsto_const_nhds (x := (0 : Coord [×0]→L[ℝ] V)))
    have hvzero : v 0 x = 0 := tendsto_nhds_unique hlim hconst
    change C0 (v 0 x) = 0
    rw [hvzero, map_zero]
  let φ : ContDiffMapSupportedIn Coord V ⊤ K := ⟨g, hg, hzero⟩
  refine ⟨φ, ?_⟩
  funext k
  apply BoundedContinuousFunction.ext
  intro x
  change ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k φ x = v k x
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact congrFun (hjet k) x

theorem supportedSmooth_completelyMetrizable (K : Compacts Coord) :
    IsCompletelyMetrizableSpace (ContDiffMapSupportedIn Coord V ⊤ K) := by
  have (k : ℕ) : IsCompletelyMetrizableSpace (Coord →ᵇ (Coord [×k]→L[ℝ] V)) := by
    have hc : CompleteSpace (Coord →ᵇ (Coord [×k]→L[ℝ] V)) := inferInstance
    refine ⟨⟨inferInstance, ?_, ?_⟩⟩
    · rfl
    · exact hc
  have : IsCompletelyMetrizableSpace (SupportedJetProduct V) := inferInstance
  have he : Topology.IsClosedEmbedding (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V) :=
    ⟨(supportedJetMap_isUniformEmbedding K).isEmbedding, supportedJetMap_isClosed_range K⟩
  exact he.IsCompletelyMetrizableSpace

theorem symmetricPerturbation_completelyMetrizable :
    IsCompletelyMetrizableSpace SymmetricPerturbation := by
  let : IsCompletelyMetrizableSpace SupportedTensor := supportedSmooth_completelyMetrizable patchCompact
  exact symmetricSupportedSubmodule_isClosed.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace

theorem symmetricPerturbation_baire : BaireSpace SymmetricPerturbation := by
  let : IsCompletelyMetrizableSpace SymmetricPerturbation := symmetricPerturbation_completelyMetrizable
  infer_instance

end SmoothLocal.Perturbation

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

theorem perturbationTensor_isHermitian (η : SymmetricPerturbation) (p : Coord) :
    (perturbationTensor η p).IsHermitian := by
  change (perturbationTensor η p)ᴴ = perturbationTensor η p
  ext i j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using
    perturbationTensor_symmetric η p j i

theorem perturbedMetric_isHermitian {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (η : SymmetricPerturbation)
    {p : Coord} (hp : p ∈ U) : (perturbedMetric g0 η p).IsHermitian :=
  (hg0.2 p hp).isHermitian.add (perturbationTensor_isHermitian η p)

def metricPositiveSet (g0 : MetricField) : Set SymmetricPerturbation :=
  {η | ∀ p ∈ modelSquare, (perturbedMetric g0 η p).PosDef}

theorem metricPositiveSet_mem_nhds {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {η : SymmetricPerturbation} (hη : η ∈ metricPositiveSet g0) :
    metricPositiveSet g0 ∈ 𝓝 η := by
  have hcompact : IsCompact (modelSquare ×ˢ Metric.sphere (0 : Coord) 1) :=
    modelSquare_isCompact.prod (isCompact_sphere (0 : Coord) 1)
  have hgood : ∀ᶠ θ in 𝓝 η, ∀ pv ∈ modelSquare ×ˢ Metric.sphere (0 : Coord) 1,
      0 < metricQuadraticValue (perturbedMetric g0 θ pv.1) pv.2 := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro pv hpv
    have hm : Continuous (fun a : SymmetricPerturbation × (Coord × Coord) => (a.1, a.2.1)) :=
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    have hcoeff (i j : Fin 2) : ContinuousAt
        (fun a : SymmetricPerturbation × (Coord × Coord) => perturbedMetric g0 a.1 a.2.1 i j)
        (η, pv) := by
      have hb : ContinuousAt
          (fun a : SymmetricPerturbation × Coord => perturbedMetric g0 a.1 a.2 i j) (η, pv.1) :=
        perturbedMetric_coeff_joint_continuousAt (η := η) hg0 hU (hSU hpv.1) i j
      have hh := hb.comp (x := (η, pv)) hm.continuousAt
      convert hh using 1 <;> try with_reducible_and_instances rfl
      rfl
    have hv (i : Fin 2) : ContinuousAt
        (fun a : SymmetricPerturbation × (Coord × Coord) => a.2.2 i) (η, pv) := by fun_prop
    have hc := metricQuadraticValue_continuousAt hcoeff hv
    have hvne : pv.2 ≠ 0 := by
      intro hz
      have hn : ‖pv.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hpv.2
      simp only [hz, norm_zero] at hn
      norm_num at hn
    have hq : 0 < metricQuadraticValue (perturbedMetric g0 η pv.1) pv.2 := by
      simpa only [metricQuadraticValue, star_trivial] using (hη pv.1 hpv.1).dotProduct_mulVec_pos hvne
    exact continuousAt_const.eventually_lt hc hq
  filter_upwards [hgood] with θ hθ
  intro p hp
  exact posDef_of_positive_on_sphere (perturbedMetric_isHermitian hg0 θ (hSU hp))
    (fun v hv => hθ (p, v) ⟨hp, hv⟩)

theorem centralBox_subset_modelSquare : centralBox ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> linarith [hp.1 i, hp.2 i]

theorem centralCurvatureJet_eventually {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {kappa : ℝ} {η : SymmetricPerturbation}
    (hpos : η ∈ metricPositiveSet g0)
    (hK : ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 η) p < -kappa / 2) :
    ∀ᶠ θ in 𝓝 η, ∀ p ∈ centralBox, perturbedCurvatureJet g0 θ p < -kappa / 2 := by
  have hc : IsCompact centralBox := isCompact_Icc
  apply hc.eventually_forall_of_forall_eventually
  intro p hp
  have hpU := hSU (centralBox_subset_modelSquare hp)
  have hpd : (perturbedMetric g0 η p).PosDef := hpos p (centralBox_subset_modelSquare hp)
  have hd : (perturbedMetric g0 η p).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit).ne_zero
  have hcont := perturbedCurvatureJet_joint_continuousAt hg0 hU hpU hd
  have hval : perturbedCurvatureJet g0 η p < -kappa / 2 := by
    rw [← gaussianCurvature_perturbedMetric_eq_jet hg0 hU η hpos hpU]
    exact hK p hp
  exact hcont.eventually_lt continuousAt_const hval

theorem metricPatchSet_isOpen {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (kappa : ℝ) :
    IsOpen (metricPatchSet g0 kappa) := by
  apply isOpen_iff_mem_nhds.mpr
  intro η hη
  have hpos : η ∈ metricPositiveSet g0 := hη.1
  filter_upwards [metricPositiveSet_mem_nhds hg0 hU hSU hpos,
    centralCurvatureJet_eventually hg0 hU hSU hpos hη.2] with θ hθpos hθK
  refine ⟨hθpos, ?_⟩
  intro p hp
  rw [gaussianCurvature_perturbedMetric_eq_jet hg0 hU θ hθpos
    (hSU (centralBox_subset_modelSquare hp))]
  exact hθK p hp

theorem metricPatchSet_baire {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (kappa : ℝ) :
    BaireSpace (metricPatchSet g0 kappa) := by
  let : BaireSpace SymmetricPerturbation := symmetricPerturbation_baire
  exact (metricPatchSet_isOpen hg0 hU hSU kappa).baireSpace

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

theorem pulseDerivativeBound_nonneg (q0 a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) :
    0 ≤ pulseDerivativeBound q0 a ha delta k :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (pulseCoreDerivativeBound_nonneg ha k))
    (pow_nonneg (pulseScaleBound_pos q0 delta).le k)

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

theorem supportedPulse_seminorm_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    (hd : 0 < delta) {tau : ℝ} (ht : 1 ≤ tau)
    (hax : a ≤ 1 / 10) (hay : delta / (2 * tau) + |q0| * a ≤ 1 / 10) (k : ℕ) :
    perturbationSeminorm k
        (supportedPulse q0 a N delta tau ha hd (lt_of_lt_of_le zero_lt_one ht) hax hay) ≤
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N := by
  have ht0 : 0 ≤ tau := le_trans zero_le_one ht
  have hC : 0 ≤ pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N :=
    div_nonneg (mul_nonneg (pulseDerivativeBound_nonneg q0 a ha delta k) (pow_nonneg ht0 k))
      (pow_nonneg ht0 N)
  unfold perturbationSeminorm
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hC k _).mpr
  intro p hp
  exact pulseTensor_derivative_le q0 a ha N delta ht k p

end SmoothLocal.Pulse

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

@[simp] theorem perturbationSeminorm_zero (k : ℕ) :
    perturbationSeminorm k 0 = 0 := map_zero (perturbationSeminormFamily k)

theorem closure_exists_finite_seminorm_approximation
    {T : Type*} [TopologicalSpace T] (f : T → SymmetricPerturbation) (hf : Continuous f)
    {A : Set T} {theta : T} (hclosure : theta ∈ closure A)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta ∈ A, ∀ k ≤ n, perturbationSeminorm k (f eta - f theta) < epsilon := by
  let O : Set T := {eta | ∀ k : Fin (n + 1),
    perturbationSeminorm k.val (f eta - f theta) < epsilon}
  have hO : IsOpen O := by
    change IsOpen {eta | ∀ k : Fin (n + 1),
      perturbationSeminorm k.val (f eta - f theta) < epsilon}
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_lt ((perturbationSeminorm_continuous k.val).comp
      (hf.sub continuous_const)) continuous_const
  have htheta : theta ∈ O := by
    intro k
    simpa only [sub_self, perturbationSeminorm_zero] using hepsilon
  obtain ⟨eta, hetaO, hetaA⟩ := mem_closure_iff.mp hclosure O hO htheta
  refine ⟨eta, hetaA, ?_⟩
  intro k hk
  exact hetaO ⟨k, by omega⟩

theorem perturbation_coefficient_derivative_norm_le
    (eta : SymmetricPerturbation) (k : ℕ) (p : Coord) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ k (fun x => perturbationTensor eta x i j) p‖ ≤
      perturbationSeminorm k eta := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    ((norm_nonneg _).trans (perturbation_derivative_norm_le eta k p))
  intro v
  change ‖iteratedFDeriv ℝ k (fun x => eta.val x i j) p v‖ ≤ _
  rw [supportedTensor_coeff_iteratedFDeriv]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k eta.val p v‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ ‖iteratedFDeriv ℝ k eta.val p‖ * ∏ l, ‖v l‖ :=
      (iteratedFDeriv ℝ k eta.val p).le_opNorm v
    _ ≤ perturbationSeminorm k eta * ∏ l, ‖v l‖ :=
      mul_le_mul_of_nonneg_right (perturbation_derivative_norm_le eta k p)
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))

theorem perturbedMetric_sub_eq_tensor_sub (g0 : MetricField) (eta theta : SymmetricPerturbation) :
    (fun p => perturbedMetric g0 eta p - perturbedMetric g0 theta p) =
      perturbationTensor (eta - theta) := by
  funext p
  ext i j
  change (g0 p i j + perturbationTensor eta p i j) -
    (g0 p i j + perturbationTensor theta p i j) =
      perturbationTensor eta p i j - perturbationTensor theta p i j
  ring

theorem perturbedMetric_coefficient_sub_eq (g0 : MetricField)
    (eta theta : SymmetricPerturbation) (i j : Fin 2) :
    (fun p => perturbedMetric g0 eta p i j - perturbedMetric g0 theta p i j) =
      (fun p => perturbationTensor (eta - theta) p i j) := by
  funext p
  exact congrFun (congrFun (congrFun (perturbedMetric_sub_eq_tensor_sub g0 eta theta) p) i) j

theorem closure_exists_metric_jet_approximation
    {T : Type*} [TopologicalSpace T] (f : T → SymmetricPerturbation) (hf : Continuous f)
    (g0 : MetricField) {A : Set T} {theta : T} (hclosure : theta ∈ closure A)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta ∈ A,
      (∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (f eta) x -
          perturbedMetric g0 (f theta) x) p‖ ≤ epsilon) ∧
      (∀ i j : Fin 2, ∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (f eta) x i j -
          perturbedMetric g0 (f theta) x i j) p‖ ≤ epsilon) := by
  obtain ⟨eta, heta, hsmall⟩ := closure_exists_finite_seminorm_approximation f hf hclosure n hepsilon
  refine ⟨eta, heta, ?_, ?_⟩
  · intro k hk p
    rw [perturbedMetric_sub_eq_tensor_sub]
    exact (perturbation_derivative_norm_le (f eta - f theta) k p).trans (hsmall k hk).le
  · intro i j k hk p
    rw [perturbedMetric_coefficient_sub_eq]
    exact (perturbation_coefficient_derivative_norm_le (f eta - f theta) k p i j).trans (hsmall k hk).le

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

theorem pulse_support_eventually (q0 a delta : ℝ) (hq : |q0| * a < 1 / 10) :
    ∀ᶠ tau : ℝ in atTop, delta / (2 * tau) + |q0| * a < 1 / 10 := by
  have h : Tendsto (fun tau : ℝ => delta / (2 * tau) + |q0| * a)
      atTop (𝓝 (|q0| * a)) := by
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0))
    simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
      (hi.const_mul (delta / 2)).add_const (|q0| * a)
  exact h.eventually_lt tendsto_const_nhds hq

theorem pulse_finite_derivative_bounds_eventually (q0 a : ℝ) (ha : 0 < a)
    (delta : ℝ) (N : ℕ) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∀ᶠ tau : ℝ in atTop, ∀ k ∈ Finset.range N,
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N < epsilon := by
  apply (Finset.range N).eventually_all.mpr
  intro k hk
  exact (fixed_order_pulse_bound_tendsto_zero q0 a ha delta N k (Finset.mem_range.mp hk)).eventually_lt
    tendsto_const_nhds heps

theorem exists_N_before_delta_eventually_mem {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧
        ∃ ρ : SymmetricPerturbation,
          perturbationTensor ρ = pulseTensor q0 a N delta tau ∧ η + ρ ∈ O := by
  obtain ⟨N, epsilon, hN, heps, hball⟩ := exists_ordered_seminorm_neighborhood hO hη
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [eventually_ge_atTop (1 : ℝ), pulse_support_eventually q0 a delta hq,
    pulse_finite_derivative_bounds_eventually q0 a ha delta N heps] with tau ht hshape hsmall
  let ρ : SymmetricPerturbation :=
    supportedPulse q0 a N delta tau ha hd (lt_of_lt_of_le zero_lt_one ht) hax hshape.le
  refine ⟨ht, ρ, rfl, hball ρ ?_⟩
  intro k hk
  exact (supportedPulse_seminorm_le q0 a ha N delta hd ht hax hshape.le k).trans_lt
    (hsmall k (Finset.mem_range.mpr hk))

theorem exists_N_before_delta_eventually_testMetric (g0 : MetricField)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧
        ∃ θ ∈ O, perturbedMetric g0 θ = testMetric (perturbedMetric g0 η) q0 a N delta tau := by
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_mem hO hη q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨ρ, hρ, hOρ⟩ := ht.2
  refine ⟨ht.1, η + ρ, hOρ, ?_⟩
  ext p i j
  change g0 p i j + (perturbationTensor η p i j + perturbationTensor ρ p i j) =
    (g0 p i j + perturbationTensor η p i j) + pulseTensor q0 a N delta tau p i j
  rw [hρ]
  ring

end SmoothLocal.Pulse

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem exists_N_before_delta_eventually_integer_testMetric (g0 : MetricField)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ ∈ O, perturbedMetric g0 θ =
          testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ) := by
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_testMetric g0 hO hη q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (hmem delta hd)

theorem exists_N_before_delta_eventually_positive_testMetric
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation}
    (hη : η ∈ O) (hηmetric : η ∈ metricPatchSet g0 kappa)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ : SymmetricPerturbation, θ ∈ O ∧ θ ∈ metricPatchSet g0 kappa ∧
          perturbedMetric g0 θ = testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ) ∧
          SmoothPositiveOn (testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ)) U ∧
          ∀ p ∈ centralBox,
            gaussianCurvature (testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ)) p < -kappa/2 := by
  have hOmetric : IsOpen (O ∩ metricPatchSet g0 kappa) :=
    hO.inter (metricPatchSet_isOpen hg0 hU hSU kappa)
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_integer_testMetric g0
    hOmetric ⟨hη, hηmetric⟩ q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨θ, hθ, heq⟩ := ht.2
  have hpositive : SmoothPositiveOn (perturbedMetric g0 θ) U :=
    perturbedMetric_smoothPositiveOn hg0 θ hθ.2.1
  have hcentral : ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 θ) p < -kappa/2 := hθ.2.2
  refine ⟨ht.1, θ, hθ.1, hθ.2, heq, ?_, ?_⟩
  · rwa [← heq]
  · rwa [← heq]

theorem exists_N_before_delta_eventually_relative_metric_neighborhood
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {η : metricPatchSet g0 kappa} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ : metricPatchSet g0 kappa, θ ∈ O ∧
          perturbedMetric g0 θ.val = testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ) ∧
          SmoothPositiveOn (testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ)) U ∧
          ∀ p ∈ centralBox,
            gaussianCurvature (testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ)) p < -kappa/2 := by
  have hOa : IsOpen (Subtype.val '' O : Set SymmetricPerturbation) :=
    (metricPatchSet_isOpen hg0 hU hSU kappa).isOpenMap_subtype_val O hO
  have hηa : η.val ∈ (Subtype.val '' O : Set SymmetricPerturbation) := ⟨η, hη, rfl⟩
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_positive_testMetric hg0 hU hSU
    hOa hηa η.property q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨θ, hθO, hθmetric, heq, hpositive, hcentral⟩ := ht.2
  obtain ⟨θ', hθ', hvalue⟩ := hθO
  refine ⟨ht.1, θ', hθ', ?_, hpositive, hcentral⟩
  simpa only [hvalue] using heq

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

theorem relative_closure_exists_metric_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U)
    {A : Set (metricPatchSet g0 kappa)} {theta : metricPatchSet g0 kappa}
    (hclosure : theta ∈ closure A) (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : metricPatchSet g0 kappa, eta ∈ A ∧
      SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
      (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa / 2) ∧
      (∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
          perturbedMetric g0 theta.val x) p‖ ≤ epsilon) ∧
      (∀ i j : Fin 2, ∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
          perturbedMetric g0 theta.val x i j) p‖ ≤ epsilon) := by
  obtain ⟨eta, heta, hT, hC⟩ := closure_exists_metric_jet_approximation
    (Subtype.val : metricPatchSet g0 kappa → SymmetricPerturbation) continuous_subtype_val
    g0 hclosure n hepsilon
  exact ⟨eta, heta, perturbedMetric_smoothPositiveOn hg0 eta.val eta.property.1,
    eta.property.2, hT, hC⟩

theorem exists_N_before_delta_eventually_class_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {A O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure A)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ eta : metricPatchSet g0 kappa, eta ∈ A ∧
          SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
          (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa / 2) ∧
          (∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
              testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x) p‖ ≤
                metricApproximationAccuracy tau) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
              testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x i j) p‖ ≤
                metricApproximationAccuracy tau) := by
  obtain ⟨N, hN, hpulse⟩ := exists_N_before_delta_eventually_relative_metric_neighborhood
    hg0 hU hSU hO hStar q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hdelta
  filter_upwards [hpulse delta hdelta] with tau htau
  have hpositive : 0 < tau := by
    have hh : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htau.1
    exact_mod_cast hh
  obtain ⟨theta, hthetaO, hthetaEq, hthetaPositive, hthetaCentral⟩ := htau.2
  obtain ⟨eta, heta, hmetric, hcentral, hT, hC⟩ :=
    relative_closure_exists_metric_approximation hg0 (hOclosure hthetaO) tau
      (metricApproximationAccuracy_pos hpositive)
  refine ⟨hpositive, eta, heta, hmetric, hcentral, ?_, ?_⟩
  · simpa only [hthetaEq] using hT
  · simpa only [hthetaEq] using hC

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
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.HighEquation

theorem PatchAdmissibleHeight.exists_integer_bound {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) : ∃ M : ℕ, BoundedAdmissibleHeight g M z := by
  have horiginal := h
  obtain ⟨U, hU, hSU, hg, hz, _, hE, hyy, _⟩ := h
  obtain ⟨Z, _, hzB⟩ := compact_finite_fullJet_bound hz hU modelSquare_isCompact hSU 8
  have hHcont : ContinuousOn (fun p => covHessian g z p 1 1) modelSquare :=
    (covHessian_contDiffOn hg hU hz 1 1).continuousOn.mono hSU
  obtain ⟨H, hH⟩ := modelSquare_isCompact.exists_bound_of_continuousOn hHcont
  obtain ⟨c, hc, hcfloor⟩ := modelSquare_isCompact.exists_forall_le'
    hHcont.abs (fun p hp => abs_pos.mpr (hyy p hp))
  obtain ⟨e, he, hefloor⟩ := modelSquare_isCompact.exists_forall_le'
    ((heightEnergy_contDiffOn hg hU hz).continuousOn.mono hSU) hE
  let B := max 1 (max Z (max H (max (1 / c) (1 / e))))
  obtain ⟨M, hM⟩ := exists_nat_ge B
  have hMone : (1 : ℝ) ≤ (M : ℝ) := (le_max_left _ _).trans hM
  have hMposR : (0 : ℝ) < (M : ℝ) := zero_lt_one.trans_le hMone
  have hMpos : 0 < M := Nat.cast_pos.mp hMposR
  have hZM : Z ≤ (M : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hM
  have hHM : H ≤ (M : ℝ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hM
  have hcM : 1 / c ≤ (M : ℝ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans hM
  have heM : 1 / e ≤ (M : ℝ) :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans hM
  have hMc : 1 / (M : ℝ) ≤ c := (one_div_le hMposR hc).mpr hcM
  have hMe : 1 / (M : ℝ) ≤ e := (one_div_le hMposR he).mpr heM
  refine ⟨M, hMpos, horiginal, ?_, ?_, ?_⟩
  · intro k hk p hp
    exact (hzB k hk p hp).trans hZM
  · intro p hp
    refine ⟨hMc.trans (hcfloor p hp), ?_⟩
    have hh : |covHessian g z p 1 1| ≤ H := by
      simpa only [Real.norm_eq_abs] using hH p hp
    exact hh.trans hHM
  · intro p hp
    exact hMe.trans (hefloor p hp)

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

theorem exists_rational_bounded_class_label (kappa : ℝ) (M : ℕ) (q : ℝ) :
    ∃ q0 : ℚ, |q - (q0 : ℝ)| < 1 / (100 * boundedClassWidth kappa M) := by
  let epsilon := 1 / (100 * boundedClassWidth kappa M)
  have hepsilon : 0 < epsilon := one_div_pos.mpr
    (mul_pos (by norm_num) (boundedClassWidth_pos kappa M))
  obtain ⟨q0, hlower, hupper⟩ := exists_rat_btwn
    (show q - epsilon < q + epsilon by linarith)
  refine ⟨q0, abs_lt.mpr ⟨?_, ?_⟩⟩ <;> linarith

def boundedHeightClass (g0 : MetricField) (kappa : ℝ) (M : ℕ) (q0 : ℚ) :
    Set (metricPatchSet g0 kappa) :=
  {eta | ∃ z : Coord → ℝ, BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
    |hessianQuotient (perturbedMetric g0 eta.val) z 0 - (q0 : ℝ)| <
      1 / (100 * boundedClassWidth kappa M)}

theorem every_admissible_height_has_class {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) (kappa : ℝ) :
    ∃ M : ℕ, BoundedAdmissibleHeight g M z ∧
      ∃ q0 : ℚ, |hessianQuotient g z 0 - (q0 : ℝ)| <
        1 / (100 * boundedClassWidth kappa M) := by
  obtain ⟨M, hM⟩ := h.exists_integer_bound
  obtain ⟨q0, hq0⟩ := exists_rational_bounded_class_label kappa M (hessianQuotient g z 0)
  exact ⟨M, hM, q0, hq0⟩

theorem boundedHeightClass_label_abs_lt {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    (hne : (boundedHeightClass g0 kappa M q0).Nonempty) : |(q0 : ℝ)| < 1 / 20 := by
  obtain ⟨eta, z, hz, hlabel⟩ := hne
  obtain ⟨_, _, _, _, _, _, _, _, hq⟩ := hz.2.1
  have hzero : (0 : Coord) ∈ SmoothLocal.Flow.modelSquare := by
    constructor <;> intro _ <;> norm_num
  have hqzero := hq 0 hzero
  have hL := boundedClassWidth_ge_hundred kappa M
  have hden : (100 : ℝ) < 100 * boundedClassWidth kappa M := by linarith
  have htolerance : 1 / (100 * boundedClassWidth kappa M) < (1 : ℝ) / 100 :=
    one_div_lt_one_div_of_lt (by norm_num) hden
  have htriangle : |(q0 : ℝ)| ≤
      |(q0 : ℝ) - hessianQuotient (perturbedMetric g0 eta.val) z 0| +
        |hessianQuotient (perturbedMetric g0 eta.val) z 0| := by
    simpa only [sub_add_cancel] using
      abs_add_le ((q0 : ℝ) - hessianQuotient (perturbedMetric g0 eta.val) z 0)
        (hessianQuotient (perturbedMetric g0 eta.val) z 0)
  rw [abs_sub_comm] at htriangle
  linarith

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse

theorem exists_N_before_delta_eventually_bounded_height_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (M : ℕ) (q0 : ℚ)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0))
    (a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |(q0 : ℝ)| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
          |hessianQuotient (perturbedMetric g0 eta.val) z 0 - (q0 : ℝ)| <
            1 / (100 * boundedClassWidth kappa M) ∧
          SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
          (∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ) a N delta (tau : ℝ) x) p‖ ≤
                metricApproximationAccuracy tau) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ) a N delta (tau : ℝ) x i j) p‖ ≤
                metricApproximationAccuracy tau) := by
  obtain ⟨N, hN, happrox⟩ := exists_N_before_delta_eventually_class_approximation
    hg0 hU hSU hO hStar hOclosure (q0 : ℝ) a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hdelta
  filter_upwards [happrox delta hdelta] with tau htau
  obtain ⟨eta, ⟨z, hz, hlabel⟩, hpositive, _, hT, hC⟩ := htau.2
  exact ⟨htau.1, eta, z, hz, hlabel, hpositive, hT, hC⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

def patchObstructionSet (g0 : MetricField) (kappa : ℝ) : Set (metricPatchSet g0 kappa) :=
  ⋂ index : ℕ × ℚ, (closure (boundedHeightClass g0 kappa index.1 index.2))ᶜ

theorem mem_patchObstructionSet_iff {g0 : MetricField} {kappa : ℝ}
    {eta : metricPatchSet g0 kappa} :
    eta ∈ patchObstructionSet g0 kappa ↔
      ∀ M : ℕ, ∀ q0 : ℚ, eta ∉ closure (boundedHeightClass g0 kappa M q0) := by
  simp only [patchObstructionSet, mem_iInter, mem_compl_iff, Prod.forall]

theorem patchObstructionSet_has_no_admissible_height
    {g0 : MetricField} {kappa : ℝ} {eta : metricPatchSet g0 kappa}
    (heta : eta ∈ patchObstructionSet g0 kappa) :
    ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z := by
  intro z hz
  obtain ⟨M,hM,q0,hq0⟩ := every_admissible_height_has_class hz kappa
  have hclass : eta ∈ boundedHeightClass g0 kappa M q0 := ⟨z,hM,hq0⟩
  exact (mem_patchObstructionSet_iff.mp heta M q0) (subset_closure hclass)

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow

theorem boundedHeightClass_nonempty_parameters
    {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    (hclass : (boundedHeightClass g0 kappa M q0).Nonempty) :
    0 < M ∧ |(q0 : ℝ)| < 1/20 := by
  obtain ⟨eta,z,hz,hcenter⟩ := hclass
  exact ⟨hz.1,boundedHeightClass_label_abs_lt ⟨eta,z,hz,hcenter⟩⟩

theorem boundedHeightClass_closure_parameters
    {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    {eta : metricPatchSet g0 kappa}
    (heta : eta ∈ closure (boundedHeightClass g0 kappa M q0)) :
    0 < M ∧ |(q0 : ℝ)| < 1/20 :=
  boundedHeightClass_nonempty_parameters (Set.Nonempty.of_closure ⟨eta,heta⟩)

theorem bounded_class_open_closure_pulse_family_at_radius
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (M : ℕ) (q0 : ℚ)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0))
    {r : ℝ} (hr : 0 < r) (hLr : boundedClassWidth kappa M*r ≤ 1/20) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-(q0 : ℝ)| ≤
            1/(100*boundedClassWidth kappa M) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j-
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ)
                (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) x i j) p‖ ≤
                  metricApproximationAccuracy tau) := by
  have hparams := boundedHeightClass_closure_parameters (hOclosure hStar)
  let a := boundedClassWidth kappa M*r/16
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  have hax : a ≤ 1/10 := by
    dsimp only [a]
    linarith
  have hq : |(q0 : ℝ)| *a < 1/10 := by
    have hm := mul_le_mul hparams.2.le hax ha.le (by norm_num : (0 : ℝ) ≤ 1/20)
    norm_num at hm
    linarith
  obtain ⟨N,hN,hfamily⟩ := exists_N_before_delta_eventually_bounded_height_approximation
    hg0 hV hSV M q0 hO hStar hOclosure a ha hax hq
  refine ⟨N,hN,?_⟩
  intro delta hdelt
  filter_upwards [hfamily delta hdelt] with tau htau
  obtain ⟨eta,z,hclass,hcenter,_,_,hC⟩ := htau.2
  exact ⟨htau.1,eta,z,hclass,hcenter.le,fun i j k hk p _ => hC i j k hk p⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow SmoothLocal.Model

theorem boundedHeightClass_isNowhereDense
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    (M : ℕ) (q0 : ℚ) :
    IsNowhereDense (boundedHeightClass g0 kappa M q0) := by
  change interior (closure (boundedHeightClass g0 kappa M q0)) = ∅
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro etaStar hStar
  let O := interior (closure (boundedHeightClass g0 kappa M q0))
  have hO : IsOpen O := isOpen_interior
  have hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0) := interior_subset
  have hparameters := boundedHeightClass_closure_parameters (hOclosure hStar)
  have hgStar : SmoothPositiveOn (perturbedMetric g0 etaStar.val) V :=
    perturbedMetric_smoothPositiveOn hg0 etaStar.val etaStar.property.1
  obtain ⟨r,hr,_,hLr,hexclusion⟩ := exists_original_pulse_exclusion
    hg0 hgStar hV hSV M hkappa hparameters.1 hparameters.2.le hbackground
  obtain ⟨N,hN,happroximants⟩ := bounded_class_open_closure_pulse_family_at_radius
    hg0 hV hSV M q0 hO hStar hOclosure hr hLr
  obtain ⟨delta,hdelt,_,hnoheight⟩ := hexclusion N hN
  obtain ⟨tau,happroxTau,hnoheightTau⟩ := ((happroximants delta hdelt).and hnoheight).exists
  obtain ⟨eta,z,hclass,hcenter,haccuracy⟩ := happroxTau.2
  exact hnoheightTau eta z hclass hcenter haccuracy

end SmoothLocal.Perturbation

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Model

theorem patchObstructionSet_dense
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    Dense (patchObstructionSet g0 kappa) := by
  let : BaireSpace (metricPatchSet g0 kappa) := metricPatchSet_baire hg0 hV hSV kappa
  change Dense (⋂ index : ℕ × ℚ, (closure (boundedHeightClass g0 kappa index.1 index.2))ᶜ)
  apply dense_iInter_of_isOpen (fun _ => isClosed_closure.isOpen_compl)
  intro index
  exact (isClosed_isNowhereDense_iff_compl.mp ⟨isClosed_closure,
    (boundedHeightClass_isNowhereDense hg0 hV hSV hkappa hbackground index.1 index.2).closure⟩).2

theorem exists_patch_obstruction_in_open
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ eta ∈ O,
      SmoothPositiveOn (perturbedMetric g0 eta.val) V ∧
      (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa/2) ∧
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z := by
  obtain ⟨eta,hetaGood,hetaO⟩ :=
    (patchObstructionSet_dense hg0 hV hSV hkappa hbackground).exists_mem_open hO hne
  exact ⟨eta,hetaO,perturbedMetric_smoothPositiveOn hg0 eta.val eta.property.1,
    eta.property.2,patchObstructionSet_has_no_admissible_height hetaGood⟩

end SmoothLocal.Perturbation

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Perturbation.exists_patch_obstruction_in_open := @OAI.SmoothLocal.Perturbation.exists_patch_obstruction_in_open
