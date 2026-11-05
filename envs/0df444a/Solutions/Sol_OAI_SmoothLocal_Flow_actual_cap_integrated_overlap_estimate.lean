-- Prove2me | solution 1 for OAI.SmoothLocal.Flow.actual_cap_integrated_overlap_estimate
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:36:27.609585+00:00
-- url     : https://prove2.me/submissions/c739dc66-ceb1-46b0-8801-2aeb76620e9e

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
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem coordPartial_div
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => f x / h x) p =
      (coordPartial i f p * h p - f p * coordPartial i h p) / (h p) ^ 2 := by
  have hinv : HasFDerivAt (fun x : Coord => (h x)⁻¹)
      (-(h p ^ 2)⁻¹ • fderiv ℝ h p) p := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv hne).comp_hasFDerivAt p hh.hasFDerivAt
  have hquot : HasFDerivAt (fun x : Coord => f x / h x)
      (f p • (-(h p ^ 2)⁻¹ • fderiv ℝ h p) +
        (h p)⁻¹ • fderiv ℝ f p) p := by
    simpa only [div_eq_mul_inv] using hf.hasFDerivAt.fun_mul hinv
  unfold coordPartial
  rw [hquot.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp [hne]
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

theorem squareTransition_range (t : ℝ) :
    0 ≤ squareTransition t ∧ squareTransition t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem squareTransition_one {t : ℝ} (ht : 1 / 2 ≤ t) : squareTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem modelProfile_bounds (y : ℝ) : 1 - y ^ 2 ≤ modelProfile y ∧ modelProfile y ≤ 1 := by
  have hh := squareTransition_range (y ^ 2)
  have hprod := mul_le_mul_of_nonneg_left hh.2 (sq_nonneg y)
  have hprod0 := mul_nonneg (sq_nonneg y) hh.1
  unfold modelProfile
  constructor <;> nlinarith

theorem modelProfile_eq_one_sub_sq {y : ℝ} (hy : 1 / 2 ≤ y ^ 2) :
    modelProfile y = 1 - y ^ 2 := by
  simp [modelProfile, squareTransition_one hy]

theorem modelCurvature_lateral_band_lower {kappa : ℝ} (hkappa : 0 < kappa) {p : Coord}
    (hp : 3 / 2 < |p 0|) : 5 / 4 * kappa < modelCurvature kappa p := by
  have hx : (3 / 2 : ℝ) ^ 2 < (p 0) ^ 2 := sq_lt_sq.mpr (by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    exact hp)
  have hmul := mul_lt_mul_of_pos_left hx hkappa
  have hh := mul_le_mul_of_nonneg_left (modelProfile_bounds (p 1)).2 hkappa.le
  unfold modelCurvature
  nlinarith

end SmoothLocal.Model

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

theorem coordPartial_mul_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

end HessianCalculus

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

end SmoothLocal.Geometry

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {I : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem directedWeight_differentiableAt
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedWeight b lambda I) p := by
  have hD := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hPhi := ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul (-lambda)).add hI.hasFDerivAt
  have hd := (hD.pow 8).fun_mul hPhi.exp
  simp only [Pi.add_def, Pi.sub_def] at hd
  exact hd.differentiableAt

theorem directedWeight_partial
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (i : Fin 2) :
    coordPartial i (directedWeight b lambda I) p =
      -8 * (edgeDistance b p) ^ 7 * (if (1 : Fin 2) = i then 1 else 0) *
          Real.exp (weightPhase lambda I p) +
        directedWeight b lambda I p *
          (coordPartial i I p - lambda * (if (1 : Fin 2) = i then 1 else 0)) := by
  have hD := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hPhi := ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul (-lambda)).add hI.hasFDerivAt
  have hd := (hD.pow 8).fun_mul hPhi.exp
  simp only [Pi.add_def, Pi.sub_def] at hd
  change fderiv ℝ (fun q : Coord => (b - q 1) ^ 8 * Real.exp (-lambda * q 1 + I q))
    p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;>
    simp [edgeDistance, directedWeight, weightPhase, coordPartial] <;> ring

theorem directedWeight_partial_t
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    coordPartial 0 (directedWeight b lambda I) p =
      directedWeight b lambda I p * coordPartial 0 I p := by
  simpa using directedWeight_partial b lambda hI 0

theorem directedWeight_partial_s
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    coordPartial 1 (directedWeight b lambda I) p =
      -8 * (edgeDistance b p) ^ 7 * Real.exp (weightPhase lambda I p) +
        directedWeight b lambda I p * (coordPartial 1 I p - lambda) := by
  simpa using directedWeight_partial b lambda hI 1

theorem directedWeight_contDiffOn (b lambda : ℝ) (hI : ContDiffOn ℝ ∞ I U) :
    ContDiffOn ℝ ∞ (directedWeight b lambda I) U := by
  have hy : ContDiffOn ℝ ∞ (fun p : Coord => p 1) U :=
    contDiffOn_apply ℝ ℝ 1 U
  have hD : ContDiffOn ℝ ∞ (fun p : Coord => b - p 1) U :=
    contDiffOn_const.sub hy
  have hLambda : ContDiffOn ℝ ∞ (fun _ : Coord => -lambda) U := contDiffOn_const
  have hPhi : ContDiffOn ℝ ∞ (fun p : Coord => -lambda * p 1 + I p) U :=
    (hLambda.mul hy).add hI
  exact (hD.pow 8).mul hPhi.exp

theorem directedWeight_edge_zero (b lambda : ℝ) (I : Coord → ℝ) (p : Coord)
    (hp : p 1 = b) : directedWeight b lambda I p = 0 := by
  simp [directedWeight, edgeDistance, hp]

theorem directedWeight_partial_edge_zero
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (hp : p 1 = b) (i : Fin 2) :
    coordPartial i (directedWeight b lambda I) p = 0 := by
  rw [directedWeight_partial b lambda hI i]
  simp [edgeDistance, directedWeight, hp]

theorem directedM_differentiableAt
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedM b lambda I) p :=
  (directedWeight_differentiableAt b lambda hI).neg

theorem directedN_differentiableAt
    (b lambda epsilon : ℝ) (hI : DifferentiableAt ℝ I p) :
    DifferentiableAt ℝ (directedN b lambda epsilon I) p :=
  ((differentiableAt_apply (𝕜 := ℝ) 0 p).const_mul epsilon).mul
    (directedWeight_differentiableAt b lambda hI)

theorem directedM_partial (b lambda : ℝ) (i : Fin 2) :
    coordPartial i (directedM b lambda I) p =
      -coordPartial i (directedWeight b lambda I) p := by
  change fderiv ℝ (fun q : Coord => -directedWeight b lambda I q) p (Pi.single i 1) =
    -fderiv ℝ (directedWeight b lambda I) p (Pi.single i 1)
  simp only [fderiv_fun_neg, neg_apply]

theorem directedN_partial
    (b lambda epsilon : ℝ) (hI : DifferentiableAt ℝ I p) (i : Fin 2) :
    coordPartial i (directedN b lambda epsilon I) p =
      epsilon * (if (0 : Fin 2) = i then 1 else 0) * directedWeight b lambda I p +
        epsilon * p 0 * coordPartial i (directedWeight b lambda I) p := by
  have hd := ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).const_mul epsilon).fun_mul
    (directedWeight_differentiableAt b lambda hI).hasFDerivAt
  change fderiv ℝ (fun q : Coord => epsilon * q 0 * directedWeight b lambda I q)
    p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp [coordPartial]
  ring

theorem directed_mn_edge_zero
    (b lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) (hp : p 1 = b) :
    directedM b lambda I p = 0 ∧ directedN b lambda epsilon I p = 0 := by
  simp [directedM, directedN, directedWeight_edge_zero b lambda I p hp]

end SmoothLocal.Weighted

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

theorem christoffel_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (k i j : Fin 2) :
    christoffel g k i j p = christoffel h k i j p := by
  have hval := heq.self_of_nhds
  have hd (a b c : Fin 2) : coordPartial a (fun q => g q b c) p =
      coordPartial a (fun q => h q b c) p :=
    coordPartial_eq_of_eventuallyEq (metric_coeff_eventuallyEq heq b c) a
  simp only [christoffel, inverseMetric, hval, hd]

theorem christoffel_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (k i j : Fin 2) :
    christoffel g k i j =ᶠ[𝓝 p] christoffel h k i j :=
  heq.eventuallyEq_nhds.mono fun _ hq => christoffel_eq_of_eventuallyEq hq k i j

theorem riemann_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (l k i j : Fin 2) :
    riemann g l k i j p = riemann h l k i j p := by
  have hΓ := christoffel_eq_of_eventuallyEq heq
  have hd (a b c d : Fin 2) : coordPartial a (christoffel g b c d) p =
      coordPartial a (christoffel h b c d) p :=
    coordPartial_eq_of_eventuallyEq (christoffel_eventuallyEq heq b c d) a
  simp only [riemann, hΓ, hd]

theorem gaussianCurvature_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) : gaussianCurvature g p = gaussianCurvature h p := by
  simp only [gaussianCurvature, heq.self_of_nhds, riemann_eq_of_eventuallyEq heq]

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

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem transitionDerivativeBound_pos : 0 < transitionDerivativeBound :=
  (Classical.choose_spec exists_smoothTransition_derivative_bound).1

theorem smoothTransition_deriv_abs_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ transitionDerivativeBound :=
  (Classical.choose_spec exists_smoothTransition_derivative_bound).2 x

theorem intervalCutoff_contDiff (a b : ℝ) : ContDiff ℝ ∞ (intervalCutoff a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a))

theorem intervalCutoff_range (a b x : ℝ) :
    0 ≤ intervalCutoff a b x ∧ intervalCutoff a b x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem intervalCutoff_zero {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    intervalCutoff a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le)

theorem intervalCutoff_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    intervalCutoff a b x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)

theorem intervalCutoff_hasDerivAt (a b x : ℝ) :
    HasDerivAt (intervalCutoff a b)
      (deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) x := by
  have htheta := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have ht : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((x - a) / (b - a))) ((x - a) / (b - a)) :=
    (htheta _).hasDerivAt
  have ha : HasDerivAt (fun y : ℝ => (y - a) / (b - a)) (1 / (b - a)) x :=
    ((hasDerivAt_id x).sub_const a).div_const (b - a)
  have hd := ht.comp x ha
  change HasDerivAt (Real.smoothTransition ∘ fun y : ℝ => (y - a) / (b - a)) _ x
  have he : deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a) =
      deriv Real.smoothTransition ((x - a) / (b - a)) * (1 / (b - a)) := by ring
  rw [he]
  exact hd

theorem intervalCutoff_deriv (a b x : ℝ) :
    deriv (intervalCutoff a b) x =
      deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a) :=
  (intervalCutoff_hasDerivAt a b x).deriv

theorem intervalCutoff_deriv_zero_left {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    deriv (intervalCutoff a b) x = 0 := by
  rw [intervalCutoff_deriv, smoothTransition_deriv_zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le), zero_div]

theorem intervalCutoff_deriv_zero_right {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    deriv (intervalCutoff a b) x = 0 := by
  rw [intervalCutoff_deriv, smoothTransition_deriv_zero_of_one_le
    ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)), zero_div]

theorem intervalCutoff_deriv_abs_le {a b : ℝ} (hab : a < b) (x : ℝ) :
    |deriv (intervalCutoff a b) x| ≤ transitionDerivativeBound / (b - a) := by
  rw [intervalCutoff_deriv, abs_div, abs_of_pos (sub_pos.mpr hab)]
  exact div_le_div_of_nonneg_right (smoothTransition_deriv_abs_le _) (sub_pos.mpr hab).le

theorem intervalCutoff_deriv_support {a b x : ℝ} (hab : a < b)
    (hx : deriv (intervalCutoff a b) x ≠ 0) : a < x ∧ x < b := by
  constructor
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_left hab (le_of_not_gt h))
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_right hab (le_of_not_gt h))

def ellipticPhi (c x : ℝ) : ℝ := intervalCutoff (c / 2) c x

theorem ellipticPhi_contDiff (c : ℝ) : ContDiff ℝ ∞ (ellipticPhi c) :=
  intervalCutoff_contDiff _ _

theorem ellipticPhi_zero {c x : ℝ} (hc : 0 < c) (hx : x ≤ c / 2) :
    ellipticPhi c x = 0 := intervalCutoff_zero (by linarith) hx

theorem ellipticPhi_one {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    ellipticPhi c x = 1 := intervalCutoff_one (by linarith) hx

theorem ellipticPhi_deriv_abs_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    |deriv (ellipticPhi c) x| ≤ 2 * transitionDerivativeBound / c := by
  have hh := intervalCutoff_deriv_abs_le (a := c / 2) (b := c) (by linarith) x
  change |deriv (intervalCutoff (c / 2) c) x| ≤ _
  have he : transitionDerivativeBound / (c - c / 2) =
      2 * transitionDerivativeBound / c := by field_simp; ring
  rw [he] at hh
  exact hh

theorem ellipticPhi_deriv_support {c x : ℝ} (hc : 0 < c)
    (hx : deriv (ellipticPhi c) x ≠ 0) : c / 2 < x ∧ x < c := by
  constructor
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_left (by linarith) (le_of_not_gt h))
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_right (by linarith) (le_of_not_gt h))

theorem threeEdgeCutoff_contDiff (l0 l1 r1 r0 a0 a1 : ℝ) :
    ContDiff ℝ ∞ (threeEdgeCutoff l0 l1 r1 r0 a0 a1) := by
  exact (((intervalCutoff_contDiff l0 l1).comp (contDiff_apply ℝ ℝ 0)).mul
    ((intervalCutoff_contDiff (-r0) (-r1)).comp (contDiff_apply ℝ ℝ 0).neg)).mul
      ((intervalCutoff_contDiff a0 a1).comp (contDiff_apply ℝ ℝ 1))

theorem threeEdgeCutoff_range (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) :
    0 ≤ threeEdgeCutoff l0 l1 r1 r0 a0 a1 p ∧
      threeEdgeCutoff l0 l1 r1 r0 a0 a1 p ≤ 1 := by
  have hL := intervalCutoff_range l0 l1 (p 0)
  have hR := intervalCutoff_range (-r0) (-r1) (-p 0)
  have hS := intervalCutoff_range a0 a1 (p 1)
  constructor
  · exact mul_nonneg (mul_nonneg hL.1 hR.1) hS.1
  · have hLR : intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) ≤ 1 := by
      nlinarith
    change intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
      intervalCutoff a0 a1 (p 1) ≤ 1
    nlinarith [mul_nonneg hL.1 hR.1]

theorem threeEdgeCutoff_one {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord)
    (hp : l1 ≤ p 0 ∧ p 0 ≤ r1 ∧ a1 ≤ p 1) :
    threeEdgeCutoff l0 l1 r1 r0 a0 a1 p = 1 := by
  rw [threeEdgeCutoff, intervalCutoff_one hL hp.1,
    intervalCutoff_one (neg_lt_neg hR) (neg_le_neg hp.2.1),
    intervalCutoff_one hS hp.2.2]
  norm_num

theorem threeEdgeCutoff_zero {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord)
    (hp : p 0 ≤ l0 ∨ r0 ≤ p 0 ∨ p 1 ≤ a0) :
    threeEdgeCutoff l0 l1 r1 r0 a0 a1 p = 0 := by
  rcases hp with h | h | h
  · simp [threeEdgeCutoff, intervalCutoff_zero hL h]
  · simp [threeEdgeCutoff, intervalCutoff_zero (neg_lt_neg hR) (neg_le_neg h)]
  · simp [threeEdgeCutoff, intervalCutoff_zero hS h]

theorem threeEdgeCutoff_partial (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p =
      if i = 0 then
        deriv (intervalCutoff l0 l1) (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
          intervalCutoff a0 a1 (p 1) -
        intervalCutoff l0 l1 (p 0) * deriv (intervalCutoff (-r0) (-r1)) (-p 0) *
          intervalCutoff a0 a1 (p 1)
      else intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
        deriv (intervalCutoff a0 a1) (p 1) := by
  have hL := (((intervalCutoff_contDiff l0 l1).differentiable (by simp) (p 0)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 0 p)
  have hR := (((intervalCutoff_contDiff (-r0) (-r1)).differentiable (by simp) (-p 0)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 0 p).neg
  have hS := (((intervalCutoff_contDiff a0 a1).differentiable (by simp) (p 1)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hd := (hL.fun_mul hR).fun_mul hS
  simp only [Function.comp_def, Pi.neg_apply] at hd
  change fderiv ℝ (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p (Pi.single i 1) = _
  change fderiv ℝ (fun q => intervalCutoff l0 l1 (q 0) *
    intervalCutoff (-r0) (-r1) (-q 0) * intervalCutoff a0 a1 (q 1)) p _ = _
  rw [hd.fderiv]
  fin_cases i <;> simp
  ring

theorem abs_mul_two_cutoffs_le (a b c : ℝ) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) : |a * b * c| ≤ |a| := by
  rw [abs_mul, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hc.1]
  calc
    |a| * b * c ≤ |a| * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg a)) hc.2 hc.1
        (mul_nonneg (abs_nonneg a) zero_le_one)
    _ = |a| := by ring

theorem threeEdgeCutoff_partial_bounds {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord) :
    |coordPartial 0 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
        transitionDerivativeBound / (l1 - l0) + transitionDerivativeBound / (r0 - r1) ∧
      |coordPartial 1 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
        transitionDerivativeBound / (a1 - a0) := by
  have hleft := intervalCutoff_range l0 l1 (p 0)
  have hright := intervalCutoff_range (-r0) (-r1) (-p 0)
  have hbottom := intervalCutoff_range a0 a1 (p 1)
  constructor
  · rw [threeEdgeCutoff_partial]
    simp only [↓reduceIte]
    refine (abs_sub _ _).trans ?_
    apply add_le_add
    · exact (abs_mul_two_cutoffs_le _ _ _ hright hbottom).trans
        (intervalCutoff_deriv_abs_le hL _)
    · rw [mul_comm (intervalCutoff l0 l1 (p 0))]
      exact (abs_mul_two_cutoffs_le _ _ _ hleft hbottom).trans
        (by simpa only [neg_sub_neg] using intervalCutoff_deriv_abs_le (neg_lt_neg hR) (-p 0))
  · rw [threeEdgeCutoff_partial]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    have he : intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
        deriv (intervalCutoff a0 a1) (p 1) = deriv (intervalCutoff a0 a1) (p 1) *
        intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) := by ring
    rw [he]
    exact (abs_mul_two_cutoffs_le _ _ _ hleft hright).trans (intervalCutoff_deriv_abs_le hS _)

theorem threeEdgeCutoff_partial_t_support {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (p : Coord)
    (hp : coordPartial 0 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p ≠ 0) :
    p 0 ∈ Ioo l0 l1 ∨ p 0 ∈ Ioo r1 r0 := by
  by_cases hl : deriv (intervalCutoff l0 l1) (p 0) = 0
  · have hr : deriv (intervalCutoff (-r0) (-r1)) (-p 0) ≠ 0 := by
      intro h
      apply hp
      rw [threeEdgeCutoff_partial]
      simp [hl, h]
    have hs := intervalCutoff_deriv_support (neg_lt_neg hR) hr
    exact Or.inr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · exact Or.inl (intervalCutoff_deriv_support hL hl)

theorem threeEdgeCutoff_partial_s_support {l0 l1 r1 r0 a0 a1 : ℝ}
    (hS : a0 < a1) (p : Coord)
    (hp : coordPartial 1 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p ≠ 0) :
    p 1 ∈ Ioo a0 a1 := by
  apply intervalCutoff_deriv_support hS
  intro hz
  apply hp
  rw [threeEdgeCutoff_partial]
  simp [hz]

theorem capSpatialCutoff_contDiff (L R A : ℝ) :
    ContDiff ℝ ∞ (capSpatialCutoff L R A) := threeEdgeCutoff_contDiff _ _ _ _ _ _

theorem capSpatialCutoff_range (L R A : ℝ) (p : Coord) :
    0 ≤ capSpatialCutoff L R A p ∧ capSpatialCutoff L R A p ≤ 1 :=
  threeEdgeCutoff_range _ _ _ _ _ _ p

theorem capSpatialCutoff_one {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord)
    (hp : L ≤ p 0 ∧ p 0 ≤ R ∧ A ≤ p 1) : capSpatialCutoff L R A p = 1 := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  apply threeEdgeCutoff_one hli (neg_lt_neg hri) hai p
  exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩

theorem capSpatialCutoff_derivative_bands {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord) (i : Fin 2)
    (hp : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    (3 / 2 < |p 0| ∧ |p 0| < 2) ∨ (-2 < p 1 ∧ p 1 < -3 / 2) := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  fin_cases i
  · rcases threeEdgeCutoff_partial_t_support hli (neg_lt_neg hri) p hp with ht | ht
    · left
      rw [abs_of_neg (by linarith [ht.2] : p 0 < 0)]
      constructor <;> linarith [ht.1, ht.2]
    · left
      rw [abs_of_pos (by linarith [ht.1] : 0 < p 0)]
      constructor <;> linarith [ht.1, ht.2]
  · have hs := threeEdgeCutoff_partial_s_support hai p hp
    exact Or.inr ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem ellipticPhi_ratio_derivative_bound
    {c d k ki di M : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hM : 0 ≤ M) (hki : |ki| ≤ M) (hdi : |di| ≤ 1) :
    |deriv (ellipticPhi c) (k / d) * ((ki * d - k * di) / d ^ 2)| ≤
      (2 * transitionDerivativeBound / c) * (M + c) / d := by
  have hC : 0 ≤ 2 * transitionDerivativeBound / c :=
    div_nonneg (mul_nonneg (by norm_num) transitionDerivativeBound_pos.le) hc.le
  by_cases hzero : deriv (ellipticPhi c) (k / d) = 0
  · rw [hzero, zero_mul, abs_zero]
    exact div_nonneg (mul_nonneg hC (add_nonneg hM hc.le)) hd.le
  have hsupp := ellipticPhi_deriv_support hc hzero
  have hkpos : 0 < k := by
    have hpos : 0 < k / d := lt_trans (by linarith : 0 < c / 2) hsupp.1
    exact (div_pos_iff.mp hpos).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge hd.le h.2))
  have hkupper : |k| ≤ c * d := by
    rw [abs_of_pos hkpos]
    exact ((div_lt_iff₀ hd).mp hsupp.2).le
  have hnum : |ki * d - k * di| ≤ (M + c) * d := by
    calc
      |ki * d - k * di| ≤ |ki| * d + |k| * |di| := by
        simpa only [abs_mul, abs_of_pos hd] using abs_sub (ki * d) (k * di)
      _ ≤ M * d + (c * d) * 1 := add_le_add
        (mul_le_mul_of_nonneg_right hki hd.le)
        (mul_le_mul hkupper hdi (abs_nonneg di) (mul_nonneg hc.le hd.le))
      _ = (M + c) * d := by ring
  rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg d)]
  calc
    |deriv (ellipticPhi c) (k / d)| * (|ki * d - k * di| / d ^ 2) ≤
        (2 * transitionDerivativeBound / c) * (((M + c) * d) / d ^ 2) :=
      mul_le_mul (ellipticPhi_deriv_abs_le hc _) (div_le_div_of_nonneg_right hnum (sq_nonneg d))
        (div_nonneg (abs_nonneg _) (sq_nonneg d)) hC
    _ = (2 * transitionDerivativeBound / c) * (M + c) / d := by
      field_simp [hd.ne']

def ellipticWeight (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 6 * (chi p) ^ 2 * (ellipticPhi c (K p / edgeDistance b p)) ^ 2

def ellipticGate (b c : ℝ) (K : Coord → ℝ) (p : Coord) : ℝ :=
  ellipticPhi c (K p / edgeDistance b p)

def ellipticAmplitude (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  (edgeDistance b p) ^ 3 * chi p * ellipticGate b c K p

theorem ellipticAmplitude_sq (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    ellipticAmplitude b c chi K p ^ 2 = ellipticWeight b c chi K p := by
  unfold ellipticAmplitude ellipticGate ellipticWeight
  ring

theorem edgeDistance_partial (b : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (edgeDistance b) p = -(if (1 : Fin 2) = i then 1 else 0) := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  simp only [Pi.sub_def] at hd
  unfold coordPartial edgeDistance
  rw [hd.fderiv]
  fin_cases i <;> simp

theorem ellipticGate_differentiableAt {b c : ℝ} {K : Coord → ℝ} {p : Coord}
    (hK : DifferentiableAt ℝ K p) (hd : edgeDistance b p ≠ 0) :
    DifferentiableAt ℝ (ellipticGate b c K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hquot : DifferentiableAt ℝ (fun q => K q / edgeDistance b q) p := by
    have hm : DifferentiableAt ℝ (fun q => K q * (edgeDistance b q)⁻¹) p :=
      hK.mul (hD.inv hd)
    simpa only [div_eq_mul_inv] using hm
  exact ((ellipticPhi_contDiff c).differentiable (by simp) _).comp p hquot

theorem ellipticGate_partial {b c : ℝ} {K : Coord → ℝ} {p : Coord}
    (hK : DifferentiableAt ℝ K p) (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticGate b c K) p =
      deriv (ellipticPhi c) (K p / edgeDistance b p) *
        ((coordPartial i K p * edgeDistance b p - K p * coordPartial i (edgeDistance b) p) /
          edgeDistance b p ^ 2) := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hquot : DifferentiableAt ℝ (fun q => K q / edgeDistance b q) p := by
    have hm : DifferentiableAt ℝ (fun q => K q * (edgeDistance b q)⁻¹) p :=
      hK.mul (hD.inv hd)
    simpa only [div_eq_mul_inv] using hm
  have hh := (((ellipticPhi_contDiff c).differentiable (by simp)
    (K p / edgeDistance b p)).hasDerivAt).comp_hasFDerivAt p hquot.hasFDerivAt
  simp only [Function.comp_def] at hh
  have he : coordPartial i (ellipticGate b c K) p =
      deriv (ellipticPhi c) (K p / edgeDistance b p) *
        coordPartial i (fun q => K q / edgeDistance b q) p := by
    unfold coordPartial ellipticGate
    rw [hh.fderiv]
    simp only [smul_apply, smul_eq_mul]
  rw [he, coordPartial_div hK hD hd i]

theorem ellipticGate_partial_bound {b c M : ℝ} {K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hM : 0 ≤ M)
    (hK : DifferentiableAt ℝ K p) (i : Fin 2) (hKi : |coordPartial i K p| ≤ M) :
    |coordPartial i (ellipticGate b c K) p| ≤
      (2 * transitionDerivativeBound / c) * (M + c) / edgeDistance b p := by
  rw [ellipticGate_partial hK hd.ne' i]
  apply ellipticPhi_ratio_derivative_bound hc hd hM hKi
  rw [edgeDistance_partial]
  fin_cases i <;> norm_num

theorem ellipticAmplitude_differentiableAt {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) : DifferentiableAt ℝ (ellipticAmplitude b c chi K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  exact ((hD.pow 3).mul hchi).mul (ellipticGate_differentiableAt hK hd)

theorem ellipticAmplitude_partial {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticAmplitude b c chi K) p =
      3 * edgeDistance b p ^ 2 * coordPartial i (edgeDistance b) p * chi p * ellipticGate b c K p +
      edgeDistance b p ^ 3 * coordPartial i chi p * ellipticGate b c K p +
      edgeDistance b p ^ 3 * chi p * coordPartial i (ellipticGate b c K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hG := ellipticGate_differentiableAt (b := b) (c := c) hK hd
  have hdpow : coordPartial i (fun q => edgeDistance b q ^ 3) p =
      3 * edgeDistance b p ^ 2 * coordPartial i (edgeDistance b) p := by
    unfold coordPartial
    rw [(hD.hasFDerivAt.pow 3).fderiv]
    simp only [smul_apply, smul_eq_mul]
    ring
  unfold ellipticAmplitude
  rw [HessianCalculus.coordPartial_mul_at
      (f := fun q => edgeDistance b q ^ 3 * chi q) (h := ellipticGate b c K)
      ((hD.pow 3).mul hchi) hG i,
    HessianCalculus.coordPartial_mul_at (f := fun q => edgeDistance b q ^ 3) (h := chi)
      (hD.pow 3) hchi i, hdpow]
  ring

theorem ellipticWeight_partial {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticWeight b c chi K) p =
      2 * ellipticAmplitude b c chi K p * coordPartial i (ellipticAmplitude b c chi K) p := by
  have hA := ellipticAmplitude_differentiableAt (c := c) hchi hK hd
  have he : ellipticWeight b c chi K =
      fun q => ellipticAmplitude b c chi K q * ellipticAmplitude b c chi K q := by
    funext q
    rw [← ellipticAmplitude_sq, pow_two]
  rw [he, HessianCalculus.coordPartial_mul_at hA hA i]
  ring

theorem amplitude_derivative_algebra_bound
    {d x g di xi gi X P : ℝ} (hd : 0 < d)
    (hx : 0 ≤ x ∧ x ≤ 1) (hg : 0 ≤ g ∧ g ≤ 1)
    (hdi : |di| ≤ 1) (hxi : |xi| ≤ X) (hgi : |gi| ≤ P / d) :
    |3 * d ^ 2 * di * x * g + d ^ 3 * xi * g + d ^ 3 * x * gi| ≤
      3 * d ^ 2 + d ^ 3 * X + d ^ 2 * P := by
  have hfirst : |3 * d ^ 2 * di * x * g| ≤ 3 * d ^ 2 := by
    calc
      _ ≤ |3 * d ^ 2 * di| := abs_mul_two_cutoffs_le _ _ _ hx hg
      _ = (3 * d ^ 2) * |di| := by rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (3 * d ^ 2) * 1 := mul_le_mul_of_nonneg_left hdi (by positivity)
      _ = 3 * d ^ 2 := mul_one _
  have hsecond : |d ^ 3 * xi * g| ≤ d ^ 3 * X := by
    calc
      _ = |(d ^ 3 * xi) * g * 1| := by rw [mul_one]
      _ ≤ |d ^ 3 * xi| := abs_mul_two_cutoffs_le _ _ _ hg ⟨zero_le_one, le_rfl⟩
      _ = d ^ 3 * |xi| := by rw [abs_mul, abs_of_pos (pow_pos hd _)]
      _ ≤ d ^ 3 * X := mul_le_mul_of_nonneg_left hxi (pow_pos hd _).le
  have hthird : |d ^ 3 * x * gi| ≤ d ^ 2 * P := by
    calc
      _ = |(d ^ 3 * gi) * x * 1| := by congr 1; ring
      _ ≤ |d ^ 3 * gi| := abs_mul_two_cutoffs_le _ _ _ hx ⟨zero_le_one, le_rfl⟩
      _ = d ^ 3 * |gi| := by rw [abs_mul, abs_of_pos (pow_pos hd _)]
      _ ≤ d ^ 3 * (P / d) := mul_le_mul_of_nonneg_left hgi (pow_pos hd _).le
      _ = d ^ 2 * P := by field_simp [hd.ne']
  calc
    _ ≤ |3 * d ^ 2 * di * x * g + d ^ 3 * xi * g| + |d ^ 3 * x * gi| :=
      abs_add_le _ _
    _ ≤ (|3 * d ^ 2 * di * x * g| + |d ^ 3 * xi * g|) + |d ^ 3 * x * gi| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (3 * d ^ 2 + d ^ 3 * X) + d ^ 2 * P :=
      add_le_add (add_le_add hfirst hsecond) hthird

theorem ellipticWeight_partial_bound {b c M X : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hM : 0 ≤ M)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1) (i : Fin 2)
    (hchii : |coordPartial i chi p| ≤ X) (hKi : |coordPartial i K p| ≤ M) :
    |coordPartial i (ellipticWeight b c chi K) p| ≤
      2 * Real.sqrt (ellipticWeight b c chi K p) *
        (3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
          edgeDistance b p ^ 2 * ((2 * transitionDerivativeBound / c) * (M + c))) := by
  have hGRange : 0 ≤ ellipticGate b c K p ∧ ellipticGate b c K p ≤ 1 :=
    intervalCutoff_range _ _ _
  have hAi : |coordPartial i (ellipticAmplitude b c chi K) p| ≤
      3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
        edgeDistance b p ^ 2 * ((2 * transitionDerivativeBound / c) * (M + c)) := by
    rw [ellipticAmplitude_partial hchi hK hd.ne' i]
    apply amplitude_derivative_algebra_bound hd hchiRange hGRange _ hchii
      (ellipticGate_partial_bound hc hd hM hK i hKi)
    rw [edgeDistance_partial]
    fin_cases i <;> norm_num
  have hAmp : 0 ≤ ellipticAmplitude b c chi K p :=
    mul_nonneg (mul_nonneg (pow_pos hd _).le hchiRange.1) hGRange.1
  have hsqrt : Real.sqrt (ellipticWeight b c chi K p) = ellipticAmplitude b c chi K p := by
    rw [← ellipticAmplitude_sq, Real.sqrt_sq hAmp]
  rw [ellipticWeight_partial hchi hK hd.ne' i, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num) hAmp), hsqrt]
  exact mul_le_mul_of_nonneg_left hAi (mul_nonneg (by norm_num) hAmp)

theorem ellipticWeight_contDiffOn {chi K : Coord → ℝ} {U : Set Coord}
    (b c : ℝ) (hchi : ContDiffOn ℝ ∞ chi U) (hK : ContDiffOn ℝ ∞ K U)
    (hd : ∀ p ∈ U, p 1 < b) : ContDiffOn ℝ ∞ (ellipticWeight b c chi K) U := by
  have hD : ContDiffOn ℝ ∞ (edgeDistance b) U :=
    contDiffOn_const.sub (contDiffOn_apply ℝ ℝ 1 U)
  have hratio := hK.div hD (fun p hp => (sub_pos.mpr (hd p hp)).ne')
  exact ((hD.pow 6).mul (hchi.pow 2)).mul
    (((ellipticPhi_contDiff c).comp_contDiffOn hratio).pow 2)

theorem ellipticWeight_nonneg (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    0 ≤ ellipticWeight b c chi K p := by
  unfold ellipticWeight
  positivity

theorem ellipticWeight_le_distance_six (b c : ℝ) (chi K : Coord → ℝ) (p : Coord)
    (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    ellipticWeight b c chi K p ≤ (edgeDistance b p) ^ 6 := by
  have hphi := intervalCutoff_range (c / 2) c (K p / edgeDistance b p)
  have hc2 : (chi p) ^ 2 ≤ 1 := by nlinarith [hchi.1, hchi.2]
  have hp2 : (ellipticPhi c (K p / edgeDistance b p)) ^ 2 ≤ 1 := by
    change (intervalCutoff (c / 2) c (K p / edgeDistance b p)) ^ 2 ≤ 1
    nlinarith
  have hprod : (chi p) ^ 2 * (ellipticPhi c (K p / edgeDistance b p)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (chi p), sq_nonneg (ellipticPhi c (K p / edgeDistance b p))]
  have hpow : 0 ≤ (edgeDistance b p) ^ 6 := by positivity
  unfold ellipticWeight
  nlinarith [mul_le_mul_of_nonneg_left hprod hpow]

theorem ellipticWeight_pos_implies_curvature {b c : ℝ} {chi K : Coord → ℝ}
    {p : Coord} (hc : 0 < c) (hd : p 1 < b)
    (hv : 0 < ellipticWeight b c chi K p) :
    c / 2 * edgeDistance b p < K p := by
  have hdist : 0 < edgeDistance b p := sub_pos.mpr hd
  by_contra h
  have hratio : K p / edgeDistance b p ≤ c / 2 :=
    (div_le_iff₀ hdist).mpr (by linarith)
  have hz := ellipticPhi_zero hc hratio
  simp [ellipticWeight, hz] at hv

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def multiplierTest (m n u : Coord → ℝ) (p : Coord) : ℝ :=
  m p * coordPartial 1 u p + n p * coordPartial 0 u p

def multiplierFluxT (A m n u : Coord → ℝ) (p : Coord) : ℝ :=
  m p * coordPartial 0 u p * coordPartial 1 u p +
    (1 / 2 : ℝ) * (n p * (coordPartial 0 u p) ^ 2) -
    (1 / 2 : ℝ) * (A p * n p * (coordPartial 1 u p) ^ 2)

def multiplierFluxS (A m n u : Coord → ℝ) (p : Coord) : ℝ :=
  (1 / 2 : ℝ) * (A p * m p * (coordPartial 1 u p) ^ 2) +
    A p * n p * coordPartial 0 u p * coordPartial 1 u p -
    (1 / 2 : ℝ) * (m p * (coordPartial 0 u p) ^ 2)

variable {A B C m n u : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem multiplierFluxT_partial_t
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p)
    (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 0 (multiplierFluxT A m n u) p =
      coordPartial 0 m p * coordPartial 0 u p * coordPartial 1 u p +
      m p * coordPartial 0 (coordPartial 0 u) p * coordPartial 1 u p +
      m p * coordPartial 0 u p * coordPartial 0 (coordPartial 1 u) p +
      (coordPartial 0 n p * (coordPartial 0 u p) ^ 2 +
        2 * n p * coordPartial 0 u p * coordPartial 0 (coordPartial 0 u) p) / 2 -
      ((coordPartial 0 A p * n p + A p * coordPartial 0 n p) * (coordPartial 1 u p) ^ 2 +
        2 * A p * n p * coordPartial 1 u p * coordPartial 0 (coordPartial 1 u) p) / 2 := by
  have hd := (((hm.hasFDerivAt.fun_mul hut.hasFDerivAt).fun_mul hus.hasFDerivAt).add
    ((hn.hasFDerivAt.fun_mul (hut.hasFDerivAt.fun_mul hut.hasFDerivAt)).const_mul
      (1 / 2 : ℝ))).sub
    (((hA.hasFDerivAt.fun_mul hn.hasFDerivAt).fun_mul
      (hus.hasFDerivAt.fun_mul hus.hasFDerivAt)).const_mul (1 / 2 : ℝ))
  simp only [Pi.add_def, Pi.sub_def, coordPartial] at hd
  unfold multiplierFluxT
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

theorem multiplierFluxS_partial_s
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p)
    (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 1 (multiplierFluxS A m n u) p =
      ((coordPartial 1 A p * m p + A p * coordPartial 1 m p) * (coordPartial 1 u p) ^ 2 +
        2 * A p * m p * coordPartial 1 u p * coordPartial 1 (coordPartial 1 u) p) / 2 +
      (coordPartial 1 A p * n p + A p * coordPartial 1 n p) *
        coordPartial 0 u p * coordPartial 1 u p +
      A p * n p * coordPartial 1 (coordPartial 0 u) p * coordPartial 1 u p +
      A p * n p * coordPartial 0 u p * coordPartial 1 (coordPartial 1 u) p -
      (coordPartial 1 m p * (coordPartial 0 u p) ^ 2 +
        2 * m p * coordPartial 0 u p * coordPartial 1 (coordPartial 0 u) p) / 2 := by
  have hd := ((((hA.hasFDerivAt.fun_mul hm.hasFDerivAt).fun_mul
    (hus.hasFDerivAt.fun_mul hus.hasFDerivAt)).const_mul (1 / 2 : ℝ)).add
    (((hA.hasFDerivAt.fun_mul hn.hasFDerivAt).fun_mul hut.hasFDerivAt).fun_mul
      hus.hasFDerivAt)).sub
    ((hm.hasFDerivAt.fun_mul (hut.hasFDerivAt.fun_mul hut.hasFDerivAt)).const_mul
      (1 / 2 : ℝ))
  simp only [Pi.add_def, Pi.sub_def, coordPartial] at hd
  unfold multiplierFluxS
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

theorem multiplier_divergence_identity
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p) (hu : ContDiffOn ℝ ∞ u U)
    (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * multiplierTest m n u p =
      coordPartial 0 (multiplierFluxT A m n u) p +
      coordPartial 1 (multiplierFluxS A m n u) p +
      multiplierT B m n p * (coordPartial 0 u p) ^ 2 +
      multiplierS A C m n p * (coordPartial 1 u p) ^ 2 +
      multiplierJ A B C m n p * coordPartial 0 u p * coordPartial 1 u p := by
  have hdu (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    (((partial_contDiffOn hu hU i) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [multiplierFluxT_partial_t hA hm hn (hdu 0) (hdu 1),
    multiplierFluxS_partial_s hA hm hn (hdu 0) (hdu 1)]
  unfold multiplierOperator multiplierTest multiplierT multiplierS multiplierJ
  rw [HessianCalculus.coordPartial_mul_at hA hm 1,
    HessianCalculus.coordPartial_mul_at hA hn 0,
    HessianCalculus.coordPartial_mul_at hA hn 1,
    coordPartial_comm hu hU hp 0 1]
  ring

theorem directed_flux_factor
    (A u I : Coord → ℝ) (b lambda epsilon : ℝ) (p : Coord) :
    multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p =
      directedWeight b lambda I p *
        (-coordPartial 0 u p * coordPartial 1 u p +
          epsilon * p 0 * (coordPartial 0 u p) ^ 2 / 2 -
          epsilon * p 0 * A p * (coordPartial 1 u p) ^ 2 / 2) ∧
    multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p =
      directedWeight b lambda I p *
        (-A p * (coordPartial 1 u p) ^ 2 / 2 +
          epsilon * p 0 * A p * coordPartial 0 u p * coordPartial 1 u p +
          (coordPartial 0 u p) ^ 2 / 2) := by
  constructor <;> simp only [multiplierFluxT, multiplierFluxS, directedM, directedN] <;> ring

theorem directed_flux_edge_zero
    (A u I : Coord → ℝ) (b lambda epsilon : ℝ) (p : Coord) (hp : p 1 = b) :
    multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p = 0 ∧
    multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p = 0 := by
  obtain ⟨ht, hs⟩ := directed_flux_factor A u I b lambda epsilon p
  rw [directedWeight_edge_zero b lambda I p hp, zero_mul] at ht hs
  exact ⟨ht, hs⟩

end SmoothLocal.Weighted

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

def zeroRectangleBoundary (tl tr sb st : ℝ) (f : Coord → ℝ) : Prop :=
  (∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) ∧
    (∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0)

theorem boxPoint_mem {tl tr sb st t s : ℝ}
    (ht : t ∈ Icc tl tr) (hs : s ∈ Icc sb st) :
    boxPoint t s ∈ closedRectangle tl tr sb st := by
  simpa [boxPoint, closedRectangle] using And.intro ht hs

theorem boxPoint_hasDerivAt_t (t s : ℝ) :
    HasDerivAt (fun x => boxPoint x s) (Pi.single 0 (1 : ℝ) : Coord) t := by
  simpa [boxPoint] using
    ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (s • (Pi.single 1 (1 : ℝ) : Coord))

theorem boxPoint_hasDerivAt_s (t s : ℝ) :
    HasDerivAt (boxPoint t) (Pi.single 1 (1 : ℝ) : Coord) s := by
  change HasDerivAt (fun x : ℝ => t • (Pi.single 0 (1 : ℝ) : Coord) +
    x • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) s
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id s).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (t • (Pi.single 0 (1 : ℝ) : Coord))

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

theorem rectangle_area_integrable
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Icc tl tr ×ˢ Icc sb st) :=
    hf.comp (by unfold boxPoint; fun_prop) (fun p hp => boxPoint_mem hp.1 hp.2)
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem rectangleIntegral_swap (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ t in tl..tr, ∫ s in sb..st, f (boxPoint t s) := by
  have hi : IntegrableOn (Function.uncurry (fun t s => f (boxPoint t s)))
      (uIoc tl tr ×ˢ uIoc sb st) := by
    simpa only [uIoc_of_le ht, uIoc_of_le hs, Function.uncurry_def] using rectangle_area_integrable hf
  exact (intervalIntegral_intervalIntegral_swap hi).symm

theorem rectangleIntegral_eq_area (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ p in Ioc tl tr ×ˢ Ioc sb st, f (boxPoint p.1 p.2) := by
  rw [rectangleIntegral_swap ht hs hf]
  simp_rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs]
  have hi : IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using rectangle_area_integrable hf
  simpa only [← Measure.volume_eq_prod] using
    (setIntegral_prod (fun p : ℝ × ℝ => f (boxPoint p.1 p.2)) hi).symm

theorem rectangleIntegral_congr (ht : tl ≤ tr) (hs : sb ≤ st)
    (heq : EqOn f g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f = rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  apply intervalIntegral.integral_congr
  intro s hs'
  apply intervalIntegral.integral_congr
  intro t ht'
  exact heq (boxPoint_mem
    (by simpa only [uIcc_of_le ht] using ht')
    (by simpa only [uIcc_of_le hs] using hs'))

theorem rectangleIntegral_add (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st))
    (hg : ContinuousOn g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => f p + g p) =
      rectangleIntegral tl tr sb st f + rectangleIntegral tl tr sb st g := by
  have hfg : ContinuousOn (fun p => f p + g p) (closedRectangle tl tr sb st) := hf.add hg
  rw [rectangleIntegral_eq_area ht hs hfg,
    rectangleIntegral_eq_area ht hs hf, rectangleIntegral_eq_area ht hs hg]
  exact integral_add (rectangle_area_integrable hf) (rectangle_area_integrable hg)

variable {U : Set Coord}

theorem rectangleIntegral_partial_t_zero
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 0 f) = 0 := by
  have hinner (s : ℝ) (hs' : s ∈ Icc sb st) :
      (∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun t => coordPartial 0 f (boxPoint t s)) (uIcc tl tr) := by
      rw [uIcc_of_le ht]
      exact (partial_contDiffOn hf hU 0).continuousOn.comp
        (by unfold boxPoint; fun_prop) (fun t ht' => hbox (boxPoint_mem ht' hs'))
    have hderiv (t : ℝ) (ht' : t ∈ uIcc tl tr) :
        HasDerivAt (fun x => f (boxPoint x s)) (coordPartial 0 f (boxPoint t s)) t := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem
        (by simpa only [uIcc_of_le ht] using ht') hs')
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt t (boxPoint_hasDerivAt_t t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge s hs').1, (hedge s hs').2, sub_self] at he
    exact he
  unfold rectangleIntegral
  calc
    (∫ s in sb..st, ∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) =
        ∫ _ in sb..st, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs'
      exact hinner s (by simpa only [uIcc_of_le hs] using hs')
    _ = 0 := intervalIntegral.integral_zero

theorem rectangleIntegral_partial_s_zero
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 1 f) = 0 := by
  rw [rectangleIntegral_swap ht hs ((partial_contDiffOn hf hU 1).continuousOn.mono hbox)]
  have hinner (t : ℝ) (ht' : t ∈ Icc tl tr) :
      (∫ s in sb..st, coordPartial 1 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun s => coordPartial 1 f (boxPoint t s)) (uIcc sb st) := by
      rw [uIcc_of_le hs]
      exact (partial_contDiffOn hf hU 1).continuousOn.comp
        (by unfold boxPoint; fun_prop) (fun s hs' => hbox (boxPoint_mem ht' hs'))
    have hderiv (s : ℝ) (hs' : s ∈ uIcc sb st) :
        HasDerivAt (fun y => f (boxPoint t y)) (coordPartial 1 f (boxPoint t s)) s := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem ht'
        (by simpa only [uIcc_of_le hs] using hs'))
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge t ht').1, (hedge t ht').2, sub_self] at he
    exact he
  calc
    (∫ t in tl..tr, ∫ s in sb..st, coordPartial 1 f (boxPoint t s)) =
        ∫ _ in tl..tr, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht'
      exact hinner t (by simpa only [uIcc_of_le ht] using ht')
    _ = 0 := intervalIntegral.integral_zero

theorem multiplierFluxes_contDiffOn
    {A m n u : Coord → ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierFluxT A m n u) U ∧
      ContDiffOn ℝ ∞ (multiplierFluxS A m n u) U := by
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  constructor
  · exact (((hm.mul ht).mul hs).add
      (contDiffOn_const.mul (hn.mul (ht.pow 2)))).sub
      (contDiffOn_const.mul ((hA.mul hn).mul (hs.pow 2)))
  · exact ((contDiffOn_const.mul ((hA.mul hm).mul (hs.pow 2))).add
      (((hA.mul hn).mul ht).mul hs)).sub
      (contDiffOn_const.mul (hm.mul (ht.pow 2)))

theorem multiplierQuadratic_contDiffOn
    {A B C m n u : Coord → ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierQuadratic A B C m n u) U := by
  have hhalf {v : Coord → ℝ} (hv : ContDiffOn ℝ ∞ v U) :
      ContDiffOn ℝ ∞ (fun p => v p / 2) U :=
    hv.div contDiffOn_const (fun _ _ => two_ne_zero)
  have hmt := partial_contDiffOn hm hU 0
  have hms := partial_contDiffOn hm hU 1
  have hnt := partial_contDiffOn hn hU 0
  have hAms := partial_contDiffOn (hA.mul hm) hU 1
  have hAnt := partial_contDiffOn (hA.mul hn) hU 0
  have hAns := partial_contDiffOn (hA.mul hn) hU 1
  have hT : ContDiffOn ℝ ∞ (multiplierT B m n) U :=
    (hhalf (hms.sub hnt)).add (hB.mul hn)
  have hS : ContDiffOn ℝ ∞ (multiplierS A C m n) U :=
    ((hhalf hAms.neg).add (hhalf hAnt)).add (hC.mul hm)
  have hJ : ContDiffOn ℝ ∞ (multiplierJ A B C m n) U :=
    ((hmt.neg.add (hB.mul hm)).sub hAns).add (hC.mul hn)
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  exact ((hT.mul (ht.pow 2)).add (hS.mul (hs.pow 2))).add ((hJ.mul ht).mul hs)

theorem integrated_multiplier_identity
    {A B C m n u : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hmb : zeroRectangleBoundary tl tr sb st m)
    (hnb : zeroRectangleBoundary tl tr sb st n) :
    rectangleIntegral tl tr sb st (fun p =>
      multiplierOperator A B C u p * multiplierTest m n u p) =
        rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
  have hflux := multiplierFluxes_contDiffOn hU hA hm hn hu
  have hQ := multiplierQuadratic_contDiffOn hU hA hB hC hm hn hu
  have hFt0 : rectangleIntegral tl tr sb st (coordPartial 0 (multiplierFluxT A m n u)) = 0 := by
    apply rectangleIntegral_partial_t_zero ht hs hU hflux.1 hbox
    intro s hs'
    constructor <;> simp [multiplierFluxT, (hmb.1 s hs').1, (hmb.1 s hs').2,
      (hnb.1 s hs').1, (hnb.1 s hs').2]
  have hFs0 : rectangleIntegral tl tr sb st (coordPartial 1 (multiplierFluxS A m n u)) = 0 := by
    apply rectangleIntegral_partial_s_zero ht hs hU hflux.2 hbox
    intro t ht'
    constructor <;> simp [multiplierFluxS, (hmb.2 t ht').1, (hmb.2 t ht').2,
      (hnb.2 t ht').1, (hnb.2 t ht').2]
  have hFt := (partial_contDiffOn hflux.1 hU 0).continuousOn.mono hbox
  have hFs := (partial_contDiffOn hflux.2 hU 1).continuousOn.mono hbox
  calc
    rectangleIntegral tl tr sb st (fun p =>
        multiplierOperator A B C u p * multiplierTest m n u p) =
      rectangleIntegral tl tr sb st (fun p =>
        coordPartial 0 (multiplierFluxT A m n u) p +
          coordPartial 1 (multiplierFluxS A m n u) p + multiplierQuadratic A B C m n u p) := by
      apply rectangleIntegral_congr ht hs
      intro p hp
      have hpU := hbox hp
      have hd := multiplier_divergence_identity (B := B) (C := C)
        ((hA.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
        ((hm.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
        ((hn.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)) hu hU hpU
      dsimp only
      rw [hd]
      unfold multiplierQuadratic
      ring
    _ = rectangleIntegral tl tr sb st (coordPartial 0 (multiplierFluxT A m n u)) +
        rectangleIntegral tl tr sb st (coordPartial 1 (multiplierFluxS A m n u)) +
        rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
      have hsum : ContinuousOn (fun p => coordPartial 0 (multiplierFluxT A m n u) p +
          coordPartial 1 (multiplierFluxS A m n u) p) (closedRectangle tl tr sb st) :=
        hFt.add hFs
      rw [rectangleIntegral_add ht hs hsum (hQ.continuousOn.mono hbox),
        rectangleIntegral_add ht hs hFt hFs]
    _ = rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
      rw [hFt0, hFs0]
      ring

def cutoffM (chi : Coord → ℝ) (edge lambda : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  chi p * directedM edge lambda I p

def cutoffN (chi : Coord → ℝ) (edge lambda epsilon : ℝ) (I : Coord → ℝ) (p : Coord) : ℝ :=
  chi p * directedN edge lambda epsilon I p

theorem cutoff_test_factor
    (chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord) :
    multiplierTest (cutoffM chi edge lambda I) (cutoffN chi edge lambda epsilon I) u p =
      chi p * directedWeight edge lambda I p *
        (-coordPartial 1 u p + epsilon * p 0 * coordPartial 0 u p) := by
  unfold multiplierTest cutoffM cutoffN directedM directedN
  ring

theorem integrated_cutoff_directed_identity
    {A B C chi I u : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hI : ContDiffOn ℝ ∞ I U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hchiSides : ∀ s ∈ Icc sb st, chi (boxPoint tl s) = 0 ∧ chi (boxPoint tr s) = 0)
    (hchiBottom : ∀ t ∈ Icc tl tr, chi (boxPoint t sb) = 0)
    (lambda epsilon : ℝ) :
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p *
      multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p) =
        rectangleIntegral tl tr sb st
          (multiplierQuadratic A B C (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) := by
  have hW := directedWeight_contDiffOn st lambda hI
  have hm : ContDiffOn ℝ ∞ (cutoffM chi st lambda I) U := hchi.mul hW.neg
  have htcoord : ContDiffOn ℝ ∞ (fun p : Coord => p 0) U := contDiffOn_apply ℝ ℝ 0 U
  have hn : ContDiffOn ℝ ∞ (cutoffN chi st lambda epsilon I) U :=
    hchi.mul ((contDiffOn_const.mul htcoord).mul hW)
  have hedge : zeroRectangleBoundary tl tr sb st (cutoffM chi st lambda I) ∧
      zeroRectangleBoundary tl tr sb st (cutoffN chi st lambda epsilon I) := by
    constructor
    · constructor
      · intro s hs'
        simp [cutoffM, (hchiSides s hs').1, (hchiSides s hs').2]
      · intro t ht'
        have hz := directed_mn_edge_zero st lambda epsilon I (boxPoint t st)
          (by simp [boxPoint])
        simp [cutoffM, hchiBottom t ht', hz.1]
    · constructor
      · intro s hs'
        simp [cutoffN, (hchiSides s hs').1, (hchiSides s hs').2]
      · intro t ht'
        have hz := directed_mn_edge_zero st lambda epsilon I (boxPoint t st)
          (by simp [boxPoint])
        simp [cutoffN, hchiBottom t ht', hz.2]
  exact integrated_multiplier_identity ht hs hU hA hB hC hm hn hu hbox hedge.1 hedge.2

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem coordLinear_norm_le (L : Coord →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (Pi.single 0 1)| + |L (Pi.single 1 1)| := by
  apply L.opNorm_le_bound (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro v
  have he : v = v 0 • Pi.single 0 (1 : ℝ) + v 1 • Pi.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  have hv0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have hv1 : |v 1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1
  calc
    ‖L v‖ = |v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1)| := by
      conv_lhs => rw [he]
      simp only [map_add, map_smul, smul_eq_mul, Real.norm_eq_abs]
    _ ≤ |v 0| * |L (Pi.single 0 1)| + |v 1| * |L (Pi.single 1 1)| := by
      simpa only [abs_mul] using abs_add_le
        (v 0 * L (Pi.single 0 1)) (v 1 * L (Pi.single 1 1))
    _ ≤ ‖v‖ * |L (Pi.single 0 1)| + ‖v‖ * |L (Pi.single 1 1)| :=
      add_le_add (mul_le_mul_of_nonneg_right hv0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hv1 (abs_nonneg _))
    _ = (|L (Pi.single 0 1)| + |L (Pi.single 1 1)|) * ‖v‖ := by ring

def ellipticEdgeRaw (c : ℝ) : Coord → ℝ :=
  ellipticWeight 0 c (fun _ => 1) (fun p => p 0)

def ellipticEdgeKernel (c : ℝ) (p : Coord) : ℝ :=
  if p 1 < 0 then ellipticEdgeRaw c p else 0

def ellipticEdgeDerivative (c : ℝ) (p : Coord) : Coord →L[ℝ] ℝ :=
  if p 1 < 0 then fderiv ℝ (ellipticEdgeRaw c) p else 0

def ellipticEdgeDerivativeConstant (c : ℝ) : ℝ :=
  4 * (3 + (2 * transitionDerivativeBound / c) * (1 + c))

theorem ellipticEdgeRaw_contDiffOn (c : ℝ) :
    ContDiffOn ℝ ∞ (ellipticEdgeRaw c) {p | p 1 < 0} := by
  exact ellipticWeight_contDiffOn 0 c contDiffOn_const
    (contDiffOn_apply ℝ ℝ 0 _) (fun _ h => h)

theorem ellipticEdgeHalfPlane_isOpen : IsOpen {p : Coord | p 1 < 0} :=
  isOpen_lt (continuous_apply 1) continuous_const

theorem ellipticEdgeKernel_norm_le (c : ℝ) (p : Coord) :
    ‖ellipticEdgeKernel c p‖ ≤ |p 1| ^ 6 := by
  unfold ellipticEdgeKernel
  split_ifs with hp
  · unfold ellipticEdgeRaw
    rw [Real.norm_eq_abs, abs_of_nonneg (ellipticWeight_nonneg _ _ _ _ _)]
    have h := ellipticWeight_le_distance_six 0 c (fun _ => 1) (fun p => p 0) p
      ⟨by norm_num, le_rfl⟩
    simpa only [edgeDistance, zero_sub, abs_of_neg hp] using h
  · simp

theorem ellipticEdgeRaw_partial_bound {c : ℝ} (hc : 0 < c) {p : Coord}
    (hp : p 1 < 0) (i : Fin 2) :
    |coordPartial i (ellipticEdgeRaw c) p| ≤
      (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 := by
  have hd : 0 < edgeDistance 0 p := by simpa only [edgeDistance, zero_sub] using neg_pos.mpr hp
  have hk : |coordPartial i (fun q : Coord => q 0) p| ≤ (1 : ℝ) := by
    unfold coordPartial
    rw [(hasFDerivAt_apply (𝕜 := ℝ) 0 p).fderiv]
    fin_cases i <;> norm_num [Pi.single_apply]
  have hx : |coordPartial i (fun _ : Coord => (1 : ℝ)) p| ≤ (0 : ℝ) := by
    simp [coordPartial]
  have hh := ellipticWeight_partial_bound (b := 0) (c := c) (M := 1) (X := 0)
    hc hd (by norm_num) (differentiableAt_const 1)
    (differentiableAt_apply (𝕜 := ℝ) 0 p) ⟨by norm_num, le_rfl⟩ i hx hk
  have hsqrt : Real.sqrt (ellipticEdgeRaw c p) ≤ (edgeDistance 0 p) ^ 3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(pow_pos hd 3).le, ?_⟩
    dsimp only [ellipticEdgeRaw]
    convert ellipticWeight_le_distance_six 0 c (fun _ => 1) (fun p => p 0) p
      ⟨by norm_num, le_rfl⟩ using 1
    ring
  have hP : 0 ≤ (2 * transitionDerivativeBound / c) * (1 + c) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) transitionDerivativeBound_pos.le) hc.le)
      (by linarith)
  calc
    _ ≤ 2 * Real.sqrt (ellipticEdgeRaw c p) *
        (3 * edgeDistance 0 p ^ 2 + edgeDistance 0 p ^ 3 * 0 +
          edgeDistance 0 p ^ 2 * ((2 * transitionDerivativeBound / c) * (1 + c))) := hh
    _ ≤ 2 * edgeDistance 0 p ^ 3 *
        (3 * edgeDistance 0 p ^ 2 + edgeDistance 0 p ^ 3 * 0 +
          edgeDistance 0 p ^ 2 * ((2 * transitionDerivativeBound / c) * (1 + c))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
        (by positivity)
    _ = _ := by unfold ellipticEdgeDerivativeConstant edgeDistance; ring

theorem ellipticEdgeDerivative_norm_le {c : ℝ} (hc : 0 < c) (p : Coord) :
    ‖ellipticEdgeDerivative c p‖ ≤ ellipticEdgeDerivativeConstant c * |p 1| ^ 5 := by
  have hC : 0 ≤ ellipticEdgeDerivativeConstant c := by
    unfold ellipticEdgeDerivativeConstant
    have := transitionDerivativeBound_pos
    positivity
  unfold ellipticEdgeDerivative
  split_ifs with hp
  · calc
      _ ≤ |coordPartial 0 (ellipticEdgeRaw c) p| +
          |coordPartial 1 (ellipticEdgeRaw c) p| := coordLinear_norm_le _
      _ ≤ (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 +
          (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 :=
        add_le_add (ellipticEdgeRaw_partial_bound hc hp 0)
          (ellipticEdgeRaw_partial_bound hc hp 1)
      _ = _ := by rw [abs_of_neg hp]; ring
  · simp only [norm_zero]
    exact mul_nonneg hC (pow_nonneg (abs_nonneg _) _)

theorem ellipticEdgeKernel_hasFDerivAt_boundary (c : ℝ) {p : Coord} (hp : p 1 = 0) :
    HasFDerivAt (ellipticEdgeKernel c) (0 : Coord →L[ℝ] ℝ) p := by
  have hpzero : ellipticEdgeKernel c p = 0 := by simp [ellipticEdgeKernel, hp]
  rw [hasFDerivAt_iff_tendsto]
  simp only [hpzero, sub_zero, zero_apply]
  apply squeeze_zero (fun q => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · intro q
    have hcoord : |q 1| ≤ ‖q - p‖ := by
      simpa only [Pi.sub_apply, hp, sub_zero, Real.norm_eq_abs] using norm_le_pi_norm (q - p) 1
    have hb : ‖ellipticEdgeKernel c q‖ ≤ ‖q - p‖ ^ 6 :=
      (ellipticEdgeKernel_norm_le c q).trans (pow_le_pow_left₀ (abs_nonneg _) hcoord 6)
    calc
      ‖q - p‖⁻¹ * ‖ellipticEdgeKernel c q‖ ≤ ‖q - p‖⁻¹ * ‖q - p‖ ^ 6 :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
      _ = ‖q - p‖ ^ 5 := by
        by_cases hz : ‖q - p‖ = 0
        · simp [hz]
        · field_simp [hz]
  · have hcont : Continuous (fun q : Coord => ‖q - p‖ ^ 5) :=
      (continuous_id.sub continuous_const).norm.pow 5
    simpa using hcont.tendsto p

theorem ellipticEdgeKernel_hasFDerivAt (c : ℝ) (p : Coord) :
    HasFDerivAt (ellipticEdgeKernel c) (ellipticEdgeDerivative c p) p := by
  rcases lt_trichotomy (p 1) 0 with hp | hp | hp
  · have hn := ellipticEdgeHalfPlane_isOpen.mem_nhds hp
    have hd := ((ellipticEdgeRaw_contDiffOn c).contDiffAt hn).differentiableAt (by simp)
    have he : ellipticEdgeKernel c =ᶠ[𝓝 p] ellipticEdgeRaw c := by
      filter_upwards [hn] with q hq
      simp [ellipticEdgeKernel, hq]
    simpa only [ellipticEdgeDerivative, hp, ite_eq_left] using hd.hasFDerivAt.congr_of_eventuallyEq he
  · simpa [ellipticEdgeDerivative, hp] using ellipticEdgeKernel_hasFDerivAt_boundary c hp
  · have hn : {q : Coord | 0 < q 1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp
    have he : ellipticEdgeKernel c =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hn] with q hq
      simp [ellipticEdgeKernel, not_lt_of_ge hq.le]
    simpa [ellipticEdgeDerivative, not_lt_of_ge hp.le] using
      (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p).congr_of_eventuallyEq he

theorem ellipticEdgeDerivative_continuous {c : ℝ} (hc : 0 < c) :
    Continuous (ellipticEdgeDerivative c) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases lt_trichotomy (p 1) 0 with hp | hp | hp
  · have hn := ellipticEdgeHalfPlane_isOpen.mem_nhds hp
    have hd := ((ellipticEdgeRaw_contDiffOn c).continuousOn_fderiv_of_isOpen
      ellipticEdgeHalfPlane_isOpen (by simp)).continuousAt hn
    apply hd.congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    simp [ellipticEdgeDerivative, hq]
  · have hz : ellipticEdgeDerivative c p = 0 := by simp [ellipticEdgeDerivative, hp]
    change Tendsto (ellipticEdgeDerivative c) (𝓝 p) (𝓝 (ellipticEdgeDerivative c p))
    rw [hz, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (ellipticEdgeDerivative_norm_le hc)
    have hcont : Continuous (fun q : Coord => ellipticEdgeDerivativeConstant c * |q 1| ^ 5) :=
      continuous_const.mul (((continuous_apply 1).abs).pow 5)
    simpa [hp] using hcont.tendsto p
  · have hn : {q : Coord | 0 < q 1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp
    apply (continuousAt_const (y := (0 : Coord →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    simp [ellipticEdgeDerivative, not_lt_of_ge hq.le]

theorem ellipticEdgeKernel_contDiff_one {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 1 (ellipticEdgeKernel c) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨ellipticEdgeDerivative c, ellipticEdgeDerivative_continuous hc,
      ellipticEdgeKernel_hasFDerivAt c⟩

def ellipticWeightC1 (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  chi p ^ 2 * ellipticEdgeKernel c ![K p, p 1 - b]

theorem ellipticWeightC1_eq {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : p 1 ≤ b) : ellipticWeightC1 b c chi K p = ellipticWeight b c chi K p := by
  rcases hp.eq_or_lt with he | hl
  · simp [ellipticWeightC1, ellipticEdgeKernel, ellipticWeight, edgeDistance, he]
  · have hs : p 1 - b < 0 := sub_neg.mpr hl
    simp only [ellipticWeightC1, ellipticEdgeKernel, Matrix.cons_val_one, Matrix.cons_val_zero,
      hs, ite_eq_left, ellipticEdgeRaw, ellipticWeight, edgeDistance]
    simp only [one_pow, mul_one]
    have hd : 0 - (p 1 - b) = b - p 1 := by ring
    rw [hd]
    ring

theorem ellipticWeightC1_zero {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : b ≤ p 1) : ellipticWeightC1 b c chi K p = 0 := by
  simp [ellipticWeightC1, ellipticEdgeKernel, not_lt_of_ge (sub_nonneg.mpr hp)]

theorem ellipticWeightC1_nonneg (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    0 ≤ ellipticWeightC1 b c chi K p := by
  by_cases hp : p 1 ≤ b
  · rw [ellipticWeightC1_eq hp]
    exact ellipticWeight_nonneg _ _ _ _ _
  · rw [ellipticWeightC1_zero (lt_of_not_ge hp).le]

theorem ellipticWeightC1_le_distance_six (b c : ℝ) (chi K : Coord → ℝ) (p : Coord)
    (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    ellipticWeightC1 b c chi K p ≤ edgeDistance b p ^ 6 := by
  by_cases hp : p 1 ≤ b
  · rw [ellipticWeightC1_eq hp]
    exact ellipticWeight_le_distance_six _ _ _ _ _ hchi
  · rw [ellipticWeightC1_zero (lt_of_not_ge hp).le]
    positivity

theorem ellipticWeightC1_partial_eq {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : p 1 < b) (i : Fin 2) :
    coordPartial i (ellipticWeightC1 b c chi K) p =
      coordPartial i (ellipticWeight b c chi K) p := by
  have he : ellipticWeightC1 b c chi K =ᶠ[𝓝 p] ellipticWeight b c chi K := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hp] with q hq
    exact ellipticWeightC1_eq hq.le
  unfold coordPartial
  rw [he.fderiv_eq]

theorem ellipticWeightC1_contDiffOn {b c : ℝ} {chi K : Coord → ℝ} {U : Set Coord}
    (hc : 0 < c) (hchi : ContDiffOn ℝ 1 chi U) (hK : ContDiffOn ℝ 1 K U) :
    ContDiffOn ℝ 1 (ellipticWeightC1 b c chi K) U := by
  have hmap : ContDiffOn ℝ 1 (fun p : Coord => ![K p, p 1 - b]) U := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · simpa using hK
    · simpa using (contDiffOn_apply ℝ ℝ 1 U).sub contDiffOn_const
  exact (hchi.pow 2).mul ((ellipticEdgeKernel_contDiff_one hc).comp_contDiffOn hmap)

end SmoothLocal.Weighted

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
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def ellipticErrorT (B v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 v p - v p * B p

def ellipticErrorS (A C v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (fun q => A q * v q) p - v p * C p

def ellipticEnergy (A v u : Coord → ℝ) (p : Coord) : ℝ :=
  v p * ((coordPartial 0 u p) ^ 2 + A p * (coordPartial 1 u p) ^ 2)

def ellipticError (A B C v u : Coord → ℝ) (p : Coord) : ℝ :=
  u p * (ellipticErrorT B v p * coordPartial 0 u p +
    ellipticErrorS A C v p * coordPartial 1 u p)

def ellipticFluxT (v u : Coord → ℝ) (p : Coord) : ℝ :=
  -(v p * u p * coordPartial 0 u p)

def ellipticFluxS (A v u : Coord → ℝ) (p : Coord) : ℝ :=
  -(A p * v p * u p * coordPartial 1 u p)

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem ellipticFluxT_partial_t
    (hv : DifferentiableAt ℝ v p) (hu : DifferentiableAt ℝ u p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p) :
    coordPartial 0 (ellipticFluxT v u) p =
      -(coordPartial 0 v p * u p * coordPartial 0 u p +
        v p * (coordPartial 0 u p) ^ 2 +
        v p * u p * coordPartial 0 (coordPartial 0 u) p) := by
  have hd := ((hv.hasFDerivAt.fun_mul hu.hasFDerivAt).fun_mul hut.hasFDerivAt).neg
  change HasFDerivAt (fun x => -(v x * u x * coordPartial 0 u x)) _ p at hd
  simp only [coordPartial] at hd
  change coordPartial 0 (fun q => -(v q * u q * coordPartial 0 u q)) p = _
  simp only [coordPartial]
  rw [hd.fderiv]
  simp only [neg_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem ellipticFluxS_partial_s
    (hA : DifferentiableAt ℝ A p) (hv : DifferentiableAt ℝ v p)
    (hu : DifferentiableAt ℝ u p) (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 1 (ellipticFluxS A v u) p =
      -(coordPartial 1 (fun q => A q * v q) p * u p * coordPartial 1 u p +
        A p * v p * (coordPartial 1 u p) ^ 2 +
        A p * v p * u p * coordPartial 1 (coordPartial 1 u) p) := by
  have hAv : DifferentiableAt ℝ (fun q => A q * v q) p := hA.mul hv
  have hd := ((hAv.hasFDerivAt.fun_mul hu.hasFDerivAt).fun_mul hus.hasFDerivAt).neg
  change HasFDerivAt (fun x => -(A x * v x * u x * coordPartial 1 u x)) _ p at hd
  simp only [coordPartial] at hd
  change coordPartial 1 (fun q => -(A q * v q * u q * coordPartial 1 u q)) p = _
  simp only [coordPartial]
  rw [hd.fderiv]
  simp only [neg_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem elliptic_divergence_identity
    (hA : DifferentiableAt ℝ A p) (hv : DifferentiableAt ℝ v p)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * (-v p * u p) =
      coordPartial 0 (ellipticFluxT v u) p + coordPartial 1 (ellipticFluxS A v u) p +
        ellipticEnergy A v u p + ellipticError A B C v u p := by
  have hud : DifferentiableAt ℝ u p :=
    (hu.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdu (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    ((partial_contDiffOn hu hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  rw [ellipticFluxT_partial_t hv hud (hdu 0), ellipticFluxS_partial_s hA hv hud (hdu 1)]
  unfold multiplierOperator ellipticEnergy ellipticError ellipticErrorT ellipticErrorS
  ring

theorem ellipticOperator_contDiffOn
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierOperator A B C u) U := by
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  exact (((partial_contDiffOn ht hU 0).add (hA.mul (partial_contDiffOn hs hU 1))).add
    (hB.mul ht)).add (hC.mul hs)

theorem rectangleIntegral_neg (tl tr sb st : ℝ) (g : Coord → ℝ) :
    rectangleIntegral tl tr sb st (fun p => -g p) = -rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_neg]

theorem rectangleIntegral_const_mul (tl tr sb st c : ℝ) (g : Coord → ℝ) :
    rectangleIntegral tl tr sb st (fun p => c * g p) = c * rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_const_mul]

variable {tl tr sb st : ℝ}

end SmoothLocal.Weighted

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

theorem weighted_young (w x y : ℝ) (hw : 0 < w) :
    |x * y| ≤ (w * x ^ 2 + y ^ 2 / w) / 2 := by
  have hminus : 0 ≤ w * x ^ 2 - 2 * x * y + y ^ 2 / w := by
    have hn := div_nonneg (sq_nonneg (w * x - y)) hw.le
    have he : (w * x - y) ^ 2 / w = w * x ^ 2 - 2 * x * y + y ^ 2 / w := by
      field_simp [ne_of_gt hw]
      ring
    rw [he] at hn
    exact hn
  have hplus : 0 ≤ w * x ^ 2 + 2 * x * y + y ^ 2 / w := by
    have hn := div_nonneg (sq_nonneg (w * x + y)) hw.le
    have he : (w * x + y) ^ 2 / w = w * x ^ 2 + 2 * x * y + y ^ 2 / w := by
      field_simp [ne_of_gt hw]
      ring
    rw [he] at hn
    exact hn
  apply abs_le.mpr
  constructor <;> nlinarith

theorem elliptic_error_scalar_bound
    (A v u x y eT eS H : ℝ) (hv : 0 < v) (hA : 0 < A)
    (hratio : eT ^ 2 / v + eS ^ 2 / (A * v) ≤ H) :
    |u * (eT * x + eS * y)| ≤ v * (x ^ 2 + A * y ^ 2) / 2 + H * u ^ 2 / 2 := by
  have hx := weighted_young v x (u * eT) hv
  have hy := weighted_young (A * v) y (u * eS) (mul_pos hA hv)
  calc
    |u * (eT * x + eS * y)| = |x * (u * eT) + y * (u * eS)| := by congr 1; ring
    _ ≤ |x * (u * eT)| + |y * (u * eS)| := abs_add_le _ _
    _ ≤ (v * x ^ 2 + (u * eT) ^ 2 / v) / 2 +
        (A * v * y ^ 2 + (u * eS) ^ 2 / (A * v)) / 2 := add_le_add hx hy
    _ = v * (x ^ 2 + A * y ^ 2) / 2 +
        (eT ^ 2 / v + eS ^ 2 / (A * v)) * u ^ 2 / 2 := by
      field_simp [ne_of_gt hv, ne_of_gt hA]
      ring
    _ ≤ v * (x ^ 2 + A * y ^ 2) / 2 + H * u ^ 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hratio (sq_nonneg u)]

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem ellipticErrors_zero_of_nonneg
    (hU : IsOpen U) (hp : p ∈ U) (hA : DifferentiableAt ℝ A p)
    (hv : DifferentiableAt ℝ v p) (hvn : ∀ q ∈ U, 0 ≤ v q) (hzero : v p = 0) :
    ellipticErrorT B v p = 0 ∧ ellipticErrorS A C v p = 0 := by
  have hmin : IsLocalMin v p := by
    change ∀ᶠ q in 𝓝 p, v p ≤ v q
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [hzero] using hvn q hq
  have hdv := hmin.fderiv_eq_zero
  have hpv (i : Fin 2) : coordPartial i v p = 0 := by simp [coordPartial, hdv]
  constructor
  · simp [ellipticErrorT, hpv 0, hzero]
  · rw [ellipticErrorS, HessianCalculus.coordPartial_mul_at hA hv 1]
    simp [hpv 1, hzero]

theorem ellipticError_abs_bound
    (hU : IsOpen U) (hp : p ∈ U) (hA : DifferentiableAt ℝ A p)
    (hv : DifferentiableAt ℝ v p) (hvn : ∀ q ∈ U, 0 ≤ v q)
    (H : ℝ) (hH : 0 ≤ H)
    (hpos : 0 < v p → 0 < A p)
    (hratio : 0 < v p → (ellipticErrorT B v p) ^ 2 / v p +
      (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤ H) :
    |ellipticError A B C v u p| ≤ ellipticEnergy A v u p / 2 + H * (u p) ^ 2 / 2 := by
  by_cases hzero : v p = 0
  · have hz := ellipticErrors_zero_of_nonneg (B := B) (C := C) hU hp hA hv hvn hzero
    simp only [ellipticError, ellipticEnergy, hz.1, hz.2, hzero,
      zero_mul, add_zero, mul_zero, abs_zero, zero_div, zero_add]
    exact div_nonneg (mul_nonneg hH (sq_nonneg _)) (by norm_num)
  · have hvpos : 0 < v p := lt_of_le_of_ne (hvn p hp) (Ne.symm hzero)
    exact elliptic_error_scalar_bound (A p) (v p) (u p)
      (coordPartial 0 u p) (coordPartial 1 u p)
      (ellipticErrorT B v p) (ellipticErrorS A C v p) H hvpos (hpos hvpos) (hratio hvpos)

theorem ellipticEnergy_nonneg (A v u : Coord → ℝ) (p : Coord)
    (hv : 0 ≤ v p) (hA : 0 < v p → 0 < A p) : 0 ≤ ellipticEnergy A v u p := by
  by_cases hz : v p = 0
  · simp [ellipticEnergy, hz]
  · have hvpos : 0 < v p := lt_of_le_of_ne hv (Ne.symm hz)
    exact mul_nonneg hv (add_nonneg (sq_nonneg _) (mul_nonneg (hA hvpos).le (sq_nonneg _)))

variable {tl tr sb st : ℝ}

theorem rectangleIntegral_sub {F G : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => F p - G p) =
      rectangleIntegral tl tr sb st F - rectangleIntegral tl tr sb st G := by
  simp only [sub_eq_add_neg]
  have hneg : ContinuousOn (fun p => -G p) (closedRectangle tl tr sb st) := hG.neg
  rw [rectangleIntegral_add ht hs hF hneg, rectangleIntegral_neg]

theorem rectangleIntegral_mono {F G : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hle : ∀ p ∈ closedRectangle tl tr sb st, F p ≤ G p) :
    rectangleIntegral tl tr sb st F ≤ rectangleIntegral tl tr sb st G := by
  rw [rectangleIntegral_eq_area ht hs hF, rectangleIntegral_eq_area ht hs hG]
  apply setIntegral_mono_on (rectangle_area_integrable hF) (rectangle_area_integrable hG)
    (measurableSet_Ioc.prod measurableSet_Ioc)
  intro p hp
  exact hle (boxPoint p.1 p.2) (boxPoint_mem
    (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2))

end SmoothLocal.Weighted

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

variable {U : Set Coord} {f : Coord → ℝ}

theorem coordPartial_continuousOn_one (hf : ContDiffOn ℝ 1 f U)
    (hU : IsOpen U) (i : Fin 2) : ContinuousOn (coordPartial i f) U := by
  have hd : ContDiffOn ℝ 0 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  exact (hd.clm_apply contDiffOn_const).continuousOn

variable {tl tr sb st : ℝ}

theorem rectangleIntegral_partial_t_zero_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 0 f) = 0 := by
  have hinner (s : ℝ) (hs' : s ∈ Icc sb st) :
      (∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun t => coordPartial 0 f (boxPoint t s)) (uIcc tl tr) := by
      rw [uIcc_of_le ht]
      exact (coordPartial_continuousOn_one hf hU 0).comp
        (by unfold boxPoint; fun_prop) (fun t ht' => hbox (boxPoint_mem ht' hs'))
    have hderiv (t : ℝ) (ht' : t ∈ uIcc tl tr) :
        HasDerivAt (fun x => f (boxPoint x s)) (coordPartial 0 f (boxPoint t s)) t := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem
        (by simpa only [uIcc_of_le ht] using ht') hs')
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt t (boxPoint_hasDerivAt_t t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge s hs').1, (hedge s hs').2, sub_self] at he
    exact he
  unfold rectangleIntegral
  calc
    (∫ s in sb..st, ∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) =
        ∫ _ in sb..st, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs'
      exact hinner s (by simpa only [uIcc_of_le hs] using hs')
    _ = 0 := intervalIntegral.integral_zero

theorem rectangleIntegral_partial_s_zero_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 1 f) = 0 := by
  rw [rectangleIntegral_swap ht hs ((coordPartial_continuousOn_one hf hU 1).mono hbox)]
  have hinner (t : ℝ) (ht' : t ∈ Icc tl tr) :
      (∫ s in sb..st, coordPartial 1 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun s => coordPartial 1 f (boxPoint t s)) (uIcc sb st) := by
      rw [uIcc_of_le hs]
      exact (coordPartial_continuousOn_one hf hU 1).comp
        (by unfold boxPoint; fun_prop) (fun s hs' => hbox (boxPoint_mem ht' hs'))
    have hderiv (s : ℝ) (hs' : s ∈ uIcc sb st) :
        HasDerivAt (fun y => f (boxPoint t y)) (coordPartial 1 f (boxPoint t s)) s := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem ht'
        (by simpa only [uIcc_of_le hs] using hs'))
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
      exact hd.hasFDerivAt.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge t ht').1, (hedge t ht').2, sub_self] at he
    exact he
  calc
    (∫ t in tl..tr, ∫ s in sb..st, coordPartial 1 f (boxPoint t s)) =
        ∫ _ in tl..tr, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht'
      exact hinner t (by simpa only [uIcc_of_le ht] using ht')
    _ = 0 := intervalIntegral.integral_zero

variable {A B C v u : Coord → ℝ}

theorem elliptic_fields_C1
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ 1 (ellipticFluxT v u) U ∧
    ContDiffOn ℝ 1 (ellipticFluxS A v u) U ∧
    ContinuousOn (ellipticEnergy A v u) U ∧
    ContinuousOn (ellipticError A B C v u) U := by
  have hA1 : ContDiffOn ℝ 1 A U := hA.of_le (by simp)
  have hu1 : ContDiffOn ℝ 1 u U := hu.of_le (by simp)
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  have ht1 : ContDiffOn ℝ 1 (coordPartial 0 u) U := ht.of_le (by simp)
  have hs1 : ContDiffOn ℝ 1 (coordPartial 1 u) U := hs.of_le (by simp)
  have hEt : ContinuousOn (ellipticErrorT B v) U :=
    (coordPartial_continuousOn_one hv hU 0).sub (hv.continuousOn.mul hB.continuousOn)
  have hEs : ContinuousOn (ellipticErrorS A C v) U :=
    (coordPartial_continuousOn_one (hA1.mul hv) hU 1).sub
      (hv.continuousOn.mul hC.continuousOn)
  exact ⟨((hv.mul hu1).mul ht1).neg, (((hA1.mul hv).mul hu1).mul hs1).neg,
    hv.continuousOn.mul ((ht.continuousOn.pow 2).add
      (hA.continuousOn.mul (hs.continuousOn.pow 2))),
    hu.continuousOn.mul ((hEt.mul ht.continuousOn).add (hEs.mul hs.continuousOn))⟩

theorem integrated_elliptic_identity_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v) :
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
      rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
  obtain ⟨hFt, hFs, hE, hErr⟩ := elliptic_fields_C1 hU hA hB hC hv hu
  have htzero : rectangleIntegral tl tr sb st (coordPartial 0 (ellipticFluxT v u)) = 0 := by
    apply rectangleIntegral_partial_t_zero_C1 ht hs hU hFt hbox
    intro s hs'
    constructor <;> simp [ellipticFluxT, (hboundary.1 s hs').1, (hboundary.1 s hs').2]
  have hszero : rectangleIntegral tl tr sb st (coordPartial 1 (ellipticFluxS A v u)) = 0 := by
    apply rectangleIntegral_partial_s_zero_C1 ht hs hU hFs hbox
    intro t ht'
    constructor <;> simp [ellipticFluxS, (hboundary.2 t ht').1, (hboundary.2 t ht').2]
  have hdt := (coordPartial_continuousOn_one hFt hU 0).mono hbox
  have hds := (coordPartial_continuousOn_one hFs hU 1).mono hbox
  calc
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
        rectangleIntegral tl tr sb st (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p + ellipticEnergy A v u p +
          ellipticError A B C v u p) := by
      apply rectangleIntegral_congr ht hs
      intro p hp
      exact elliptic_divergence_identity (B := B) (C := C)
        ((hA.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp))
        ((hv.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp)) hu hU (hbox hp)
    _ = rectangleIntegral tl tr sb st (coordPartial 0 (ellipticFluxT v u)) +
        rectangleIntegral tl tr sb st (coordPartial 1 (ellipticFluxS A v u)) +
        rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
      have hsum : ContinuousOn (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p) (closedRectangle tl tr sb st) :=
        hdt.add hds
      have hsumE : ContinuousOn (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p + ellipticEnergy A v u p)
          (closedRectangle tl tr sb st) := hsum.add (hE.mono hbox)
      rw [rectangleIntegral_add ht hs hsumE (hErr.mono hbox),
        rectangleIntegral_add ht hs hsum (hE.mono hbox),
        rectangleIntegral_add ht hs hdt hds]
    _ = rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
      rw [htzero, hszero]
      ring

theorem integrated_elliptic_equation_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p) :
    rectangleIntegral tl tr sb st (ellipticEnergy A v u) =
      -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) -
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
  have hid := integrated_elliptic_identity_C1 ht hs hU hA hB hC hv hu hbox hboundary
  have hsource : rectangleIntegral tl tr sb st
      (fun p => multiplierOperator A B C u p * (-v p * u p)) =
      -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) := by
    calc
      rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
          rectangleIntegral tl tr sb st (fun p => -(v p * u p * f p)) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        dsimp only
        rw [hEq p (hbox hp)]
        ring
      _ = -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) :=
        rectangleIntegral_neg tl tr sb st _
  linarith

theorem integrated_elliptic_energy_bound_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p)
    (V H : ℝ) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hvn : ∀ p ∈ U, 0 ≤ v p)
    (hvV : ∀ p ∈ closedRectangle tl tr sb st, v p ≤ V)
    (hpos : ∀ p ∈ closedRectangle tl tr sb st, 0 < v p → 0 < A p)
    (hratio : ∀ p ∈ closedRectangle tl tr sb st, 0 < v p →
      (ellipticErrorT B v p) ^ 2 / v p + (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤ H) :
    rectangleIntegral tl tr sb st (ellipticEnergy A v u) ≤
      V * rectangleIntegral tl tr sb st (fun p => (f p) ^ 2) +
        (V + H) * rectangleIntegral tl tr sb st (fun p => (u p) ^ 2) := by
  have hf : ContDiffOn ℝ ∞ f U :=
    (ellipticOperator_contDiffOn hU hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  obtain ⟨_, _, hE, hErr⟩ := elliptic_fields_C1 hU hA hB hC hv hu
  have hSource : ContinuousOn (fun p => v p * u p * f p) U :=
    (hv.continuousOn.mul hu.continuousOn).mul hf.continuousOn
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      -(v p * u p * f p) - ellipticError A B C v u p ≤
        (1 / 2 : ℝ) * ellipticEnergy A v u p +
          ((V + H) / 2) * (u p) ^ 2 + (V / 2) * (f p) ^ 2 := by
    have hpU := hbox hp
    have hErrBound := ellipticError_abs_bound (u := u) hU hpU
      ((hA.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
      ((hv.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp))
      hvn H hH (hpos p hp) (hratio p hp)
    have hyoung : -(u p * f p) ≤ ((u p) ^ 2 + (f p) ^ 2) / 2 := by
      nlinarith [sq_nonneg (u p + f p)]
    have hm := mul_le_mul_of_nonneg_left hyoung (hvn p hpU)
    have hcost := mul_le_mul (hvV p hp)
      (le_refl (((u p) ^ 2 + (f p) ^ 2) / 2))
      (div_nonneg (add_nonneg (sq_nonneg (u p)) (sq_nonneg (f p)))
        (by norm_num : (0 : ℝ) ≤ 2)) hV
    have hsource : -(v p * u p * f p) ≤ V * ((u p) ^ 2 + (f p) ^ 2) / 2 := by
      nlinarith [hm, hcost]
    nlinarith [hsource, neg_le_abs (ellipticError A B C v u p)]
  have hEhalf : ContinuousOn (fun p => (1 / 2 : ℝ) * ellipticEnergy A v u p)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul hE).mono hbox
  have hUhalf : ContinuousOn (fun p => ((V + H) / 2) * (u p) ^ 2)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul (hu.continuousOn.pow 2)).mono hbox
  have hFhalf : ContinuousOn (fun p => (V / 2) * (f p) ^ 2)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul (hf.continuousOn.pow 2)).mono hbox
  have hNegSource : ContinuousOn (fun p => -(v p * u p * f p)) U := hSource.neg
  have hi := rectangleIntegral_mono ht hs
    ((hNegSource.sub hErr).mono hbox) ((hEhalf.add hUhalf).add hFhalf) hpoint
  simp only [Pi.add_def, Pi.sub_def] at hi
  have hsum : ContinuousOn (fun p => (1 / 2 : ℝ) * ellipticEnergy A v u p +
      ((V + H) / 2) * (u p) ^ 2) (closedRectangle tl tr sb st) := hEhalf.add hUhalf
  have heq := integrated_elliptic_equation_C1 ht hs hU hA hB hC hv hu hbox hboundary hEq
  have hleft : rectangleIntegral tl tr sb st
      (fun p => -(v p * u p * f p) - ellipticError A B C v u p) =
      rectangleIntegral tl tr sb st (ellipticEnergy A v u) := by
    rw [rectangleIntegral_sub ht hs (hNegSource.mono hbox) (hErr.mono hbox), rectangleIntegral_neg]
    exact heq.symm
  rw [hleft,
    rectangleIntegral_add ht hs hsum hFhalf,
    rectangleIntegral_add ht hs hEhalf hUhalf,
    rectangleIntegral_const_mul tl tr sb st (1 / 2 : ℝ) (ellipticEnergy A v u),
    rectangleIntegral_const_mul tl tr sb st ((V + H) / 2) (fun p => (u p) ^ 2),
    rectangleIntegral_const_mul tl tr sb st (V / 2) (fun p => (f p) ^ 2)] at hi
  nlinarith

end SmoothLocal.Weighted

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

theorem ellipticRatioConstant_nonneg {D c Cv M : ℝ}
    (hD : 0 ≤ D) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ ellipticRatioConstant D c Cv M := by
  unfold ellipticRatioConstant
  positivity

theorem square_bound_of_abs_bound {x R : ℝ} (hx : |x| ≤ R) :
    x ^ 2 ≤ R ^ 2 := by
  calc
    x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2

theorem elliptic_ratio_scalar
    {d D c Cv M v vt vs A As B C : ℝ}
    (hd : 0 < d) (hdD : d ≤ D) (hc : 0 < c) (hCv : 0 ≤ Cv) (hM : 0 ≤ M)
    (hv : 0 < v) (hvd : v ≤ d ^ 6)
    (hvt : |vt| ≤ Cv * Real.sqrt v * (d ^ 2 + d ^ 3))
    (hvs : |vs| ≤ Cv * Real.sqrt v * (d ^ 2 + d ^ 3))
    (hAlo : c * d ≤ A) (hAhi : |A| ≤ M)
    (hAs : |As| ≤ M) (hB : |B| ≤ M) (hC : |C| ≤ M) :
    (vt - v * B) ^ 2 / v + (As * v + A * vs - v * C) ^ 2 / (A * v) ≤
      ellipticRatioConstant D c Cv M := by
  have hD : 0 ≤ D := hd.le.trans hdD
  have hA : 0 < A := (mul_pos hc hd).trans_le hAlo
  have hAM : A ≤ M := (le_abs_self A).trans hAhi
  let W : ℝ := Cv ^ 2 * (d ^ 2 + d ^ 3) ^ 2
  have hW : 0 ≤ W := mul_nonneg (pow_nonneg hCv 2) (sq_nonneg _)
  have hvt2 : vt ^ 2 ≤ v * W := by
    calc
      vt ^ 2 ≤ (Cv * Real.sqrt v * (d ^ 2 + d ^ 3)) ^ 2 :=
        square_bound_of_abs_bound hvt
      _ = Cv ^ 2 * (Real.sqrt v) ^ 2 * (d ^ 2 + d ^ 3) ^ 2 := by ring
      _ = v * W := by rw [Real.sq_sqrt hv.le]; dsimp [W]; ring
  have hvs2 : vs ^ 2 ≤ v * W := by
    calc
      vs ^ 2 ≤ (Cv * Real.sqrt v * (d ^ 2 + d ^ 3)) ^ 2 :=
        square_bound_of_abs_bound hvs
      _ = Cv ^ 2 * (Real.sqrt v) ^ 2 * (d ^ 2 + d ^ 3) ^ 2 := by ring
      _ = v * W := by rw [Real.sq_sqrt hv.le]; dsimp [W]; ring
  have hB2 := square_bound_of_abs_bound hB
  have hb : |As - C| ≤ 2 * M := by
    calc
      |As - C| ≤ |As| + |C| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le As 0 C
      _ ≤ M + M := add_le_add hAs hC
      _ = 2 * M := by ring
  have hb2 : (As - C) ^ 2 ≤ 4 * M ^ 2 := by
    nlinarith only [square_bound_of_abs_bound hb]
  have ht : (vt - v * B) ^ 2 / v ≤ 2 * W + 2 * v * M ^ 2 := by
    apply (div_le_iff₀ hv).2
    have hBv := mul_le_mul_of_nonneg_left hB2 (sq_nonneg v)
    nlinarith only [hvt2, hBv, sq_nonneg (vt + v * B)]
  have hvsdiv : vs ^ 2 / v ≤ W := (div_le_iff₀ hv).2 (by nlinarith only [hvs2])
  have hsum : (As * v + A * vs - v * C) ^ 2 ≤
      2 * (A * vs) ^ 2 + 2 * (v * (As - C)) ^ 2 := by
    nlinarith only [sq_nonneg (A * vs - v * (As - C))]
  have hsraw : (As * v + A * vs - v * C) ^ 2 / (A * v) ≤
      2 * A * W + 8 * (v / A) * M ^ 2 := by
    calc
      _ ≤ (2 * (A * vs) ^ 2 + 2 * (v * (As - C)) ^ 2) / (A * v) :=
        div_le_div_of_nonneg_right hsum (mul_pos hA hv).le
      _ = 2 * A * (vs ^ 2 / v) + 2 * (v / A) * (As - C) ^ 2 := by
        field_simp [hA.ne', hv.ne']
      _ ≤ 2 * A * W + 2 * (v / A) * (4 * M ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hvsdiv (by positivity))
          (mul_le_mul_of_nonneg_left hb2 (by positivity))
      _ = 2 * A * W + 8 * (v / A) * M ^ 2 := by ring
  have hva : v / A ≤ d ^ 5 / c := by
    apply (div_le_iff₀ hA).2
    calc
      v ≤ d ^ 6 := hvd
      _ = (d ^ 5 / c) * (c * d) := by field_simp [hc.ne']
      _ ≤ (d ^ 5 / c) * A := mul_le_mul_of_nonneg_left hAlo (by positivity)
  have hvsD : v / A ≤ D ^ 5 / c := hva.trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hd.le hdD 5) hc.le)
  have hvD : v ≤ D ^ 6 := hvd.trans (pow_le_pow_left₀ hd.le hdD 6)
  have hWD : W ≤ Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2 := by
    dsimp [W]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg Cv)
    apply pow_le_pow_left₀ (by positivity : 0 ≤ d ^ 2 + d ^ 3)
    exact add_le_add (pow_le_pow_left₀ hd.le hdD 2) (pow_le_pow_left₀ hd.le hdD 3)
  have hAW : 2 * A * W ≤ 2 * M * W := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAM (by norm_num)) hW
  calc
    _ ≤ (2 * W + 2 * v * M ^ 2) + (2 * A * W + 8 * (v / A) * M ^ 2) :=
      add_le_add ht hsraw
    _ ≤ 2 * (1 + M) * W + 2 * v * M ^ 2 + 8 * (v / A) * M ^ 2 := by
      nlinarith only [hAW]
    _ ≤ 2 * (1 + M) * (Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2) +
        2 * D ^ 6 * M ^ 2 + 8 * (D ^ 5 / c) * M ^ 2 := by
      apply add_le_add
      · exact add_le_add
          (mul_le_mul_of_nonneg_left hWD (by positivity))
          (by nlinarith only [mul_le_mul_of_nonneg_right hvD (sq_nonneg M)])
      · nlinarith only [mul_le_mul_of_nonneg_right hvsD (sq_nonneg M)]
    _ = ellipticRatioConstant D c Cv M := by unfold ellipticRatioConstant; ring

theorem actual_elliptic_ratio
    {A B C v : Coord → ℝ} {p : Coord} {d D c Cv M : ℝ}
    (hAd : DifferentiableAt ℝ A p) (hvdiff : DifferentiableAt ℝ v p)
    (hd : 0 < d) (hdD : d ≤ D) (hc : 0 < c) (hCv : 0 ≤ Cv) (hM : 0 ≤ M)
    (hv : 0 < v p) (hvd : v p ≤ d ^ 6)
    (hvt : |coordPartial 0 v p| ≤ Cv * Real.sqrt (v p) * (d ^ 2 + d ^ 3))
    (hvs : |coordPartial 1 v p| ≤ Cv * Real.sqrt (v p) * (d ^ 2 + d ^ 3))
    (hAlo : c * d ≤ A p) (hAhi : |A p| ≤ M)
    (hAs : |coordPartial 1 A p| ≤ M) (hB : |B p| ≤ M) (hC : |C p| ≤ M) :
    (ellipticErrorT B v p) ^ 2 / v p + (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤
      ellipticRatioConstant D c Cv M := by
  rw [ellipticErrorT, ellipticErrorS, HessianCalculus.coordPartial_mul_at hAd hvdiff 1]
  exact elliptic_ratio_scalar hd hdD hc hCv hM hv hvd hvt hvs hAlo hAhi hAs hB hC

theorem ellipticCutoffDerivativeConstant_nonneg {c MK X : ℝ}
    (hc : 0 < c) (hMK : 0 ≤ MK) (hX : 0 ≤ X) :
    0 ≤ ellipticCutoffDerivativeConstant c MK X := by
  have htheta := transitionDerivativeBound_pos.le
  unfold ellipticCutoffDerivativeConstant
  positivity

theorem ellipticWeight_partial_bound_common {b c MK X : ℝ}
    {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hMK : 0 ≤ MK) (hX : 0 ≤ X)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1) (i : Fin 2)
    (hchii : |coordPartial i chi p| ≤ X) (hKi : |coordPartial i K p| ≤ MK) :
    |coordPartial i (ellipticWeight b c chi K) p| ≤
      ellipticCutoffDerivativeConstant c MK X * Real.sqrt (ellipticWeight b c chi K p) *
        (edgeDistance b p ^ 2 + edgeDistance b p ^ 3) := by
  let P := (2 * transitionDerivativeBound / c) * (MK + c)
  have hP : 0 ≤ P := by
    have htheta := transitionDerivativeBound_pos.le
    dsimp [P]
    positivity
  have hcompare : 3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
      edgeDistance b p ^ 2 * P ≤
      (3 + X + P) * (edgeDistance b p ^ 2 + edgeDistance b p ^ 3) := by
    nlinarith [mul_nonneg hX (sq_nonneg (edgeDistance b p)),
      mul_nonneg hP (pow_pos hd 3).le]
  calc
    _ ≤ 2 * Real.sqrt (ellipticWeight b c chi K p) *
        (3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
          edgeDistance b p ^ 2 * P) :=
      ellipticWeight_partial_bound hc hd hMK hchi hK hchiRange i hchii hKi
    _ ≤ 2 * Real.sqrt (ellipticWeight b c chi K p) *
        ((3 + X + P) * (edgeDistance b p ^ 2 + edgeDistance b p ^ 3)) :=
      mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = _ := by unfold ellipticCutoffDerivativeConstant; dsimp [P]; ring

theorem ellipticCutoff_actual_ratio
    {b c MK X D g0 M : ℝ} {chi K G1 B C : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hMK : 0 ≤ MK) (hX : 0 ≤ X) (hg0 : 0 < g0) (hM : 0 ≤ M)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hG1 : DifferentiableAt ℝ G1 p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1)
    (hchii : ∀ i : Fin 2, |coordPartial i chi p| ≤ X)
    (hKi : ∀ i : Fin 2, |coordPartial i K p| ≤ MK)
    (hv : 0 < ellipticWeight b c chi K p) (hGlow : g0 ≤ G1 p)
    (hAhi : |G1 p * K p| ≤ M)
    (hAs : |coordPartial 1 (fun q => G1 q * K q) p| ≤ M)
    (hB : |B p| ≤ M) (hC : |C p| ≤ M) :
    (ellipticErrorT B (ellipticWeight b c chi K) p) ^ 2 /
        ellipticWeight b c chi K p +
      (ellipticErrorS (fun q => G1 q * K q) C (ellipticWeight b c chi K) p) ^ 2 /
        (G1 p * K p * ellipticWeight b c chi K p) ≤
      ellipticRatioConstant D (g0 * c / 2) (ellipticCutoffDerivativeConstant c MK X) M := by
  have hKlo : c / 2 * edgeDistance b p < K p :=
    ellipticWeight_pos_implies_curvature hc (sub_pos.mp hd) hv
  have hKpos : 0 < K p := (mul_pos (by positivity) hd).trans hKlo
  have hAlo : (g0 * c / 2) * edgeDistance b p ≤ G1 p * K p := by
    have hfirst := mul_le_mul_of_nonneg_left hKlo.le hg0.le
    have hsecond := mul_le_mul_of_nonneg_right hGlow hKpos.le
    nlinarith [hfirst, hsecond]
  have hvdiff : DifferentiableAt ℝ (ellipticWeight b c chi K) p := by
    unfold ellipticWeight
    have hdiffer : DifferentiableAt ℝ (edgeDistance b) p :=
      (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
    have hgate : DifferentiableAt ℝ (fun q => ellipticPhi c (K q / edgeDistance b q)) p :=
      ellipticGate_differentiableAt hK hd.ne'
    exact ((hdiffer.pow 6).mul (hchi.pow 2)).mul (hgate.pow 2)
  exact actual_elliptic_ratio (hG1.mul hK) hvdiff hd hdD (by positivity)
    (ellipticCutoffDerivativeConstant_nonneg hc hMK hX) hM hv
    (ellipticWeight_le_distance_six b c chi K p hchiRange)
    (ellipticWeight_partial_bound_common hc hd hMK hX hchi hK hchiRange 0 (hchii 0) (hKi 0))
    (ellipticWeight_partial_bound_common hc hd hMK hX hchi hK hchiRange 1 (hchii 1) (hKi 1))
    hAlo hAhi hAs hB hC

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def multiplierCutoffError (A chi m n u : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 chi p * multiplierFluxT A m n u p +
    coordPartial 1 chi p * multiplierFluxS A m n u p

theorem multiplier_divergence_quadratic
    {A B C m n u : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * multiplierTest m n u p =
      coordPartial 0 (multiplierFluxT A m n u) p + coordPartial 1 (multiplierFluxS A m n u) p +
        multiplierQuadratic A B C m n u p := by
  have hh := multiplier_divergence_identity (B := B) (C := C) hA hm hn hu hU hp
  unfold multiplierQuadratic
  linear_combination hh

theorem multiplierQuadratic_cutoff_split
    {A B C chi m n u : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hm : ContDiffOn ℝ ∞ m U) (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U)
    (hp : p ∈ U) :
    multiplierQuadratic A B C (fun q => chi q * m q) (fun q => chi q * n q) u p =
      chi p * multiplierQuadratic A B C m n u p - multiplierCutoffError A chi m n u p := by
  have hAd := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hmd := (hm.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hnd := (hn.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hcd := (hchi.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hbase := multiplier_divergence_quadratic (B := B) (C := C) hAd hmd hnd hu hU hp
  have hcut := multiplier_divergence_quadratic (B := B) (C := C) hAd (hcd.mul hmd) (hcd.mul hnd) hu hU hp
  change multiplierOperator A B C u p *
      multiplierTest (fun q => chi q * m q) (fun q => chi q * n q) u p =
    coordPartial 0 (multiplierFluxT A (fun q => chi q * m q) (fun q => chi q * n q) u) p +
      coordPartial 1 (multiplierFluxS A (fun q => chi q * m q) (fun q => chi q * n q) u) p +
      multiplierQuadratic A B C (fun q => chi q * m q) (fun q => chi q * n q) u p at hcut
  have htest : multiplierTest (fun q => chi q * m q) (fun q => chi q * n q) u p =
      chi p * multiplierTest m n u p := by unfold multiplierTest; ring
  have hFt : multiplierFluxT A (fun q => chi q * m q) (fun q => chi q * n q) u =
      (fun q => chi q * multiplierFluxT A m n u q) := by funext q; unfold multiplierFluxT; ring
  have hFs : multiplierFluxS A (fun q => chi q * m q) (fun q => chi q * n q) u =
      (fun q => chi q * multiplierFluxS A m n u q) := by funext q; unfold multiplierFluxS; ring
  obtain ⟨hFts, hFss⟩ := multiplierFluxes_contDiffOn hU hA hm hn hu
  rw [htest, hFt, hFs,
    HessianCalculus.coordPartial_mul_at (f := chi) (h := multiplierFluxT A m n u) hcd
      ((hFts.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) 0,
    HessianCalculus.coordPartial_mul_at (f := chi) (h := multiplierFluxS A m n u) hcd
      ((hFss.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) 1] at hcut
  unfold multiplierCutoffError
  linear_combination chi p * hbase - hcut

theorem multiplierCutoffError_contDiffOn
    {A chi m n u : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hm : ContDiffOn ℝ ∞ m U) (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierCutoffError A chi m n u) U := by
  obtain ⟨hFt, hFs⟩ := multiplierFluxes_contDiffOn hU hA hm hn hu
  exact ((partial_contDiffOn hchi hU 0).mul hFt).add ((partial_contDiffOn hchi hU 1).mul hFs)

theorem multiplierCutoffError_zero (A chi m n u : Coord → ℝ) (p : Coord)
    (ht : coordPartial 0 chi p = 0) (hs : coordPartial 1 chi p = 0) :
    multiplierCutoffError A chi m n u p = 0 := by simp [multiplierCutoffError, ht, hs]

theorem directed_source_young_scalar {w f ut us epsilon t R c : ℝ}
    (hw : 0 ≤ w) (hc : 0 < c) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (ht : |t| ≤ R) :
    |f * (w * (-us + epsilon * t * ut))| ≤
      c / 2 * w * (ut^2 + us^2) + ((1 + R^2) / (2 * c)) * w * f^2 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have het : |epsilon * t| ≤ R := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans
      (by have hh := mul_le_mul_of_nonneg_right heps1 hR; simpa only [one_mul] using hh)
  have hsquare : (epsilon * t)^2 ≤ R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (epsilon * t)) het 2
  have hyu := weighted_young c us f hc
  have hyt := weighted_young c ut (epsilon * t * f) hc
  have hraw : |f * (-us + epsilon * t * ut)| ≤
      c / 2 * (ut^2 + us^2) + (1 + R^2) / (2 * c) * f^2 := by
    have htriangle : |f * (-us + epsilon * t * ut)| ≤ |us * f| + |ut * (epsilon * t * f)| := by
      calc
        _ = |-(us * f) + ut * (epsilon * t * f)| := by congr 1; ring
        _ ≤ |us * f| + |ut * (epsilon * t * f)| := by simpa only [abs_neg] using abs_add_le (-(us * f)) (ut * (epsilon * t * f))
    have hproduct := mul_le_mul_of_nonneg_right hsquare (sq_nonneg f)
    have hdiv := div_le_div_of_nonneg_right hproduct (show 0 ≤ 2 * c by positivity)
    calc
      _ ≤ (c * us^2 + f^2 / c) / 2 + (c * ut^2 + (epsilon * t * f)^2 / c) / 2 :=
        htriangle.trans (add_le_add hyu hyt)
      _ = c / 2 * (ut^2 + us^2) + f^2 / (2 * c) + (epsilon * t)^2 * f^2 / (2 * c) := by
        field_simp [hc.ne']
        ring
      _ ≤ c / 2 * (ut^2 + us^2) + f^2 / (2 * c) + R^2 * f^2 / (2 * c) :=
        add_le_add le_rfl hdiv
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left hraw hw
  calc
    _ = w * |f * (-us + epsilon * t * ut)| := by
      rw [show f * (w * (-us + epsilon * t * ut)) = w * (f * (-us + epsilon * t * ut)) by ring,
        abs_mul, abs_of_nonneg hw]
    _ ≤ w * (c / 2 * (ut^2 + us^2) + (1 + R^2) / (2 * c) * f^2) := hmul
    _ = _ := by ring

end SmoothLocal.Weighted

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

theorem threeEdgeDerivativeConstant_nonneg {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) :
    0 ≤ threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1 := by
  have ht := transitionDerivativeBound_pos.le
  have hl := sub_pos.mpr hL
  have hr := sub_pos.mpr hR
  have hs := sub_pos.mpr hS
  unfold threeEdgeDerivativeConstant
  positivity

theorem threeEdgeCutoff_partial_common {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord) (i : Fin 2) :
    |coordPartial i (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
      threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1 := by
  have hb := threeEdgeCutoff_partial_bounds hL hR hS p
  have ht := transitionDerivativeBound_pos.le
  have hl : 0 ≤ transitionDerivativeBound / (l1 - l0) := div_nonneg ht (sub_pos.mpr hL).le
  have hr : 0 ≤ transitionDerivativeBound / (r0 - r1) := div_nonneg ht (sub_pos.mpr hR).le
  have hs : 0 ≤ transitionDerivativeBound / (a1 - a0) := div_nonneg ht (sub_pos.mpr hS).le
  unfold threeEdgeDerivativeConstant
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one] <;> linarith [hb.1, hb.2]

theorem ellipticWeightC1_errors_eq {b c : ℝ} (A B C chi K : Coord → ℝ)
    {p : Coord} (hp : p 1 < b) :
    ellipticErrorT B (ellipticWeightC1 b c chi K) p =
        ellipticErrorT B (ellipticWeight b c chi K) p ∧
      ellipticErrorS A C (ellipticWeightC1 b c chi K) p =
        ellipticErrorS A C (ellipticWeight b c chi K) p := by
  have he : (fun q => A q * ellipticWeightC1 b c chi K q) =ᶠ[𝓝 p]
      (fun q => A q * ellipticWeight b c chi K q) := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hp] with q hq
    rw [ellipticWeightC1_eq hq.le]
  have hderiv : coordPartial 1 (fun q => A q * ellipticWeightC1 b c chi K q) p =
      coordPartial 1 (fun q => A q * ellipticWeight b c chi K q) p := by
    unfold coordPartial
    rw [he.fderiv_eq]
  constructor
  · rw [ellipticErrorT, ellipticErrorT, ellipticWeightC1_partial_eq hp 0,
      ellipticWeightC1_eq hp.le]
  · rw [ellipticErrorS, ellipticErrorS, hderiv, ellipticWeightC1_eq hp.le]

theorem threeEdge_ellipticWeight_boundary {l0 l1 r1 r0 a0 a1 b c : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (K : Coord → ℝ) :
    zeroRectangleBoundary l0 r0 a0 b
      (ellipticWeightC1 b c (threeEdgeCutoff l0 l1 r1 r0 a0 a1) K) := by
  constructor
  · intro s hs
    have hl := threeEdgeCutoff_zero hL hR hS (boxPoint l0 s)
      (Or.inl (by simp [boxPoint]))
    have hr := threeEdgeCutoff_zero hL hR hS (boxPoint r0 s)
      (Or.inr (Or.inl (by simp [boxPoint])))
    constructor <;> simp [ellipticWeightC1, hl, hr]
  · intro t ht
    have hb := threeEdgeCutoff_zero hL hR hS (boxPoint t a0)
      (Or.inr (Or.inr (by simp [boxPoint])))
    constructor
    · simp [ellipticWeightC1, hb]
    · exact ellipticWeightC1_zero (by simp [boxPoint])

variable {U : Set Coord} {K G1 B C u f : Coord → ℝ}
  {l0 l1 r1 r0 a0 a1 b c MK g0 M : ℝ}

theorem threeEdge_elliptic_energy_bound
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1)
    (ht : l0 ≤ r0) (hs : a0 ≤ b) (hc : 0 < c)
    (hMK : 0 ≤ MK) (hg0 : 0 < g0) (hM : 0 ≤ M)
    (hU : IsOpen U) (hK : ContDiffOn ℝ ∞ K U) (hG1 : ContDiffOn ℝ ∞ G1 U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle l0 r0 a0 b ⊆ U)
    (hEq : ∀ p ∈ U, multiplierOperator (fun q => G1 q * K q) B C u p = f p)
    (hKi : ∀ p ∈ closedRectangle l0 r0 a0 b, ∀ i : Fin 2, |coordPartial i K p| ≤ MK)
    (hGlow : ∀ p ∈ closedRectangle l0 r0 a0 b, g0 ≤ G1 p)
    (hAhi : ∀ p ∈ closedRectangle l0 r0 a0 b, |G1 p * K p| ≤ M)
    (hAs : ∀ p ∈ closedRectangle l0 r0 a0 b,
      |coordPartial 1 (fun q => G1 q * K q) p| ≤ M)
    (hBb : ∀ p ∈ closedRectangle l0 r0 a0 b, |B p| ≤ M)
    (hCb : ∀ p ∈ closedRectangle l0 r0 a0 b, |C p| ≤ M) :
    rectangleIntegral l0 r0 a0 b
      (ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeight b c (threeEdgeCutoff l0 l1 r1 r0 a0 a1) K) u) ≤
      (b - a0) ^ 6 * rectangleIntegral l0 r0 a0 b (fun p => (f p) ^ 2) +
        ((b - a0) ^ 6 + ellipticRatioConstant (b - a0) (g0 * c / 2)
          (ellipticCutoffDerivativeConstant c MK (threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1)) M) *
          rectangleIntegral l0 r0 a0 b (fun p => (u p) ^ 2) := by
  let chi := threeEdgeCutoff l0 l1 r1 r0 a0 a1
  let v := ellipticWeightC1 b c chi K
  let X := threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1
  let H := ellipticRatioConstant (b - a0) (g0 * c / 2) (ellipticCutoffDerivativeConstant c MK X) M
  have hX : 0 ≤ X := threeEdgeDerivativeConstant_nonneg hL hR hS
  have hchi : ContDiffOn ℝ ∞ chi U := (threeEdgeCutoff_contDiff _ _ _ _ _ _).contDiffOn
  have hv : ContDiffOn ℝ 1 v U := ellipticWeightC1_contDiffOn hc
    (hchi.of_le (by simp)) (hK.of_le (by simp))
  have hA : ContDiffOn ℝ ∞ (fun q => G1 q * K q) U := hG1.mul hK
  have hH : 0 ≤ H := ellipticRatioConstant_nonneg (sub_nonneg.mpr hs) (by positivity) hM
  have hposD (p : Coord) (hpv : 0 < v p) : p 1 < b := by
    by_contra hn
    have hz : v p = 0 := ellipticWeightC1_zero (le_of_not_gt hn)
    linarith
  have hweightEq (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) :
      v p = ellipticWeight b c chi K p := ellipticWeightC1_eq hp.2.2
  have hposA (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) (hpv : 0 < v p) :
      0 < G1 p * K p := by
    have hd := hposD p hpv
    have hcurv := ellipticWeight_pos_implies_curvature hc hd
      (show 0 < ellipticWeight b c chi K p by simpa only [← hweightEq p hp] using hpv)
    have hKpos : 0 < K p := (mul_pos (by positivity : 0 < c / 2) (sub_pos.mpr hd)).trans hcurv
    exact mul_pos (hg0.trans_le (hGlow p hp)) hKpos
  have hratio (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) (hpv : 0 < v p) :
      (ellipticErrorT B v p) ^ 2 / v p +
        (ellipticErrorS (fun q => G1 q * K q) C v p) ^ 2 / (G1 p * K p * v p) ≤ H := by
    have hd := hposD p hpv
    have herrors := ellipticWeightC1_errors_eq (c := c) (fun q => G1 q * K q) B C chi K hd
    change (ellipticErrorT B (ellipticWeightC1 b c chi K) p) ^ 2 / v p +
      (ellipticErrorS (fun q => G1 q * K q) C (ellipticWeightC1 b c chi K) p) ^ 2 /
        (G1 p * K p * v p) ≤ H
    rw [herrors.1, herrors.2, hweightEq p hp]
    exact ellipticCutoff_actual_ratio hc (sub_pos.mpr hd)
      (by unfold edgeDistance; linarith [hp.2.1]) hMK hX hg0 hM
      ((hchi.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp))
      ((hK.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp))
      ((hG1.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by simp))
      (threeEdgeCutoff_range _ _ _ _ _ _ p)
      (threeEdgeCutoff_partial_common hL hR hS p) (hKi p hp)
      (show 0 < ellipticWeight b c chi K p by simpa only [← hweightEq p hp] using hpv)
      (hGlow p hp) (hAhi p hp) (hAs p hp) (hBb p hp) (hCb p hp)
  have hestimate := integrated_elliptic_energy_bound_C1 ht hs hU hA hB hC hv hu hbox
    (threeEdge_ellipticWeight_boundary hL hR hS K) hEq ((b - a0) ^ 6) H
    (by positivity) hH (fun p _ => ellipticWeightC1_nonneg _ _ _ _ p)
    (fun p hp => (ellipticWeightC1_le_distance_six _ _ _ _ p
      (threeEdgeCutoff_range _ _ _ _ _ _ p)).trans
        (pow_le_pow_left₀ (sub_nonneg.mpr hp.2.2)
          (by linarith [hp.2.1]) 6))
    hposA hratio
  have henergyEq : rectangleIntegral l0 r0 a0 b
      (ellipticEnergy (fun q => G1 q * K q) v u) =
      rectangleIntegral l0 r0 a0 b
        (ellipticEnergy (fun q => G1 q * K q) (ellipticWeight b c chi K) u) := by
    apply rectangleIntegral_congr ht hs
    intro p hp
    change v p * _ = ellipticWeight b c chi K p * _
    rw [hweightEq p hp]
  rw [henergyEq] at hestimate
  exact hestimate

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedForcingEnergy (chi I f : Coord → ℝ) (edge lambda : ℝ) (p : Coord) : ℝ :=
  chi p * directedWeight edge lambda I p * (f p)^2

def directedCutoffError (A chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) : Coord → ℝ :=
  multiplierCutoffError A chi (directedM edge lambda I) (directedN edge lambda epsilon I) u

def directedCoercivityDefect (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord) : ℝ :=
  chi p * max 0 (c * directedWeight edge lambda I p *
    ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) -
      multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p)

theorem directedCoercivityDefect_zero
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord)
    (hcoercive : c * directedWeight edge lambda I p *
      ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) ≤
        multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p) :
    directedCoercivityDefect A B C chi I u edge lambda epsilon c p = 0 := by
  simp only [directedCoercivityDefect, max_eq_left (sub_nonpos.mpr hcoercive), mul_zero]

theorem directedCoercivityDefect_domination
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord) (hchi : 0 ≤ chi p) :
    c * directedGradientEnergy chi I u edge lambda p ≤
      chi p * multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p +
        directedCoercivityDefect A B C chi I u edge lambda epsilon c p := by
  have hh := mul_le_mul_of_nonneg_left
    (le_max_right (0 : ℝ) (c * directedWeight edge lambda I p *
      ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) -
        multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p)) hchi
  dsimp [directedGradientEnergy, directedCoercivityDefect]
  nlinarith only [hh]

theorem integrated_directed_energy_with_explicit_costs
    {A B C chi I u f : Coord → ℝ} {U : Set Coord} {tl tr sb st : ℝ}
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U)
    (hchi : ContDiffOn ℝ ∞ chi U) (hI : ContDiffOn ℝ ∞ I U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hchiSides : ∀ s ∈ Icc sb st, chi (boxPoint tl s) = 0 ∧ chi (boxPoint tr s) = 0)
    (hchiBottom : ∀ t ∈ Icc tl tr, chi (boxPoint t sb) = 0)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p)
    (hchin : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ chi p)
    (lambda epsilon R c : ℝ) (hc : 0 < c) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hR : ∀ p ∈ closedRectangle tl tr sb st, |p 0| ≤ R) :
    (c / 2) * rectangleIntegral tl tr sb st (directedGradientEnergy chi I u st lambda) ≤
      ((1 + R^2) / (2 * c)) * rectangleIntegral tl tr sb st (directedForcingEnergy chi I f st lambda) +
      rectangleIntegral tl tr sb st (fun p => |directedCutoffError A chi I u st lambda epsilon p|) +
      rectangleIntegral tl tr sb st (directedCoercivityDefect A B C chi I u st lambda epsilon c) := by
  let m := directedM st lambda I
  let n := directedN st lambda epsilon I
  let Q := multiplierQuadratic A B C m n u
  let E := directedGradientEnergy chi I u st lambda
  let F := directedForcingEnergy chi I f st lambda
  let Err := directedCutoffError A chi I u st lambda epsilon
  let Def := directedCoercivityDefect A B C chi I u st lambda epsilon c
  let Source := fun p => f p * multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p
  have hW := directedWeight_contDiffOn st lambda hI
  have hm : ContDiffOn ℝ ∞ m U := hW.neg
  have hn : ContDiffOn ℝ ∞ n U :=
    (contDiffOn_const.mul (contDiffOn_apply ℝ ℝ 0 U)).mul hW
  have hcm := hchi.mul hm
  have hcn := hchi.mul hn
  have hut := partial_contDiffOn hu hU 0
  have hus := partial_contDiffOn hu hU 1
  have hgrad := (hut.pow 2).add (hus.pow 2)
  have hf : ContDiffOn ℝ ∞ f U :=
    (ellipticOperator_contDiffOn hU hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  have hEc : ContinuousOn E (closedRectangle tl tr sb st) :=
    (((hchi.mul hW).mul hgrad).continuousOn.mono hbox)
  have hFc : ContinuousOn F (closedRectangle tl tr sb st) :=
    (((hchi.mul hW).mul (hf.pow 2)).continuousOn.mono hbox)
  have hQ := multiplierQuadratic_contDiffOn hU hA hB hC hm hn hu
  have hchiQ : ContinuousOn (fun p => chi p * Q p) (closedRectangle tl tr sb st) :=
    (hchi.mul hQ).continuousOn.mono hbox
  have hErr := multiplierCutoffError_contDiffOn hU hA hchi hm hn hu
  have hErrc : ContinuousOn Err (closedRectangle tl tr sb st) := hErr.continuousOn.mono hbox
  have hDef : ContinuousOn Def (closedRectangle tl tr sb st) :=
    (hchi.continuousOn.mul ((continuousOn_const (c := (0 : ℝ))).sup
      ((((contDiffOn_const (c := c)).mul hW).mul hgrad).sub hQ).continuousOn)).mono hbox
  have htest : ContDiffOn ℝ ∞ (multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) U :=
    (hcm.mul hus).add (hcn.mul hut)
  have hSource : ContinuousOn Source (closedRectangle tl tr sb st) := (hf.mul htest).continuousOn.mono hbox
  have hsplit : rectangleIntegral tl tr sb st Source =
      rectangleIntegral tl tr sb st (fun p => chi p * Q p) - rectangleIntegral tl tr sb st Err := by
    calc
      _ = rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p *
          multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        change f p * multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p =
          multiplierOperator A B C u p *
            multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p
        rw [hEq p (hbox hp)]
      _ = rectangleIntegral tl tr sb st
          (multiplierQuadratic A B C (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) :=
        integrated_cutoff_directed_identity ht hs hU hA hB hC hchi hI hu hbox hchiSides hchiBottom lambda epsilon
      _ = rectangleIntegral tl tr sb st (fun p => chi p * Q p - Err p) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        exact multiplierQuadratic_cutoff_split hU hA hchi hm hn hu (hbox hp)
      _ = _ := rectangleIntegral_sub ht hs hchiQ hErrc
  have hdom := rectangleIntegral_mono ht hs (continuousOn_const.mul hEc) (hchiQ.add hDef)
    (fun p hp => directedCoercivityDefect_domination A B C chi I u st lambda epsilon c p (hchin p hp))
  change rectangleIntegral tl tr sb st (fun p => c * E p) ≤
    rectangleIntegral tl tr sb st (fun p => chi p * Q p + Def p) at hdom
  rw [rectangleIntegral_const_mul, rectangleIntegral_add ht hs hchiQ hDef] at hdom
  have hsourceBound (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      Source p ≤ (c / 2) * E p + ((1 + R^2) / (2 * c)) * F p := by
    have hWn : 0 ≤ directedWeight st lambda I p :=
      mul_nonneg (pow_nonneg (sub_nonneg.mpr hp.2.2) 8) (Real.exp_pos _).le
    have hpoint := directed_source_young_scalar (mul_nonneg (hchin p hp) hWn) hc heps heps1 (hR p hp)
      (f := f p) (ut := coordPartial 0 u p) (us := coordPartial 1 u p)
    have hfac := cutoff_test_factor chi I u st lambda epsilon p
    dsimp [Source]
    rw [hfac]
    exact (le_abs_self _).trans (by
      convert hpoint using 1 <;> try with_reducible_and_instances rfl
      try dsimp [E, F, directedGradientEnergy, directedForcingEnergy]
      ring)
  have hsourceIntegral := rectangleIntegral_mono ht hs hSource
    ((continuousOn_const.mul hEc).add (continuousOn_const.mul hFc)) hsourceBound
  change rectangleIntegral tl tr sb st Source ≤ rectangleIntegral tl tr sb st
    (fun p => (c / 2) * E p + ((1 + R^2) / (2 * c)) * F p) at hsourceIntegral
  have hcE : ContinuousOn (fun p => (c / 2) * E p) (closedRectangle tl tr sb st) :=
    continuousOn_const.mul hEc
  have hcF : ContinuousOn (fun p => ((1 + R^2) / (2 * c)) * F p) (closedRectangle tl tr sb st) :=
    continuousOn_const.mul hFc
  rw [rectangleIntegral_add ht hs hcE hcF,
    rectangleIntegral_const_mul, rectangleIntegral_const_mul] at hsourceIntegral
  have herrorIntegral := rectangleIntegral_mono ht hs hErrc hErrc.abs (fun p hp => le_abs_self (Err p))
  change (c / 2) * rectangleIntegral tl tr sb st E ≤
    ((1 + R^2) / (2 * c)) * rectangleIntegral tl tr sb st F +
    rectangleIntegral tl tr sb st (fun p => |Err p|) + rectangleIntegral tl tr sb st Def
  nlinarith only [hdom, hsplit, hsourceIntegral, herrorIntegral]

end SmoothLocal.Weighted

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

def weightedGradient (b : ℝ) (u : Coord → ℝ) (p : Coord) : ℝ :=
  edgeDistance b p ^ 7 * ((coordPartial 0 u p) ^ 2 + (coordPartial 1 u p) ^ 2)

theorem elliptic_gradient_scalar {d D a A x y : ℝ}
    (hd : 0 < d) (hdD : d ≤ D) (ha : 0 < a) (hA : a * d ≤ A) :
    d ^ 7 * (x ^ 2 + y ^ 2) ≤ (D + 1 / a) * (d ^ 6 * (x ^ 2 + A * y ^ 2)) := by
  have hD : 0 ≤ D := hd.le.trans hdD
  have hApos : 0 < A := (mul_pos ha hd).trans_le hA
  have hda : d ≤ A / a := (le_div_iff₀ ha).2 (by nlinarith)
  have hx := mul_le_mul_of_nonneg_right hdD (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_right hda (sq_nonneg y)
  have hfirst : d * (x ^ 2 + y ^ 2) ≤ D * x ^ 2 + (A / a) * y ^ 2 := by nlinarith
  have hsecond : D * x ^ 2 + (A / a) * y ^ 2 ≤
      (D + 1 / a) * (x ^ 2 + A * y ^ 2) := by
    have hgap : 0 ≤ D * A * y ^ 2 + x ^ 2 / a := by positivity
    have he : (D + 1 / a) * (x ^ 2 + A * y ^ 2) -
        (D * x ^ 2 + (A / a) * y ^ 2) = D * A * y ^ 2 + x ^ 2 / a := by ring
    linarith
  have hm := mul_le_mul_of_nonneg_left (hfirst.trans hsecond) (pow_pos hd 6).le
  nlinarith only [hm]

theorem ellipticWeight_eq_distance_six {b c c1 : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hcc : c ≤ c1) (hd : 0 < edgeDistance b p)
    (hchi : chi p = 1) (hK : c1 * edgeDistance b p ≤ K p) :
    ellipticWeight b c chi K p = edgeDistance b p ^ 6 := by
  have hratio : c ≤ K p / edgeDistance b p := by
    apply (le_div_iff₀ hd).2
    exact (mul_le_mul_of_nonneg_right hcc hd.le).trans hK
  simp [ellipticWeight, hchi, ellipticPhi_one hc hratio]

theorem ellipticCutoff_gradient_pointwise
    {b c c1 g0 D : ℝ} {chi K G1 u : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hcc : c ≤ c1) (hg0 : 0 < g0)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hchi : chi p = 1) (hK : c1 * edgeDistance b p ≤ K p) (hG1 : g0 ≤ G1 p) :
    weightedGradient b u p ≤ (D + 1 / (g0 * c1)) *
      ellipticEnergy (fun q => G1 q * K q) (ellipticWeight b c chi K) u p := by
  have hc1 : 0 < c1 := hc.trans_le hcc
  have hKpos : 0 < K p := (mul_pos hc1 hd).trans_le hK
  have hA : (g0 * c1) * edgeDistance b p ≤ G1 p * K p := by
    have h1 := mul_le_mul_of_nonneg_left hK hg0.le
    have h2 := mul_le_mul_of_nonneg_right hG1 hKpos.le
    nlinarith [h1, h2]
  unfold weightedGradient ellipticEnergy
  rw [ellipticWeight_eq_distance_six hc hcc hd hchi hK]
  exact elliptic_gradient_scalar hd hdD (mul_pos hg0 hc1) hA

variable {tl tr sb st : ℝ} {S : Set Coord} {F G : Coord → ℝ}

variable {U : Set Coord} {K G1 B C u f : Coord → ℝ}
  {l0 l1 r1 r0 a0 a1 b c c1 MK g0 M : ℝ}

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedQuadratic_edge_zero
    (A B C I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p) (hedge : p 1 = edge) :
    multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p = 0 := by
  have hW := directedWeight_edge_zero edge lambda I p hedge
  have hWd (i : Fin 2) := directedWeight_partial_edge_zero edge lambda hI hedge i
  have hm := directedM_differentiableAt edge lambda hI
  have hn := directedN_differentiableAt edge lambda epsilon hI
  obtain ⟨hm0, hn0⟩ := directed_mn_edge_zero edge lambda epsilon I p hedge
  have hmd (i : Fin 2) : coordPartial i (directedM edge lambda I) p = 0 := by
    rw [directedM_partial, hWd i, neg_zero]
  have hnd (i : Fin 2) : coordPartial i (directedN edge lambda epsilon I) p = 0 := by
    rw [directedN_partial edge lambda epsilon hI i, hW, hWd i]
    ring
  have hAm (i : Fin 2) : coordPartial i (fun q => A q * directedM edge lambda I q) p = 0 := by
    rw [HessianCalculus.coordPartial_mul_at hA hm i, hm0, hmd i]
    ring
  have hAn (i : Fin 2) : coordPartial i (fun q => A q * directedN edge lambda epsilon I q) p = 0 := by
    rw [HessianCalculus.coordPartial_mul_at hA hn i, hn0, hnd i]
    ring
  simp only [multiplierQuadratic, multiplierT, multiplierS, multiplierJ,
    hmd, hnd, hAm, hAn, hm0, hn0]
  ring

theorem directedCutoffError_edge_zero
    (A chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord) (hedge : p 1 = edge) :
    directedCutoffError A chi I u edge lambda epsilon p = 0 := by
  obtain ⟨ht, hs⟩ := directed_flux_edge_zero A u I edge lambda epsilon p hedge
  simp [directedCutoffError, multiplierCutoffError, ht, hs]

theorem directedCoercivityDefect_edge_zero
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p) (hedge : p 1 = edge) :
    directedCoercivityDefect A B C chi I u edge lambda epsilon c p = 0 := by
  rw [directedCoercivityDefect, directedWeight_edge_zero edge lambda I p hedge,
    directedQuadratic_edge_zero A B C I u edge lambda epsilon p hA hI hedge]
  simp

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem capChartDomain_isOpen : IsOpen capChartDomain := coordinateRectangle_isOpen _ _ _

theorem capChart_zero (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 0 = p 0 := by
  simp [capChart, coordinatePoint]

theorem capChart_one (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 1 = capFlowHeight Y p := by
  simp [capChart, coordinatePoint]

variable {Y : ℝ → ℝ → ℝ}

variable {q : Coord → ℝ}

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capOuterSpatialCutoff (L R A : ℝ) : Coord → ℝ :=
  capSpatialCutoff (capOuterEdge L) (-capOuterEdge (-R)) (capOuterEdge A)

theorem capOuterSpatialCutoff_contDiff (L R A : ℝ) :
    ContDiff ℝ ∞ (capOuterSpatialCutoff L R A) :=
  capSpatialCutoff_contDiff _ _ _

theorem capSpatialCutoff_nonzero_bounds {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) {p : Coord}
    (hp : capSpatialCutoff L R A p ≠ 0) :
    capOuterEdge L < p 0 ∧ p 0 < -capOuterEdge (-R) ∧ capOuterEdge A < p 1 := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  have hz (h : p 0 ≤ capOuterEdge L ∨ -capOuterEdge (-R) ≤ p 0 ∨
      p 1 ≤ capOuterEdge A) : capSpatialCutoff L R A p = 0 :=
    threeEdgeCutoff_zero hli (neg_lt_neg hri) hai p h
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    exact hp (hz (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hp (hz (Or.inr (Or.inl (le_of_not_gt h))))
  · by_contra h
    exact hp (hz (Or.inr (Or.inr (le_of_not_gt h))))

theorem capOuterSpatialCutoff_one_of_nonzero {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) {p : Coord}
    (hp : capSpatialCutoff L R A p ≠ 0) : capOuterSpatialCutoff L R A p = 1 := by
  have hlo := (capEdges_bounds hL).1
  have hro := (capEdges_bounds (x := -R) (by linarith)).1
  have hao := (capEdges_bounds hA).1
  obtain ⟨htl, htr, hsb⟩ := capSpatialCutoff_nonzero_bounds hL hR hA hp
  exact capSpatialCutoff_one hlo (by linarith) hao p ⟨htl.le, htr.le, hsb.le⟩

theorem capSpatialCutoff_nonzero_of_partial {L R A : ℝ} {p : Coord} {i : Fin 2}
    (hp : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    capSpatialCutoff L R A p ≠ 0 := by
  intro hz
  have hmin : IsLocalMin (capSpatialCutoff L R A) p := by
    change ∀ᶠ q in 𝓝 p, capSpatialCutoff L R A p ≤ capSpatialCutoff L R A q
    exact Filter.Eventually.of_forall (fun q => by
      simpa only [hz] using (capSpatialCutoff_range L R A q).1)
  have hd := hmin.fderiv_eq_zero
  exact hp (by simp [coordPartial, hd])

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem modelCurvature_lower_flow_bottom {kappa : ℝ} (hk : 0 < kappa)
    {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) (hs : p 1 < -3 / 2) :
    kappa < modelCurvature kappa (capChart Y p) := by
  have hy : capFlowHeight Y p < -(37 / 25 : ℝ) := by
    linarith [(abs_le.mp hdisp).2]
  have hy2 : 2 < (capFlowHeight Y p)^2 := by
    nlinarith [sq_nonneg (capFlowHeight Y p + 37 / 25)]
  have hh := modelProfile_eq_one_sub_sq (y := capFlowHeight Y p) (by linarith)
  unfold modelCurvature
  rw [capChart_zero, capChart_one, hh]
  have hbase : 1 < (p 0)^2 - (1 - (capFlowHeight Y p)^2) := by
    nlinarith [sq_nonneg (p 0)]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hbase hk

theorem capChart_not_mem_patchBox_of_cutoff_band
    {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hband : (3 / 2 < |p 0| ∧ |p 0| < 2) ∨ (-2 < p 1 ∧ p 1 < -3 / 2)) :
    capChart Y p ∉ patchBox := by
  intro hin
  rcases hband with ht | hs
  · have hxlo := hin.1 0
    have hxhi := hin.2 0
    simp only [capChart_zero] at hxlo hxhi
    have habs : |p 0| ≤ (1 : ℝ) / 10 := abs_le.mpr ⟨hxlo, hxhi⟩
    linarith [ht.1]
  · have hylo := hin.1 1
    simp only [capChart_one] at hylo
    linarith [hs.2, (abs_le.mp hdisp).2]

theorem capSpatialCutoff_partial_actual_curvature_lower
    {g0 eta : MetricField} {kappa L R A : ℝ} {U : Set Coord}
    {Y : ℝ → ℝ → ℝ} {p : Coord} {i : Fin 2}
    (hk : 0 < kappa) (hL : -2 < L) (hR : R < 2) (hA : -2 < A)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hpartial : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    kappa < capPullback Y (gaussianCurvature (g0 + eta)) p := by
  have hband := capSpatialCutoff_derivative_bands hL hR hA p i hpartial
  have hnot := capChart_not_mem_patchBox_of_cutoff_band hdisp hband
  have hts : capChart Y p ∉ tsupport eta := fun h => hnot (hsupport h)
  have hsame := gaussianCurvature_eq_of_eventuallyEq
    (metric_add_eventuallyEq_of_not_mem_tsupport g0 eta hts)
  change kappa < gaussianCurvature (g0 + eta) (capChart Y p)
  rw [hsame, hbackground _ hpU]
  rcases hband with ht | hs
  · have hh := modelCurvature_lateral_band_lower hk (p := capChart Y p)
      (by simpa only [capChart_zero] using ht.1)
    linarith
  · exact modelCurvature_lower_flow_bottom hk hdisp hs.2

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem capOverlapThreshold_pos {kappa c1 D : ℝ}
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) :
    0 < capOverlapThreshold kappa c1 D := by
  exact lt_min hc1 (div_pos hk (by linarith))

theorem capOverlapThreshold_le (kappa c1 D : ℝ) :
    capOverlapThreshold kappa c1 D ≤ c1 := min_le_left _ _

theorem capOverlapThreshold_distance_le {kappa c1 D d : ℝ}
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) (_ : 0 ≤ d) (hdD : d ≤ D) :
    capOverlapThreshold kappa c1 D * d ≤ kappa := by
  have hc := (capOverlapThreshold_pos hk hc1 hD).le
  have hD1 : 0 < D + 1 := by linarith
  have hcd : capOverlapThreshold kappa c1 D * (D + 1) ≤ kappa :=
    (le_div_iff₀ hD1).mp (min_le_right _ _)
  exact (mul_le_mul_of_nonneg_left (show d ≤ D + 1 by linarith) hc).trans hcd

theorem capOuterElliptic_gradient_pointwise
    {L R A b c g0 D : ℝ} {K G1 u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A)
    (hc : 0 < c) (hg0 : 0 < g0) (hd : 0 < edgeDistance b p)
    (hdD : edgeDistance b p ≤ D) (hchi : capSpatialCutoff L R A p ≠ 0)
    (hK : c * edgeDistance b p ≤ K p) (hG1 : g0 ≤ G1 p) :
    weightedGradient b u p ≤ (D + 1 / (g0 * c)) *
      ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeightC1 b c (capOuterSpatialCutoff L R A) K) u p := by
  have houter := capOuterSpatialCutoff_one_of_nonzero hL hR hA hchi
  have hh := ellipticCutoff_gradient_pointwise (u := u) hc le_rfl hg0 hd hdD houter hK hG1
  have hp : p 1 ≤ b := (sub_pos.mp hd).le
  simpa only [ellipticEnergy, ellipticWeightC1_eq hp] using hh

theorem directedCoercivityDefect_nonzero_cutoff
    {A B C chi I u : Coord → ℝ} {b lambda epsilon c2 : ℝ} {p : Coord}
    (hdef : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≠ 0) : chi p ≠ 0 := by
  intro hz
  apply hdef
  simp only [directedCoercivityDefect, hz, zero_mul]

theorem capOuterElliptic_gradient_on_defect
    {L R A0 b c1 c2 kappa D g0 lambda epsilon : ℝ}
    {A B C K G1 I u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) (hg0 : 0 < g0)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D) (hG1 : g0 ≤ G1 p)
    (hcoercive : K p ≤ c1 * edgeDistance b p →
      c2 * directedWeight b lambda I p * ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) ≤
        multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p)
    (hdef : directedCoercivityDefect A B C (capSpatialCutoff L R A0) I u b lambda epsilon c2 p ≠ 0) :
    weightedGradient b u p ≤ (D + 1 / (g0 * capOverlapThreshold kappa c1 D)) *
      ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeightC1 b (capOverlapThreshold kappa c1 D) (capOuterSpatialCutoff L R A0) K) u p := by
  have hK : c1 * edgeDistance b p < K p := by
    by_contra h
    exact hdef (directedCoercivityDefect_zero _ _ _ _ _ _ _ _ _ _ _ (hcoercive (le_of_not_gt h)))
  apply capOuterElliptic_gradient_pointwise hL hR hA0 (capOverlapThreshold_pos hk hc1 hD)
    hg0 hd hdD (directedCoercivityDefect_nonzero_cutoff hdef) _ hG1
  exact (mul_le_mul_of_nonneg_right (capOverlapThreshold_le kappa c1 D) hd.le).trans hK.le

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem capOuterElliptic_gradient_on_actual_cutoff_support
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A b kappa c1 D glow : ℝ} {G1 u : Coord → ℝ} {p : Coord} {i : Fin 2}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (hk : 0 < kappa)
    (hc1 : 0 < c1) (hD : 0 ≤ D) (hg : 0 < glow)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = SmoothLocal.Model.modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D) (hG1 : glow ≤ G1 p)
    (hpartial : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    weightedGradient b u p ≤ (D + 1 / (glow * capOverlapThreshold kappa c1 D)) *
      ellipticEnergy (fun q => G1 q * capPullback Y (gaussianCurvature (g0 + eta)) q)
        (ellipticWeightC1 b (capOverlapThreshold kappa c1 D) (capOuterSpatialCutoff L R A)
          (capPullback Y (gaussianCurvature (g0 + eta)))) u p := by
  have hK := capSpatialCutoff_partial_actual_curvature_lower hk hL hR hA hbackground hsupport
    hpU hdisp hpartial
  apply capOuterElliptic_gradient_pointwise hL hR hA (capOverlapThreshold_pos hk hc1 hD)
    hg hd hdD (capSpatialCutoff_nonzero_of_partial hpartial) _ hG1
  exact (capOverlapThreshold_distance_le hk hc1 hD hd.le hdD).trans hK.le

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem scalarQuadratic_abs_bound {alpha beta gamma a b c x y : ℝ}
    (ha : |alpha| ≤ a) (hb : |beta| ≤ b) (hc : |gamma| ≤ c) :
    |alpha*x^2 + beta*(x*y) + gamma*y^2| ≤ (a+b+c)*(x^2+y^2) := by
  have ha0 := (abs_nonneg alpha).trans ha
  have hb0 := (abs_nonneg beta).trans hb
  have hc0 := (abs_nonneg gamma).trans hc
  have hE : 0 ≤ x^2+y^2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hxy : |x*y| ≤ x^2+y^2 := by
    have hh := weighted_young 1 x y (by norm_num)
    norm_num only [one_mul, div_one] at hh
    linarith
  have hxa : |alpha| *x^2 ≤ a*(x^2+y^2) :=
    (mul_le_mul_of_nonneg_right ha (sq_nonneg x)).trans
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg y]) ha0)
  have hxb : |beta| *|x*y| ≤ b*(x^2+y^2) := mul_le_mul hb hxy (abs_nonneg _) hb0
  have hxc : |gamma| *y^2 ≤ c*(x^2+y^2) :=
    (mul_le_mul_of_nonneg_right hc (sq_nonneg y)).trans
      (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg x]) hc0)
  calc
    _ ≤ |alpha*x^2 + beta*(x*y)| + |gamma*y^2| := abs_add_le _ _
    _ ≤ (|alpha*x^2| + |beta*(x*y)|) + |gamma*y^2| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |alpha| *x^2 + |beta| *|x*y| + |gamma| *y^2 := by
      rw [abs_mul alpha, abs_mul beta, abs_mul gamma, abs_of_nonneg (sq_nonneg x),
        abs_of_nonneg (sq_nonneg y)]
    _ ≤ a*(x^2+y^2)+b*(x^2+y^2)+c*(x^2+y^2) := add_le_add (add_le_add hxa hxb) hxc
    _ = _ := by ring

theorem directedFlux_scalar_bound {eta A M x y : ℝ}
    (he : |eta| ≤ 2) (hA : |A| ≤ M) :
    |-x*y + eta*x^2/2 - eta*A*y^2/2| ≤ 3*(M+1)*(x^2+y^2) ∧
    |-A*y^2/2 + eta*A*x*y + x^2/2| ≤ 3*(M+1)*(x^2+y^2) := by
  have hM : 0 ≤ M := (abs_nonneg A).trans hA
  have hetaA : |eta*A| ≤ 2*M := by
    rw [abs_mul]
    exact mul_le_mul he hA (abs_nonneg _) (by norm_num)
  have hehalf : |eta/2| ≤ (1 : ℝ) := by rw [abs_div]; norm_num; linarith
  have hAhalf : |-(A/2)| ≤ M := by rw [abs_neg, abs_div]; norm_num; linarith
  have hetaAhalf : |-(eta*A/2)| ≤ M := by
    calc
      _ = |eta*A| / 2 := by rw [abs_neg, abs_div]; norm_num
      _ ≤ M := by linarith only [hetaA]
  have hE : 0 ≤ x^2+y^2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  constructor
  · have hh := scalarQuadratic_abs_bound (x := x) (y := y) hehalf
      (show |(-1 : ℝ)| ≤ 1 by norm_num) hetaAhalf
    have heq : -x*y + eta*x^2/2 - eta*A*y^2/2 =
        (eta/2)*x^2 + (-1)*(x*y) + (-(eta*A/2))*y^2 := by ring
    rw [heq]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hE)
  · have hh := scalarQuadratic_abs_bound (x := x) (y := y)
      (show |(1/2 : ℝ)| ≤ 1 by norm_num) hetaA hAhalf
    have heq : -A*y^2/2 + eta*A*x*y + x^2/2 =
        (1/2)*x^2 + (eta*A)*(x*y) + (-(A/2))*y^2 := by ring
    rw [heq]
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) hE)

theorem directedWeight_le_seven {b lambda D S MI : ℝ} {I : Coord → ℝ} {p : Coord}
    (hlambda : 0 ≤ lambda) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) :
    directedWeight b lambda I p ≤ D * Real.exp (lambda*S+MI) * edgeDistance b p^7 := by
  have hphase : weightPhase lambda I p ≤ lambda*S+MI := by
    have hs' : -p 1 ≤ S := by linarith [(abs_le.mp hs).1]
    have hm := mul_le_mul_of_nonneg_left hs' hlambda
    unfold weightPhase
    linarith [(abs_le.mp hI).2]
  have he := Real.exp_le_exp.mpr hphase
  have hprod := mul_le_mul hdD he (Real.exp_pos _).le (hd.trans hdD)
  have hh := mul_le_mul_of_nonneg_left hprod (pow_nonneg hd 7)
  calc
    _ = edgeDistance b p^7 * (edgeDistance b p * Real.exp (weightPhase lambda I p)) := by
      unfold directedWeight
      ring
    _ ≤ edgeDistance b p^7 * (D*Real.exp (lambda*S+MI)) := hh
    _ = _ := by ring

theorem directedCutoffError_abs_le_seven
    {A chi I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M X : ℝ}
    (hlambda : 0 ≤ lambda) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (ht : |p 0| ≤ 2) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) (hA : |A p| ≤ M)
    (hchi : ∀ i : Fin 2, |coordPartial i chi p| ≤ X) :
    |directedCutoffError A chi I u b lambda epsilon p| ≤
      (6*X*D*Real.exp (lambda*S+MI)*(M+1)) * weightedGradient b u p := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hA
  have hX : 0 ≤ X := (abs_nonneg _).trans (hchi 0)
  have hD : 0 ≤ D := hd.trans hdD
  have hW : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have he : |epsilon*p 0| ≤ (2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans (by linarith)
  obtain ⟨hT, hS⟩ := directedFlux_scalar_bound (x := coordPartial 0 u p)
    (y := coordPartial 1 u p) he hA
  obtain ⟨hFt, hFs⟩ := directed_flux_factor A u I b lambda epsilon p
  have hT' : |multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedWeight b lambda I p * (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by
    rw [hFt, abs_mul, abs_of_nonneg hW]
    exact mul_le_mul_of_nonneg_left hT hW
  have hS' : |multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedWeight b lambda I p * (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by
    rw [hFs, abs_mul, abs_of_nonneg hW]
    exact mul_le_mul_of_nonneg_left hS hW
  have hbound : 0 ≤ directedWeight b lambda I p *
      (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by positivity
  have hbase : |directedCutoffError A chi I u b lambda epsilon p| ≤
      6*X*(M+1)*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) := by
    unfold directedCutoffError multiplierCutoffError
    calc
      _ ≤ |coordPartial 0 chi p * multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p| +
          |coordPartial 1 chi p * multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p| :=
        abs_add_le _ _
      _ ≤ X*(directedWeight b lambda I p*(3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2))) +
          X*(directedWeight b lambda I p*(3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2))) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hchi 0) hT' (abs_nonneg _) hX)
          (mul_le_mul (hchi 1) hS' (abs_nonneg _) hX)
      _ = _ := by ring
  have hWbound := directedWeight_le_seven hlambda hd hdD hs hI
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWbound
    (show 0 ≤ 6*X*(M+1) by positivity))
      (add_nonneg (sq_nonneg (coordPartial 0 u p)) (sq_nonneg (coordPartial 1 u p)))
  exact hbase.trans (by
    convert hh using 1 <;> try with_reducible_and_instances rfl
    unfold weightedGradient
    ring)

theorem capSpatialCutoff_partial_uniform {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord) (i : Fin 2) :
    |coordPartial i (capSpatialCutoff L R A) p| ≤ capSpatialDerivativeConstant L R A := by
  exact threeEdgeCutoff_partial_common (capEdges_bounds hL).2.1
    (neg_lt_neg (capEdges_bounds (x := -R) (by linarith)).2.1) (capEdges_bounds hA).2.1 p i

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedWeightJetBudget_bounds {D M lambda : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda) :
    0 ≤ directedWeightJetBudget D M lambda ∧
    D ≤ directedWeightJetBudget D M lambda ∧
    2*D ≤ directedWeightJetBudget D M lambda ∧
    D*M ≤ directedWeightJetBudget D M lambda ∧
    8+D*(M+lambda) ≤ directedWeightJetBudget D M lambda ∧
    D+2*D*M ≤ directedWeightJetBudget D M lambda ∧
    16+2*D*(M+lambda) ≤ directedWeightJetBudget D M lambda := by
  have hDM := mul_nonneg hD hM
  have hDl := mul_nonneg hD hlambda
  unfold directedWeightJetBudget
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem directedWeight_value_and_partials_bound
    {I : Coord → ℝ} {p : Coord} {b lambda D S MI M : ℝ}
    (hId : DifferentiableAt ℝ I p) (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M) :
    |directedWeight b lambda I p| ≤ D*(Real.exp (lambda*S+MI)*edgeDistance b p^7) ∧
    |coordPartial 0 (directedWeight b lambda I) p| ≤
      (D*M)*(Real.exp (lambda*S+MI)*edgeDistance b p^7) ∧
    |coordPartial 1 (directedWeight b lambda I) p| ≤
      (8+D*(M+lambda))*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
  have hD : 0 ≤ D := hd.trans hdD
  have hW : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hE : 0 ≤ Real.exp (lambda*S+MI)*edgeDistance b p^7 := by positivity
  have hw : |directedWeight b lambda I p| ≤ D*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
    rw [abs_of_nonneg hW]
    convert directedWeight_le_seven hlambda hd hdD hs hIv using 1 <;> try with_reducible_and_instances rfl
    ring
  have hphase : weightPhase lambda I p ≤ lambda*S+MI := by
    have hs' : -p 1 ≤ S := by linarith [(abs_le.mp hs).1]
    have hm := mul_le_mul_of_nonneg_left hs' hlambda
    unfold weightPhase
    linarith [(abs_le.mp hIv).2]
  refine ⟨hw, ?_, ?_⟩
  · rw [directedWeight_partial_t b lambda hId, abs_mul]
    have hh := mul_le_mul hw (hIi 0) (abs_nonneg _) (mul_nonneg hD hE)
    convert hh using 1 <;> try with_reducible_and_instances rfl
    ring
  · rw [directedWeight_partial_s b lambda hId]
    have hIs : |coordPartial 1 I p - lambda| ≤ M+lambda := by
      calc
        _ ≤ |coordPartial 1 I p| + |lambda| := abs_sub _ _
        _ ≤ M+lambda := by rw [abs_of_nonneg hlambda]; exact add_le_add (hIi 1) le_rfl
    have hlead : |-8*edgeDistance b p^7*Real.exp (weightPhase lambda I p)| ≤
        8*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
      have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase)
        (show 0 ≤ 8*edgeDistance b p^7 by positivity)
      calc
        _ = 8*edgeDistance b p^7*Real.exp (weightPhase lambda I p) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hd 7),
            abs_of_pos (Real.exp_pos _)]
          norm_num
        _ ≤ 8*edgeDistance b p^7*Real.exp (lambda*S+MI) := hh
        _ = _ := by ring
    have hrest : |directedWeight b lambda I p*(coordPartial 1 I p-lambda)| ≤
        (D*(M+lambda))*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
      rw [abs_mul]
      calc
        _ ≤ (D*(Real.exp (lambda*S+MI)*edgeDistance b p^7))*(M+lambda) :=
          (mul_le_mul_of_nonneg_left hIs (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_right hw (add_nonneg hM hlambda))
        _ = _ := by ring
    exact (abs_add_le _ _).trans (by
      have hh := add_le_add hlead hrest
      convert hh using 1 <;> try with_reducible_and_instances rfl
      ring)

theorem directedMultiplier_firstJet_abs_le_seven
    {I : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M : ℝ}
    (hId : DifferentiableAt ℝ I p) (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M) :
    let V := directedWeightJetBudget D M lambda * Real.exp (lambda*S+MI)*edgeDistance b p^7
    |directedM b lambda I p| ≤ V ∧ |directedN b lambda epsilon I p| ≤ V ∧
      (∀ i : Fin 2, |coordPartial i (directedM b lambda I) p| ≤ V) ∧
      (∀ i : Fin 2, |coordPartial i (directedN b lambda epsilon I) p| ≤ V) := by
  let E := Real.exp (lambda*S+MI)*edgeDistance b p^7
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 ≤ D := hd.trans hdD
  have het : |epsilon*p 0| ≤ (2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans (by linarith)
  have heabs : |epsilon| ≤ 1 := by rwa [abs_of_nonneg heps]
  obtain ⟨hw, hwt, hws⟩ := directedWeight_value_and_partials_bound hId hlambda hM hd hdD hs hIv hIi
  obtain ⟨hN, hND, hN2D, hNDM, hNs, hNt, hNss⟩ := directedWeightJetBudget_bounds hD hM hlambda
  change |directedWeight b lambda I p| ≤ D*E at hw
  change |coordPartial 0 (directedWeight b lambda I) p| ≤ (D*M)*E at hwt
  change |coordPartial 1 (directedWeight b lambda I) p| ≤ (8+D*(M+lambda))*E at hws
  have hlift {a x : ℝ} (hx : |x| ≤ a*E) (ha : a ≤ directedWeightJetBudget D M lambda) :
      |x| ≤ directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)*edgeDistance b p^7 := by
    have hh := hx.trans (mul_le_mul_of_nonneg_right ha hE)
    convert hh using 1 <;> try with_reducible_and_instances rfl
    dsimp only [E]
    ring
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold directedM
    rw [abs_neg]
    exact hlift hw hND
  · have hh : |directedN b lambda epsilon I p| ≤ (2*D)*E := by
      unfold directedN
      rw [abs_mul]
      convert mul_le_mul het hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> try with_reducible_and_instances rfl
      ring
    exact hlift hh hN2D
  · intro i
    rw [directedM_partial b lambda i, abs_neg]
    fin_cases i
    · simpa only [Fin.mk_zero] using hlift hwt hNDM
    · simpa only [Fin.mk_one] using hlift hws hNs
  · intro i
    rw [directedN_partial b lambda epsilon hId i]
    fin_cases i
    · simp only [Fin.mk_zero, Fin.isValue, ↓reduceIte, mul_one]
      have hfirst : |epsilon*directedWeight b lambda I p| ≤ D*E := by
        rw [abs_mul]
        have hh := mul_le_mul heabs hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using hh
      have hsecond : |epsilon*p 0*coordPartial 0 (directedWeight b lambda I) p| ≤ (2*D*M)*E := by
        rw [abs_mul]
        convert mul_le_mul het hwt (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> try with_reducible_and_instances rfl
        ring
      have hh : |epsilon*directedWeight b lambda I p +
          epsilon*p 0*coordPartial 0 (directedWeight b lambda I) p| ≤ (D+2*D*M)*E := by
        exact (abs_add_le _ _).trans (by
          convert add_le_add hfirst hsecond using 1 <;> try with_reducible_and_instances rfl
          ring)
      exact hlift hh hNt
    · simp only [Fin.mk_one, Fin.isValue, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte,
        mul_zero, zero_mul, zero_add]
      have hh : |epsilon*p 0*coordPartial 1 (directedWeight b lambda I) p| ≤
          (16+2*D*(M+lambda))*E := by
        rw [abs_mul]
        convert mul_le_mul het hws (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> try with_reducible_and_instances rfl
        ring
      exact hlift hh hNss

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem multiplierProduct_partial_abs_bound
    {A m : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hAv : |A p| ≤ M) (hmv : |m p| ≤ V)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V) (i : Fin 2) :
    |coordPartial i (fun q => A q*m q) p| ≤ 2*M*V := by
  rw [HessianCalculus.coordPartial_mul_at hA hm i]
  calc
    _ ≤ |coordPartial i A p*m p| + |A p*coordPartial i m p| := abs_add_le _ _
    _ ≤ M*V + M*V := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (hAi i) hmv (abs_nonneg _) hM)
        ((mul_le_mul_of_nonneg_left (hmi i) (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hAv hV))
    _ = _ := by ring

theorem multiplierCoefficients_abs_bound
    {A B C m n : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmv : |m p| ≤ V) (hnv : |n p| ≤ V)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V)
    (hni : ∀ i : Fin 2, |coordPartial i n p| ≤ V) :
    |multiplierT B m n p| ≤ (1+M)*V ∧
    |multiplierS A C m n p| ≤ (3*M)*V ∧
    |multiplierJ A B C m n p| ≤ (1+4*M)*V := by
  have hAm := multiplierProduct_partial_abs_bound hA hm hM hV hAv hmv hAi hmi
  have hAn := multiplierProduct_partial_abs_bound hA hn hM hV hAv hnv hAi hni
  have hprod {a b : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ V) : |a*b| ≤ M*V := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hM
  have hbn := hprod hBv hnv
  have hbm := hprod hBv hmv
  have hcm := hprod hCv hmv
  have hcn := hprod hCv hnv
  refine ⟨?_, ?_, ?_⟩
  · unfold multiplierT
    have hdiff : |coordPartial 1 m p - coordPartial 0 n p| ≤ 2*V :=
      (abs_sub _ _).trans (by linarith [hmi 1, hni 0])
    have hhalf : |(coordPartial 1 m p-coordPartial 0 n p)/2| ≤ V := by
      rw [abs_div]
      norm_num
      linarith
    exact (abs_add_le _ _).trans (by nlinarith only [hhalf, hbn])
  · unfold multiplierS
    have h1 : |-coordPartial 1 (fun q => A q*m q) p/2| ≤ M*V := by
      rw [abs_div, abs_neg]
      norm_num
      linarith [hAm 1]
    have h2 : |coordPartial 0 (fun q => A q*n q) p/2| ≤ M*V := by
      rw [abs_div]
      norm_num
      linarith [hAn 0]
    calc
      _ ≤ |-coordPartial 1 (fun q => A q*m q) p/2 +
          coordPartial 0 (fun q => A q*n q) p/2| + |C p*m p| := abs_add_le _ _
      _ ≤ (|-coordPartial 1 (fun q => A q*m q) p/2| +
          |coordPartial 0 (fun q => A q*n q) p/2|) + |C p*m p| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by nlinarith only [h1, h2, hcm]
  · unfold multiplierJ
    calc
      _ ≤ |-coordPartial 0 m p + B p*m p - coordPartial 1 (fun q => A q*n q) p| +
          |C p*n p| := abs_add_le _ _
      _ ≤ (|-coordPartial 0 m p+B p*m p| + |coordPartial 1 (fun q => A q*n q) p|) +
          |C p*n p| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ ((|-coordPartial 0 m p|+|B p*m p|) + |coordPartial 1 (fun q => A q*n q) p|) +
          |C p*n p| := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ _ := by rw [abs_neg]; nlinarith only [hmi 0, hbm, hAn 1, hcn]

theorem multiplierQuadratic_abs_bound
    {A B C m n u : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmv : |m p| ≤ V) (hnv : |n p| ≤ V)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V)
    (hni : ∀ i : Fin 2, |coordPartial i n p| ≤ V) :
    |multiplierQuadratic A B C m n u p| ≤
      (2+8*M)*V*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) := by
  obtain ⟨hT,hS,hJ⟩ := multiplierCoefficients_abs_bound hA hm hn hM hV hAv hBv hCv hAi hmv hnv hmi hni
  have hh := scalarQuadratic_abs_bound (x := coordPartial 0 u p) (y := coordPartial 1 u p) hT hJ hS
  have heq : multiplierQuadratic A B C m n u p =
      multiplierT B m n p*(coordPartial 0 u p)^2 +
      multiplierJ A B C m n p*(coordPartial 0 u p*coordPartial 1 u p) +
      multiplierS A C m n p*(coordPartial 1 u p)^2 := by unfold multiplierQuadratic; ring
  rw [heq]
  convert hh using 1 <;> try with_reducible_and_instances rfl
  ring

theorem directedQuadratic_abs_le_seven
    {A B C I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M : ℝ}
    (hA : DifferentiableAt ℝ A p) (hId : DifferentiableAt ℝ I p)
    (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M) :
    |multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedQuadraticCostConstant D M lambda S MI * weightedGradient b u p := by
  obtain ⟨hmv,hnv,hmi,hni⟩ := directedMultiplier_firstJet_abs_le_seven
    hId hlambda hM heps heps1 ht hd hdD hs hIv hIi
  have hD : 0 ≤ D := hd.trans hdD
  have hN := (directedWeightJetBudget_bounds hD hM hlambda).1
  have hV : 0 ≤ directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)*edgeDistance b p^7 := by
    positivity
  have hh := multiplierQuadratic_abs_bound (u := u) hA
    (directedM_differentiableAt b lambda hId) (directedN_differentiableAt b lambda epsilon hId)
    hM hV hAv hBv hCv hAi hmv hnv hmi hni
  convert hh using 1 <;> try with_reducible_and_instances rfl
  unfold directedQuadraticCostConstant weightedGradient
  ring

theorem nonnegative_cutoff_defect_bound {chi a q : ℝ}
    (hchi : 0 ≤ chi ∧ chi ≤ 1) (ha : 0 ≤ a) : chi*max 0 (a-q) ≤ a+|q| := by
  have hmax : max 0 (a-q) ≤ a+|q| := by
    apply max_le
    · exact add_nonneg ha (abs_nonneg q)
    · linarith [neg_le_abs q]
  have hh := mul_le_mul hchi.2 hmax (le_max_left (0 : ℝ) (a-q)) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using hh

theorem directedCoercivityDefect_le_seven
    {A B C chi I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M c2 : ℝ}
    (hA : DifferentiableAt ℝ A p) (hId : DifferentiableAt ℝ I p)
    (hlambda : 0 ≤ lambda) (hM : 0 ≤ M) (hc2 : 0 ≤ c2)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M) (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤
      directedDefectCostConstant D M lambda S MI c2 * weightedGradient b u p := by
  have hQ := directedQuadratic_abs_le_seven (u := u) hA hId hlambda hM heps heps1 ht hd hdD
    hs hIv hIi hAv hBv hCv hAi
  have hW := directedWeight_le_seven hlambda hd hdD hs hIv
  have hW0 : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hE : 0 ≤ (coordPartial 0 u p)^2+(coordPartial 1 u p)^2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hc2) hE
  have hbase := nonnegative_cutoff_defect_bound
    (q := multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p)
    hchi (mul_nonneg (mul_nonneg hc2 hW0) hE)
  change directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ _ at hbase
  exact hbase.trans (by
    have hh := add_le_add hfirst hQ
    convert hh using 1 <;> try with_reducible_and_instances rfl
    unfold directedDefectCostConstant weightedGradient
    ring)

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem ellipticWeightC1_energy_nonneg
    {b c glow : ℝ} {chi K G1 u : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hg : 0 < glow) (hG1 : glow ≤ G1 p) (hp : p 1 ≤ b) :
    0 ≤ ellipticEnergy (fun q => G1 q*K q) (ellipticWeightC1 b c chi K) u p := by
  apply ellipticEnergy_nonneg _ _ _ p (ellipticWeightC1_nonneg _ _ _ _ _)
  intro hv
  have hplt : p 1 < b := by
    by_contra h
    have heq : p 1 = b := le_antisymm hp (le_of_not_gt h)
    rw [ellipticWeightC1_zero heq.ge] at hv
    exact (lt_irrefl (0 : ℝ)) hv
  have hvraw : 0 < ellipticWeight b c chi K p := by
    simpa only [ellipticWeightC1_eq hp] using hv
  have hk := ellipticWeight_pos_implies_curvature hc hplt hvraw
  have hKpos : 0 < K p := (mul_pos (by positivity : 0 < c/2) (sub_pos.mpr hplt)).trans hk
  exact mul_pos (hg.trans_le hG1) hKpos

theorem directedCostConstants_nonneg {D M lambda S MI X c2 : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda) (hX : 0 ≤ X) (hc2 : 0 ≤ c2) :
    0 ≤ directedFluxCostConstant D M lambda S MI X ∧
    0 ≤ directedDefectCostConstant D M lambda S MI c2 := by
  have hN := (directedWeightJetBudget_bounds hD hM hlambda).1
  constructor
  · unfold directedFluxCostConstant
    positivity
  · unfold directedDefectCostConstant directedQuadraticCostConstant
    positivity

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem actual_cap_directed_costs_le_elliptic
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A0 b kappa c1 c2 D glow lambda epsilon S MI M : ℝ}
    {G1 B C I u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hg : 0 < glow)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hbelow : p 1 ≤ b) (hdD : edgeDistance b p ≤ D)
    (ht : |p 0| ≤ 2) (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hId : DifferentiableAt ℝ I p) (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hG1 : glow ≤ G1 p)
    (hAd : DifferentiableAt ℝ (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p)
    (hAv : |G1 p*capPullback Y (gaussianCurvature (g0+eta)) p| ≤ M)
    (hAi : ∀ i : Fin 2,
      |coordPartial i (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p| ≤ M)
    (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hcoercive : capPullback Y (gaussianCurvature (g0+eta)) p ≤ c1*edgeDistance b p →
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C
          (directedM b lambda I) (directedN b lambda epsilon I) u p) :
    let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
    let chi := capSpatialCutoff L R A0
    let c := capOverlapThreshold kappa c1 D
    let X := capSpatialDerivativeConstant L R A0
    |directedCutoffError A chi I u b lambda epsilon p| +
      directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤
      (directedFluxCostConstant D M lambda S MI X + directedDefectCostConstant D M lambda S MI c2)*
        (D+1/(glow*c))*
          ellipticEnergy A (ellipticWeightC1 b c (capOuterSpatialCutoff L R A0)
            (capPullback Y (gaussianCurvature (g0+eta)))) u p := by
  let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
  let K := capPullback Y (gaussianCurvature (g0+eta))
  let chi := capSpatialCutoff L R A0
  let c := capOverlapThreshold kappa c1 D
  let X := capSpatialDerivativeConstant L R A0
  let E := ellipticEnergy A (ellipticWeightC1 b c (capOuterSpatialCutoff L R A0) K) u p
  let CE := D+1/(glow*c)
  let CF := directedFluxCostConstant D M lambda S MI X
  let CD := directedDefectCostConstant D M lambda S MI c2
  change |directedCutoffError A chi I u b lambda epsilon p| +
    directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ (CF+CD)*CE*E
  have hc : 0 < c := capOverlapThreshold_pos hk hc1 hD
  have hX : 0 ≤ X := (abs_nonneg _).trans (capSpatialCutoff_partial_uniform hL hR hA0 p 0)
  have hEnonneg : 0 ≤ E := ellipticWeightC1_energy_nonneg hc hg hG1 hbelow
  have hCE : 0 ≤ CE := by dsimp only [CE]; positivity
  have hconst := directedCostConstants_nonneg (S := S) (MI := MI) hD hM hlambda hX hc2
  have hCF : 0 ≤ CF := hconst.1
  have hCD : 0 ≤ CD := hconst.2
  have hd : 0 ≤ edgeDistance b p := sub_nonneg.mpr hbelow
  have hfluxcost : |directedCutoffError A chi I u b lambda epsilon p| ≤ CF*weightedGradient b u p :=
    directedCutoffError_abs_le_seven hlambda heps heps1 ht hd hdD hs hIv hAv
      (capSpatialCutoff_partial_uniform hL hR hA0 p)
  have hdefcost : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ CD*weightedGradient b u p :=
    directedCoercivityDefect_le_seven hAd hId hlambda hM hc2 heps heps1 ht hd hdD hs hIv hIi
      hAv hBv hCv hAi (capSpatialCutoff_range L R A0 p)
  by_cases hedge : p 1 < b
  · have hdpos : 0 < edgeDistance b p := sub_pos.mpr hedge
    have hflux : |directedCutoffError A chi I u b lambda epsilon p| ≤ CF*CE*E := by
      by_cases hz : directedCutoffError A chi I u b lambda epsilon p = 0
      · rw [hz, abs_zero]
        positivity
      · have hder : ∃ i : Fin 2, coordPartial i chi p ≠ 0 := by
          by_contra h
          have hh : ∀ i : Fin 2, coordPartial i chi p = 0 := by
            intro i
            by_contra hi
            exact h ⟨i,hi⟩
          exact hz (multiplierCutoffError_zero A chi (directedM b lambda I)
            (directedN b lambda epsilon I) u p (hh 0) (hh 1))
        obtain ⟨i,hi⟩ := hder
        have hgrad : weightedGradient b u p ≤ CE*E :=
          capOuterElliptic_gradient_on_actual_cutoff_support hL hR hA0 hk hc1 hD hg
            hbackground hsupport hpU hdisp hdpos hdD hG1 hi
        exact hfluxcost.trans (by
          have hh := mul_le_mul_of_nonneg_left hgrad hCF
          convert hh using 1 <;> try with_reducible_and_instances rfl
          ring)
    have hdef : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ CD*CE*E := by
      by_cases hz : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p = 0
      · rw [hz]
        positivity
      · have hgrad : weightedGradient b u p ≤ CE*E :=
          capOuterElliptic_gradient_on_defect hL hR hA0 hk hc1 hD hg hdpos hdD hG1 hcoercive hz
        exact hdefcost.trans (by
          have hh := mul_le_mul_of_nonneg_left hgrad hCD
          convert hh using 1 <;> try with_reducible_and_instances rfl
          ring)
    have hh := add_le_add hflux hdef
    convert hh using 1 <;> try with_reducible_and_instances rfl
    ring
  · have heq : p 1 = b := le_antisymm hbelow (le_of_not_gt hedge)
    rw [directedCutoffError_edge_zero A chi I u b lambda epsilon p heq,
      directedCoercivityDefect_edge_zero A B C chi I u b lambda epsilon c2 p hAd hId heq,
      abs_zero, zero_add]
    positivity

end SmoothLocal.Flow

end

end OAI
end

section
namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem capOuterSpatialCutoff_eq_threeEdge (L R A : ℝ) :
    capOuterSpatialCutoff L R A =
      threeEdgeCutoff (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
        (capOuterRight R) (capOuterBottom A) (capOuterBottomOne A) := by
  simp only [capOuterSpatialCutoff, capSpatialCutoff, neg_neg, capOuterLeft, capOuterLeftOne,
    capOuterRightOne, capOuterRight, capOuterBottom, capOuterBottomOne]

theorem capOuterRectangle_subset_domain {L R A b : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (hb : b < 2) :
    closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A) b ⊆ capChartDomain := by
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hA
  intro p hp
  exact ⟨⟨hlo.trans_le hp.1.1, hp.1.2.trans_lt hro⟩,
    ⟨hao.trans_le hp.2.1,hp.2.2.trans_lt hb⟩⟩

theorem capSpatialCutoff_outer_boundary {L R A b : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) :
    (∀ s ∈ Icc (capOuterBottom A) b,
      capSpatialCutoff L R A (boxPoint (capOuterLeft L) s) = 0 ∧
      capSpatialCutoff L R A (boxPoint (capOuterRight R) s) = 0) ∧
    (∀ t ∈ Icc (capOuterLeft L) (capOuterRight R),
      capSpatialCutoff L R A (boxPoint t (capOuterBottom A)) = 0) := by
  obtain ⟨hlo,hli,hlu,hlx⟩ := capEdges_bounds hL
  obtain ⟨hro,hri,hru,hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao,hai,hau,hax⟩ := capEdges_bounds hA
  have hlout : capOuterLeft L < capOuterEdge L := by
    have hh := capEdges_bounds hlo
    exact hh.2.1.trans hh.2.2.2
  have hrout : -capOuterEdge (-R) < capOuterRight R := by
    have hh := capEdges_bounds hro
    exact neg_lt_neg (hh.2.1.trans hh.2.2.2)
  have haout : capOuterBottom A < capOuterEdge A := by
    have hh := capEdges_bounds hao
    exact hh.2.1.trans hh.2.2.2
  constructor
  · intro s hs
    constructor
    · apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
      exact Or.inl (by simpa [boxPoint] using hlout.le)
    · apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
      exact Or.inr (Or.inl (by simpa [boxPoint] using hrout.le))
  · intro t ht
    apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
    exact Or.inr (Or.inr (by simpa [boxPoint] using haout.le))

end SmoothLocal.Weighted

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedForcingEnergy_bound
    {chi I f : Coord → ℝ} {p : Coord} {b lambda D S MI : ℝ}
    (hlambda : 0 ≤ lambda) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    directedForcingEnergy chi I f b lambda p ≤ D^8*Real.exp (lambda*S+MI)*(f p)^2 := by
  have hD : 0 ≤ D := hd.trans hdD
  have hW0 : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hW7 := directedWeight_le_seven hlambda hd hdD hs hI
  have hdpow := pow_le_pow_left₀ hd hdD 7
  have hW : directedWeight b lambda I p ≤ D^8*Real.exp (lambda*S+MI) := by
    calc
      _ ≤ D*Real.exp (lambda*S+MI)*edgeDistance b p^7 := hW7
      _ ≤ D*Real.exp (lambda*S+MI)*D^7 :=
        mul_le_mul_of_nonneg_left hdpow (by positivity)
      _ = _ := by ring
  have hchiW := mul_le_mul hchi.2 hW hW0 (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul, directedForcingEnergy] using mul_le_mul_of_nonneg_right hchiW (sq_nonneg (f p))

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem actual_cap_integrated_overlap_estimate
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A0 b kappa c1 c2 glow lambda epsilon MI M MK : ℝ}
    {G1 B C I u f : Coord → ℝ}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0) (hAb : A0 ≤ b) (hb : b ≤ 0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hc2 : 0 < c2) (hg : 0 < glow)
    (hM : 0 ≤ M) (hMK : 0 ≤ MK) (hlambda : 0 ≤ lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hK : ContDiffOn ℝ ∞ (capPullback Y (gaussianCurvature (g0+eta))) capChartDomain)
    (hG1 : ContDiffOn ℝ ∞ G1 capChartDomain) (hB : ContDiffOn ℝ ∞ B capChartDomain)
    (hC : ContDiffOn ℝ ∞ C capChartDomain) (hI : ContDiffOn ℝ ∞ I capChartDomain)
    (hu : ContDiffOn ℝ ∞ u capChartDomain)
    (hEq : ∀ p ∈ capChartDomain,
      multiplierOperator (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C u p = f p)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox)
    (himage : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      capChart Y p ∈ U)
    (hdisp : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hIv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |I p| ≤ MI)
    (hIi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hGlow : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, glow ≤ G1 p)
    (hAv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      |G1 p*capPullback Y (gaussianCurvature (g0+eta)) p| ≤ M)
    (hAi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p| ≤ M)
    (hBv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |B p| ≤ M)
    (hCv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |C p| ≤ M)
    (hKi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0+eta))) p| ≤ MK)
    (hcoercive : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      capPullback Y (gaussianCurvature (g0+eta)) p ≤ c1*edgeDistance b p →
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C
          (directedM b lambda I) (directedN b lambda epsilon I) u p) :
    let D := capDistanceBound A0 b
    let COverlap := capOverlapEnergyCost L R A0 b kappa c1 c2 glow M lambda MI
    let HElliptic := capEllipticRatioBudget L R A0 b kappa c1 glow MK M
    (c2/2)*rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b
      (directedGradientEnergy (capSpatialCutoff L R A0) I u b lambda) ≤
      ((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b (fun p => (f p)^2) +
      (COverlap*(D^6+HElliptic))*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b (fun p => (u p)^2) := by
  let tl := capOuterLeft L
  let tr := capOuterRight R
  let sb := capOuterBottom A0
  let D := capDistanceBound A0 b
  let c := capOverlapThreshold kappa c1 D
  let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
  let K := capPullback Y (gaussianCurvature (g0+eta))
  let chi := capSpatialCutoff L R A0
  let chi2 := capOuterSpatialCutoff L R A0
  let v := ellipticWeightC1 b c chi2 K
  let E := ellipticEnergy A v u
  let Err := directedCutoffError A chi I u b lambda epsilon
  let Def := directedCoercivityDefect A B C chi I u b lambda epsilon c2
  let COverlap := capOverlapEnergyCost L R A0 b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R A0 b kappa c1 glow MK M
  obtain ⟨htlo,htwidth,htone,hrone,hrwidth,htrhi,hsblo,hswidth,hsone,hlt,hrt⟩ :=
    capOuterRectangle_edges hL hR hA0
  have ht : tl ≤ tr := by dsimp only [tl,tr]; linarith
  have hs : sb ≤ b := by dsimp only [sb]; linarith
  have hD : 0 ≤ D := sub_nonneg.mpr hs
  have hc : 0 < c := capOverlapThreshold_pos hk hc1 hD
  have hbox : closedRectangle tl tr sb b ⊆ capChartDomain :=
    capOuterRectangle_subset_domain hL hR hA0 (by linarith)
  have hA : ContDiffOn ℝ ∞ A capChartDomain := hG1.mul hK
  have hchi : ContDiffOn ℝ ∞ chi capChartDomain := (capSpatialCutoff_contDiff _ _ _).contDiffOn
  have hchi2 : ContDiffOn ℝ ∞ chi2 capChartDomain := (capOuterSpatialCutoff_contDiff _ _ _).contDiffOn
  have hv : ContDiffOn ℝ 1 v capChartDomain := ellipticWeightC1_contDiffOn hc
    (hchi2.of_le (by simp)) (hK.of_le (by simp))
  have hW := directedWeight_contDiffOn b lambda hI
  have hm := hW.neg
  have hn : ContDiffOn ℝ ∞ (directedN b lambda epsilon I) capChartDomain :=
    (contDiffOn_const.mul (contDiffOn_apply ℝ ℝ 0 _)).mul hW
  have hut := partial_contDiffOn hu capChartDomain_isOpen 0
  have hus := partial_contDiffOn hu capChartDomain_isOpen 1
  have hgrad := (hut.pow 2).add (hus.pow 2)
  have hQ := multiplierQuadratic_contDiffOn capChartDomain_isOpen hA hB hC hm hn hu
  have hErr : ContinuousOn Err (closedRectangle tl tr sb b) :=
    (multiplierCutoffError_contDiffOn capChartDomain_isOpen hA hchi hm hn hu).continuousOn.mono hbox
  have hDef : ContinuousOn Def (closedRectangle tl tr sb b) :=
    (hchi.continuousOn.mul ((continuousOn_const (c := (0 : ℝ))).sup
      ((((contDiffOn_const (c := c2)).mul hW).mul hgrad).sub hQ).continuousOn)).mono hbox
  obtain ⟨_,_,hEnergy,_⟩ := elliptic_fields_C1 capChartDomain_isOpen hA hB hC hv hu
  have hE : ContinuousOn E (closedRectangle tl tr sb b) := hEnergy.mono hbox
  have hX : 0 ≤ capSpatialDerivativeConstant L R A0 :=
    (abs_nonneg _).trans (capSpatialCutoff_partial_uniform hL hR hA0 (boxPoint 0 0) 0)
  have hconst := directedCostConstants_nonneg (S := 2) (MI := MI) hD hM hlambda hX hc2.le
  have hOverlap : 0 ≤ COverlap := by
    dsimp only [COverlap,capOverlapEnergyCost]
    exact mul_nonneg (add_nonneg hconst.1 hconst.2) (by positivity)
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb b) : |Err p|+Def p ≤ COverlap*E p := by
    have hpD := hbox hp
    exact actual_cap_directed_costs_le_elliptic hL hR hA0 hk hc1 hc2.le hg hD hM hlambda heps heps1
      hbackground hsupport (himage p hp) (hdisp p hp) hp.2.2
      (by dsimp only [edgeDistance,D,capDistanceBound]; linarith [hp.2.1])
      (abs_lt.mpr hpD.1).le (abs_lt.mpr hpD.2).le (hIv p hp)
      ((hI.contDiffAt (capChartDomain_isOpen.mem_nhds hpD)).differentiableAt (by simp)) (hIi p hp)
      (hGlow p hp) ((hA.contDiffAt (capChartDomain_isOpen.mem_nhds hpD)).differentiableAt (by simp))
      (hAv p hp) (hAi p hp) (hBv p hp) (hCv p hp) (hcoercive p hp)
  have hcostIntegral := rectangleIntegral_mono ht hs (hErr.abs.add hDef) (continuousOn_const.mul hE) hpoint
  change rectangleIntegral tl tr sb b (fun p => |Err p| + Def p) ≤
    rectangleIntegral tl tr sb b (fun p => COverlap * E p) at hcostIntegral
  rw [rectangleIntegral_add ht hs hErr.abs hDef, rectangleIntegral_const_mul] at hcostIntegral
  have hEllRaw := threeEdge_elliptic_energy_bound htwidth hrwidth hswidth ht hs hc hMK hg hM
    capChartDomain_isOpen hK hG1 hB hC hu hbox hEq hKi hGlow hAv (fun p hp => hAi p hp 1) hBv hCv
  have hEll : rectangleIntegral tl tr sb b E ≤
      D^6*rectangleIntegral tl tr sb b (fun p => (f p)^2) +
        (D^6+HElliptic)*rectangleIntegral tl tr sb b (fun p => (u p)^2) := by
    calc
      _ = rectangleIntegral tl tr sb b
          (ellipticEnergy A (ellipticWeight b c
            (threeEdgeCutoff (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
              (capOuterRight R) (capOuterBottom A0) (capOuterBottomOne A0)) K) u) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        change ellipticWeightC1 b c chi2 K p * _ = _
        rw [ellipticWeightC1_eq hp.2.2]
        change ellipticWeight b c (capOuterSpatialCutoff L R A0) K p * _ = _
        rw [capOuterSpatialCutoff_eq_threeEdge]
        rfl
      _ ≤ _ := hEllRaw
  have hf : ContDiffOn ℝ ∞ f capChartDomain :=
    (ellipticOperator_contDiffOn capChartDomain_isOpen hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  have hF : ContinuousOn (directedForcingEnergy chi I f b lambda) (closedRectangle tl tr sb b) :=
    (((hchi.mul hW).mul (hf.pow 2)).continuousOn.mono hbox)
  have hf2 : ContinuousOn (fun p => (f p)^2) (closedRectangle tl tr sb b) := (hf.pow 2).continuousOn.mono hbox
  have hforcing := rectangleIntegral_mono ht hs hF (continuousOn_const.mul hf2)
    (fun p hp => directedForcingEnergy_bound hlambda (sub_nonneg.mpr hp.2.2)
      (show edgeDistance b p ≤ D by dsimp only [edgeDistance,D,capDistanceBound]; linarith [hp.2.1])
      (abs_lt.mpr (hbox hp).2).le (hIv p hp) (capSpatialCutoff_range L R A0 p))
  change rectangleIntegral tl tr sb b (directedForcingEnergy chi I f b lambda) ≤
    rectangleIntegral tl tr sb b (fun p => (D^8*Real.exp (lambda*2+MI)) * (f p)^2) at hforcing
  rw [rectangleIntegral_const_mul] at hforcing
  obtain ⟨hsides,hbottom⟩ := capSpatialCutoff_outer_boundary (b := b) hL hR hA0
  have hdir := integrated_directed_energy_with_explicit_costs ht hs capChartDomain_isOpen hA hB hC
    hchi hI hu hbox hsides hbottom hEq (fun p _ => (capSpatialCutoff_range L R A0 p).1)
      lambda epsilon 2 c2 hc2 heps heps1 (fun p hp => (abs_lt.mpr (hbox hp).1).le)
  norm_num only [show (1 : ℝ)+2^2=5 by norm_num] at hdir
  have hsourceConstant : 0 ≤ (5 : ℝ)/(2*c2) := by positivity
  have hcombined := add_le_add (mul_le_mul_of_nonneg_left hforcing hsourceConstant)
    (hcostIntegral.trans (mul_le_mul_of_nonneg_left hEll hOverlap))
  change (c2/2)*rectangleIntegral tl tr sb b (directedGradientEnergy chi I u b lambda) ≤ _
  exact hdir.trans (by
    convert hcombined using 1 <;> (first | rfl | ring))

end SmoothLocal.Flow

end

end OAI
end

theorem solution : type_of% @OAI.SmoothLocal.Flow.actual_cap_integrated_overlap_estimate := @OAI.SmoothLocal.Flow.actual_cap_integrated_overlap_estimate
