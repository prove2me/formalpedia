-- Prove2me | solution 1 for OAI.CKSSpatialManifold.original_CKS_replacement_intrinsic_chart_package
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:29:44.407205+00:00
-- url     : https://prove2.me/submissions/89e46f5f-b4d4-4a9f-87b6-aa39cadcf237

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSLorentz_exists_uniform_boost_collar_atlas
import Theorems.Thm_OAI_CKSLorentz_actual_same_end_smooth_replacement
import Theorems.Thm_OAI_CKSLorentz_original_source_patch_properties
import Theorems.Thm_OAI_CKSLorentz_hyperbolic_source_geometry
import Theorems.Thm_OAI_CKSLorentz_actual_same_end_DEC
import Theorems.Thm_OAI_CKSLorentz_actual_same_end_AF_ADM
import Theorems.Thm_OAI_CKSLorentz_actual_same_end_tail_integrable
import Theorems.Thm_OAI_CKSLorentz_actual_same_end_uniform_lower
import Theorems.Thm_OAI_CKSIntrinsicConstraints_global_constraints_from_end

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_congr {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (e : E) : D e f x = D e g x := by
  unfold D
  rw [h.fderiv_eq]

lemma contDiffAt_D {f : E → ℝ} {x : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f x)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) (e : E) : ContDiffAt ℝ m (D e f) x :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

end
end CKSCalculus

end









end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma matrix_det_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) : ContDiffAt ℝ ∞ (fun y => (G y).det) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  simp only [Matrix.det_fin_three]
  fun_prop

lemma matrix_inv_component_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => (G y)⁻¹ i j) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hd := (matrix_det_contDiffAt hg).inv h0
  simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul,
    Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 1 * G y 2 2 - G y 1 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 1 * G y 2 2) + G y 0 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 1 * G y 1 2 - G y 0 2 * G y 1 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 1 0 * G y 2 2) + G y 1 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 2 2 - G y 0 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 1 2) + G y 0 2 * G y 1 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 0 * G y 2 1 - G y 1 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 2 1) + G y 0 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 1 1 - G y 0 1 * G y 1 0)) x
    exact hd.mul (by fun_prop)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma injection_basis (a : A) : injection (CKSAngularGeometry.basis a)=CKSMixedGeometry.basis a.succ := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [CKSMixedGeometry.basis]
  · simp [CKSAngularGeometry.basis,CKSMixedGeometry.basis,Pi.single_apply]

lemma slice_hasFDerivAt (r : ℝ) (x : AP) : HasFDerivAt (slice r) injection x :=
  injection.hasFDerivAt.const_add _

lemma D_slice (a : A) (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : DifferentiableAt ℝ f (slice r x)) :
    D (CKSAngularGeometry.basis a) (fun y => f (slice r y)) x=
      D (CKSMixedGeometry.basis a.succ) f (slice r x) := by
  unfold D
  erw [fderiv_comp x hf (slice_hasFDerivAt r x).differentiableAt,
    (slice_hasFDerivAt r x).fderiv,ContinuousLinearMap.comp_apply,injection_basis]

end
end CKSAngularSlice

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

open MeasureTheory

open scoped Pointwise
def sphereHome (u : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  u.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      u.norm_map])

lemma sphereHome_val (u : Ambient ≃ₗᵢ[ℝ] Ambient) (x : Sphere) :
    (sphereHome u x).1 = u x.1 := rfl

lemma volume_preimage_isometry (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Ambient) :
    (volume : Measure Ambient) (u ⁻¹' s) = volume s := by
  have hm := u.toHomeomorph.toMeasurableEquiv.map_apply (μ := volume) s
  change (Measure.map u volume) s = volume (u ⁻¹' s) at hm
  rw [u.measurePreserving.map_eq] at hm
  exact hm.symm

lemma sphereCone_preimage (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Sphere) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereHome u ⁻¹' s)) =
      u ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨r, hr, u v.1, ⟨sphereHome u v, hv, rfl⟩, (u.map_smul r v.1).symm⟩
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, hx⟩
    refine ⟨r, hr, u.symm v.1, ⟨sphereHome u.symm v, ?_, rfl⟩, ?_⟩
    · change sphereHome u (sphereHome u.symm v) ∈ s
      have h : sphereHome u (sphereHome u.symm v) = v := by
        apply Subtype.ext
        exact u.apply_symm_apply v.1
      simpa [h] using hv
    · apply u.injective
      simpa using hx

theorem sphereHome_measurePreserving (u : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (sphereHome u) surfaceMeasure surfaceMeasure := by
  refine ⟨(sphereHome u).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereHome u).continuous.measurable hs,
    Measure.toSphere_apply' _ (hs.preimage (sphereHome u).continuous.measurable),
    Measure.toSphere_apply' _ hs, sphereCone_preimage, volume_preimage_isometry]

lemma sphereIntegral_apply (f : C(Sphere, ℝ)) :
    sphereIntegral f = ∫ x, f x ∂surfaceMeasure := by
  change inner ℝ (toL2 1) (toL2 f) = _
  rw [toL2, MeasureTheory.ContinuousMap.inner_toLp]
  simp

open scoped Manifold ContDiff Topology
open Set

lemma rotationGenerator_apply (i j k : Fin 3) (x : Ambient) :
    rotationGenerator i j x k = (if k = j then x i else 0) - (if k = i then x j else 0) := rfl

attribute [local instance] cksLocalInst_1853

lemma rotationGenerator_smooth (i j : Fin 3) : ContDiff ℝ ∞ (rotationGenerator i j) :=
  (rotationGenerator i j).toContinuousLinearMap.contDiff

lemma smoothRotation_smooth {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (i j : Fin 3) : ContDiffOn ℝ ∞ (smoothRotation i j F) puncturedSpace := by
  exact (hF.fderiv_of_isOpen puncturedSpace.isOpen (by simp)).clm_apply
    (rotationGenerator_smooth i j).contDiffOn

lemma planeRotation_hasDerivAt (i j : Fin 3) (hij : i ≠ j) (x : Ambient) (t : ℝ) :
    HasDerivAt (fun s => planeRotation i j hij s x)
      (rotationGenerator i j (planeRotation i j hij t x)) t := by
  have h : HasDerivAt (fun s => fun k : Fin 3 =>
      if k = i then Real.cos s * x i - Real.sin s * x j
      else if k = j then Real.sin s * x i + Real.cos s * x j else x k)
      (fun k => (rotationGenerator i j (planeRotation i j hij t x)) k) t := by
    apply hasDerivAt_pi.mpr
    intro k
    by_cases hi : k = i
    · subst k
      convert! ((Real.hasDerivAt_cos t).mul_const (x i)).sub
        ((Real.hasDerivAt_sin t).mul_const (x j)) using 1
      · funext s; simp
      · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij, hij.symm]
        ring
    · by_cases hj : k = j
      · subst k
        convert! ((Real.hasDerivAt_sin t).mul_const (x i)).add
          ((Real.hasDerivAt_cos t).mul_const (x j)) using 1
        · funext s; simp [hij.symm]
        · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij.symm]
          ring
      · simpa [rotationGenerator_apply, hi, hj] using hasDerivAt_const t (x k)
  convert! (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t h using 1

lemma smoothRotation_orbit_derivative {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) (x : Sphere) (t : ℝ) :
    HasDerivAt (fun s => F (planeRotation i j hij s (x : Ambient)))
      (smoothRotation i j F (planeRotation i j hij t (x : Ambient))) t := by
  have hn : (planeRotation i j hij t (x : Ambient)) ≠ 0 := by
    simpa using (planeRotation i j hij t).injective.ne (sphere_ne_zero x)
  have hd := (hF.contDiffAt (puncturedSpace.isOpen.mem_nhds hn)).differentiableAt (by simp)
  exact hd.hasFDerivAt.comp_hasDerivAt t (planeRotation_hasDerivAt i j hij x t)

theorem sphereIntegral_smoothRotation {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (i j : Fin 3) (hij : i ≠ j) :
    sphereIntegral (smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)) = 0 := by
  let f := smoothRestriction F hF
  let g := smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)
  let orb (t : ℝ) (x : Sphere) := sphereHome (planeRotation i j hij t) x
  have hcF (t : ℝ) : Continuous (fun x : Sphere => f (orb t x)) :=
    f.continuous.comp (sphereHome (planeRotation i j hij t)).continuous
  have hcG (t : ℝ) : Continuous (fun x : Sphere => g (orb t x)) :=
    g.continuous.comp (sphereHome (planeRotation i j hij t)).continuous
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := surfaceMeasure) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t x => f (orb t x)) (F' := fun t x => g (orb t x))
    (bound := fun _ => ‖g‖)
    (by simp) (Filter.Eventually.of_forall (fun t => (hcF t).aestronglyMeasurable))
    ((hcF 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hcG 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x t _ => g.norm_coe_le_norm (orb t x)))
    (integrable_const ‖g‖)
    (Filter.Eventually.of_forall (fun x t _ => smoothRotation_orbit_derivative hF i j hij x t))
  have he : (fun t : ℝ => ∫ x, f (orb t x) ∂surfaceMeasure) =
      fun _ => sphereIntegral f := by
    funext t
    rw [sphereIntegral_apply]
    exact (sphereHome_measurePreserving (planeRotation i j hij t)).integral_comp
      (sphereHome (planeRotation i j hij t)).measurableEmbedding f
  have hz := hd.2
  rw [he] at hz
  have he' := hz.unique (hasDerivAt_const 0 (sphereIntegral f))
  simpa [sphereIntegral_apply, orb, sphereHome_val, g, smoothRestriction] using he'

lemma smoothRotation_mul {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace)
    (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j (F * G) x = F x * smoothRotation i j G x + G x * smoothRotation i j F x := by
  have hf := (hF.contDiffAt (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hg := (hG.contDiffAt (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  simp [smoothRotation, fderiv_mul hf hg]

lemma inner_toL2 (f g : C(Sphere, ℝ)) :
    inner ℝ (toL2 f) (toL2 g) = sphereIntegral (f * g) := by
  rw [sphereIntegral_apply]
  change inner ℝ (ContinuousMap.toLp 2 surfaceMeasure ℝ f)
    (ContinuousMap.toLp 2 surfaceMeasure ℝ g) = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  simp [mul_comm]

theorem smoothRotation_skew_adjoint {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (toL2 (smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)))
      (toL2 (smoothRestriction G hG)) =
    -inner ℝ (toL2 (smoothRestriction F hF))
      (toL2 (smoothRestriction (smoothRotation i j G) (smoothRotation_smooth hG i j))) := by
  have he : smoothRestriction (smoothRotation i j (F * G)) (smoothRotation_smooth (hF.mul hG) i j) =
      smoothRestriction F hF * smoothRestriction (smoothRotation i j G) (smoothRotation_smooth hG i j) +
      smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j) * smoothRestriction G hG := by
    ext x
    change smoothRotation i j (F * G) x = _
    rw [smoothRotation_mul hF hG i j (sphere_ne_zero x)]
    change _ = F x * smoothRotation i j G x + smoothRotation i j F x * G x
    ring
  have h := sphereIntegral_smoothRotation (F := F * G) (hF.mul hG) i j hij
  rw [he, map_add] at h
  rw [inner_toL2, inner_toL2]
  linarith

lemma rotationGenerator_decomposition (x v : Ambient) :
    ‖x‖ ^ 2 • v = (∑ i : Fin 3, ∑ j : Fin 3, (x i * v j) • rotationGenerator i j x) +
      (∑ i : Fin 3, x i * v i) • x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Fin.sum_univ_three, rotationGenerator_apply] <;> ring

end
end CKSSphericalHarmonics

end


end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MeasureTheory Set

theorem sphereArea_eq_four_pi : sphereArea = 4 * Real.pi := by
  rw [sphereArea, sphereIntegral_apply]
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one]
  rw [Measure.toSphere_real_apply_univ]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI


noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

lemma boost_mass {e m : ℝ} {p : E} (hm0 : m ≠ 0) : boost e m p (m,0) = (e,p) := by
  simp [boost, hm0]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff Manifold Topology
open Set

def boundaryAmbient (e m : ℝ) (p : E) (n : E) : E :=
  (denominator e m p n)⁻¹ • boundarySpatial e m p n

lemma boundary_null (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) :
    boost e (mass e p) p (1,(n:E)) =
      denominator e (mass e p) p n • ((1:ℝ), (boundary e p he n : E)) := by
  have hd := (denominator_pos he (mass_pos he) n).ne'
  apply Prod.ext
  · simp [boost, denominator]
  · change boundarySpatial e (mass e p) p n =
      denominator e (mass e p) p n • ((denominator e (mass e p) p n)⁻¹ • _)
    simp [smul_smul, hd]

lemma boundaryAmbient_smooth {e m : ℝ} {p : E} {n : E}
    (hd : denominator e m p n ≠ 0) : ContDiffAt ℝ ∞ (boundaryAmbient e m p) n := by
  have hi : ContDiff ℝ ∞ (fun n : E => inner ℝ p n) :=
    ContDiff.inner ℝ contDiff_const contDiff_id
  have hD : ContDiff ℝ ∞ (denominator e m p) :=
    (contDiff_const.add hi).div_const m
  have hS : ContDiff ℝ ∞ (boundarySpatial e m p) :=
    contDiff_id.add ((contDiff_const.add (hi.div_const (m*(e+m)))).smul contDiff_const)
  exact (hD.contDiffAt.inv hd).smul hS.contDiffAt

lemma boundary_smooth (e : ℝ) (p : E) (he : ‖p‖ < e) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (boundary e p he) := by
  have h : ContMDiff (𝓡 2) 𝓘(ℝ,E) ∞
      (fun n : Sphere => boundaryAmbient e (mass e p) p n) := by
    intro n
    exact (boundaryAmbient_smooth (denominator_pos he (mass_pos he) n).ne').comp_contMDiffAt
      (contMDiff_coe_sphere (E := E) (n := 2)).contMDiffAt
  exact h.codRestrict_sphere fun n => (boundary e p he n).property

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def hyperbolicMetric (x Y Z : E) : ℝ :=
  inner ℝ Y Z - inner ℝ x Y * inner ℝ x Z / (1+‖x‖^2)

lemma hyperTime_derivative (x : E) :
    HasFDerivAt hyperTime ((hyperTime x)⁻¹ • innerSL ℝ x) x := by
  have h := (Real.hasDerivAt_sqrt (show 1+‖x‖^2 ≠ 0 by positivity)).comp_hasFDerivAt x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1)
  convert! h using 1
  ext Y
  simp [hyperTime, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma hyperboloid_derivative_pair (x Y Z : E) :
    minkowski (fderiv ℝ hyperboloid x Y) (fderiv ℝ hyperboloid x Z) = hyperbolicMetric x Y Z := by
  have hd := (hyperTime_derivative x).prodMk (hasFDerivAt_id x)
  change HasFDerivAt hyperboloid _ x at hd
  rw [hd.fderiv]
  simp only [minkowski, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    smul_apply, innerSL_apply_apply, smul_eq_mul, hyperbolicMetric]
  rw [← hyperTime_sq]
  ring

theorem hyperbolicMap_isometry {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (x Y Z : E) :
    hyperbolicMetric (hyperbolicMap e m p x)
      (fderiv ℝ (hyperbolicMap e m p) x Y) (fderiv ℝ (hyperbolicMap e m p) x Z) =
        hyperbolicMetric x Y Z := by
  have heq : hyperboloid ∘ hyperbolicMap e m p = boostCLM e m p ∘ hyperboloid := by
    funext z; exact hyperboloid_boost he hm0 hm z
  have hh := congrArg (fun f : E → V => fderiv ℝ f x) heq
  rw [fderiv_comp x (hyperboloid_smooth.differentiable (by simp)).differentiableAt
      ((hyperbolicMap_smooth e m p).differentiable (by simp)).differentiableAt,
    fderiv_comp x (boostCLM e m p).differentiableAt
      (hyperboloid_smooth.differentiable (by simp)).differentiableAt,
    (boostCLM e m p).fderiv] at hh
  have hy := congrArg (fun L : E →L[ℝ] V => L Y) hh
  have hz := congrArg (fun L : E →L[ℝ] V => L Z) hh
  simp only [ContinuousLinearMap.comp_apply] at hy hz
  rw [← hyperboloid_derivative_pair, hy, hz]
  exact (boost_minkowski hm0.ne' (add_pos (energy_pos he) hm0).ne' hm _ _).trans
    (hyperboloid_derivative_pair x Y Z)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped InnerProductSpace RealInnerProductSpace ContDiff

lemma denominator_derivative (e m : ℝ) (p n : E) :
    HasFDerivAt (denominator e m p) (timeDifferential m p) n := by
  convert! ((innerSL ℝ p).hasFDerivAt.const_add e).mul_const m⁻¹ using 1

lemma boundarySpatial_derivative (e m : ℝ) (p n : E) :
    HasFDerivAt (boundarySpatial e m p) (spaceDifferential e m p) n := by
  convert! (hasFDerivAt_id n).add
    ((((innerSL ℝ p).hasFDerivAt.mul_const (m*(e+m))⁻¹).const_add (1/m)).smul_const p) using 1

lemma boundaryAmbient_fderiv {e m : ℝ} {p n : E} (hd : denominator e m p n ≠ 0) (Y : E) :
    fderiv ℝ (boundaryAmbient e m p) n Y =
      (denominator e m p n)⁻¹ • spaceDifferential e m p Y -
        (timeDifferential m p Y / (denominator e m p n)^2) • boundarySpatial e m p n := by
  have hi := (hasDerivAt_inv hd).comp_hasFDerivAt n (denominator_derivative e m p n)
  have h := hi.smul (boundarySpatial_derivative e m p n)
  change HasFDerivAt (boundaryAmbient e m p) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  change _ = _
  simp only [smul_eq_mul, Function.comp_apply]
  module

lemma minkowski_null_tangent {e m : ℝ} {p n : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (Y : E) :
    -(denominator e m p n) * timeDifferential m p Y +
      inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Y) = inner ℝ n Y := by
  convert boost_minkowski hm0 hd hm ((1:ℝ),n) ((0:ℝ),Y) using 1 <;>
    simp [minkowski, boost, denominator, boundarySpatial]

lemma minkowski_tangent_tangent {e m : ℝ} {p : E} (hm0 : m ≠ 0) (hd : e+m ≠ 0)
    (hm : m^2 = e^2 - ‖p‖^2) (Y Z : E) :
    -timeDifferential m p Y * timeDifferential m p Z +
      inner ℝ (spaceDifferential e m p Y) (spaceDifferential e m p Z) = inner ℝ Y Z := by
  convert boost_minkowski hm0 hd hm ((0:ℝ),Y) ((0:ℝ),Z) using 1 <;>
    simp [minkowski, boost]

theorem boundary_conformal {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2 - ‖p‖^2) (n : Sphere) (Y Z : E)
    (hY : inner ℝ (n:E) Y = 0) (hZ : inner ℝ (n:E) Z = 0) :
    inner ℝ (fderiv ℝ (boundaryAmbient e m p) n Y)
      (fderiv ℝ (boundaryAmbient e m p) n Z) =
        (denominator e m p n)⁻¹ ^2 * inner ℝ Y Z := by
  have hD := (denominator_pos he hm0 n).ne'
  have hd := (add_pos (energy_pos he) hm0).ne'
  have hy := minkowski_null_tangent hm0.ne' hd hm Y (n := (n:E))
  have hz := minkowski_null_tangent hm0.ne' hd hm Z (n := (n:E))
  have hyz := minkowski_tangent_tangent hm0.ne' hd hm Y Z
  rw [hY] at hy
  rw [hZ] at hz
  have hself : inner ℝ (boundarySpatial e m p n) (boundarySpatial e m p n) =
      (denominator e m p n)^2 := by
    rw [real_inner_self_eq_norm_sq, boundarySpatial_norm he hm0 hm]
  rw [boundaryAmbient_fderiv hD, boundaryAmbient_fderiv hD]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_trivial, hself]
  rw [real_inner_comm (boundarySpatial e m p n) (spaceDifferential e m p Y)]
  have hy' : inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Y) =
      denominator e m p n * timeDifferential m p Y := by linarith
  have hz' : inner ℝ (boundarySpatial e m p n) (spaceDifferential e m p Z) =
      denominator e m p n * timeDifferential m p Z := by linarith
  have hyz' : inner ℝ (spaceDifferential e m p Y) (spaceDifferential e m p Z) =
      inner ℝ Y Z + timeDifferential m p Y * timeDifferential m p Z := by linarith
  rw [hy', hz', hyz']
  field_simp [hD]
  ring

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

lemma compactRoot_smooth : ContDiff ℝ ∞ compactRoot :=
  (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun s => by positivity)

lemma compactSpatial_smooth (e m : ℝ) (p : E) : ContDiff ℝ ∞ (compactSpatial e m p) := by
  have hi := ContDiff.inner ℝ (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × E => p)) contDiff_snd
  exact contDiff_snd.add ((((compactRoot_smooth.comp contDiff_fst).div_const m).add
    (hi.div_const (m*(e+m)))).smul contDiff_const)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Set

def compactRegion (e m : ℝ) (p : E) : Set (ℝ × E) :=
  {z | 0 < denominator e m p z.2 ∧ 0 < compactScale e m p z}

lemma compactScale_smooth_region (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : ContDiffAt ℝ ∞ (compactScale e m p) z :=
  (compactSpatial_smooth e m p).contDiffAt.norm ℝ (norm_ne_zero_iff.mp hz.2.ne')

end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma sum_coordinate_basis (v : Point) : ∑ k : I, v k • basis k = v := by
  ext k
  simp [basis, Finset.sum_apply, Pi.single_apply]

end
end CKSMixedGeometry

end




noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma compactPolar_contDiffAt {φ : Angle → E} {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z)) : ContDiffAt ℝ ∞ (compactPolar φ) z :=
  (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).contDiff.contDiffAt.prodMk
    (hφ.comp z angularProjection.contDiff.contDiffAt)

lemma compactAngle_contDiffAt (e m : ℝ) (p : E) {z : ℝ × E}
    (hz : z ∈ compactRegion e m p) : ContDiffAt ℝ ∞ (compactAngle e m p) z :=
  ((compactScale_smooth_region e m p hz).inv hz.2.ne').smul
    (compactSpatial_smooth e m p).contDiffAt

lemma compactLorentzCoefficients_contDiffAt (e m : ℝ) (p : E)
    (φ : Angle → E) (ψ : E → Angle) {z : Point}
    (hφ : ContDiffAt ℝ ∞ φ (angularProjection z))
    (hz : compactPolar φ z ∈ compactRegion e m p)
    (hψ : ContDiffAt ℝ ∞ ψ (compactAngle e m p (compactPolar φ z))) :
    ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) z := by
  have hp := compactPolar_contDiffAt hφ
  have hA := (compactScale_smooth_region e m p hz).comp z hp
  have ha := (compactAngle_contDiffAt e m p hz).comp z hp
  have hang := hψ.comp z ha
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · simpa only [compactLorentzCoefficients,slice_zero,Function.comp_def] using hA.log hz.2.ne'
  · simpa only [compactLorentzCoefficients,slice_succ,Function.comp_def] using (contDiffAt_pi.mp hang) a

end
end CKSLorentz

end

































noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus

def boundaryChart (e m : ℝ) (p : E) (φ : Angle → E) (ψ : E → Angle) (θ : Angle) : Angle :=
  ψ (boundaryAmbient e m p (φ θ))

def angularCoordinatePullback (Φ : Angle → Angle) (mg : I → I → Angle → ℝ)
    (a b : Fin 2) (θ : Angle) : ℝ :=
  ∑ i : Fin 2, ∑ k : Fin 2,
    D (CKSAngularGeometry.basis a) (fun η => Φ η i) θ *
    D (CKSAngularGeometry.basis b) (fun η => Φ η k) θ * mg i.succ k.succ (Φ θ)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularProjection_slice (r : ℝ) (θ : Angle) : angularProjection (slice r θ)=θ := by
  ext a
  exact slice_succ r θ a

lemma compactPolar_slice (r : ℝ) (θ : Angle) (φ : Angle → E) :
    compactPolar φ (slice r θ) = (r,φ θ) := by
  simp [compactPolar,angularProjection_slice]

lemma compactScale_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) :
    compactScale e m p (0,n) = denominator e m p n := by
  change ‖compactSpatial e m p (0,n)‖ = _
  rw [compactSpatial_zero]
  exact boundarySpatial_norm he hm0 hm ⟨n,hn⟩

lemma compactAngle_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) :
    compactAngle e m p (0,n) = boundaryAmbient e m p n := by
  simp only [compactAngle,compactScale_boundary he hm0 hm hn,compactSpatial_zero,boundaryAmbient]

lemma compactRegion_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2) {n : E}
    (hn : n ∈ Metric.sphere (0:E) 1) : (0,n) ∈ compactRegion e m p := by
  refine ⟨denominator_pos he hm0 ⟨n,hn⟩,?_⟩
  rw [compactScale_boundary he hm0 hm hn]
  exact denominator_pos he hm0 ⟨n,hn⟩

lemma compactLorentzCoefficients_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    compactLorentzCoefficients e m p φ ψ (slice 0 θ) =
      slice (Real.log (denominator e m p (φ θ))) (boundaryChart e m p φ ψ θ) := by
  simp only [compactLorentzCoefficients,compactPolar_slice,compactScale_boundary he hm0 hm hn,
    compactAngle_boundary he hm0 hm hn,boundaryChart]

lemma compactLeadingCoefficient_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (q : ℕ) (M : Angle → ℝ) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    compactLeadingCoefficient e m p φ ψ q M (slice 0 θ) =
      (denominator e m p (φ θ))⁻¹^q * M (boundaryChart e m p φ ψ θ) := by
  simp only [compactLeadingCoefficient,compactLorentzCoefficients_boundary he hm0 hm φ ψ hn,
    slice_zero,angularProjection_slice,neg_mul,Real.exp_neg,Real.exp_nat_mul,
    Real.exp_log (denominator_pos he hm0 ⟨φ θ,hn⟩),inv_pow]

theorem lorentzRadialLeading_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (mr : Angle → ℝ) {θ : Angle}
    (hn : φ θ ∈ Metric.sphere (0:E) 1) :
    lorentzRadialLeading e m p φ ψ mr θ =
      (denominator e m p (φ θ))⁻¹^3 * mr (boundaryChart e m p φ ψ θ) :=
  compactLeadingCoefficient_boundary he hm0 hm φ ψ 3 mr hn

lemma lorentzLogJac_boundary_angular {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) {θ : Angle}
    (hn : ∀ᶠ η in 𝓝 θ, φ η ∈ Metric.sphere (0:E) 1)
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hψ : ContDiffAt ℝ ∞ ψ (boundaryAmbient e m p (φ θ))) (a i : Fin 2) :
    lorentzLogJac e m p φ ψ a.succ i.succ (slice 0 θ) =
      D (CKSAngularGeometry.basis a) (fun η => boundaryChart e m p φ ψ η i) θ := by
  have hn0 := hn.self_of_nhds
  have hc : ContDiffAt ℝ ∞ (compactLorentzCoefficients e m p φ ψ) (slice 0 θ) := by
    apply compactLorentzCoefficients_contDiffAt e m p φ ψ
    · simpa only [angularProjection_slice] using hφ
    · simpa only [compactPolar_slice] using compactRegion_boundary he hm0 hm hn0
    · simpa only [compactPolar_slice,compactAngle_boundary he hm0 hm hn0] using hψ
  have hci := ((contDiffAt_pi.mp hc) i.succ).differentiableAt (by simp)
  simp only [lorentzLogJac,Fin.succ_ne_zero,false_and,ite_false,zero_add,
    backwardScaledD,backwardFactor,one_mul]
  rw [←D_slice a 0 hci]
  apply D_congr
  filter_upwards [hn] with η hη
  simp only [compactLorentzCoefficients_boundary he hm0 hm φ ψ hη,slice_succ]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

theorem lorentzAngularLeading_boundary {e m : ℝ} {p : E}
    (he : ‖p‖ < e) (hm0 : 0 < m) (hm : m^2=e^2-‖p‖^2)
    (φ : Angle → E) (ψ : E → Angle) (mg : I → I → Angle → ℝ) {θ : Angle}
    (hn : ∀ᶠ η in 𝓝 θ, φ η ∈ Metric.sphere (0:E) 1)
    (hφ : ContDiffAt ℝ ∞ φ θ)
    (hψ : ContDiffAt ℝ ∞ ψ (boundaryAmbient e m p (φ θ))) (a b : Fin 2) :
    lorentzAngularLeading e m p φ ψ mg a.succ b.succ θ =
      (denominator e m p (φ θ))⁻¹ *
        angularCoordinatePullback (boundaryChart e m p φ ψ) mg a b θ := by
  simp only [lorentzAngularLeading,transformedAngularLeading,Fin.sum_univ_succ,
    angularLeadingEntry,ne_eq,not_true_eq_false,false_and,and_false,ite_false,
    mul_zero,Finset.sum_const_zero,zero_add,Fin.succ_ne_zero,not_false_eq_true,
    and_self,ite_true,compactAngularCoefficient]
  simp_rw [lorentzLogJac_boundary_angular he hm0 hm φ ψ hn hφ hψ]
  have hc (M : Angle → ℝ) :
      compactLeadingCoefficient e m p φ ψ 1 M (slice 0 θ) =
        (denominator e m p (φ θ))⁻¹ * M (boundaryChart e m p φ ψ θ) := by
    simpa only [Nat.cast_one,pow_one] using
      compactLeadingCoefficient_boundary he hm0 hm φ ψ 1 M hn.self_of_nhds
  simp_rw [hc]
  simp only [angularCoordinatePullback,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  ring

end
end CKSLorentz

end





noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

attribute [local instance] stereoDimension

namespace SmoothAngularPatch

lemma param_chart (P : SmoothAngularPatch) {n : Sphere} (hn : n ∈ P.chart.source) :
    P.param (P.chart n)=(n:E) := congrArg Subtype.val (P.chart.left_inv hn)

end SmoothAngularPatch
end
end CKSLorentz

end





noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularSlice Set
open scoped ContDiff Topology

lemma SourceRemainderOn.mono {j q : ℕ} {U V : Set Point} {f : Point → ℝ}
    (hf : SourceRemainderOn j q V f) (hUV : U ⊆ V) : SourceRemainderOn j q U f := by
  obtain ⟨B,hB,hb⟩ := hf.bound
  exact ⟨fun y hy => hf.regular y (hUV hy),B,hB,fun y hy => hb y (hUV hy)⟩

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

lemma SourceCKSComponents.mono {j q : ℕ} {U V : Set Point}
    {A : I → I → Point → ℝ} {mr : Angle → ℝ} {mg : I → I → Angle → ℝ}
    (hA : SourceCKSComponents j q V A mr mg) (hUV : U ⊆ V) :
    SourceCKSComponents j q U A mr mg :=
  ⟨hA.radial.mono hUV,fun i k hik => (hA.mixed i k hik).mono hUV,
    fun i k hi hk => (hA.angular i k hi hk).mono hUV⟩

end
end CKSLorentz

end



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
def angularJacobian (Φ : Angle → Angle) (θ : Angle) : AngularMatrix := fun a i =>
  D (CKSAngularGeometry.basis a) (fun η => Φ η i) θ
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

lemma param_fderiv_leftInverse (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) :
    (fderiv ℝ P.extension (P.param θ)).comp (fderiv ℝ P.param θ) =
      ContinuousLinearMap.id ℝ Angle := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hψ := (P.extension_contDiffAt_param hθ).differentiableAt (by simp)
  have hg : (fun η => P.extension (P.param η)) =ᶠ[𝓝 θ] id := by
    filter_upwards [P.chart.open_target.mem_nhds hθ] with η hη
    exact P.extension_param hη
  have ht := hg.fderiv_eq (𝕜:=ℝ)
  change fderiv ℝ (P.extension ∘ P.param) θ = fderiv ℝ id θ at ht
  rw [fderiv_comp θ hψ hφ,fderiv_id] at ht
  exact ht

lemma param_fderiv_injective (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : Function.Injective (fderiv ℝ P.param θ) := by
  intro v w hvw
  have h := congrArg (fderiv ℝ P.extension (P.param θ)) hvw
  have hl := P.param_fderiv_leftInverse hθ
  have hv := congrArg (fun L : Angle →L[ℝ] Angle => L v) hl
  have hw := congrArg (fun L : Angle →L[ℝ] Angle => L w) hl
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
    hv.symm.trans (h.trans hw)

lemma param_tangent (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (v : Angle) : inner ℝ (P.param θ) (fderiv ℝ P.param θ v) = 0 := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hconst : (fun η => inner ℝ (P.param η) (P.param η)) = fun _ : Angle => (1:ℝ) := by
    funext η
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖P.param η‖=1 := P.param_norm η
    rw [hn,one_pow]
  have hd := fderiv_inner_apply (𝕜:=ℝ) hφ hφ v
  rw [hconst] at hd
  simp only [fderiv_fun_const] at hd
  change 0 = inner ℝ (P.param θ) (fderiv ℝ P.param θ v) +
    inner ℝ (fderiv ℝ P.param θ v) (P.param θ) at hd
  have hc := real_inner_comm (fderiv ℝ P.param θ v) (P.param θ)
  linarith

lemma roundMetric_posDef (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    (angularRoundMetric P.param θ).PosDef := by
  change (Matrix.gram ℝ (fun a => fderiv ℝ P.param θ (CKSAngularGeometry.basis a))).PosDef
  apply Matrix.posDef_gram_iff_linearIndependent.mpr
  have h := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map'
    (fderiv ℝ P.param θ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (P.param_fderiv_injective hθ))
  simpa only [Function.comp_def,Pi.basisFun_apply,CKSAngularGeometry.basis,
    ContinuousLinearMap.coe_coe] using h

end SmoothAngularPatch

lemma angular_vector_expansion (v : Angle) :
    ∑ a : Fin 2, v a • CKSAngularGeometry.basis a = v := by
  funext i
  fin_cases i <;> simp [CKSAngularGeometry.basis,Pi.single_apply]

lemma angularJacobian_apply {Φ : Angle → Angle} {θ : Angle}
    (hΦ : DifferentiableAt ℝ Φ θ) (a : Fin 2) :
    fderiv ℝ Φ θ (CKSAngularGeometry.basis a) =
      ∑ i : Fin 2, angularJacobian Φ θ a i • CKSAngularGeometry.basis i := by
  conv_lhs => rw [← angular_vector_expansion (fderiv ℝ Φ θ (CKSAngularGeometry.basis a))]
  congr 1; funext i
  congr 1
  simp only [angularJacobian,D,fderiv_apply hΦ,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

end
end CKSLorentz

end











































































































end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def boostField (p n : E) : E := p-inner ℝ p n • n

def flowDLinear (p : E) (t : ℝ) : E →L[ℝ] ℝ := t • innerSL ℝ p
def flowSLinear (p : E) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (flowCoeff p t • innerSL ℝ p).smulRight p

lemma flowEnergy_pos (p : E) (t : ℝ) : 0 < flowEnergy p t := Real.sqrt_pos.2 (by positivity)
lemma flowEnergy_sq (p : E) (t : ℝ) : flowEnergy p t ^2 = 1+t^2*‖p‖^2 := Real.sq_sqrt (by positivity)
lemma flowEnergy_add_pos (p : E) (t : ℝ) : 0 < flowEnergy p t+1 := by linarith [flowEnergy_pos p t]
lemma flowEnergy_gt (p : E) (t : ℝ) : ‖t • p‖ < flowEnergy p t := by
  rw [norm_smul, Real.norm_eq_abs]
  have hs : (|t| * ‖p‖)^2 = t^2*‖p‖^2 := by rw [mul_pow, sq_abs]
  nlinarith [flowEnergy_sq p t, flowEnergy_pos p t, norm_nonneg p, abs_nonneg t]

lemma flowEnergy_smooth (p : E) : ContDiff ℝ ∞ (flowEnergy p) :=
  (contDiff_const.add ((contDiff_id.pow 2).mul contDiff_const)).sqrt (fun t => by positivity)
lemma flowCoeff_smooth (p : E) : ContDiff ℝ ∞ (flowCoeff p) :=
  (contDiff_id.pow 2).div ((flowEnergy_smooth p).add contDiff_const)
    (fun t => (flowEnergy_add_pos p t).ne')
lemma flowD_smooth (p : E) : ContDiff ℝ ∞ (fun z : ℝ × E => flowD p z.1 z.2) :=
  ((flowEnergy_smooth p).comp contDiff_fst).add
    (contDiff_fst.mul (ContDiff.inner ℝ contDiff_const contDiff_snd))
lemma flowS_smooth (p : E) : ContDiff ℝ ∞ (fun z : ℝ × E => flowS p z.1 z.2) :=
  contDiff_snd.add ((contDiff_fst.add (((flowCoeff_smooth p).comp contDiff_fst).mul
    (ContDiff.inner ℝ contDiff_const contDiff_snd))).smul contDiff_const)

lemma flowD_eq (p : E) (t : ℝ) (n : E) :
    flowD p t n = denominator (flowEnergy p t) 1 (t • p) n := by simp [flowD, denominator, inner_smul_left]
lemma flowS_eq (p : E) (t : ℝ) (n : E) :
    flowS p t n = boundarySpatial (flowEnergy p t) 1 (t • p) n := by
  simp only [flowS, flowCoeff, boundarySpatial, inner_smul_left, conj_trivial, one_div,
    inv_one, one_mul, smul_smul]
  congr 1
  ring_nf
lemma flowD_pos (p : E) (t : ℝ) (n : Sphere) : 0 < flowD p t n := by
  rw [flowD_eq]
  exact denominator_pos (flowEnergy_gt p t) zero_lt_one n
lemma flowS_norm (p : E) (t : ℝ) (n : Sphere) : ‖flowS p t n‖ = flowD p t n := by
  rw [flowS_eq, flowD_eq]
  apply boundarySpatial_norm (flowEnergy_gt p t) zero_lt_one
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [flowEnergy_sq p t]
lemma flowPhi_norm (p : E) (t : ℝ) (n : Sphere) : ‖flowPhi p t n‖ = 1 := by
  rw [flowPhi, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (flowD_pos p t n)), flowS_norm]
  exact inv_mul_cancel₀ (flowD_pos p t n).ne'

lemma flowEnergy_derivative (p : E) (t : ℝ) :
    HasDerivAt (flowEnergy p) (t*‖p‖^2/flowEnergy p t) t := by
  have h := (Real.hasDerivAt_sqrt (show 1+t^2*‖p‖^2 ≠ 0 by positivity)).comp t
    ((((hasDerivAt_id t).pow 2).mul_const (‖p‖^2)).const_add 1)
  convert! h using 1
  simp [flowEnergy]
  ring

lemma flowCoeff_derivative (p : E) (t : ℝ) :
    HasDerivAt (flowCoeff p) (t/flowEnergy p t) t := by
  have h := ((hasDerivAt_id t).pow 2).div
    ((flowEnergy_derivative p t).add_const 1) (flowEnergy_add_pos p t).ne'
  convert! h using 1
  have hq := flowEnergy_sq p t
  have hpos := (flowEnergy_pos p t).ne'
  have hadd := (flowEnergy_add_pos p t).ne'
  simp only [id_eq, Pi.pow_apply, pow_one, mul_one, Nat.cast_ofNat, Nat.reduceSub]
  field_simp
  nlinarith [congrArg (fun x : ℝ => t*x) hq]

lemma flowD_derivative (p : E) (t : ℝ) (n : E) :
    HasDerivAt (fun t => flowD p t n) (t*‖p‖^2/flowEnergy p t+inner ℝ p n) t := by
  convert! (flowEnergy_derivative p t).add ((hasDerivAt_id t).mul_const (inner ℝ p n)) using 1
  simp
lemma flowS_derivative (p : E) (t : ℝ) (n : E) :
    HasDerivAt (fun t => flowS p t n) ((1+t/flowEnergy p t*inner ℝ p n) • p) t := by
  convert! (((hasDerivAt_id t).add ((flowCoeff_derivative p t).mul_const (inner ℝ p n))).smul_const p).const_add n using 1

lemma flowD_fderivative (p : E) (t : ℝ) (n : E) :
    HasFDerivAt (flowD p t) (flowDLinear p t) n := by
  convert! (((innerSL ℝ p).hasFDerivAt.const_mul t).const_add (flowEnergy p t)) using 1
lemma flowS_fderivative (p : E) (t : ℝ) (n : E) :
    HasFDerivAt (flowS p t) (flowSLinear p t) n := by
  convert! (hasFDerivAt_id n).add
    ((((innerSL ℝ p).hasFDerivAt.const_mul (flowCoeff p t)).const_add t).smul_const p) using 1

lemma flowD_transport (p : E) (t : ℝ) (n : E) :
    flowEnergy p t * (t*‖p‖^2/flowEnergy p t + inner ℝ p n) =
      flowDLinear p t (boostField p n)+inner ℝ p n*flowD p t n := by
  simp only [flowDLinear, smul_apply, innerSL_apply_apply, smul_eq_mul,
    boostField, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, flowD]
  field_simp [(flowEnergy_pos p t).ne']
  ring

lemma flowS_transport (p : E) (t : ℝ) (n : E) :
    flowEnergy p t • ((1+t/flowEnergy p t*inner ℝ p n) • p) =
      flowSLinear p t (boostField p n)+inner ℝ p n • flowS p t n := by
  simp only [flowSLinear, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul,
    boostField, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, flowS, flowCoeff]
  have hq : t^2*‖p‖^2/(flowEnergy p t+1) = flowEnergy p t-1 := by
    apply (div_eq_iff (flowEnergy_add_pos p t).ne').2
    nlinarith [flowEnergy_sq p t]
  have hc : flowEnergy p t * (1+t/flowEnergy p t*inner ℝ p n) =
      1+t*inner ℝ p n+t^2/(flowEnergy p t+1)*‖p‖^2 := by
    rw [show t^2/(flowEnergy p t+1)*‖p‖^2 = t^2*‖p‖^2/(flowEnergy p t+1) by ring, hq]
    field_simp [(flowEnergy_pos p t).ne']
    ring
  rw [smul_smul, hc]
  module

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open scoped RealInnerProductSpace ContDiff
open Finset

def boostField (p x : Ambient) : Ambient := p - inner ℝ p x • x

def coordinateCM (i : Fin 3) : C(Sphere,ℝ) :=
  smoothRestriction (fun x : Ambient => x i) (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn

lemma smoothRotation_coordinate (i j k : Fin 3) (x : Ambient) :
    smoothRotation i j (fun x : Ambient => x k) x =
      (if k=j then x i else 0) - (if k=i then x j else 0) := by
  change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) k) x _ = _
  rw [(EuclideanSpace.proj (𝕜 := ℝ) k).fderiv]
  exact rotationGenerator_apply i j k x

lemma sphereIntegral_coordinate_rotation {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (i j : Fin 3) :
    sphereIntegral (coordinateCM i *
      smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j)) =
      if i=j then 0 else sphereIntegral (coordinateCM j * smoothRestriction F hF) := by
  by_cases hij : i=j
  · subst j
    have hzero : smoothRestriction (smoothRotation i i F) (smoothRotation_smooth hF i i) = 0 := by
      ext n
      change fderiv ℝ F n (rotationGenerator i i n) = 0
      have hgen : rotationGenerator i i (n:Ambient) = 0 := by ext k; simp [rotationGenerator_apply]
      rw [hgen, map_zero]
    simp [hzero]
  have h := smoothRotation_skew_adjoint (F := fun x : Ambient => x i) (G := F)
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn hF i j hij
  rw [inner_toL2, inner_toL2] at h
  have he : smoothRestriction (smoothRotation i j (fun x : Ambient => x i))
      (smoothRotation_smooth (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn i j) = -coordinateCM j := by
    ext n
    change smoothRotation i j (fun x : Ambient => x i) n = -(n:Ambient) j
    simp [smoothRotation_coordinate, hij]
  rw [he] at h
  simp only [neg_mul, map_neg] at h
  simpa [hij, coordinateCM] using neg_injective h.symm

lemma boostField_decomposition (p : Ambient) (n : Sphere) :
    boostField p n = ∑ i : Fin 3, ∑ j : Fin 3,
      ((n:Ambient) i * p j) • rotationGenerator i j n := by
  have h := rotationGenerator_decomposition (n:Ambient) p
  have hn : ‖(n:Ambient)‖ = 1 := by simp
  rw [hn, one_pow, one_smul] at h
  have hi : inner ℝ p (n:Ambient) = ∑ i : Fin 3, (n:Ambient) i * p i := by
    rw [PiLp.inner_apply]
    simp [mul_comm]
  unfold boostField
  rw [hi]
  exact sub_eq_iff_eq_add.mpr h

theorem sphereIntegral_boostField {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (p : Ambient) :
    ∫ n : Sphere, fderiv ℝ F n (boostField p n) ∂surfaceMeasure =
      2 * ∫ n : Sphere, inner ℝ p (n:Ambient) * F n ∂surfaceMeasure := by
  let L : C(Sphere,ℝ) := ∑ i : Fin 3, ∑ j : Fin 3,
    p j • (coordinateCM i * smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j))
  have hL : ∀ n : Sphere, L n = fderiv ℝ F n (boostField p n) := by
    intro n
    rw [boostField_decomposition]
    simp only [map_sum, map_smul, L, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      ContinuousMap.mul_apply, smul_eq_mul, coordinateCM, smoothRestriction, smoothRotation, ContinuousMap.coe_mk]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    ring
  have hi : ∫ n : Sphere, fderiv ℝ F n (boostField p n) ∂surfaceMeasure = sphereIntegral L := by
    rw [sphereIntegral_apply]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun n => (hL n).symm
  rw [hi]
  have hsig : sphereIntegral L =
      2 * sphereIntegral ((∑ j : Fin 3, p j • coordinateCM j) * smoothRestriction F hF) := by
    simp only [L, map_sum, map_smul, smul_eq_mul, sphereIntegral_coordinate_rotation hF]
    simp only [Fin.sum_univ_three]
    simp only [Fin.reduceEq, ite_true, ite_false, mul_zero, zero_add, add_zero]
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  rw [hsig, sphereIntegral_apply]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with n
  simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, coordinateCM, smoothRestriction, ContinuousMap.coe_mk]
  congr 1
  rw [PiLp.inner_apply]
  simp [mul_comm]

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open Set

lemma boostField_tangent (p : E) (n : Sphere) : inner ℝ (n:E) (boostField p n) = 0 := by
  simp [boostField, inner_sub_right, inner_smul_right, real_inner_comm]

lemma norm_derivative_sphere (n : Sphere) : HasFDerivAt (norm : E → ℝ) (innerSL ℝ (n:E)) n := by
  have h := (Real.hasDerivAt_sqrt (show ‖(n:E)‖^2 ≠ 0 by rw [sphere_norm]; norm_num)).comp_hasFDerivAt (n:E)
    (hasStrictFDerivAt_norm_sq (n:E)).hasFDerivAt
  convert! h using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg x)).symm
  · ext x
    simp

lemma normalizeAmbient_fderiv_tangent (n : Sphere) (Y : E) (hY : inner ℝ (n:E) Y = 0) :
    fderiv ℝ normalizeAmbient n Y = Y := by
  have hi := (hasDerivAt_inv (show ‖(n:E)‖ ≠ 0 by rw [sphere_norm]; norm_num)).comp_hasFDerivAt (n:E)
    (norm_derivative_sphere n)
  have h := hi.smul (hasFDerivAt_id (n:E))
  change HasFDerivAt normalizeAmbient _ n at h
  rw [h.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, hY]

lemma flowPhi_smooth_at (p : E) (t : ℝ) (n : Sphere) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => flowPhi p z.1 z.2) (t,(n:E)) :=
  (((flowD_smooth p).contDiffAt).inv (flowD_pos p t n).ne').smul (flowS_smooth p).contDiffAt

lemma flowPhi_nonzero (p : E) (t : ℝ) (n : Sphere) : flowPhi p t n ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [flowPhi_norm]; norm_num

lemma flowPhi_fderiv (p : E) (t : ℝ) (n : Sphere) (Y : E) :
    fderiv ℝ (flowPhi p t) n Y =
      (flowD p t n)⁻¹ • flowSLinear p t Y -
        (flowDLinear p t Y/(flowD p t n)^2) • flowS p t n := by
  have hi := (hasDerivAt_inv (flowD_pos p t n).ne').comp_hasFDerivAt (n:E) (flowD_fderivative p t n)
  have h := hi.smul (flowS_fderivative p t n)
  change HasFDerivAt (flowPhi p t) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Function.comp_apply]
  module

lemma flowPhi_derivative (p : E) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => flowPhi p t n)
      ((flowD p t n)⁻¹ • ((1+t/flowEnergy p t*inner ℝ p (n:E)) • p) -
        ((t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E))/(flowD p t n)^2) • flowS p t n) t := by
  convert! ((flowD_derivative p t n).inv (flowD_pos p t n).ne').smul (flowS_derivative p t n) using 1
  module

lemma flowPhi_transport (p : E) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => flowPhi p t n)
      ((flowEnergy p t)⁻¹ • fderiv ℝ (flowPhi p t) n (boostField p n)) t := by
  convert! flowPhi_derivative p t n using 1
  rw [flowPhi_fderiv]
  have hS := flowS_transport p t (n:E)
  have hD := flowD_transport p t (n:E)
  have hS' : flowSLinear p t (boostField p n) =
      flowEnergy p t • ((1+t/flowEnergy p t*inner ℝ p (n:E)) • p) - inner ℝ p (n:E) • flowS p t n :=
    eq_sub_of_add_eq hS.symm
  have hD' : flowDLinear p t (boostField p n) =
      flowEnergy p t * (t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E)) - inner ℝ p (n:E)*flowD p t n :=
    eq_sub_of_add_eq hD.symm
  rw [hS', hD']
  have hE := (flowEnergy_pos p t).ne'
  have hden := (flowD_pos p t n).ne'
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hE, hden]
  ring

lemma weightedPullback_smooth_at (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    ContDiffAt ℝ ∞ (fun z : ℝ × E => weightedPullback p z.1 F z.2) (t,(n:E)) := by
  have hc := hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))
  have hd : ContDiffAt ℝ ∞ (fun z : ℝ × E => (flowD p z.1 z.2)⁻¹ ^2) (t,(n:E)) :=
    ((flowD_smooth p).contDiffAt.inv (flowD_pos p t n).ne').pow 2
  exact hd.mul (hc.comp (t,(n:E)) (flowPhi_smooth_at p t n))

lemma weightedPullback_spatial_derivative (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) (Y : E) :
    fderiv ℝ (weightedPullback p t F) n Y =
      (2*(flowD p t n)⁻¹*(-flowDLinear p t Y/(flowD p t n)^2))*F (flowPhi p t n) +
        (flowD p t n)⁻¹ ^2 * fderiv ℝ F (flowPhi p t n) (fderiv ℝ (flowPhi p t) n Y) := by
  have hphi : DifferentiableAt ℝ (flowPhi p t) (n:E) := by
    convert! ((flowPhi_smooth_at p t n).comp (n:E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hf := (hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))).differentiableAt (by simp)
  have ha := ((hasDerivAt_inv (flowD_pos p t n).ne').pow 2).comp_hasFDerivAt (n:E) (flowD_fderivative p t n)
  have h := ha.mul (hf.hasFDerivAt.comp (n:E) hphi.hasFDerivAt)
  change HasFDerivAt (weightedPullback p t F) _ n at h
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  ring

lemma weightedPullback_transport (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => weightedPullback p t F n)
      ((flowEnergy p t)⁻¹ * (fderiv ℝ (weightedPullback p t F) n (boostField p n) -
        2*inner ℝ p (n:E)*weightedPullback p t F n)) t := by
  have hf := (hF.contDiffAt (CKSSphericalHarmonics.puncturedSpace.isOpen.mem_nhds (flowPhi_nonzero p t n))).differentiableAt (by simp)
  have h := (((flowD_derivative p t n).inv (flowD_pos p t n).ne').pow 2).mul
    (hf.hasFDerivAt.comp_hasDerivAt t (flowPhi_transport p t n))
  convert! h using 1
  rw [weightedPullback_spatial_derivative p hF]
  simp only [map_smul, smul_eq_mul, weightedPullback, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply, Pi.inv_apply, Function.comp_apply]
  have hD := flowD_transport p t (n:E)
  have hD' : flowDLinear p t (boostField p n) =
      flowEnergy p t * (t*‖p‖^2/flowEnergy p t+inner ℝ p (n:E)) - inner ℝ p (n:E)*flowD p t n :=
    eq_sub_of_add_eq hD.symm
  rw [hD']
  field_simp [(flowEnergy_pos p t).ne', (flowD_pos p t n).ne']
  ring

lemma normalizedPullback_smooth (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) :
    ContDiffOn ℝ ∞ (normalizedPullback p F) (Set.univ ×ˢ (CKSSphericalHarmonics.puncturedSpace : Set E)) := by
  intro z hz
  let n : Sphere := CKSSphericalHarmonics.normalizeSphere ⟨z.2,hz.2⟩
  have h := weightedPullback_smooth_at p hF z.1 n
  exact (h.comp z (contDiffAt_fst.prodMk ((normalizeAmbient_smooth hz.2).comp z contDiffAt_snd))).contDiffWithinAt

lemma normalizedPullback_spatial (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun x => normalizedPullback p F (t,x)) CKSSphericalHarmonics.puncturedSpace :=
  (normalizedPullback_smooth p hF).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨Set.mem_univ _,hx⟩)

lemma normalizedPullback_fderiv_tangent (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) =
      fderiv ℝ (weightedPullback p t F) n (boostField p n) := by
  have hf := ((weightedPullback_smooth_at p hF t n).comp (n:E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hn := (normalizeAmbient_smooth (CKSSphericalHarmonics.sphere_ne_zero n)).differentiableAt (by simp)
  change fderiv ℝ ((weightedPullback p t F) ∘ normalizeAmbient) n _ = _
  have hf' : DifferentiableAt ℝ (weightedPullback p t F) (normalizeAmbient n) := by
    rw [normalizeAmbient_sphere]
    convert! hf
  rw [fderiv_comp (n:E) hf' hn, ContinuousLinearMap.comp_apply, normalizeAmbient_sphere,
    normalizeAmbient_fderiv_tangent n _ (boostField_tangent p n)]

lemma normalizedPullback_transport (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F CKSSphericalHarmonics.puncturedSpace) (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => normalizedPullback p F (t,(n:E)))
      ((flowEnergy p t)⁻¹ * (fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) -
        2*inner ℝ p (n:E)*normalizedPullback p F (t,(n:E)))) t := by
  simp only [normalizedPullback_sphere, normalizedPullback_fderiv_tangent p hF]
  exact weightedPullback_transport p hF t n

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open Set MeasureTheory
open CKSSphericalHarmonics (puncturedSpace surfaceMeasure smoothRestriction)

def pullbackRate (p : E) (F : E → ℝ) (z : ℝ × E) : ℝ :=
  fderiv ℝ (normalizedPullback p F) z (1,0)

lemma normalizedDomain_open : IsOpen (Set.univ ×ˢ (puncturedSpace : Set E) : Set (ℝ × E)) :=
  isOpen_univ.prod puncturedSpace.isOpen

lemma pullbackRate_smooth (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    ContDiffOn ℝ ∞ (pullbackRate p F) (Set.univ ×ˢ (puncturedSpace : Set E)) :=
  ((normalizedPullback_smooth p hF).fderiv_of_isOpen normalizedDomain_open (by simp)).clm_apply contDiffOn_const

lemma pullback_time_derivative (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (t : ℝ) (n : Sphere) :
    HasDerivAt (fun t => normalizedPullback p F (t,(n:E))) (pullbackRate p F (t,(n:E))) t := by
  have hg := ((normalizedPullback_smooth p hF).contDiffAt (x := (t,(n:E)))
    (normalizedDomain_open.mem_nhds ⟨mem_univ t,CKSSphericalHarmonics.sphere_ne_zero n⟩)).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => (t,(n:E))) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (n:E))
  convert! hg.hasFDerivAt.comp_hasDerivAt t hline using 1

lemma pullbackRate_transport (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (t : ℝ) (n : Sphere) :
    pullbackRate p F (t,(n:E)) =
      (flowEnergy p t)⁻¹ * (fderiv ℝ (fun x => normalizedPullback p F (t,x)) n (boostField p n) -
        2*inner ℝ p (n:E)*normalizedPullback p F (t,(n:E))) :=
  (pullback_time_derivative p hF t n).unique (normalizedPullback_transport p hF t n)

lemma continuous_restrict_sphere {G : ℝ × E → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Set.univ ×ˢ (puncturedSpace : Set E))) :
    Continuous (fun z : ℝ × Sphere => G (z.1,(z.2:E))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hi : Continuous (fun z : ℝ × Sphere => (z.1,(z.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have ho : ContinuousAt G (z.1,(z.2:E)) :=
    (hG.contDiffAt (x := (z.1,(z.2:E))) (normalizedDomain_open.mem_nhds
      ⟨mem_univ _, CKSSphericalHarmonics.sphere_ne_zero z.2⟩)).continuousAt
  exact ho.comp (f := fun z : ℝ × Sphere => (z.1,(z.2:E))) hi.continuousAt

lemma sphere_integrable_smooth {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H puncturedSpace) :
    Integrable (fun n : Sphere => H n) surfaceMeasure :=
  (smoothRestriction H hH).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma boostField_smooth (p : E) : ContDiff ℝ ∞ (boostField p) :=
  contDiff_const.sub ((ContDiff.inner ℝ contDiff_const contDiff_id).smul contDiff_id)

lemma pullbackRate_integral_zero (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t : ℝ) :
    ∫ n : Sphere, pullbackRate p F (t,(n:E)) ∂surfaceMeasure = 0 := by
  let G : E → ℝ := fun x => normalizedPullback p F (t,x)
  have hG : ContDiffOn ℝ ∞ G puncturedSpace := normalizedPullback_spatial p hF t
  have hDG : ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x (boostField p x)) puncturedSpace :=
    (hG.fderiv_of_isOpen puncturedSpace.isOpen (by simp)).clm_apply (boostField_smooth p).contDiffOn
  have hqG : ContDiffOn ℝ ∞ (fun x => inner ℝ p x * G x) puncturedSpace :=
    (ContDiff.inner ℝ contDiff_const contDiff_id).contDiffOn.mul hG
  have he : (fun n : Sphere => pullbackRate p F (t,(n:E))) =
      fun n : Sphere => (flowEnergy p t)⁻¹ * (fderiv ℝ G n (boostField p n) - 2*(inner ℝ p (n:E)*G n)) := by
    funext n
    rw [pullbackRate_transport p hF]
    dsimp only [G]; ring
  rw [he, integral_const_mul, integral_sub (sphere_integrable_smooth hDG) ((sphere_integrable_smooth hqG).const_mul 2), integral_const_mul]
  have hi := CKSSphericalHarmonics.sphereIntegral_boostField hG p
  change (∫ n : Sphere, fderiv ℝ G n (boostField p n) ∂surfaceMeasure) = _ at hi
  rw [hi]; ring

lemma normalizedIntegral_derivative_zero (p : E) {F : E → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ n : Sphere, normalizedPullback p F (t,(n:E)) ∂surfaceMeasure) 0 t₀ := by
  let H (t : ℝ) (n : Sphere) := normalizedPullback p F (t,(n:E))
  let R (t : ℝ) (n : Sphere) := pullbackRate p F (t,(n:E))
  have hH : Continuous (fun z : ℝ × Sphere => H z.1 z.2) :=
    continuous_restrict_sphere (normalizedPullback_smooth p hF)
  have hR : Continuous (fun z : ℝ × Sphere => R z.1 z.2) :=
    continuous_restrict_sphere (pullbackRate_smooth p hF)
  have hHt (t : ℝ) : Continuous (H t) := by
    have hc : Continuous (fun n : Sphere => (t,n)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (f := fun n : Sphere => (t,n))
      (g := fun z : ℝ × Sphere => H z.1 z.2) hH hc
  have hRt (t : ℝ) : Continuous (R t) := by
    have hc : Continuous (fun n : Sphere => (t,n)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (f := fun n : Sphere => (t,n))
      (g := fun z : ℝ × Sphere => R z.1 z.2) hR hc
  let K : Set (ℝ × Sphere) := Icc (t₀-1) (t₀+1) ×ˢ univ
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hR.continuousOn
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := surfaceMeasure) (x₀ := t₀) (s := Ioo (t₀-1) (t₀+1))
    (F := H) (F' := R) (bound := fun _ => C)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun t => (hHt t).aestronglyMeasurable)
    ((hHt t₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hRt t₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun n t ht => hC (t,n) ⟨⟨ht.1.le,ht.2.le⟩, mem_univ n⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun n t _ => pullback_time_derivative p hF t n)
  convert! h.2 using 1
  exact (pullbackRate_integral_zero p hF t₀).symm

theorem flow_area_substitution (p : E) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) (t : ℝ) :
    ∫ n : Sphere, (flowD p t n)⁻¹ ^2 * F (flowPhi p t n) ∂surfaceMeasure =
      ∫ n : Sphere, F n ∂surfaceMeasure := by
  let H (t : ℝ) (n : Sphere) := normalizedPullback p F (t,(n:E))
  have hd := normalizedIntegral_derivative_zero p hF
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have hzero : ∀ n : Sphere, H 0 n = F n := by
    intro n
    simp [H, normalizedPullback_sphere, weightedPullback, flowPhi, flowD, flowEnergy,
      flowS, flowCoeff]
  have ht : ∀ n : Sphere, H t n = (flowD p t n)⁻¹ ^2 * F (flowPhi p t n) := by
    intro n
    rw [show H t n = weightedPullback p t F n by exact normalizedPullback_sphere p F t n]
    rfl
  change (∫ n : Sphere, H t n ∂surfaceMeasure) = ∫ n : Sphere, H 0 n ∂surfaceMeasure at he
  simpa only [hzero,ht] using he

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Topology
open MeasureTheory
open CKSSphericalHarmonics (puncturedSpace surfaceMeasure)

lemma flowEnergy_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) : flowEnergy (m⁻¹ • p) 1 = e/m := by
  have hs : (e/m)^2 = 1+‖m⁻¹ • p‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm0)]
    field_simp
    nlinarith
  have hf := flowEnergy_sq (m⁻¹ • p) 1
  simp only [one_pow, one_mul] at hf
  nlinarith [flowEnergy_pos (m⁻¹ • p) 1, div_pos (energy_pos he) hm0]

lemma flowD_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowD (m⁻¹ • p) 1 n = denominator e m p n := by
  simp only [flowD, flowEnergy_normalized he hm0 hm, one_mul, inner_smul_left, conj_trivial, denominator]
  ring

lemma flowS_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowS (m⁻¹ • p) 1 n = boundarySpatial e m p n := by
  simp only [flowS, flowCoeff, flowEnergy_normalized he hm0 hm, one_pow, boundarySpatial,
    inner_smul_left, conj_trivial, smul_smul]
  congr 1
  congr 1
  field_simp

lemma flowPhi_normalized {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) (n : E) :
    flowPhi (m⁻¹ • p) 1 n = boundaryAmbient e m p n := by
  rw [flowPhi, flowD_normalized he hm0 hm, flowS_normalized he hm0 hm]
  rfl

theorem boost_area_substitution {e m : ℝ} {p : E} (he : ‖p‖ < e) (hm0 : 0 < m)
    (hm : m^2 = e^2-‖p‖^2) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    ∫ n : Sphere, (denominator e m p n)⁻¹ ^2 * F (boundaryAmbient e m p n) ∂surfaceMeasure =
      ∫ n : Sphere, F n ∂surfaceMeasure := by
  have h := flow_area_substitution (m⁻¹ • p) hF 1
  simpa only [flowD_normalized he hm0 hm, flowPhi_normalized he hm0 hm] using h

lemma inverse_null_boundary (e : ℝ) (p : E) (he : ‖p‖ < e) (n : Sphere) :
    boostCLM e (mass e p) (-p) (1,(boundary e p he n:E)) =
      (denominator e (mass e p) p n)⁻¹ • ((1:ℝ),(n:E)) := by
  have h := congrArg (boostCLM e (mass e p) (-p)) (boundary_null e p he n)
  simp only [map_smul, boostCLM_apply] at h
  rw [boost_neg_inverse (mass_pos he).ne' (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he)] at h
  rw [h, smul_smul, inv_mul_cancel₀ (denominator_pos he (mass_pos he) n).ne', one_smul]
  rfl

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere radialExtension radialExtension_smooth radialExtension_on_sphere surfaceMeasure)

lemma nullDirection_smooth : ContMDiff (𝓡 2) 𝓘(ℝ,V) ∞ nullDirection :=
by
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : Sphere => (1:ℝ)) := contMDiff_const
  exact hc.prodMk_space (contMDiff_coe_sphere (E := E) (n := 2))

lemma aspectPullback_smooth (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) : SmoothSphere (aspectPullback e p he M) := by
  have hd : ContDiff ℝ ∞ (denominator e (mass e p) p) :=
    (contDiff_const.add (ContDiff.inner ℝ contDiff_const contDiff_id)).div_const _
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun n : Sphere => denominator e (mass e p) p n) :=
    hd.comp_contMDiff (contMDiff_coe_sphere (E := E) (n := 2))
  exact ((hc.inv₀ (fun n => (denominator_pos he (mass_pos he) n).ne')).pow 3).mul
    (hM.comp (boundary_smooth e p he))

lemma rawCharge_integrable {M : Sphere → ℝ} (hM : SmoothSphere M) :
    Integrable (fun n => M n • nullDirection n) surfaceMeasure :=
  (hM.continuous.smul nullDirection_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma rawCharge_test {M : Sphere → ℝ} (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge M) = ∫ n : Sphere, M n * L (nullDirection n) ∂surfaceMeasure := by
  rw [rawCharge, ← L.integral_comp_comm (rawCharge_integrable hM)]
  simp only [map_smul, smul_eq_mul]

lemma transformedCharge_test (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge (aspectPullback e p he M)) =
      L (boostCLM e (mass e p) (-p) (rawCharge M)) := by
  let B := boostCLM e (mass e p) (-p)
  let Q : Sphere → ℝ := fun n => M n * L (B (nullDirection n))
  have hQ : SmoothSphere Q := hM.mul
    (L.contMDiff.comp (B.contMDiff.comp nullDirection_smooth))
  have hi := boost_area_substitution he (mass_pos he) (mass_sq he) (radialExtension_smooth hQ)
  have hiR : (∫ n : Sphere, radialExtension Q n ∂surfaceMeasure) =
      L (B (rawCharge M)) := by
    change _ = (L.comp B) (rawCharge M)
    rw [rawCharge_test hM (L.comp B)]
    congr 1
    funext n
    rw [radialExtension_on_sphere]
    rfl
  have hiL : (∫ n : Sphere,
      (denominator e (mass e p) p n)⁻¹ ^2 * radialExtension Q (boundaryAmbient e (mass e p) p n) ∂surfaceMeasure) =
      L (rawCharge (aspectPullback e p he M)) := by
    rw [rawCharge_test (aspectPullback_smooth e p he hM)]
    congr 1
    funext n
    change (denominator e (mass e p) p n)⁻¹ ^2 * radialExtension Q (boundary e p he n) = _
    rw [radialExtension_on_sphere]
    dsimp only [Q, B, nullDirection]
    rw [inverse_null_boundary e p he n, map_smul, smul_eq_mul]
    dsimp only [aspectPullback, nullDirection]
    ring
  rw [hiL,hiR] at hi
  exact hi

theorem rawCharge_lorentz (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) :
    rawCharge (aspectPullback e p he M) = boostCLM e (mass e p) (-p) (rawCharge M) := by
  apply Prod.ext
  · exact transformedCharge_test e p he hM (ContinuousLinearMap.fst ℝ ℝ E)
  · ext i
    exact transformedCharge_test e p he hM ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))

theorem bondiCharge_lorentz (e : ℝ) (p : E) (he : ‖p‖ < e) {M : Sphere → ℝ}
    (hM : SmoothSphere M) :
    bondiCharge (aspectPullback e p he M) = boostCLM e (mass e p) (-p) (bondiCharge M) := by
  simp only [bondiCharge, rawCharge_lorentz e p he hM, map_smul]

end
end CKSLorentz

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure Balanced sphereIntegral sphereArea)

lemma boost_to_rest {e : ℝ} {p : E} (he : ‖p‖ < e) :
    boostCLM e (mass e p) (-p) (e,p) = (mass e p,0) := by
  have h := boost_neg_inverse (mass_pos he).ne'
    (add_pos (energy_pos he) (mass_pos he)).ne' (mass_sq he) (mass e p,0)
  rw [boost_mass (mass_pos he).ne'] at h
  exact h

lemma charge_energy {M : Sphere → ℝ} (hM : SmoothSphere M) :
    (bondiCharge M).1 = (16*Real.pi)⁻¹ * ∫ n, M n ∂surfaceMeasure := by
  have h := rawCharge_test hM (ContinuousLinearMap.fst ℝ ℝ E)
  change (rawCharge M).1 = ∫ n, M n * 1 ∂surfaceMeasure at h
  simp only [mul_one] at h
  change (16*Real.pi)⁻¹ * (rawCharge M).1 = _
  rw [h]

lemma charge_momentum {M : Sphere → ℝ} (hM : SmoothSphere M) (i : Fin 3) :
    (bondiCharge M).2 i = (16*Real.pi)⁻¹ * ∫ n, M n * (n:E) i ∂surfaceMeasure := by
  have h := rawCharge_test hM
    ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))
  change (rawCharge M).2 i = ∫ n, M n * (n:E) i ∂surfaceMeasure at h
  change (16*Real.pi)⁻¹ * (rawCharge M).2 i = _
  rw [h]

lemma heatDatum_smooth {M : Sphere → ℝ} (hM : SmoothSphere M) :
    SmoothSphere (heatDatum M hM) := hM.div_const 4

lemma heatDatum_balanced {M : Sphere → ℝ} (hM : SmoothSphere M) {m : ℝ}
    (hc : bondiCharge M = (m,0)) : Balanced (heatDatum M hM) m := by
  have hp : 16*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have he := charge_energy hM
  rw [hc] at he
  have hm : ∫ n, M n ∂surfaceMeasure = (16*Real.pi)*m := by
    change m = (16*Real.pi)⁻¹ * _ at he
    calc
      _ = (16*Real.pi)*((16*Real.pi)⁻¹ * ∫ n, M n ∂surfaceMeasure) := by field_simp
      _ = _ := by rw [← he]
  constructor
  · rw [CKSSphericalHarmonics.sphereIntegral_apply, CKSSphericalHarmonics.sphereArea_eq_four_pi]
    change (∫ n, M n/4 ∂surfaceMeasure) = m*(4*Real.pi)
    simp only [div_eq_mul_inv, integral_mul_const, hm]
    ring
  · intro i
    have hq := charge_momentum hM i
    rw [hc] at hq
    have hi : ∫ n, M n * (n:E) i ∂surfaceMeasure = 0 := by
      have hz : (16*Real.pi)⁻¹ * (∫ n, M n * (n:E) i ∂surfaceMeasure) = 0 := hq.symm
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hp)
    rw [CKSSphericalHarmonics.sphereIntegral_apply]
    change (∫ n, (M n/4)*(n:E) i ∂surfaceMeasure) = 0
    have heq : (fun n : Sphere => (M n/4)*(n:E) i) = fun n => (M n*(n:E) i)/4 := by
      funext n; ring
    rw [heq]
    simp only [div_eq_mul_inv, integral_mul_const, hi, zero_mul]

theorem balanced_charge_and_heat {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let M' := aspectPullback e p ht M
    ∃ hM' : SmoothSphere M',
      bondiCharge M' = (mass e p,0) ∧
      SmoothSphere (heatDatum M' hM') ∧
      Balanced (heatDatum M' hM') (mass e p) := by
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let M' := aspectPullback e p ht M
  have hM' : SmoothSphere M' := aspectPullback_smooth e p ht hM
  refine ⟨hM', ?_, heatDatum_smooth hM', ?_⟩
  · rw [bondiCharge_lorentz e p ht hM]
    exact boost_to_rest ht
  · apply heatDatum_balanced hM'
    rw [bondiCharge_lorentz e p ht hM]
    exact boost_to_rest ht

end
end CKSLorentz

end




































noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma hyperbolicField_apply (x v w : E) : hyperbolicField x v w = hyperbolicMetric x v w := by
  change inner ℝ v w - (1/(1+‖x‖^2)) * (inner ℝ x v * inner ℝ x w) =
    inner ℝ v w - inner ℝ x v * inner ℝ x w / (1+‖x‖^2)
  ring

end
end CKSLorentz

end







end OAI
end

section
namespace OAI









































noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
structure ContinuousMetricJetAt (g : PhysicalPoint → CKSRound.MetricJet) (x : PhysicalPoint) : Prop where
  inv : ∀ i j, ContinuousAt (fun y => (g y).inv i j) x
  d : ∀ a i j, ContinuousAt (fun y => (g y).d a i j) x
  dd : ∀ a b i j, ContinuousAt (fun y => (g y).dd a b i j) x
structure ContinuousTensorJetAt (k : PhysicalPoint → CKSRound.TensorJet) (x : PhysicalPoint) : Prop where
  val : ∀ i j, ContinuousAt (fun y => (k y).val i j) x
  d : ∀ a i j, ContinuousAt (fun y => (k y).d a i j) x
lemma ContinuousMetricJetAt.gamma {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a i j : Fin 3) :
    ContinuousAt (fun y => (g y).gamma a i j) x := by
  have hi := h.inv
  have hd := h.d
  unfold CKSRound.MetricJet.gamma
  fun_prop
lemma ContinuousMetricJetAt.dInv {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a i j : Fin 3) :
    ContinuousAt (fun y => (g y).dInv a i j) x := by
  have hi := h.inv
  have hd := h.d
  unfold CKSRound.MetricJet.dInv
  fun_prop
lemma ContinuousMetricJetAt.dGamma {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a b i j : Fin 3) :
    ContinuousAt (fun y => (g y).dGamma a b i j) x := by
  have hi := h.inv
  have hd := h.d
  have hdd := h.dd
  have hdi := h.dInv
  unfold CKSRound.MetricJet.dGamma
  fun_prop
lemma ContinuousMetricJetAt.ricci {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (i j : Fin 3) :
    ContinuousAt (fun y => (g y).ricci i j) x := by
  have hc := h.gamma
  have hd := h.dGamma
  unfold CKSRound.MetricJet.ricci
  fun_prop
lemma ContinuousMetricJetAt.scalar {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) : ContinuousAt (fun y => (g y).scalar) x := by
  have hi := h.inv
  have hr := h.ricci
  unfold CKSRound.MetricJet.scalar
  fun_prop
lemma ContinuousMetricJetAt.trace {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).trace (k y)) x := by
  have hi := h.inv
  have hv := hk.val
  unfold CKSRound.MetricJet.trace
  fun_prop
lemma ContinuousMetricJetAt.normSq {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).normSq (k y)) x := by
  have hi := h.inv
  have hv := hk.val
  unfold CKSRound.MetricJet.normSq
  fun_prop
lemma ContinuousMetricJetAt.dTrace {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).dTrace (k y) i) x := by
  have hi := h.inv
  have hdi := h.dInv
  have hv := hk.val
  have hd := hk.d
  unfold CKSRound.MetricJet.dTrace
  fun_prop
lemma ContinuousMetricJetAt.tensorDivergence {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).tensorDivergence (k y) i) x := by
  have hi := h.inv
  have hc := h.gamma
  have hv := hk.val
  have hd := hk.d
  unfold CKSRound.MetricJet.tensorDivergence
  fun_prop
lemma ContinuousMetricJetAt.energy {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).energy (k y)) x := by
  have hs := h.scalar
  have ht := h.trace hk
  have hn := h.normSq hk
  unfold CKSRound.MetricJet.energy
  fun_prop
lemma ContinuousMetricJetAt.momentum {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) (i : Fin 3) :
    ContinuousAt (fun y => (g y).momentum (k y) i) x := by
  have ht := h.dTrace hk i
  have hd := h.tensorDivergence hk i
  unfold CKSRound.MetricJet.momentum
  fun_prop
lemma ContinuousMetricJetAt.momentumSq {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => CKSLocalBending.momentumSq (g y) (k y)) x := by
  have hi := h.inv
  have hm := h.momentum hk
  unfold CKSLocalBending.momentumSq
  fun_prop
lemma physicalMetricJet_continuousAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) : ContinuousMetricJetAt (physicalMetricJet G) x := by
  have hc (i j) := contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  refine ⟨fun i j => (matrix_inv_component_contDiffAt hg h0 i j).continuousAt,?_,?_⟩
  · intro a i j
    exact (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
  · intro a b i j
    exact (contDiffAt_D (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis b))
      (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
lemma physicalTensorJet_continuousAt {K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hk : ContDiffAt ℝ ∞ K x) : ContinuousTensorJetAt (physicalTensorJet K) x := by
  have hc (i j) := contDiffAt_pi.mp (contDiffAt_pi.mp hk i) j
  refine ⟨fun i j => (hc i j).continuousAt,?_⟩
  intro a i j
  exact (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt

end
end CKSAngularGeometry

end


























noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry
open scoped BigOperators
lemma spatialCoefficients_pair (A : SpatialTensor) (y v w : PhysicalPoint) :
    metricPair (spatialCoefficients A y) v w =
      A (CKSCartesianOuter.toPoint.symm y) (CKSCartesianOuter.toPoint.symm v)
        (CKSCartesianOuter.toPoint.symm w) := by
  conv_rhs => rw [← CKSMixedGeometry.sum_coordinate_basis v,
    ← CKSMixedGeometry.sum_coordinate_basis w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,spatialCoefficients,metricPair]
  simp only [Fin.sum_univ_three]
  ring

end
end CKSLorentz

end








noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.sgpNorm
attribute [local instance] OAI.CKSLorentz.sgpSpace

lemma spatialCoefficients_smooth {A : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (spatialCoefficients A) (CKSCartesianOuter.toPoint x) := by
  have h := hA.comp (CKSCartesianOuter.toPoint x) CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  exact (h.clm_apply contDiffAt_const).clm_apply contDiffAt_const
lemma spatialCoefficients_symmetric {A : SpatialTensor} {x : E}
    (hA : ∀ v w, A x v w = A x w v) :
    (spatialCoefficients A (CKSCartesianOuter.toPoint x)).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  simpa [spatialCoefficients] using (hA (CKSCartesianOuter.toPoint.symm (CKSMixedGeometry.basis i))
    (CKSCartesianOuter.toPoint.symm (CKSMixedGeometry.basis j))).symm
lemma spatialCoefficients_positive {A : SpatialTensor} {x : E}
    (hA : ∀ v w, A x v w = A x w v)
    (hp : ∀ v : E, v ≠ 0 → 0 < A x v v) :
    (spatialCoefficients A (CKSCartesianOuter.toPoint x)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (spatialCoefficients_symmetric hA)
  intro v hv
  have hz : CKSCartesianOuter.toPoint.symm v ≠ 0 := by
    simpa only [map_zero] using CKSCartesianOuter.toPoint.symm.injective.ne hv
  have h := hp _ hz
  have he := spatialCoefficients_pair A (CKSCartesianOuter.toPoint x) v v
  simp only [ContinuousLinearEquiv.symm_apply_apply] at he
  rw [← he] at h
  simpa only [metricPair,dotProduct,Matrix.mulVec,Finset.mul_sum,star_trivial,
    mul_assoc,mul_left_comm,mul_comm] using h

end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] CKSSpatialManifold.real_id_isometric real_smulCommClass
  spatialDual_smulCommClass
attribute [local instance] OAI.CKSLorentz.hsgNorm

attribute [local instance] OAI.CKSLorentz.hsgSpace

attribute [local instance] spatialBilinear_isScalarTower

lemma sourceSpatial_boost {e : ℝ} {p : E} (he : ‖p‖ < e) (A : SpatialTensor) :
    sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A) =
      spatialTensorPullback (hyperbolicMap e (mass e p) p) (sourceSpatial A) := by
  funext x; ext v w
  change hyperbolicField x v w + A _ _ _ = hyperbolicField _ _ _ + A _ _ _
  rw [hyperbolicField_apply,hyperbolicField_apply]
  exact congrArg (fun z : ℝ => z + A _ _ _) (hyperbolicMap_isometry he (mass_pos he) (mass_sq he) x v w).symm

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable def SpatialBoostPatch.collarSourcePatch {e R δ : ℝ} {p : E} {he : ‖p‖ < e}
    {A B : SpatialTensor} {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ : Angle}
    (h : SpatialBoostPatch e p he A B Q P θ δ R) {W : Set Angle}
    (hW : IsOpen W) (hsub : W ⊆ Metric.ball θ δ) :
    CollarSourcePatch (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
      (spatialTensorPullback (hyperbolicMap e (mass e p) p) B) where
  patch := P
  region := W
  region_open := hW
  region_target := hsub.trans h.genuine.estimates.ball_target
  radius := R
  mr := lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr
  mg := lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg
  mK := lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK
  metric_CKS := h.metric_CKS.mono (fun _ hy => ⟨hy.1,hsub hy.2⟩)
  tensor_CKS := h.second_CKS.mono (fun _ hy => ⟨hy.1,hsub hy.2⟩)

lemma homeomorph_maps_far_tail (h : E ≃ₜ E) (S R : ℝ) :
    ∃ T : ℝ, 0 < T ∧ R ≤ T ∧ ∀ x : E, T < ‖x‖ → S < ‖h x‖ := by
  have hc := h.isCompact_preimage.mpr (isCompact_closedBall (0:E) S)
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:E)).mp hc.isBounded
  refine ⟨max 1 (max R r),lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    (le_max_left R r).trans (le_max_right _ _),?_⟩
  intro x hx
  by_contra hn
  have hm : h x ∈ Metric.closedBall (0:E) S := by simpa using (not_lt.mp hn)
  have hb : ‖x‖ ≤ r := by simpa using hr hm
  have hrt : r ≤ max 1 (max R r) := (le_max_right R r).trans (le_max_right _ _)
  linarith
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open Matrix

lemma trace_conformal_congruence {d : ℝ} (hd : d ≠ 0)
    (σ J A : AngularMatrix) (hσ : IsUnit σ.det) (hJ : IsUnit J.det) :
    angularMetricTrace (d^2 • (J*σ*J.transpose)) (d⁻¹ • (J*A*J.transpose)) =
      d⁻¹^3 * angularMetricTrace σ A := by
  have hJt : IsUnit J.transpose.det := by simpa using hJ
  have hi : (d^2 • (J*σ*J.transpose))⁻¹ =
      (d^2)⁻¹ • (J.transpose⁻¹ * σ⁻¹ * J⁻¹) := by
    apply Matrix.inv_eq_left_inv
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hd),one_smul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
    rw [← Matrix.mul_assoc σ⁻¹, Matrix.nonsing_inv_mul _ hσ,Matrix.one_mul]
    exact Matrix.nonsing_inv_mul _ hJt
  simp only [angularMetricTrace,hi,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.trace_smul]
  have ht : (J.transpose⁻¹ * σ⁻¹ * J⁻¹ * (J*A*J.transpose)).trace = (σ⁻¹*A).trace := by
    calc
      _ = (J.transpose⁻¹ * (σ⁻¹ * A) * J.transpose).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
      _ = (J.transpose * J.transpose⁻¹ * (σ⁻¹*A)).trace := Matrix.trace_mul_cycle _ _ _
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hJt,Matrix.one_mul]
  rw [ht]
  simp only [smul_eq_mul,inv_pow]
  ring

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularGram_congruence (L : Angle →L[ℝ] E) {Φ : Angle → Angle} {θ : Angle}
    (hΦ : DifferentiableAt ℝ Φ θ) (a b : Fin 2) :
    (angularJacobian Φ θ *
      Matrix.gram ℝ (fun i : Fin 2 => L (CKSAngularGeometry.basis i)) *
      (angularJacobian Φ θ).transpose) a b =
    inner ℝ (L (fderiv ℝ Φ θ (CKSAngularGeometry.basis a)))
      (L (fderiv ℝ Φ θ (CKSAngularGeometry.basis b))) := by
  rw [angularJacobian_apply hΦ a,angularJacobian_apply hΦ b]
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    conj_trivial,Matrix.gram_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
  ring

lemma boundaryChart_regular {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    boundaryChart e (mass e p) p P.param Q.extension θ ∈ Q.chart.target ∧
    ContDiffAt ℝ ∞ (boundaryChart e (mass e p) p P.param Q.extension) θ := by
  have hb : boundaryAmbient e (mass e p) p (P.param θ) ∈ Q.domain :=
    Q.source_domain _ hQ
  constructor
  · change Q.extension (boundaryAmbient e (mass e p) p (P.param θ)) ∈ Q.chart.target
    rw [show boundaryAmbient e (mass e p) p (P.param θ)=
      (boundary e p he (P.chart.symm θ):E) from rfl,Q.extension_eq _ hQ]
    exact Q.chart.map_source hQ
  · have hB : ContDiffAt ℝ ∞ (fun η => boundaryAmbient e (mass e p) p (P.param η)) θ :=
      (boundaryAmbient_smooth (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne').comp
        (f := P.param) (g := boundaryAmbient e (mass e p) p) θ
        (P.param_contDiffAt hθ)
    exact (Q.extension_smooth.contDiffAt (Q.isOpen_domain.mem_nhds hb)).comp θ hB

lemma boundary_param_fderiv {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    (fderiv ℝ Q.param (boundaryChart e (mass e p) p P.param Q.extension θ)).comp
        (fderiv ℝ (boundaryChart e (mass e p) p P.param Q.extension) θ) =
      (fderiv ℝ (boundaryAmbient e (mass e p) p) (P.param θ)).comp (fderiv ℝ P.param θ) := by
  have hs : ContinuousAt (fun η => boundary e p he (P.chart.symm η)) θ :=
    (boundary_smooth e p he).continuous.continuousAt.comp (P.chart.symm.continuousAt hθ)
  have hn : ∀ᶠ η in 𝓝 θ, boundary e p he (P.chart.symm η) ∈ Q.chart.source :=
    hs.preimage_mem_nhds (Q.chart.open_source.mem_nhds hQ)
  have hg : (fun η => Q.param (boundaryChart e (mass e p) p P.param Q.extension η)) =ᶠ[𝓝 θ]
      (fun η => boundaryAmbient e (mass e p) p (P.param η)) := by
    filter_upwards [hn] with η hη
    change Q.param (Q.extension (boundary e p he (P.chart.symm η))) =
      (boundary e p he (P.chart.symm η):E)
    rw [Q.extension_eq _ hη]
    exact Q.param_chart hη
  have hreg := boundaryChart_regular he P Q hθ hQ
  have h := hg.fderiv_eq (𝕜:=ℝ)
  change fderiv ℝ (Q.param ∘ boundaryChart e (mass e p) p P.param Q.extension) θ =
    fderiv ℝ (boundaryAmbient e (mass e p) p ∘ P.param) θ at h
  rw [fderiv_comp θ ((Q.param_contDiffAt hreg.1).differentiableAt (by simp))
      (hreg.2.differentiableAt (by simp)),
    fderiv_comp θ ((boundaryAmbient_smooth
      (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne').differentiableAt (by simp))
      ((P.param_contDiffAt hθ).differentiableAt (by simp))] at h
  exact h

lemma boundary_roundMetric_conformal {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source) :
    let Φ := boundaryChart e (mass e p) p P.param Q.extension
    angularJacobian Φ θ * angularRoundMetric Q.param (Φ θ) * (angularJacobian Φ θ).transpose =
      (denominator e (mass e p) p (P.param θ))⁻¹ ^ 2 • angularRoundMetric P.param θ := by
  dsimp only
  ext a b
  change (angularJacobian _ θ * Matrix.gram ℝ (fun i : Fin 2 =>
    fderiv ℝ Q.param _ (CKSAngularGeometry.basis i)) * (angularJacobian _ θ).transpose) a b = _
  rw [angularGram_congruence _ ((boundaryChart_regular he P Q hθ hQ).2.differentiableAt (by simp))]
  have hd := boundary_param_fderiv he P Q hθ hQ
  have ha := congrArg (fun L : Angle →L[ℝ] E => L (CKSAngularGeometry.basis a)) hd
  have hb := congrArg (fun L : Angle →L[ℝ] E => L (CKSAngularGeometry.basis b)) hd
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  rw [ha,hb]
  exact boundary_conformal he (mass_pos he) (mass_sq he) (P.chart.symm θ) _ _
    (P.param_tangent hθ _) (P.param_tangent hθ _)

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

theorem lorentz_leading_trace {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source)
    (mg : I → I → Angle → ℝ) :
    angularMetricTrace (angularRoundMetric P.param θ)
      (fun a b => lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ) =
    (denominator e (mass e p) p (P.param θ))⁻¹ ^ 3 *
      angularMetricTrace (angularRoundMetric Q.param (boundaryChart e (mass e p) p P.param Q.extension θ))
        (fun a b => mg a.succ b.succ (boundaryChart e (mass e p) p P.param Q.extension θ)) := by
  let Φ := boundaryChart e (mass e p) p P.param Q.extension
  let J := angularJacobian Φ θ
  let d := denominator e (mass e p) p (P.param θ)
  let σ := angularRoundMetric Q.param (Φ θ)
  let A : AngularMatrix := fun a b => mg a.succ b.succ (Φ θ)
  have hd : d ≠ 0 := (denominator_pos he (mass_pos he) (P.chart.symm θ)).ne'
  have hreg := boundaryChart_regular he P Q hθ hQ
  have hσ : IsUnit σ.det := isUnit_iff_ne_zero.mpr (Q.roundMetric_posDef hreg.1).det_pos.ne'
  have hconf : J*σ*J.transpose = d⁻¹^2 • angularRoundMetric P.param θ :=
    boundary_roundMetric_conformal he P Q hθ hQ
  have hp : (J*σ*J.transpose).PosDef := by
    rw [hconf]
    exact (P.roundMetric_posDef hθ).smul (sq_pos_of_ne_zero (inv_ne_zero hd))
  have hJ : IsUnit J.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hdet := hp.det_pos.ne'
    simp only [Matrix.det_mul,Matrix.det_transpose,hz,zero_mul,mul_zero,ne_eq,not_true_eq_false] at hdet
  have hback : angularRoundMetric P.param θ=d^2 • (J*σ*J.transpose) := by
    rw [hconf,smul_smul,inv_pow,mul_inv_cancel₀ (pow_ne_zero 2 hd),one_smul]
  have hψ : ContDiffAt ℝ ∞ Q.extension (boundaryAmbient e (mass e p) p (P.param θ)) :=
    Q.extension_smooth.contDiffAt (Q.isOpen_domain.mem_nhds (Q.source_domain _ hQ))
  have hA : (fun a b : Fin 2 =>
      lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ) =
      d⁻¹ • (J*A*J.transpose) := by
    ext a b
    change lorentzAngularLeading e (mass e p) p P.param Q.extension mg a.succ b.succ θ =
      d⁻¹ * ∑ i : Fin 2, (∑ j : Fin 2, J a j * A j i) * J b i
    rw [lorentzAngularLeading_boundary he (mass_pos he) (mass_sq he) P.param Q.extension mg
      (Eventually.of_forall P.param_sphere) (P.param_contDiffAt hθ) hψ a b]
    simp only [angularCoordinatePullback,J,A,d,Φ,angularJacobian,Fin.sum_univ_two]
    ring
  rw [hback,hA]
  exact trace_conformal_congruence hd σ J A hσ hJ

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
lemma angularMetricTrace_add (σ A B : AngularMatrix) :
    angularMetricTrace σ (A+B)=angularMetricTrace σ A+angularMetricTrace σ B := by
  simp only [angularMetricTrace,Matrix.mul_add,Matrix.trace_add]
lemma angularMetricTrace_smul (σ A : AngularMatrix) (c : ℝ) :
    angularMetricTrace σ (c • A)=c*angularMetricTrace σ A := by
  simp only [angularMetricTrace,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]
lemma cksChartMassAspect_split (φ : Angle → E) (mr : Angle → ℝ)
    (mg mK : I → I → Angle → ℝ) (θ : Angle) :
    cksChartMassAspect φ mr mg mK θ =
      angularMetricTrace (angularRoundMetric φ θ) (fun a b => mg a.succ b.succ θ) +
      2*angularMetricTrace (angularRoundMetric φ θ) (fun a b => mK a.succ b.succ θ) + 2*mr θ := by
  let σ := angularRoundMetric φ θ
  let A : AngularMatrix := fun a b => mg a.succ b.succ θ
  let B : AngularMatrix := fun a b => mK a.succ b.succ θ
  change angularMetricTrace σ (A + (2:ℝ) • B) + 2*mr θ =
    angularMetricTrace σ A + 2*angularMetricTrace σ B + 2*mr θ
  rw [angularMetricTrace_add,angularMetricTrace_smul]

theorem lorentz_cks_massAspect {e : ℝ} {p : E} (he : ‖p‖ < e)
    (P Q : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (hQ : boundary e p he (P.chart.symm θ) ∈ Q.chart.source)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) :
    cksChartMassAspect P.param (lorentzRadialLeading e (mass e p) p P.param Q.extension mr)
      (lorentzAngularLeading e (mass e p) p P.param Q.extension mg)
      (lorentzAngularLeading e (mass e p) p P.param Q.extension mK) θ =
    (denominator e (mass e p) p (P.param θ))⁻¹ ^3 *
      cksChartMassAspect Q.param mr mg mK
        (boundaryChart e (mass e p) p P.param Q.extension θ) := by
  rw [cksChartMassAspect_split,cksChartMassAspect_split,
    lorentz_leading_trace he P Q hθ hQ mg,lorentz_leading_trace he P Q hθ hQ mK,
    lorentzRadialLeading_boundary he (mass_pos he) (mass_sq he) P.param Q.extension mr
      (P.param_sphere θ)]
  ring
end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
lemma genuine_patch_massAspect {M : Sphere → ℝ} {e : ℝ} {p : E} {he : ‖p‖ < e}
    {Q : CKSTensorPatch} {P : SmoothAngularPatch} {θ₀ : Angle} {δ R : ℝ}
    (h : GenuineBoostPatch e p he Q P θ₀ δ R) (hrep : Q.RepresentsMassAspect M)
    {θ : Angle} (hθ : θ ∈ Metric.ball θ₀ δ) :
    cksChartMassAspect P.param
      (lorentzRadialLeading e (mass e p) p P.param Q.patch.extension Q.mr)
      (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mg)
      (lorentzAngularLeading e (mass e p) p P.param Q.patch.extension Q.mK) θ =
      aspectPullback e p he M (P.chart.symm θ) := by
  have hb := h.boundary_image θ hθ
  rw [lorentz_cks_massAspect he P Q.patch (h.estimates.ball_target hθ) hb.1]
  change (denominator e (mass e p) p (P.param θ))⁻¹ ^3 *
      cksChartMassAspect Q.patch.param Q.mr Q.mg Q.mK
        (Q.patch.extension (boundary e p he (P.chart.symm θ))) = _
  rw [Q.patch.extension_eq _ hb.1,hrep _ hb]
  rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem source_atlas_from_original {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (_hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
    let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
    let M' := aspectPullback e p ht M
    ∃ (ι : Type) (q : SourceCollarAtlas A' B' ι) (hM' : SmoothSphere M'),
      Nonempty ι ∧ q.HasMassAspect M' ∧ bondiCharge M' = (mass e p,0) ∧
      SmoothSphere (heatDatum M' hM') ∧ Balanced (heatDatum M' hM') (mass e p) ∧
      ∀ x : E, q.radius < ‖x‖ → S < ‖hyperbolicMap e (mass e p) p x‖ := by
  classical
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
  let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
  obtain ⟨s,P,δ,R,K,C,hR,hK,hKpos,hC,hpatch,hbounds,hcover⟩ :=
    exists_uniform_boost_collar_atlas ht A B old hold hreal
  obtain ⟨T,hT,hRT,hfar⟩ := homeomorph_maps_far_tail (hyperbolicHomeomorph e p ht) S R
  have geom (x : E) (hx : T < ‖x‖) := hyperbolic_source_geometry ht A B
    (U := {z | S < ‖z‖}) (isOpen_lt continuous_const continuous_norm)
    hAs hBs hA hB hpos hDEC (hfar x hx)
  let ι := {n : Sphere // n ∈ s}
  have hd (i : ι) : 0 < δ i := by
    have hh := (hpatch i i.2).genuine.estimates.ball_pos
    linarith
  have hsub (i : ι) : Metric.ball ((P i).chart i) (δ i) ⊆
      Metric.ball ((P i).chart i) (2*δ i) := Metric.ball_subset_ball (by linarith [hd i])
  let Q : ι → CollarSourcePatch A' B' := fun i =>
    (hpatch i i.2).collarSourcePatch Metric.isOpen_ball (hsub i)
  have hg (i : ι) (y : CKSMixedGeometry.Point)
      (hy : y ∈ angularRadialTail T (Q i).region) :=
    original_source_patch_properties (Q i) hT
      (fun x hx => (geom x hx).1) (fun x hx => (geom x hx).2.1)
      (fun x hx => (geom x hx).2.2.1) (fun x hx => (geom x hx).2.2.2.1)
      (fun x hx => (geom x hx).2.2.2.2.1) (fun x hx => (geom x hx).2.2.2.2.2)
      (fun θ hθ => ((hpatch i i.2).genuine.estimates.radial_smooth θ (hsub i hθ)).contDiffAt
        (Metric.isOpen_ball.mem_nhds (hsub i hθ)))
      (fun a b θ hθ => ((hpatch i i.2).genuine.estimates.angular_smooth a b θ (hsub i hθ)).contDiffAt
        (Metric.isOpen_ball.mem_nhds (hsub i hθ)))
      (fun a b θ hθ => ((hpatch i i.2).genuine.estimates.second_smooth a b θ (hsub i hθ)).contDiffAt
        (Metric.isOpen_ball.mem_nhds (hsub i hθ))) hy
  let q : SourceCollarAtlas A' B' ι := {
    patch := Q
    radius := T
    radius_pos := hT
    jetSet := K
    jetSet_compact := hK
    jetSet_positive := hKpos
    bound := C
    bound_nonneg := hC
    bounds := by
      intro i θ hθ ρ
      have hb := hbounds i i.2 θ (Metric.ball_subset_closedBall hθ) ρ
      refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,?_⟩
      intro hr
      exact hb.2.2.2.2.2 (hRT.trans_lt hr)
    source_smooth := fun i y hy => (hg i y hy).1
    source_positive := fun i y hy => (hg i y hy).2.1
    source_symmetric := fun i y hy => (hg i y hy).2.2.1
    source_DEC := fun i y hy => (hg i y hy).2.2.2
    covers := by
      intro n
      obtain ⟨i,hi,hn⟩ := hcover n
      exact ⟨⟨i,hi⟩,hn⟩ }
  obtain ⟨hM',hcharge,hsmooth,hbalanced⟩ := balanced_charge_and_heat hM ht
  refine ⟨ι,q,hM',?_,?_,hcharge,hsmooth,hbalanced,hfar⟩
  · obtain ⟨i,_⟩ := q.covers (spatialDirection 0)
    exact ⟨i⟩
  · intro i θ hθ
    exact genuine_patch_massAspect (hpatch i i.2).genuine (hrep _) (hsub i hθ)
end
end CKSLorentz

end







noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set
open scoped ENNReal

lemma tailRegion_measurable (L : ℝ) : MeasurableSet (tailRegion L) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet

end
end CKSTailVolume

end











noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem original_CKS_end_replacement {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
    let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
    ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
      1 ≤ T ∧ T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ x : E, T < ‖x‖ → S < ‖hyperbolicMap e (mass e p) p x‖) ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ContDiffOn ℝ ∞ (G R) {x | T < ‖x‖} ∧
        ContDiffOn ℝ ∞ (k R) {x | T < ‖x‖} ∧
        (∀ x, T < ‖x‖ →
          (∀ v w, G R x v w = G R x w v) ∧
          (∀ v : E, v ≠ 0 → 0 < G R x v v) ∧
          (∀ v w, k R x v w = k R x w v) ∧
          spatialDEC (G R) (k R) x ∧
          ∀ v : E, (1-ε R)*sourceSpatial A' x v v ≤ G R x v v) ∧
        (∀ x, ‖x‖ ≤ R → G R x = sourceSpatial A' x ∧ k R x = sourceSpatial B' x) ∧
        (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
        (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
        Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
        Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
        0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
        (∃ L : ℝ, 2*R^2 ≤ L ∧
          IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion L) (spatialVolume (G R))) ∧
        ∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0 := by
  classical
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
  let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
  obtain ⟨ι,q,hM',hne,hmass,hcharge,hheat,hbalanced,hfar⟩ :=
    source_atlas_from_original hM ht A B old hold hrep hreal hS hAs hBs hA hB hpos hDEC
  have hA' (x : E) (hx : q.radius < ‖x‖) (v w : E) : A' x v w = A' x w v :=
    hA _ (hfar x hx) _ _
  have hB' (x : E) (hx : q.radius < ‖x‖) (v w : E) : B' x v w = B' x w v :=
    hB _ (hfar x hx) _ _
  let f := heatDatum (aspectPullback e p ht M) hM'
  let m := mass e p
  obtain ⟨S₁,R₁,hS₁,hq₁,h₁,hsm⟩ :=
    actual_same_end_smooth_replacement q hM' hmass m hcharge hA' hB'
  obtain ⟨S₂,R₂,hS₂,hq₂,h₂,hdec⟩ := actual_same_end_DEC q hM' hmass m hcharge hA' hB'
  obtain ⟨R₃,hR₃,hq₃,ε,hε,hεb,hlower⟩ := actual_same_end_uniform_lower q f hheat m hA' hB'
  obtain ⟨R₄,hR₄,hint⟩ := actual_same_end_tail_integrable q f hheat m
  let T := max S₁ S₂
  let R₀ := max (T+1) (max (max R₁ R₂) (max R₃ R₄))
  have h1 : R₁ ≤ R₀ := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h2 : R₂ ≤ R₀ := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have h3 : R₃ ≤ R₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h4 : R₄ ≤ R₀ := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hs1 : S₁ ≤ T := le_max_left _ _
  have hs2 : S₂ ≤ T := le_max_right _ _
  have hqt : q.radius < T := hq₁.trans_le hs1
  refine ⟨T,R₀,ε,q.replacementMetric f m,q.replacementTensor f m,
    hS₁.trans hs1,lt_of_lt_of_le (by linarith : T < T+1) (le_max_left _ _),
    hR₃.trans h3,hε,fun x hx => hfar x (hqt.trans hx),?_⟩
  intro R hR
  obtain ⟨hg,hk,hpk,heq,_,_⟩ := hsm R (h1.trans hR)
  obtain ⟨hz,haf,hE,hP,hη0,hη1⟩ := actual_same_end_AF_ADM q f hheat m ((hR₃.trans h3).trans hR)
  obtain ⟨L,hL,hint',hmom⟩ := hint R (h4.trans hR)
  refine ⟨hεb R (h3.trans hR),hg.mono (fun x hx => hs1.trans_lt hx),
    hk.mono (fun x hx => hs1.trans_lt hx),?_,heq,hz,haf,hE,hP,hη0,hη1,⟨L,hL,hint'⟩,hmom⟩
  intro x hx
  obtain ⟨hgs,hgp,hks⟩ := hpk x (hs1.trans_lt hx)
  exact ⟨hgs,hgp,hks,hdec R (h2.trans hR) x (hs2.trans_lt hx),hlower R (h3.trans hR) x (hqt.trans hx)⟩
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise
lemma spatial_energy_continuousAt {A B : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (hsym : ∀ v w, A x v w = A x w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < A x v v) :
    ContinuousAt (spatialEnergy A B) x := by
  have hg := physicalMetricJet_continuousAt (spatialCoefficients_smooth hA)
    (spatialCoefficients_positive hsym hpos).det_pos.ne'
  have hk := physicalTensorJet_continuousAt (spatialCoefficients_smooth hB)
  exact (hg.energy hk).comp CKSCartesianOuter.toPoint.continuous.continuousAt
lemma spatial_density_continuousAt {A : SpatialTensor} {x : E}
    (hA : ContDiffAt ℝ ∞ A x) :
    ContinuousAt (fun y => Real.sqrt (spatialCartesian A y).det) x := by
  have hc : ContinuousAt (spatialCartesian A) x :=
    (spatialCoefficients_smooth hA).continuousAt.comp CKSCartesianOuter.toPoint.continuous.continuousAt
  exact (((continuous_id : Continuous (fun M : AmbientMat => M)).matrix_det).continuousAt.comp hc).sqrt
lemma spatial_integrableOn_compact {A : SpatialTensor} {f : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hA : ∀ x ∈ K, ContDiffAt ℝ ∞ A x)
    (hf : ContinuousOn f K) : IntegrableOn f K (spatialVolume A) := by
  have hd : ContinuousOn (fun x => Real.sqrt (spatialCartesian A x).det) K :=
    fun x hx => (spatial_density_continuousAt (hA x hx)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hd
  have hμ : (spatialVolume A).restrict K ≤ ENNReal.ofReal C • volume.restrict K := by
    rw [spatialVolume,restrict_withDensity hK.measurableSet,← withDensity_const]
    apply withDensity_mono
    filter_upwards [self_mem_ae_restrict hK.measurableSet] with x hx
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x hx)
  exact ((hf.integrableOn_compact hK).smul_measure ENNReal.ofReal_ne_top).mono_measure hμ

theorem end_constraints_integrable {A B : SpatialTensor} {T L s : ℝ}
    (hA : ContDiffOn ℝ ∞ A {x | T < ‖x‖})
    (hB : ContDiffOn ℝ ∞ B {x | T < ‖x‖})
    (hsym : ∀ x, T < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hpos : ∀ x, T < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < A x v v)
    (hDEC : ∀ x, T < ‖x‖ → spatialDEC A B x)
    (htail : IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion L) (spatialVolume A))
    (hs : T < s) :
    IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion s) (spatialVolume A) ∧
    IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
      (physicalMetricJet (spatialCoefficients A) (CKSCartesianOuter.toPoint x))
      (physicalTensorJet (spatialCoefficients B) (CKSCartesianOuter.toPoint x))))
      (CKSTailVolume.tailRegion s) (spatialVolume A) := by
  have ho : IsOpen {x : E | T < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have ha (x : E) (hx : T < ‖x‖) := hA.contDiffAt (ho.mem_nhds hx)
  have hb (x : E) (hx : T < ‖x‖) := hB.contDiffAt (ho.mem_nhds hx)
  let K : Set E := {x | s ≤ ‖x‖ ∧ ‖x‖ ≤ L}
  have hK : IsCompact K := by
    have he : K = Metric.closedBall (0:E) L ∩ {x | s ≤ ‖x‖} := by
      ext x
      simp only [K,mem_ofPred_eq,mem_inter_iff,Metric.mem_closedBall,dist_zero_right]
      tauto
    rw [he]
    exact (isCompact_closedBall (0:E) L).inter_right (isClosed_le continuous_const continuous_norm)
  have hkt (x : E) (hx : x ∈ K) : T < ‖x‖ := hs.trans_le hx.1
  have hiK : IntegrableOn (spatialEnergy A B) K (spatialVolume A) :=
    spatial_integrableOn_compact hK (fun x hx => ha x (hkt x hx)) fun x hx =>
      (spatial_energy_continuousAt (ha x (hkt x hx)) (hb x (hkt x hx))
        (hsym x (hkt x hx)) (hpos x (hkt x hx))).continuousWithinAt
  have hie : IntegrableOn (spatialEnergy A B) (CKSTailVolume.tailRegion s) (spatialVolume A) := by
    apply (hiK.union htail).mono_set
    intro x hx
    by_cases hL : L < ‖x‖
    · exact Or.inr hL
    · exact Or.inl ⟨hx.le,le_of_not_gt hL⟩
  refine ⟨hie,?_⟩
  have hc : ContinuousOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
      (physicalMetricJet (spatialCoefficients A) (CKSCartesianOuter.toPoint x))
      (physicalTensorJet (spatialCoefficients B) (CKSCartesianOuter.toPoint x))))
      (CKSTailVolume.tailRegion s) := by
    intro x hx
    have hxt : T < ‖x‖ := hs.trans hx
    have hg := physicalMetricJet_continuousAt (spatialCoefficients_smooth (ha x hxt))
      (spatialCoefficients_positive (hsym x hxt) (hpos x hxt)).det_pos.ne'
    have hk := physicalTensorJet_continuousAt (spatialCoefficients_smooth (hb x hxt))
    exact ((hg.momentumSq hk).sqrt.comp CKSCartesianOuter.toPoint.continuous.continuousAt).continuousWithinAt
  apply hie.mono' (hc.aestronglyMeasurable (CKSTailVolume.tailRegion_measurable s))
  filter_upwards [self_mem_ae_restrict (CKSTailVolume.tailRegion_measurable s)] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact hDEC x (hs.trans hx)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

theorem original_CKS_end_integrable_replacement {M : Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let A' := spatialTensorPullback (hyperbolicMap e (mass e p) p) A
    let B' := spatialTensorPullback (hyperbolicMap e (mass e p) p) B
    ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
      1 ≤ T ∧ T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ x : E, T < ‖x‖ → S < ‖hyperbolicMap e (mass e p) p x‖) ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ContDiffOn ℝ ∞ (G R) {x | T < ‖x‖} ∧
        ContDiffOn ℝ ∞ (k R) {x | T < ‖x‖} ∧
        (∀ x, T < ‖x‖ →
          (∀ v w, G R x v w = G R x w v) ∧
          (∀ v : E, v ≠ 0 → 0 < G R x v v) ∧
          (∀ v w, k R x v w = k R x w v) ∧
          spatialDEC (G R) (k R) x ∧
          ∀ v : E, (1-ε R)*sourceSpatial A' x v v ≤ G R x v v) ∧
        (∀ x, ‖x‖ ≤ R → G R x = sourceSpatial A' x ∧ k R x = sourceSpatial B' x) ∧
        (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
        (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
        Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
        Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
        0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
        (∀ s : ℝ, T < s →
          IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion s) (spatialVolume (G R)) ∧
          IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
            (physicalMetricJet (spatialCoefficients (G R)) (CKSCartesianOuter.toPoint x))
            (physicalTensorJet (spatialCoefficients (k R)) (CKSCartesianOuter.toPoint x))))
            (CKSTailVolume.tailRegion s) (spatialVolume (G R))) ∧
        ∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0 := by
  classical
  dsimp only
  obtain ⟨T,R₀,ε,G,k,hT,hTR,hR₀,hε,hfar,hall⟩ :=
    original_CKS_end_replacement hM ht A B old hold hrep hreal hS hAs hBs hA hB hpos hDEC
  refine ⟨T,R₀,ε,G,k,hT,hTR,hR₀,hε,hfar,?_⟩
  intro R hR
  obtain ⟨heps,hGs,hks,hgeom,heq,hzero,hAF,hE,hP,hpad0,hpad1,⟨L,hL,hi⟩,hmom⟩ := hall R hR
  refine ⟨heps,hGs,hks,hgeom,heq,hzero,hAF,hE,hP,hpad0,hpad1,?_,hmom⟩
  intro s hs
  exact end_constraints_integrable hGs hks (fun x hx => (hgeom x hx).1)
    (fun x hx => (hgeom x hx).2.1) (fun x hx => (hgeom x hx).2.2.2.1) hi hs
end
end CKSLorentz

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Set Filter CKSLorentz
open scoped Topology
variable {M : Type*} [TopologicalSpace M]

theorem boosted_end_proper (h : E ≃ₜ E) (f : M → E) {U : Set M}
    (hU : IsOpen U) (hf : ContinuousOn f U) {S : ℝ}
    (hclosed : ∀ r, S < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖}) (T₀ : ℝ) :
    ∃ T : ℝ, 0 < T ∧ T₀ ≤ T ∧
      (∀ z : E, T < ‖z‖ → S+1 < ‖h z‖) ∧
      IsOpen {x : M | x ∈ U ∧ T < ‖h.symm (f x)‖} ∧
      ∀ r, T < r → IsClosed {x : M |
        (x ∈ U ∧ T < ‖h.symm (f x)‖) ∧ r ≤ ‖h.symm (f x)‖} := by
  obtain ⟨T,hT,hT₀,hfar⟩ := homeomorph_maps_far_tail h (S+1) T₀
  have hnew : ContinuousOn (fun x => ‖h.symm (f x)‖) U :=
    (h.symm.continuous.comp_continuousOn hf).norm
  refine ⟨T,hT,hT₀,hfar,?_,?_⟩
  · exact hnew.isOpen_inter_preimage hU isOpen_Ioi
  · intro r hr
    let C : Set M := {x | x ∈ U ∧ S+1 ≤ ‖f x‖}
    have hC : IsClosed C := hclosed _ (by linarith)
    have hc : ContinuousOn (fun x => ‖h.symm (f x)‖) C :=
      hnew.mono (fun x hx => hx.1)
    have hh := hc.preimage_isClosed_of_isClosed hC (isClosed_Ici : IsClosed (Ici r))
    convert hh using 1
    ext x
    constructor
    · rintro ⟨⟨hx,hTx⟩,hrx⟩
      have hxS := hfar (h.symm (f x)) hTx
      rw [h.apply_symm_apply] at hxS
      exact ⟨⟨hx,hxS.le⟩,hrx⟩
    · rintro ⟨⟨hx,hxS⟩,hrx⟩
      exact ⟨⟨hx,hr.trans_le hrx⟩,hrx⟩
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Bundle Manifold
open scoped Bundle Manifold ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
def tangentNorm (g : Metric I (M := M)) (x : M) (v : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x v v)
def metricEDist (g : Metric I (M := M)) (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y

end
end CKSReplacementCompleteness

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Filter
open scoped Topology ENNReal

theorem complete_of_emetricLower {X : Type*} (g G : EMetricSpace X)
    (htop : g.toUniformSpace.toTopologicalSpace = G.toUniformSpace.toTopologicalSpace)
    (c : ℝ≥0∞) (hc : 0 < c) (hcfin : c ≠ ⊤)
    (hg : @CompleteSpace X g.toUniformSpace)
    (hlow : ∀ x y, c * @edist X g.toEDist x y ≤ @edist X G.toEDist x y) :
    @CompleteSpace X G.toUniformSpace := by
  refine @CompleteSpace.mk X G.toUniformSpace ?_
  intro f hf
  have hf' : @Cauchy X g.toUniformSpace f := by
    apply (@EMetric.cauchy_iff X g.toPseudoEMetricSpace f).2
    obtain ⟨hne, hsmall⟩ := (@EMetric.cauchy_iff X G.toPseudoEMetricSpace f).1 hf
    refine ⟨hne, fun δ hδ => ?_⟩
    obtain ⟨s, hs, hdist⟩ := hsmall (c * δ) (ENNReal.mul_pos hc.ne' hδ.ne')
    refine ⟨s, hs, fun x hx y hy => ?_⟩
    exact (ENNReal.mul_lt_mul_iff_right hc.ne' hcfin).mp
      ((hlow x y).trans_lt (hdist x hx y hy))
  obtain ⟨x, hx⟩ := @CompleteSpace.complete X g.toUniformSpace hg f hf'
  refine ⟨x, ?_⟩
  rw [← htop]
  exact hx
end
end CKSReplacementCompleteness

end

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Bundle Manifold ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
lemma metricEDist_eq (g : Metric I (M := M)) (x y : M) :
    metricEDist I g x y =
      ⨅ γ : Path x y, ⨅ (_ : ContMDiff (modelWithCornersEuclideanHalfSpace 1) I 1 γ),
        ∫⁻ t : unitInterval, ENNReal.ofReal (tangentNorm I g (γ t) (mfderiv% γ t 1)) := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  unfold metricEDist
  rw [Manifold.riemannianEDist_def]
  congr 1
  funext γ
  congr 1
  funext hγ
  apply lintegral_congr
  intro t
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl
lemma tangentNorm_lower (g G : Metric I (M := M)) {ε : ℝ} (hε : ε < 1)
    (hlow : MetricLower I g G ε) (x : M) (v : TangentSpace I x) :
    Real.sqrt (1-ε) * tangentNorm I g x v ≤ tangentNorm I G x v := by
  unfold tangentNorm
  rw [← Real.sqrt_mul (by linarith : 0 ≤ 1-ε)]
  exact Real.sqrt_le_sqrt (hlow x v)

theorem metricEDist_lower (g G : Metric I (M := M)) {ε : ℝ} (hε : ε < 1)
    (hlow : MetricLower I g G ε) (x y : M) :
    ENNReal.ofReal (Real.sqrt (1-ε)) * metricEDist I g x y ≤ metricEDist I G x y := by
  rw [metricEDist_eq, metricEDist_eq]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt (1-ε)) *
        ∫⁻ t : unitInterval, ENNReal.ofReal (tangentNorm I g (γ t) (mfderiv% γ t 1)) :=
      mul_le_mul' le_rfl (iInf_le_of_le γ (iInf_le _ hγ))
    _ = ∫⁻ t : unitInterval, ENNReal.ofReal (Real.sqrt (1-ε)) *
        ENNReal.ofReal (tangentNorm I g (γ t) (mfderiv% γ t 1)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg (1-ε))]
      exact ENNReal.ofReal_le_ofReal (tangentNorm_lower I g G hε hlow _ _)
variable [T3Space M]
lemma metricSpace_topology (g : Metric I (M := M)) :
    (metricSpace I g).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› := rfl
lemma metricSpace_edist (g : Metric I (M := M)) (x y : M) :
    @edist M (metricSpace I g).toEDist x y = metricEDist I g x y := rfl

theorem complete_of_metricLower (g G : Metric I (M := M))
    {ε : ℝ} (_hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hg : IsComplete I g) (hlow : MetricLower I g G ε) : IsComplete I G := by
  have htop : (metricSpace I g).toUniformSpace.toTopologicalSpace =
      (metricSpace I G).toUniformSpace.toTopologicalSpace :=
    (metricSpace_topology I g).trans (metricSpace_topology I G).symm
  have hdist : ∀ x y, ENNReal.ofReal (Real.sqrt (1-ε)) *
      @edist M (metricSpace I g).toEDist x y ≤ @edist M (metricSpace I G).toEDist x y := by
    intro x y
    rw [metricSpace_edist, metricSpace_edist]
    exact metricEDist_lower I g G hε1 hlow x y
  exact complete_of_emetricLower (metricSpace I g) (metricSpace I G) htop
    (ENNReal.ofReal (Real.sqrt (1-ε)))
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 (sub_pos.mpr hε1)))
    ENNReal.ofReal_ne_top hg hdist

end
end CKSReplacementCompleteness

end


noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
universe u

lemma rawHausdorffArea_lower {X : Type u} (m n : EMetricSpace X) {c : ℝ≥0}
    (hc : 0 < c)
    (h : ∀ x y : X, (c : ℝ≥0∞) * @edist X m.toEDist x y ≤ @edist X n.toEDist x y)
    (s : Set X) :
    (c : ℝ≥0∞)^2 * rawHausdorffArea m s ≤ rawHausdorffArea n s := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hcE : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc0
  have ha : @AntilipschitzWith X X m.toPseudoEMetricSpace n.toPseudoEMetricSpace c⁻¹ id := by
    intro x y
    change @edist X m.toEDist x y ≤ (↑(c⁻¹) : ℝ≥0∞) * @edist X n.toEDist x y
    rw [ENNReal.coe_inv hc0]
    calc
      _ = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * @edist X m.toEDist x y) := by
        rw [← mul_assoc,ENNReal.inv_mul_cancel hcE ENNReal.coe_ne_top,one_mul]
      _ ≤ _ := mul_le_mul' le_rfl (h x y)
  have hm := @AntilipschitzWith.le_hausdorffMeasure_image X X m n
    (@borel X m.toUniformSpace.toTopologicalSpace)
    (@BorelSpace.mk X m.toUniformSpace.toTopologicalSpace (@borel X m.toUniformSpace.toTopologicalSpace) rfl)
    (@borel X n.toUniformSpace.toTopologicalSpace)
    (@BorelSpace.mk X n.toUniformSpace.toTopologicalSpace (@borel X n.toUniformSpace.toTopologicalSpace) rfl) id c⁻¹ (2 : ℝ) ha (by norm_num) s
  simp only [Set.image_id] at hm
  change rawHausdorffArea m s ≤ (↑(c⁻¹) : ℝ≥0∞)^(2 : ℝ) * rawHausdorffArea n s at hm
  have he : (c : ℝ≥0∞)^2 * (↑(c⁻¹) : ℝ≥0∞)^(2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = (2 : ℕ) from rfl,ENNReal.rpow_natCast,ENNReal.coe_inv hc0,
      ← mul_pow,ENNReal.mul_inv_cancel hcE ENNReal.coe_ne_top,one_pow]
  calc
    _ ≤ (c : ℝ≥0∞)^2 * ((↑(c⁻¹) : ℝ≥0∞)^(2 : ℝ) * rawHausdorffArea n s) :=
      mul_le_mul' le_rfl hm
    _ = _ := by rw [← mul_assoc,he,one_mul]
end
end CKSGeometricCuts

end

noncomputable section
namespace CKSGeometricCuts
noncomputable section
open Set Manifold MeasureTheory CKSReplacementCompleteness
open scoped ContDiff ENNReal NNReal
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H3 M]
  [IsManifold I3 1 M] [T3Space M]

theorem area_lower (g G : Metric I3 (M := M)) {ε : ℝ}
    (hε1 : ε < 1) (hlow : MetricLower I3 g G ε) (Γ : Set M) :
    ENNReal.ofReal (1-ε) * area M g Γ ≤ area M G Γ := by
  let c : ℝ≥0 := ⟨Real.sqrt (1-ε),Real.sqrt_nonneg _⟩
  have hc : 0 < c := Real.sqrt_pos.mpr (sub_pos.mpr hε1)
  have he : (c : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt (1-ε)) := by
    exact (ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)).symm
  have hs : (c : ℝ≥0∞)^2 = ENNReal.ofReal (1-ε) := by
    rw [he,← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,Real.sq_sqrt (le_of_lt (sub_pos.mpr hε1))]
  have hdist : ∀ x y : M, (c : ℝ≥0∞) * @edist M (metricSpace I3 g).toEDist x y ≤
      @edist M (metricSpace I3 G).toEDist x y := by
    intro x y
    rw [he,metricSpace_edist,metricSpace_edist]
    exact metricEDist_lower I3 g G hε1 hlow x y
  have hraw := rawHausdorffArea_lower (metricSpace I3 g) (metricSpace I3 G) hc hdist Γ
  rw [hs] at hraw
  unfold area
  calc
    _ = ENNReal.ofReal (Real.pi/4) * (ENNReal.ofReal (1-ε) * rawHausdorffArea (metricSpace I3 g) Γ) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hraw

theorem geometric_min_area_lower (g G : Metric I3 (M := M)) {ε : ℝ}
    (_hε0 : 0 ≤ ε) (hε1 : ε < 1) (hlow : MetricLower I3 g G ε) :
    ENNReal.ofReal (1-ε) * minEnclosingArea M g ≤ minEnclosingArea M G := by
  unfold minEnclosingArea
  refine le_iInf fun Γ => ?_
  calc
    _ ≤ ENNReal.ofReal (1-ε) * area M g Γ.val := mul_le_mul' le_rfl (iInf_le _ Γ)
    _ ≤ _ := area_lower g G hε1 hlow Γ.val

end
end CKSGeometricCuts

end


noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSGeometricCuts
open scoped Bundle Manifold ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N] [T3Space N]

omit [IsManifold I3 ∞ N] [T3Space N] in
theorem boosted_exterior_coordinates [IsManifold I3 ∞ N] [T3Space N]
    {e : ℝ} {p : E} (he : ‖p‖ < e)
    (f : N → E) (finv : E → N) {U : Set N} {S : ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
    (hi : ContMDiffOn 𝓘(ℝ,E) I3 ∞ finv {y | S < ‖y‖})
    (hleft : ∀ x ∈ U, finv (f x) = x)
    (hright : ∀ y, S < ‖y‖ → finv y ∈ U ∧ f (finv y) = y)
    (hclosed : ∀ r, S < r → IsClosed {x : N | x ∈ U ∧ r ≤ ‖f x‖})
    (hcompact : ∀ r, S < r → IsCompact {x : N | x ∉ U ∨ ‖f x‖ ≤ r})
    (T₀ : ℝ) :
    let H := hyperbolicHomeomorph e p he
    let f' := H.symm ∘ f
    let inv' := finv ∘ H
    ∃ T : ℝ, 0 < T ∧ T₀ ≤ T ∧
      let V := {x : N | x ∈ U ∧ T < ‖f' x‖}
      IsOpen V ∧ ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V ∧
      ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} ∧
      (∀ x ∈ V, inv' (f' x) = x) ∧
      (∀ y, T < ‖y‖ → inv' y ∈ V ∧ f' (inv' y) = y) ∧
      (∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖}) ∧
      ∀ r, T ≤ r → IsCompact {x : N | x ∉ V ∨ ‖f' x‖ ≤ r} := by
  classical
  dsimp only
  let H := hyperbolicHomeomorph e p he
  let f' := H.symm ∘ f
  let inv' := finv ∘ H
  obtain ⟨T,hT,hTT₀,hfar,hVo,hVc⟩ := boosted_end_proper H f hU hf.continuousOn hclosed T₀
  let V : Set N := {x | x ∈ U ∧ T < ‖f' x‖}
  have hHs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ H :=
    (hyperbolicMap_smooth e (mass e p) p).contMDiff
  have hHis : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ H.symm :=
    (hyperbolicMap_smooth e (mass e p) (-p)).contMDiff
  have hf' : ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V :=
    (hHis.comp_contMDiffOn hf).mono (fun x hx => hx.1)
  have hi' : ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} :=
    hi.comp hHs.contMDiffOn (fun y hy => lt_trans (by linarith : S < S+1) (hfar y hy))
  refine ⟨T,hT,hTT₀,hVo,hf',hi',?_,?_,hVc,?_⟩
  · intro x hx
    change finv (H (H.symm (f x))) = x
    rw [H.apply_symm_apply]
    exact hleft x hx.1
  · intro y hy
    have hyr := hright (H y) (lt_trans (by linarith : S < S+1) (hfar y hy))
    have hfy : f' (inv' y) = y := by
      change H.symm (f (finv (H y))) = y
      rw [hyr.2,H.symm_apply_apply]
    exact ⟨⟨hyr.1,by change T < ‖f' (inv' y)‖; rw [hfy]; exact hy⟩,hfy⟩
  · intro r hr
    obtain ⟨B,hB,hBS,hBr⟩ := homeomorph_maps_far_tail H.symm r (S+1)
    have hc := hcompact B (lt_of_lt_of_le (by linarith : S < S+1) hBS)
    have hopen : IsOpen {x : N | x ∈ V ∧ r < ‖f' x‖} :=
      hf'.continuousOn.norm.isOpen_inter_preimage hVo isOpen_Ioi
    have hcl : IsClosed {x : N | x ∉ V ∨ ‖f' x‖ ≤ r} := by
      convert hopen.isClosed_compl using 1
      ext x
      simp only [mem_compl_iff,mem_ofPred_eq,not_and_or,not_lt]
    exact hc.of_isClosed_subset hcl (by
      intro x hx
      by_cases hxU : x ∈ U
      · right
        by_contra hxb
        have hfar' : r < ‖f' x‖ := hBr (f x) (lt_of_not_ge hxb)
        have hxV : x ∈ V := ⟨hxU,hr.trans_lt hfar'⟩
        exact hx.elim (fun h => h hxV) (fun h => (not_lt_of_ge h) hfar')
      · exact Or.inl hxU)
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] spatialScalarAtlas real_id_isometric CKSMetricGluing.real_continuousAdd
  CKSMetricGluing.real_continuousConstSMul CKSMetricGluing.real_smulCommClass
  covector_smulCommClass
attribute [local instance] OAI.CKSSpatialManifold.bilNorm
attribute [local instance] OAI.CKSSpatialManifold.bilSpace

lemma spatialBilinearTriv_pair (e : SpatialTangentTriv I (M := M)) [MemTrivializationAtlas e]
    {x : M} (hx : x ∈ e.baseSet)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
    ((spatialBilinearTriv I e) ⟨x,B⟩).2 v w = B (e.symmL ℝ x v) (e.symmL ℝ x w) := by
  let := CKSLorentz.real_smulCommClass
  unfold spatialBilinearTriv
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ))
    (show x ∈ (e.continuousLinearMap (RingHom.id ℝ) (Trivial.trivialization M ℝ)).baseSet by simpa using hx)]
  rw [Trivialization.continuousLinearMap_apply]
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
    (Trivial.trivialization M ℝ) (show x ∈ (Trivial.trivialization M ℝ).baseSet from mem_univ x)]
  rfl
lemma mfderiv_gauge_smooth {f : M → E} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, E) ∞ f x) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun y => ((NormedSpace.fromTangentSpace (f y)).toContinuousLinearMap.comp
        (mfderiv I 𝓘(ℝ, E) f y)).comp
        ((trivializationAt E (TangentSpace I) x).symmL ℝ y)) x := by
  have h := hf.mfderiv_const (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  convert! h using 1
  funext y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space, NormedSpace.fromTangentSpace]
  rfl

omit [IsManifold I ∞ M] in
lemma bilinearComp_smoothAt [IsManifold I ∞ M]
    {B : M → SpatialBilinear} {A : M → E →L[ℝ] E} {x : M}
    (hB : ContMDiffAt I 𝓘(ℝ, SpatialBilinear) ∞ B x)
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ A x) :
    ContMDiffAt I 𝓘(ℝ, SpatialBilinear) ∞ (fun y => (B y).bilinearComp (A y) (A y)) x := by
  have flipSmooth : ContDiff ℝ ∞ (fun B : SpatialBilinear => B.flip) :=
    by
      let L : SpatialBilinear →L[ℝ] SpatialBilinear := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      exact L.contDiff
  exact flipSmooth.comp_contMDiffAt
    ((flipSmooth.comp_contMDiffAt (hB.clm_comp hA)).clm_comp hA)
lemma endInner_smoothAt {f : M → E} {A : SpatialTensor} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x)
    (hA : ContDiffAt ℝ ∞ A (f x)) :
    ContMDiffAt I (I.prod 𝓘(ℝ,SpatialBilinear)) ∞
      (innerSection I (endInner I f A)) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  apply ((spatialBilinearTriv I e).contMDiffAt_section_iff (IB := I) (n := ∞)
    (F := SpatialBilinear) (s := endInner I f A)
    (show x ∈ (spatialBilinearTriv I e).baseSet by simpa using hx)).mpr
  have hB := hA.contMDiffAt.comp x hf
  apply (bilinearComp_smoothAt hB (mfderiv_gauge_smooth hf)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  ext v w
  rw [spatialBilinearTriv_pair e hy]
  rfl
lemma positive_bilinear_bounded (B : SpatialBilinear) (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v : E | B v v < 1} := by
  have hc : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨a,ha,hm⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.continuousOn
  have haNorm : ‖a‖ = 1 := by simpa [Metric.mem_sphere] using ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at haNorm
  have hp : 0 < B a a := hB a ha0
  have hlow : ∀ v : E, B a a * ‖v‖ ^ 2 ≤ B v v := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hy : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have h := hm (show (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : E) 1 by
      simpa [Metric.mem_sphere] using hy)
    have he : B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) = B v v / ‖v‖^2 := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      field_simp
    change B a a ≤ B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) at h
    rw [he] at h
    exact (le_div_iff₀ (sq_pos_of_pos hn)).mp h
  apply (NormedSpace.isVonNBounded_iff ℝ).mpr
  apply (Metric.isBounded_iff_subset_ball (0 : E)).mpr
  refine ⟨1 + (B a a)⁻¹, ?_⟩
  intro v hv
  change dist v 0 < 1 + (B a a)⁻¹
  rw [dist_zero_right]
  have hbv : B v v < 1 := hv
  have hl := hlow v
  have hinv : 0 < (B a a)⁻¹ := inv_pos.mpr hp
  have he : B a a * (B a a)⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  by_contra hh
  have hn : 1 + (B a a)⁻¹ ≤ ‖v‖ := le_of_not_gt hh
  have hn1 : 1 ≤ ‖v‖ := by linarith
  have hn2 : ‖v‖ ≤ ‖v‖^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hn hp.le
  have hmul2 := mul_le_mul_of_nonneg_left hn2 hp.le
  nlinarith
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] Classical.propDecidable
lemma end_extend_smooth (old : InnerField I (M := M))
    (hOld : ContMDiff I (I.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I old))
    (f : M → E) {U : Set M} (hU : IsOpen U) {T R : ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ f U)
    (htail : ∀ x ∈ U, T < ‖f x‖)
    (hclosed : ∀ r, T < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖})
    (A G : SpatialTensor)
    (hsource : ∀ x ∈ U, old x = endInner I f A x)
    (hR : T < R)
    (hG : ContDiffOn ℝ ∞ G {x | T < ‖x‖})
    (hold : ∀ x, ‖x‖ ≤ R → G x = A x) :
    ContMDiff I (I.prod 𝓘(ℝ,SpatialBilinear)) ∞
      (innerSection I (fun x => if x ∈ U then endInner I f G x else old x)) := by
  intro x
  by_cases hx : x ∈ U
  · have hGat := (hG (f x) (htail x hx)).contDiffAt
      ((isOpen_lt continuous_const continuous_norm).mem_nhds (htail x hx))
    apply (endInner_smoothAt ((hf x hx).contMDiffAt (hU.mem_nhds hx)) hGat).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [innerSection,ite_eq_left hy]
  · let c := (T+R)/2
    have hcT : T < c := by dsimp [c]; linarith
    have hcR : c < R := by dsimp [c]; linarith
    have hx' : x ∈ {x : M | x ∈ U ∧ c ≤ ‖f x‖}ᶜ := by simp [hx]
    apply (hOld x).congr_of_eventuallyEq
    filter_upwards [(hclosed c hcT).isOpen_compl.mem_nhds hx'] with y hy
    by_cases hyU : y ∈ U
    · have hyR : ‖f y‖ ≤ R := by
        have : ¬ c ≤ ‖f y‖ := fun hc => hy ⟨hyU,hc⟩
        exact (lt_of_not_ge this).le.trans hcR.le
      simp only [innerSection,ite_eq_left hyU,hsource y hyU]
      congr 1
      unfold endInner
      rw [hold (f y) hyR]
    · simp only [innerSection,ite_eq_right hyU]
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Bornology Filter CKSLorentz CKSMetricGluing CKSGeometricCuts
open scoped Bundle Manifold ContDiff Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M] [T3Space M]

theorem extend_actual_end (g : SmoothMetric I3 (M := M))
    (K : InnerField I3 (M := M))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (f : M → E) {U : Set M} (hU : IsOpen U) {T R ε : ℝ}
    (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
    (htail : ∀ x ∈ U, T < ‖f x‖)
    (hclosed : ∀ r, T < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖})
    (A B G k : SpatialTensor)
    (hsource : ∀ x ∈ U, g.inner x = endInner I3 f A x ∧ K x = endInner I3 f B x)
    (hR : T < R) (hε : 0 ≤ ε)
    (hG : ContDiffOn ℝ ∞ G {x | T < ‖x‖})
    (hk : ContDiffOn ℝ ∞ k {x | T < ‖x‖})
    (hGsym : ∀ x, T < ‖x‖ → ∀ v w, G x v w = G x w v)
    (hksym : ∀ x, T < ‖x‖ → ∀ v w, k x v w = k x w v)
    (hpos : ∀ x, T < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < G x v v)
    (hold : ∀ x, ‖x‖ ≤ R → G x = A x ∧ k x = B x)
    (hlower : ∀ x, T < ‖x‖ → ∀ v : E, (1-ε)*A x v v ≤ G x v v) :
    ∃ (g' : SmoothMetric I3 (M := M)) (K' : InnerField I3 (M := M)),
      ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K') ∧
      (∀ x v w, K' x v w = K' x w v) ∧
      (∀ x ∈ U, g'.inner x = endInner I3 f G x ∧ K' x = endInner I3 f k x) ∧
      (∀ x, (x ∉ U ∨ ‖f x‖ ≤ R) → g'.inner x = g.inner x ∧ K' x = K x) ∧
      CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric ε ∧
      (ε < 1 → CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric →
        CKSReplacementCompleteness.IsComplete I3 g'.toContinuousRiemannianMetric) ∧
      (ε < 1 → ENNReal.ofReal (1-ε)*minEnclosingArea M g.toContinuousRiemannianMetric ≤
        minEnclosingArea M g'.toContinuousRiemannianMetric) := by
  classical
  let Q : InnerField I3 (M := M) := fun x => if x ∈ U then endInner I3 f G x else g.inner x
  let L : InnerField I3 (M := M) := fun x => if x ∈ U then endInner I3 f k x else K x
  have hQs : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 Q) :=
    end_extend_smooth g.inner g.contMDiff f hU hf htail hclosed A G
      (fun x hx => (hsource x hx).1) hR hG (fun x hx => (hold x hx).1)
  have hLs : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 L) :=
    end_extend_smooth K hK f hU hf htail hclosed B k
      (fun x hx => (hsource x hx).2) hR hk (fun x hx => (hold x hx).2)
  have hQsym : ∀ x v w, Q x v w = Q x w v := by
    intro x v w
    by_cases hx : x ∈ U
    · change (if x ∈ U then endInner I3 f G x else g.inner x) v w =
        (if x ∈ U then endInner I3 f G x else g.inner x) w v
      rw [ite_eq_left hx]
      exact hGsym (f x) (htail x hx) _ _
    · simpa only [Q,ite_eq_right hx] using g.symm x v w
  have hQpos : ∀ x (v : TangentSpace I3 x), v ≠ 0 → 0 < Q x v v := by
    intro x v hv
    by_cases hx : x ∈ U
    · let df := (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap.comp
        (mfderiv I3 𝓘(ℝ,E) f x)
      have hvd : df v ≠ 0 := by
        intro hz
        have hp := g.pos x v hv
        rw [(hsource x hx).1] at hp
        change 0 < A (f x) (df v) (df v) at hp
        simp only [hz,map_zero,lt_self_iff_false] at hp
      change 0 < (if x ∈ U then endInner I3 f G x else g.inner x) v v
      rw [ite_eq_left hx]
      exact hpos (f x) (htail x hx) (df v) hvd
    · simpa only [Q,ite_eq_right hx] using g.pos x v hv
  let g' : SmoothMetric I3 (M := M) := {
    inner := Q
    symm := hQsym
    pos := hQpos
    isVonNBounded := fun x => positive_bilinear_bounded (Q x) (hQpos x)
    contMDiff := hQs }
  have hlow : CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric
      g'.toContinuousRiemannianMetric ε := by
    intro x v
    change (1-ε)*g.inner x v v ≤ Q x v v
    by_cases hx : x ∈ U
    · rw [(hsource x hx).1]
      change (1-ε)*endInner I3 f A x v v ≤
        (if x ∈ U then endInner I3 f G x else g.inner x) v v
      rw [ite_eq_left hx]
      exact hlower (f x) (htail x hx) _
    · simp only [Q,ite_eq_right hx]
      have hn : 0 ≤ g.inner x v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact (g.pos x v hv).le
      nlinarith
  refine ⟨g',L,hLs,?_,?_,?_,hlow,?_,?_⟩
  · intro x v w
    by_cases hx : x ∈ U
    · change (if x ∈ U then endInner I3 f k x else K x) v w =
        (if x ∈ U then endInner I3 f k x else K x) w v
      rw [ite_eq_left hx]
      exact hksym (f x) (htail x hx) _ _
    · simpa only [L,ite_eq_right hx] using hKsym x v w
  · intro x hx
    exact ⟨by simp [g',Q,hx],by simp [L,hx]⟩
  · intro x hx
    by_cases hxU : x ∈ U
    · have hxR : ‖f x‖ ≤ R := hx.resolve_left (not_not_intro hxU)
      have hGA : endInner I3 f G x = endInner I3 f A x := by
        unfold endInner
        rw [(hold (f x) hxR).1]
      have hkB : endInner I3 f k x = endInner I3 f B x := by
        unfold endInner
        rw [(hold (f x) hxR).2]
      simpa only [g',Q,L,ite_eq_left hxU,hGA,hkB] using
        ⟨(hsource x hxU).1.symm,(hsource x hxU).2.symm⟩
    · simp [g',Q,L,hxU]
  · intro hε1 hg
    exact CKSReplacementCompleteness.complete_of_metricLower I3
      g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric hε hε1 hg hlow
  · intro hε1
    exact geometric_min_area_lower g.toContinuousRiemannianMetric
      g'.toContinuousRiemannianMetric hε hε1 hlow
end
end CKSSpatialManifold

end


noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
lemma endInner_fullRank (g : SmoothMetric I (M := M)) (f : M → E)
    (A : SpatialTensor) {x : M} (heq : g.inner x = endInner I f A x) :
    Function.Bijective (mfderiv I 𝓘(ℝ,E) f x) := by
  let : FiniteDimensional ℝ (TangentSpace I x) := by exact (inferInstance : FiniteDimensional ℝ E)
  have hi : Function.Injective (mfderiv I 𝓘(ℝ,E) f x) := by
    intro v w hvw
    by_contra hne
    have hp := g.pos x (v-w) (sub_ne_zero.mpr hne)
    rw [heq] at hp
    have hz : (mfderiv I 𝓘(ℝ,E) f x) (v-w) = 0 := by rw [map_sub,hvw,sub_self]
    change 0 < A (f x) ((mfderiv I 𝓘(ℝ,E) f x) (v-w))
      ((mfderiv I 𝓘(ℝ,E) f x) (v-w)) at hp
    rw [hz] at hp
    have ha : A (f x) (0:E) (0:E) = 0 := by simp
    exact (lt_irrefl 0) (ha ▸ hp)
  exact ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
omit [IsManifold I ∞ M] in
lemma PhysicalDECAt.congr_nhds [IsManifold I ∞ M]
    {g K g' K' : InnerField I (M := M)} {x : M}
    (h : PhysicalDECAt I g K x)
    (heq : {y : M | g' y = g y ∧ K' y = K y} ∈ 𝓝 x) :
    PhysicalDECAt I g' K' x := by
  obtain ⟨U,f,A,B,hU,hx,hf,hd,hs,hp,he,hDEC⟩ := h
  obtain ⟨V,hV,hVo,hVx⟩ := mem_nhds_iff.mp heq
  refine ⟨U∩V,f,A,B,hU.inter hVo,⟨hx,hVx⟩,hf.mono inter_subset_left,
    fun y hy => hd y hy.1,fun y hy => hs y hy.1,fun y hy => hp y hy.1,?_,hDEC⟩
  intro y hy
  exact ⟨(hV hy.2).1.trans (he y hy.1).1,(hV hy.2).2.trans (he y hy.1).2⟩
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem extended_manifold_DEC (g g' : SmoothMetric I (M := M))
    (K K' : InnerField I (M := M)) (hDEC : PhysicalDEC I g.inner K)
    (f : M → E) {U : Set M} (hU : IsOpen U) {T R : ℝ} (hR : T < R)
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ f U)
    (htail : ∀ x ∈ U, T < ‖f x‖)
    (hclosed : ∀ r, T < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖})
    (A B : SpatialTensor)
    (hAs : ContDiffOn ℝ ∞ A {x | T < ‖x‖})
    (hBs : ContDiffOn ℝ ∞ B {x | T < ‖x‖})
    (hA : ∀ x, T < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, T < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, T < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < A x v v)
    (hnew : ∀ x, T < ‖x‖ → spatialDEC A B x)
    (hend : ∀ x ∈ U, g'.inner x = endInner I f A x ∧ K' x = endInner I f B x)
    (hold : ∀ x, (x ∉ U ∨ ‖f x‖ ≤ R) → g'.inner x = g.inner x ∧ K' x = K x) :
    PhysicalDEC I g'.inner K' := by
  intro x
  by_cases hx : x ∈ U
  · refine ⟨U,f,A,B,hU,hx,hf,?_,?_,?_,hend,hnew (f x) (htail x hx)⟩
    · intro y hy
      exact endInner_fullRank g' f A (hend y hy).1
    · intro y hy
      have ho := (isOpen_lt continuous_const continuous_norm).mem_nhds (htail y hy)
      exact ⟨(hAs (f y) (htail y hy)).contDiffAt ho,(hBs (f y) (htail y hy)).contDiffAt ho⟩
    · intro y hy
      exact ⟨hA (f y) (htail y hy),hpos (f y) (htail y hy),hB (f y) (htail y hy)⟩
  · apply (hDEC x).congr_nhds
    let c := (T+R)/2
    have hcT : T < c := by dsimp [c]; linarith
    have hcR : c < R := by dsimp [c]; linarith
    have hx' : x ∈ {x : M | x ∈ U ∧ c ≤ ‖f x‖}ᶜ := by simp [hx]
    filter_upwards [(hclosed c hcT).isOpen_compl.mem_nhds hx'] with y hy
    apply hold
    by_cases hyU : y ∈ U
    · right
      have hh : ¬ c ≤ ‖f y‖ := fun hz => hy ⟨hyU,hz⟩
      exact (lt_of_not_ge hh).le.trans hcR.le
    · exact Or.inl hyU
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
omit [IsManifold I ∞ M] in
lemma endInner_comp [IsManifold I ∞ M] {F : E → E} {f : M → E}
    (A : SpatialTensor) {x : M}
    (hF : ContDiffAt ℝ ∞ F (f x)) (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x) :
    endInner I (F ∘ f) A x = endInner I f (spatialTensorPullback F A) x := by
  have hc := mfderiv_comp x (hF.contMDiffAt.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hc
  ext v w
  change A (F (f x)) ((mfderiv I 𝓘(ℝ,E) (F ∘ f) x) v)
      ((mfderiv I 𝓘(ℝ,E) (F ∘ f) x) w) =
    A (F (f x)) ((fderiv ℝ F (f x)) ((mfderiv I 𝓘(ℝ,E) f x) v))
      ((fderiv ℝ F (f x)) ((mfderiv I 𝓘(ℝ,E) f x) w))
  rw [hc]
  rfl
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing
open scoped Bundle Manifold ContDiff Topology
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem endInner_balanced {e : ℝ} {p : E} (he : ‖p‖ < e)
    (f : M → E) (A : SpatialTensor) {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ,E) ∞ f x) :
    endInner I ((hyperbolicHomeomorph e p he).symm ∘ f)
      (sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)) x =
      endInner I f (sourceSpatial A) x := by
  rw [sourceSpatial_boost he]
  let h := hyperbolicHomeomorph e p he
  have hi : ContDiff ℝ ∞ h.symm := hyperbolicMap_smooth e (mass e p) (-p)
  have hs : ContDiff ℝ ∞ h := hyperbolicMap_smooth e (mass e p) p
  have hf' : ContMDiffAt I 𝓘(ℝ,E) ∞ (h.symm ∘ f) x := hi.contDiffAt.contMDiffAt.comp x hf
  have ht := endInner_comp (I := I) (F := h) (f := h.symm ∘ f)
    (sourceSpatial A) hs.contDiffAt hf'
  have heq : h ∘ (h.symm ∘ f) = f := by funext y; exact h.apply_symm_apply (f y)
  rw [heq] at ht
  exact ht.symm
end
end CKSSpatialManifold

end

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Set Filter CKSLorentz
open scoped Topology
variable {M : Type*} [TopologicalSpace M]

theorem compact_side_eventually (f : M → E) {U : Set M} {T : ℝ}
    (hclosed : ∀ r, T < r → IsClosed {x : M | x ∈ U ∧ r ≤ ‖f x‖})
    {C : Set M} (hC : IsCompact C) :
    ∃ R : ℝ, T < R ∧ ∀ r ≥ R, ∀ x ∈ C, x ∉ U ∨ ‖f x‖ ≤ r := by
  classical
  let V : ℕ → Set M := fun n => {x : M | x ∈ U ∧ T+(n:ℝ)+1 ≤ ‖f x‖}ᶜ
  have hVo : ∀ n, IsOpen (V n) := by
    intro n
    exact (hclosed _ (by have : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)).isOpen_compl
  have hcover : C ⊆ ⋃ n, V n := by
    intro x hx
    obtain ⟨n,hn⟩ := exists_nat_gt (‖f x‖-T)
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    intro hy
    have hh : T+(n:ℝ)+1 ≤ ‖f x‖ := hy.2
    linarith
  obtain ⟨q,hq⟩ := hC.elim_finite_subcover V hVo hcover
  refine ⟨T+(q.sup id:ℕ)+1,?_,?_⟩
  · have : 0 ≤ ((q.sup id:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  · intro r hr x hx
    by_cases hxU : x ∈ U
    · right
      obtain ⟨n,hn⟩ := mem_iUnion.mp (hq hx)
      obtain ⟨hnq,hm⟩ := mem_iUnion.mp hn
      have hnle : n ≤ q.sup id := Finset.le_sup (f := id) hnq
      have hnr : (n:ℝ) ≤ ((q.sup id:ℕ):ℝ) := by exact_mod_cast hnle
      have hlt : ‖f x‖ < T+(n:ℝ)+1 := by
        exact lt_of_not_ge (fun h => hm ⟨hxU,h⟩)
      linarith
    · exact Or.inl hxU
end
end CKSSpatialManifold

end


end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSBoundarySurface
attribute [local instance] Classical.propDecidable
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M]
  [@IsManifold ℝ _ E3 _ _ H3
    (@instTopologicalSpaceEuclideanHalfSpace 3 halfSpaceDimension_neZero) I3 ∞ M _ _]

lemma boundaryInverse_val (x : Boundary M) {z : E2}
    (hz : liftHalf z ∈ (chartAt H3 x.val).target) :
    (boundaryInverse x z).val = (chartAt H3 x.val).symm (liftHalf z) := by
  simp only [boundaryInverse,dite_eq_left hz]

lemma boundaryChart_symm_val (x : Boundary M) {z : E2} (hz : z ∈ (boundaryChart x).target) :
    ((boundaryChart x).symm z).val = (chartAt H3 x.val).symm (liftHalf z) :=
  boundaryInverse_val x hz

end CKSBoundarySurface

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology
namespace CKSEmbeddingDerivative
attribute [local instance] halfSpaceDimension_neZero

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [IsManifold I ∞ M] in
lemma extended_chart_derivative_injective [IsManifold I ∞ M] (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    Injective (mfderiv I 𝓘(ℝ,E) (e.extend I) x) := by
  have hed : e.MDifferentiable I I := ⟨
    (contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have hcomp := mfderiv_comp x I.mdifferentiableAt ((hed.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx))
  change mfderiv I 𝓘(ℝ,E) (e.extend I) x = _ at hcomp
  rw [I.hasMFDerivAt.mfderiv] at hcomp
  change mfderiv I 𝓘(ℝ,E) (e.extend I) x = mfderiv I I e x at hcomp
  rw [hcomp]
  exact hed.mfderiv_injective hx

omit [IsManifold I ∞ N] in
lemma immersion_derivative_injective [IsManifold I ∞ N] {f : M → N} {x : M}
    (h : IsImmersionAt I I ∞ f x) : Injective (mfderiv I I f x) := by
  let A : E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E h.complement).comp
    h.equiv.symm.toContinuousLinearMap
  let L : N → E := A ∘ (h.codChart.extend I)
  have hL : ContMDiffAt I 𝓘(ℝ,E) ∞ L (f x) :=
    A.contMDiff.contMDiffAt.comp _
      (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas h.mem_codChart_source)
  have heq : (L ∘ f) =ᶠ[𝓝 x] h.domChart.extend I := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hy' : y ∈ (h.domChart.extend I).source := by simpa only [OpenPartialHomeomorph.extend_source] using hy
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    dsimp only [Function.comp_apply] at hw
    rw [(h.domChart.extend I).left_inv hy'] at hw
    change A ((h.codChart.extend I) (f y)) = _
    rw [hw]
    simp only [A,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply ]
    rfl
  have hdL := hL.mdifferentiableAt (by simp)
  have hdf := h.contMDiffAt.mdifferentiableAt (by simp)
  have hder := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ,E))
  rw [mfderiv_comp x hdL hdf] at hder
  change _ = mfderiv I 𝓘(ℝ,E) (h.domChart.extend I) x at hder
  have hinj := extended_chart_derivative_injective h.domChart h.domChart_mem_maximalAtlas
    h.mem_domChart_source
  rw [← hder] at hinj
  have hi' : Injective ((mfderiv I 𝓘(ℝ,E) L (f x)) ∘ (mfderiv I I f x)) := hinj
  exact hi'.of_comp

lemma smooth_embedding_derivative_injective {f : M → N} (h : IsSmoothEmbedding I I ∞ f) :
    ∀ x, Injective (mfderiv I I f x) := fun x =>
  immersion_derivative_injective (h.isImmersion.isImmersionAt x)

end CKSEmbeddingDerivative

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory Matrix
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

lemma det_two_add_smul_lower (A D : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.PosSemidef) (hD : D.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    c^2 * A.det ≤ (c • A + D).det := by
  have hAs : A 1 0 = A 0 1 := by simpa using hA.1.apply 0 1
  have hDs : D 1 0 = D 0 1 := by simpa using hD.1.apply 0 1
  have hA0 : 0 ≤ A 0 0 := hA.diag_nonneg
  have hA1 : 0 ≤ A 1 1 := hA.diag_nonneg
  have hD0 : 0 ≤ D 0 0 := hD.diag_nonneg
  have hD1 : 0 ≤ D 1 1 := hD.diag_nonneg
  have ha : (A 0 1)^2 ≤ A 0 0 * A 1 1 := by
    have h := hA.det_nonneg
    rw [Matrix.det_fin_two,hAs] at h
    nlinarith
  have hd : (D 0 1)^2 ≤ D 0 0 * D 1 1 := by
    have h := hD.det_nonneg
    rw [Matrix.det_fin_two,hDs] at h
    nlinarith
  have hp : (A 0 1 * D 0 1)^2 ≤ (A 0 0 * D 1 1) * (A 1 1 * D 0 0) := by
    have h := mul_le_mul ha hd (sq_nonneg (D 0 1)) (mul_nonneg hA0 hA1)
    nlinarith only [h]
  have hcross := two_mul_le_add_of_sq_le_mul
    (mul_nonneg hA0 hD1) (mul_nonneg hA1 hD0) hp
  have hcross' : 0 ≤ A 0 0 * D 1 1 + A 1 1 * D 0 0 - 2*A 0 1*D 0 1 := by
    linarith
  have hfinal := mul_nonneg hc hcross'
  have hdd := hD.det_nonneg
  simp only [Matrix.det_fin_two,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hAs,hDs] at hdd ⊢
  nlinarith only [hfinal,hdd]

lemma sqrt_det_two_lower (A G : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) (hlow : (G-c•A).PosSemidef) :
    c * Real.sqrt A.det ≤ Real.sqrt G.det := by
  have h := det_two_add_smul_lower A (G-c•A) hA hlow hc
  rw [add_sub_cancel] at h
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc] at hs
  exact hs

end CKSSurfaceVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology
namespace CKSBoundarySurface
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H3 M] [IsManifold I3 ∞ M]

lemma inclusion_chart_formula (x : Boundary M) {z : E2}
    (hz : z ∈ (boundaryChart x).target) :
    writtenInExtChartAt I2 I3 x (Subtype.val : Boundary M → M) z = liftPlane z := by
  change I3 (chartAt H3 x.val (((boundaryChart x).symm z).val)) = _
  rw [boundaryChart_symm_val x hz, (chartAt H3 x.val).right_inv hz]
  rfl

lemma inclusion_chart_eventually (x : Boundary M) :
    writtenInExtChartAt I2 I3 x (Subtype.val : Boundary M → M) =ᶠ[𝓝 (extChartAt I2 x x)] liftPlane := by
  have ht : (boundaryChart x).target ∈ 𝓝 (extChartAt I2 x x) :=
    (boundaryChart x).open_target.mem_nhds ((boundaryChart x).map_source (mem_chart_source E2 x))
  filter_upwards [ht] with z hz
  exact inclusion_chart_formula x hz

lemma inclusion_smooth : ContMDiff I2 I3 ∞ (Subtype.val : Boundary M → M) := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact ((liftPlane.contDiff.contDiffAt).congr_of_eventuallyEq (inclusion_chart_eventually x)).contDiffWithinAt

lemma inclusion_hasMFDeriv (x : Boundary M) :
    HasMFDerivAt I2 I3 (Subtype.val : Boundary M → M) x liftPlane := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact (liftPlane.hasFDerivAt.congr_of_eventuallyEq (inclusion_chart_eventually x)).hasFDerivWithinAt

lemma inclusion_mfderiv_injective (x : Boundary M) :
    Injective (mfderiv I2 I3 (Subtype.val : Boundary M → M) x) := by
  rw [(inclusion_hasMFDeriv x).mfderiv]
  intro a b h
  change liftPlane a = liftPlane b at h
  have hh : dropPlane (liftPlane a) = dropPlane (liftPlane b) := congrArg dropPlane h
  change (a : E2) = (b : E2)
  exact (drop_lift a).symm.trans (hh.trans (drop_lift b))

end CKSBoundarySurface

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Bundle Manifold ContDiff Topology
namespace CKSInducedArea
variable {H3 : Type*} [TopologicalSpace H3] {I3 : ModelWithCorners ℝ E3 H3}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold I2 ∞ S]
attribute [local instance] real_continuousAdd real_continuousConstSMul real_smulCommClass
  real_id_isometric


attribute [local instance] OAI.CKSInducedArea.bilNorm2

attribute [local instance] OAI.CKSInducedArea.bilSpace2

attribute [local instance] OAI.CKSInducedArea.bilNorm3

attribute [local instance] OAI.CKSInducedArea.bilSpace3

attribute [local instance] OAI.CKSInducedArea.mixNorm23

attribute [local instance] OAI.CKSInducedArea.mixSpace23

attribute [local instance] OAI.CKSInducedArea.mixNorm32

attribute [local instance] OAI.CKSInducedArea.mixSpace32

lemma inducedMetric_lower (g G : Smooth3 (I3 := I3) (N := N)) (φ : S → N)
    (hφ : ContMDiff I2 I3 ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I2 I3 φ x)) {c : ℝ}
    (hlow : ∀ x v, c * g.inner x v v ≤ G.inner x v v) :
    ∀ x v, c * (inducedMetric g φ hφ hinj).inner x v v ≤
      (inducedMetric G φ hφ hinj).inner x v v := by
  intro x v
  exact hlow (φ x) _

end CKSInducedArea

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory Matrix
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma metric_nonneg (g : Metric (M := M)) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

lemma chartMatrix_posSemidef (g : Metric (M := M)) (x : M) (y : E) :
    (chartMatrix g x y).PosSemidef := by
  rw [chartMatrix_eq_toMatrix]
  apply (LinearMap.isPosSemidef_iff_posSemidef_toMatrix stdBasis).mp
  constructor
  · constructor
    intro v w
    exact g.symm _ _ _
  · constructor
    intro v
    exact metric_nonneg g _ _

lemma chartMatrix_sub_posSemidef (g G : Metric (M := M)) {c : ℝ}
    (hlow : ∀ x (v : TangentSpace I x), c*g.inner x v v ≤ G.inner x v v)
    (x : M) (y : E) :
    (chartMatrix G x y - c • chartMatrix g x y).PosSemidef := by
  have h : LinearMap.IsPosSemidef (pullbackInner G x y - c • pullbackInner g x y) := by
    constructor
    · constructor
      intro v w
      change G.inner _ _ _ - c*g.inner _ _ _ = G.inner _ _ _ - c*g.inner _ _ _
      exact congrArg₂ (fun a b : ℝ => a - c*b) (G.symm _ _ _) (g.symm _ _ _)
    · constructor
      intro v
      exact sub_nonneg.mpr (hlow _ _)
  have hh := (LinearMap.isPosSemidef_iff_posSemidef_toMatrix stdBasis).mp h
  have heq : (LinearMap.toMatrix₂ stdBasis stdBasis)
      (pullbackInner G x y - c • pullbackInner g x y) =
      chartMatrix G x y - c • chartMatrix g x y := by
    ext i j
    simp [chartMatrix_eq_toMatrix, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.toMatrix₂_apply]
  rw [heq] at hh
  exact hh

lemma chartDensity_lower (g G : Metric (M := M)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x (v : TangentSpace I x), c*g.inner x v v ≤ G.inner x v v)
    (x : M) (y : E) : c * chartDensity g x y ≤ chartDensity G x y :=
  sqrt_det_two_lower _ _ (chartMatrix_posSemidef g x y) hc
    (chartMatrix_sub_posSemidef g G hlow x y)

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

omit [SecondCountableTopology M] in
lemma localVolume_lower [SecondCountableTopology M] (g G : Metric (M := M)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x (v : TangentSpace I x), c*g.inner x v v ≤ G.inner x v v)
    (x : M) : ENNReal.ofReal c • localVolume g x ≤ localVolume G x := by
  apply Measure.le_iff.2
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,localVolume_apply g x hs,localVolume_apply G x hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro y
  change ENNReal.ofReal c * ENNReal.ofReal (chartDensity g x y) ≤
    ENNReal.ofReal (chartDensity G x y)
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (chartDensity_lower g G hc hlow x y)

end CKSSurfaceVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle Function
open scoped ContDiff Topology
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N]

lemma cutInclusion_smooth [IsManifold I3 ∞ N] (D : OuterDomain N) :
    ContMDiff I2 I3 ∞ (cutInclusion D) :=
  D.embedding.isImmersion.contMDiff.comp CKSBoundarySurface.inclusion_smooth

lemma cutInclusion_derivative_injective [IsManifold I3 ∞ N] (D : OuterDomain N) (x : Surface D) :
    Injective (mfderiv I2 I3 (cutInclusion D) x) := by
  unfold cutInclusion
  rw [mfderiv_comp x ((D.embedding.isImmersion.contMDiff x.val).mdifferentiableAt (by simp))
    ((CKSBoundarySurface.inclusion_smooth x).mdifferentiableAt (by simp))]
  · change Injective ((mfderiv I3 I3 D.inclusion x.val) ∘
      (mfderiv I2 I3 (Subtype.val : Surface D → D.Carrier) x))
    exact (CKSEmbeddingDerivative.smooth_embedding_derivative_injective D.embedding x.val).comp
      (CKSBoundarySurface.inclusion_mfderiv_injective x)

variable [@IsManifold ℝ _ E3 _ _ H3
  (@instTopologicalSpaceEuclideanHalfSpace 3 CKSBoundarySurface.halfSpaceDimension_neZero) I3 ∞ N _ _]

end CKSFullCutArea

end

end OAI
end

section
namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

lemma measure_le_of_restrict_cover {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hcover : ⋃ n, U n = univ) (hle : ∀ n, μ.restrict (U n) ≤ ν.restrict (U n)) : μ ≤ ν := by
  let D := disjointed U
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed hU
  have hDc : ⋃ n, D n = univ := iUnion_disjointed.trans hcover
  have hrestr : ∀ n, μ.restrict (D n) ≤ ν.restrict (D n) := by
    intro n
    calc
      _ = (μ.restrict (U n)).restrict (D n) :=
        (Measure.restrict_restrict_of_subset (disjointed_subset U n)).symm
      _ ≤ (ν.restrict (U n)).restrict (D n) :=
        Measure.restrict_mono (Subset.refl _) (hle n)
      _ = _ := Measure.restrict_restrict_of_subset (disjointed_subset U n)
  calc
    μ = μ.restrict (⋃ n, D n) := by rw [hDc,Measure.restrict_univ]
    _ = Measure.sum (fun n => μ.restrict (D n)) :=
      Measure.restrict_iUnion (disjoint_disjointed U) hD
    _ ≤ Measure.sum (fun n => ν.restrict (D n)) := by
      apply Measure.le_iff.2
      intro s hs
      simp only [Measure.sum_apply _ hs]
      exact ENNReal.tsum_le_tsum (fun n => hrestr n s)
    _ = ν.restrict (⋃ n, D n) := (Measure.restrict_iUnion (disjoint_disjointed U) hD).symm
    _ = ν := by rw [hDc,Measure.restrict_univ]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem riemannianVolume_lower (g G : Metric (M := M)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x (v : TangentSpace I x), c * g.inner x v v ≤ G.inner x v v) :
    ENNReal.ofReal c • riemannianVolume g ≤ riemannianVolume G := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact le_of_eq (Subsingleton.elim _ _)
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    apply measure_le_of_restrict_cover _ _ (fun n => (extChartAt I (f n)).source)
      (fun n => (isOpen_extChartAt_source (f n)).measurableSet) (eq_univ_of_univ_subset hf)
    intro n
    rw [Measure.restrict_smul,riemannianVolume_isVolume g (f n),riemannianVolume_isVolume G (f n)]
    exact localVolume_lower g G hc hlow (f n)

end CKSSurfaceVolume

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSFullCutArea
open CKSGeometricCuts (OuterDomain)
open CKSBoundarySurface
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [SecondCountableTopology N]

theorem area_finite (g : SmoothMetric (N := N)) (D : OuterDomain N) : area g D < ⊤ := by
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  exact isCompact_univ.measure_lt_top

theorem area_lower (g G : SmoothMetric (N := N)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x v, c * g.inner x v v ≤ G.inner x v v) (D : OuterDomain N) :
    ENNReal.ofReal c * area g D ≤ area G D := by
  let : MeasurableSpace (Surface D) := borel (Surface D)
  let : BorelSpace (Surface D) := ⟨rfl⟩
  have h := CKSSurfaceVolume.riemannianVolume_lower
    (cutMetric g D).toContinuousRiemannianMetric (cutMetric G D).toContinuousRiemannianMetric hc
    (CKSInducedArea.inducedMetric_lower g G (cutInclusion D) (cutInclusion_smooth D)
      (cutInclusion_derivative_injective D) hlow)
  exact h univ

theorem minEnclosingArea_lower (g G : SmoothMetric (N := N)) {c : ℝ} (hc : 0 ≤ c)
    (hlow : ∀ x v, c * g.inner x v v ≤ G.inner x v v) :
    ENNReal.ofReal c * minEnclosingArea g ≤ minEnclosingArea G := by
  unfold minEnclosingArea
  apply le_iInf
  intro D
  exact (mul_le_mul' le_rfl (iInf_le _ D)).trans (area_lower g G hc hlow D)

end CKSFullCutArea

end

end OAI
end

section
namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory CKSLorentz CKSMetricGluing
open scoped ContDiff Topology ENNReal
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M]

lemma physical_normalization [BorelSpace M] [SecondCountableTopology M] (g : SmoothMetric I (M := M)) (K : InnerField I (M := M))
    (h : ∃ C Q : M → ℝ, Continuous C ∧ Continuous Q ∧
      Integrable C (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      Integrable Q (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      (∀ x, 0 ≤ Q x ∧ Q x ≤ C x) ∧
      ∀ x (c : ConstraintChart g.inner K x), C x = c.energy ∧ Q x = c.momentumNorm) :
    IntegrableConstraints g K := by
  obtain ⟨C,Q,hC,hQ,hiC,hiQ,hd,hval⟩ := h
  have hpi : 0 < 8 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨fun x => C x / (8*Real.pi),fun x => Q x / (8*Real.pi),
    hC.div_const _,hQ.div_const _,hiC.div_const _,hiQ.div_const _,?_,?_⟩
  · intro x
    exact ⟨div_nonneg (hd x).1 hpi.le,div_le_div_of_nonneg_right (hd x).2 hpi.le⟩
  · intro x c
    constructor
    · rw [mul_div_cancel₀ _ hpi.ne', (hval x c).1]
    · rw [mul_div_cancel₀ _ hpi.ne', (hval x c).2]

end CKSIntrinsicConstraints

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSpatialManifold
noncomputable section
open Bundle Manifold Set Filter MeasureTheory CKSLorentz CKSMetricGluing CKSGeometricCuts
open CKSSphericalHarmonics CKSADM CKSBending
open scoped Bundle Manifold ContDiff Topology
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N] [T3Space N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]

theorem original_CKS_replacement_intrinsic_chart_package
    {M : CKSLorentz.Sphere → ℝ} (hM : SmoothSphere M)
    (ht : ‖(bondiCharge M).2‖ < (bondiCharge M).1)
    (A B : SpatialTensor) (old : CKSLorentz.Sphere → CKSTensorPatch)
    (hold : ∀ n, n ∈ (old n).patch.sphereRegion (old n).region)
    (hrep : ∀ n, (old n).RepresentsMassAspect M)
    (hreal : ∀ n, (old n).Realizes A B)
    {S : ℝ} (hS : 0 < S)
    (hAs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ A x)
    (hBs : ∀ x, S < ‖x‖ → ContDiffAt ℝ ∞ B x)
    (hA : ∀ x, S < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, S < ‖x‖ → ∀ v w, B x v w = B x w v)
    (hpos : ∀ x, S < ‖x‖ → ∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v)
    (hDEC : ∀ x, S < ‖x‖ → spatialDEC (sourceSpatial A) (sourceSpatial B) x)
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (hgDEC : PhysicalDEC I3 g.inner K)
    (hgcomplete : CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric)
    (f : N → E) {U : Set N} (hU : IsOpen U)
    (hf : ContMDiffOn I3 𝓘(ℝ,E) ∞ f U)
    (hclosed : ∀ r, S < r → IsClosed {x : N | x ∈ U ∧ r ≤ ‖f x‖})
    (finv : E → N)
    (hi : ContMDiffOn 𝓘(ℝ,E) I3 ∞ finv {y | S < ‖y‖})
    (hleft : ∀ x ∈ U, finv (f x) = x)
    (hright : ∀ y, S < ‖y‖ → finv y ∈ U ∧ f (finv y) = y)
    (hcompact : ∀ r, S < r → IsCompact {x : N | x ∉ U ∨ ‖f x‖ ≤ r})
    (hsource : ∀ x ∈ U, g.inner x = endInner I3 f (sourceSpatial A) x ∧
      K x = endInner I3 f (sourceSpatial B) x)
    {C : Set N} (hC : IsCompact C) :
    let e := (bondiCharge M).1
    let p := (bondiCharge M).2
    let H := hyperbolicHomeomorph e p ht
    let f' := H.symm ∘ f
    let inv' := finv ∘ H
    ∃ (T R₀ : ℝ) (ε : ℝ → ℝ) (G k : ℝ → SpatialTensor),
      0 < T ∧ T < R₀ ∧ 12 ≤ R₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      let V := {x : N | x ∈ U ∧ T < ‖f' x‖}
      IsOpen V ∧ ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V ∧
      ContMDiffOn 𝓘(ℝ,E) I3 ∞ inv' {y | T < ‖y‖} ∧
      (∀ x ∈ V, inv' (f' x) = x) ∧
      (∀ y, T < ‖y‖ → inv' y ∈ V ∧ f' (inv' y) = y) ∧
      (∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖}) ∧
      (∀ r, T ≤ r → IsCompact {x : N | x ∉ V ∨ ‖f' x‖ ≤ r}) ∧
      ∀ R ≥ R₀, (0 ≤ ε R ∧ ε R < 1) ∧
        ∃ (g' : SmoothMetric I3 (M := N)) (K' : InnerField I3 (M := N)),
          ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K') ∧
          (∀ x v w, K' x v w = K' x w v) ∧
          PhysicalDEC I3 g'.inner K' ∧
          CKSReplacementCompleteness.IsComplete I3 g'.toContinuousRiemannianMetric ∧
          (∀ x ∈ C, g'.inner x = g.inner x ∧ K' x = K x) ∧
          (∀ x, x ∉ V ∨ ‖f' x‖ ≤ R → g'.inner x = g.inner x ∧ K' x = K x) ∧
          CKSReplacementCompleteness.MetricLower I3 g.toContinuousRiemannianMetric g'.toContinuousRiemannianMetric (ε R) ∧
          ENNReal.ofReal (1-ε R)*minEnclosingArea N g.toContinuousRiemannianMetric ≤
            minEnclosingArea N g'.toContinuousRiemannianMetric ∧
          (∀ x, x ∈ U ∧ T < ‖f' x‖ →
            g'.inner x = endInner I3 f' (G R) x ∧ K' x = endInner I3 f' (k R) x) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → k R x = 0) ∧
          (∀ i j : Fin 3, Symbol 1 (fun x => spatialCartesian (G R) x i j - (if i=j then 1 else 0))) ∧
          Tendsto (spatialADMEnergy (G R)) atTop (𝓝 (mass e p + paddingCharge R)) ∧
          Tendsto (spatialADMMomentum (G R) (k R)) atTop (𝓝 0) ∧
          0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R ∧
          (∀ s : ℝ, T < s →
            IntegrableOn (spatialEnergy (G R) (k R)) (CKSTailVolume.tailRegion s) (spatialVolume (G R)) ∧
            IntegrableOn (fun x => Real.sqrt (CKSLocalBending.momentumSq
              (CKSAngularGeometry.physicalMetricJet (spatialCoefficients (G R)) (CKSCartesianOuter.toPoint x))
              (CKSAngularGeometry.physicalTensorJet (spatialCoefficients (k R)) (CKSCartesianOuter.toPoint x))))
              (CKSTailVolume.tailRegion s) (spatialVolume (G R))) ∧
          (∀ x : E, 2*R^2 < ‖x‖ → spatialMomentum (G R) (k R) x = 0) ∧
          CKSIntrinsicConstraints.IntegrableConstraints g' K' ∧
          ENNReal.ofReal (1-ε R) * CKSFullCutArea.minEnclosingArea g ≤
            CKSFullCutArea.minEnclosingArea g' ∧
          ∀ D : OuterDomain N,
            CKSFullCutArea.area g D < ⊤ ∧ CKSFullCutArea.area g' D < ⊤ ∧
            ENNReal.ofReal (1-ε R) * CKSFullCutArea.area g D ≤ CKSFullCutArea.area g' D := by
  classical
  dsimp only
  let e := (bondiCharge M).1
  let p := (bondiCharge M).2
  let H := hyperbolicHomeomorph e p ht
  let f' := H.symm ∘ f
  let A' := sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) A)
  let B' := sourceSpatial (spatialTensorPullback (hyperbolicMap e (mass e p) p) B)
  obtain ⟨T₀,Q,ε,G,k,hT₀,hTQ,hQ,hε,hfar,hend⟩ :=
    original_CKS_end_integrable_replacement hM ht A B old hold hrep hreal hS hAs hBs hA hB hpos hDEC
  obtain ⟨T,hT,hT₀T,hVo,hfsV,hiV,hleftV,hrightV,hVclosed,hVcompact⟩ :=
    boosted_exterior_coordinates ht f finv hU hf hi hleft hright hclosed hcompact T₀
  let V : Set N := {x | x ∈ U ∧ T < ‖f' x‖}
  have hVopen : IsOpen V := hVo
  have hVc : ∀ r, T < r → IsClosed {x : N | x ∈ V ∧ r ≤ ‖f' x‖} := hVclosed
  have hfs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ H.symm :=
    (hyperbolicMap_smooth e (mass e p) (-p)).contMDiff
  have hf' : ContMDiffOn I3 𝓘(ℝ,E) ∞ f' V :=
    (hfs.comp_contMDiffOn hf).mono (fun x hx => hx.1)
  have hVtail : ∀ x ∈ V, T < ‖f' x‖ := fun x hx => hx.2
  have hsame : ∀ x ∈ V, g.inner x = endInner I3 f' A' x ∧ K x = endInner I3 f' B' x := by
    intro x hx
    have hsx := hf.contMDiffAt (hU.mem_nhds hx.1)
    exact ⟨(hsource x hx.1).1.trans (endInner_balanced ht f A hsx).symm,
      (hsource x hx.1).2.trans (endInner_balanced ht f B hsx).symm⟩
  obtain ⟨D,hD,hDC⟩ := compact_side_eventually f' hVc hC
  let R₀ := max Q (max (T+1) D)
  have hQR : Q ≤ R₀ := le_max_left _ _
  have hTR : T < R₀ := lt_of_lt_of_le (by linarith : T < T+1)
    ((le_max_left _ _).trans (le_max_right _ _))
  have hDR : D ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T,R₀,ε,G,k,hT,hTR,hQ.trans hQR,hε,hVopen,hfsV,hiV,hleftV,hrightV,hVc,hVcompact,?_⟩
  intro R hR
  obtain ⟨heps,hGs,hks,hgeom,holdR,hzero,hAF,hE,hP,hpad0,hpad1,hint,hmom⟩ := hend R (hQR.trans hR)
  have hGs' := hGs.mono (fun x hx => hT₀T.trans_lt hx)
  have hks' := hks.mono (fun x hx => hT₀T.trans_lt hx)
  have hgeom' (x : E) (hx : T < ‖x‖) := hgeom x (hT₀T.trans_lt hx)
  obtain ⟨g',K',hK',hKsym',hnew,hold',hlower,hcomplete,harea⟩ :=
    extend_actual_end g K hK hKsym f' hVopen hf' hVtail hVc A' B' (G R) (k R)
      hsame (hTR.trans_le hR) heps.1 hGs' hks'
      (fun x hx => (hgeom' x hx).1)
      (fun x hx => (hgeom' x hx).2.2.1)
      (fun x hx => (hgeom' x hx).2.1)
      holdR (fun x hx => (hgeom' x hx).2.2.2.2)
  have hDECall : PhysicalDEC I3 g'.inner K' :=
    extended_manifold_DEC g g' K K' hgDEC f' hVopen (hTR.trans_le hR) hf' hVtail hVc
      (G R) (k R) hGs' hks'
      (fun x hx => (hgeom' x hx).1)
      (fun x hx => (hgeom' x hx).2.2.1)
      (fun x hx => (hgeom' x hx).2.1)
      (fun x hx => (hgeom' x hx).2.2.2.1) hnew hold'
  have hintglobal : CKSIntrinsicConstraints.IntegrableConstraints g' K' := by
    apply CKSIntrinsicConstraints.physical_normalization
    exact CKSIntrinsicConstraints.global_constraints_from_end g' K' hDECall f' (finv ∘ H)
      (show T < T+1 by linarith) hVopen hf' hiV hleftV hrightV
      (hVcompact (T+1) (by linarith)) (G R) (k R) hGs' hks'
      (fun x hx => ⟨(hgeom' x hx).1,(hgeom' x hx).2.1⟩)
      (fun x hx => (hgeom' x hx).2.2.1) hnew
      (hint (T+1) (hT₀T.trans_lt (by linarith))).1
      (hint (T+1) (hT₀T.trans_lt (by linarith))).2
  have hindarea := CKSFullCutArea.minEnclosingArea_lower g g' (sub_nonneg.mpr heps.2.le) hlower
  have hcutarea (D : OuterDomain N) := CKSFullCutArea.area_lower g g'
    (sub_nonneg.mpr heps.2.le) hlower D
  refine ⟨heps,g',K',hK',hKsym',hDECall,hcomplete heps.2 hgcomplete,?_,
    hold',hlower,harea heps.2,hnew,hzero,hAF,hE,hP,hpad0,hpad1,
    (fun s hs => hint s (hT₀T.trans_lt hs)),hmom,hintglobal,hindarea,
    (fun D => ⟨CKSFullCutArea.area_finite g D,CKSFullCutArea.area_finite g' D,hcutarea D⟩)⟩
  intro x hx
  exact hold' x (hDC R (hDR.trans hR) x hx)
end
end CKSSpatialManifold

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSSpatialManifold.original_CKS_replacement_intrinsic_chart_package.{u_1} := @OAI.CKSSpatialManifold.original_CKS_replacement_intrinsic_chart_package.{u_1}
