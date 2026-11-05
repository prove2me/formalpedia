-- Prove2me | solution 1 for OAI.CKSLorentz.actual_same_end_smooth_replacement
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:57:39.127826+00:00
-- url     : https://prove2.me/submissions/5c1a5c45-d8b0-459a-99e4-8ea17f3b19b5

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid
import Theorems.Thm_OAI_CKSCartesianOuter_cartesian_radicand_positive
import Theorems.Thm_OAI_CKSLorentz_SourceCollarAtlas_replacement_localization

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

end
end CKSCalculus

end









end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma phi_smooth : ContDiffOn ℝ ∞ phi (Ioi 0) := by
  unfold phi
  have hc : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition ((x-6)/6)) := by fun_prop
  exact (contDiffOn_const.sub hc.contDiffOn).add
    (hc.contDiffOn.mul ((contDiffOn_id.inv (fun x hx => ne_of_gt hx)).pow 3))
lemma xi_smooth : ContDiff ℝ ∞ xi := by unfold xi; fun_prop
lemma zeta_smooth : ContDiff ℝ ∞ zeta := by unfold zeta; fun_prop
lemma beta_smooth : ContDiff ℝ ∞ beta := by unfold beta; fun_prop

lemma bendingV_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (bendingV R) (Ioi 0) := by
  unfold bendingV
  have hc : ContDiffOn ℝ ∞ (fun r : ℝ => phi (r/R)) (Ioi 0) :=
    phi_smooth.comp (contDiffOn_id.div_const R) (fun r hr => div_pos hr hR)
  exact (contDiffOn_id.mul hc).mul
    ((xi_smooth.comp (contDiff_id.div_const (R^2))).contDiffOn)
lemma bendingZeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingZeta R) :=
  zeta_smooth.comp (contDiff_id.div_const R)
lemma bendingBeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingBeta R) :=
  beta_smooth.comp (contDiff_id.div_const R)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

lemma hermitian_real_symmetry {n : Type*} {q : Matrix n n ℝ} (h : q.IsHermitian) (i j : n) :
    q j i=q i j := by
  simpa only [conjTranspose_apply,star_trivial] using congrFun (congrFun h i) j

lemma metricBlock_hermitian (a : ℝ) (b : Point) {q : Mat} (hq : q.IsHermitian) :
    (metricBlock a b q).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTranspose_apply,metricBlock,hermitian_real_symmetry hq 0 1]

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma angularLift_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Angle → E} {x : Point} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f (angularProjection x)) :
    ContDiffAt ℝ n (angularLift f) x := hf.comp x angularProjection.contDiff.contDiffAt

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Finset

lemma proj_symm (x : Vec) (i j : Ix) : proj x i j = proj x j i := by
  simp only [proj, eq_comm, mul_comm]

lemma hessTF_symm (x : Vec) (H : Mat) (hH : ∀ i j, H i j = H j i) (i j : Ix) :
    hessTF x H i j = hessTF x H j i := by
  unfold hessTF
  rw [proj_symm x i j]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [proj_symm x i b, proj_symm x a j, hH b a]
  ring

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

lemma rotation_apply (i j : Fin 3) (p : Poly) :
    rotation i j p = X i * pderiv j p - X j * pderiv i p := by
  simp [rotation, smul_eq_mul]

lemma sphereEval_X (i : Fin 3) : sphereEval (X i) = sphereCoordinate i :=
  aeval_X _ _

open MeasureTheory

open scoped Pointwise
def sphereHome (u : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  u.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      u.norm_map])

def rotatedCoordinate (i j : Fin 3) (t : ℝ) (k : Fin 3) : C(Sphere, ℝ) :=
  if k = i then Real.cos t • sphereCoordinate i - Real.sin t • sphereCoordinate j
  else if k = j then Real.sin t • sphereCoordinate i + Real.cos t • sphereCoordinate j
  else sphereCoordinate k

def rotationAction (i j : Fin 3) (t : ℝ) : Poly →ₐ[ℝ] C(Sphere, ℝ) :=
  aeval (rotatedCoordinate i j t)

lemma rotationAction_zero (i j : Fin 3) : rotationAction i j 0 = sphereEval := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [rotationAction, sphereEval, aeval_X, rotatedCoordinate, Real.cos_zero,
    Real.sin_zero, one_smul, zero_smul, sub_zero, zero_add]
  split_ifs with hi hj
  · subst k; rfl
  · subst k; rfl
  · rfl

lemma rotationAction_apply (i j : Fin 3) (hij : i ≠ j) (t : ℝ)
    (p : Poly) (x : Sphere) :
    rotationAction i j t p x = sphereEval p (sphereHome (planeRotation i j hij t) x) := by
  have h : (ContinuousMap.evalAlgHom ℝ ℝ x).comp (rotationAction i j t) =
      (ContinuousMap.evalAlgHom ℝ ℝ (sphereHome (planeRotation i j hij t) x)).comp
        sphereEval := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, ContinuousMap.evalAlgHom_apply, rotationAction,
      aeval_X, sphereEval]
    change rotatedCoordinate i j t k x = (planeRotationMap i j t x.1) k
    rw [planeRotationMap_apply]
    simp only [rotatedCoordinate]
    split_ifs <;> rfl
  exact congrArg (fun f : Poly →ₐ[ℝ] ℝ => f p) h

lemma rotatedCoordinate_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (k : Fin 3) :
    HasDerivAt (fun t => rotatedCoordinate i j t k)
      (sphereEval (rotation i j (X k))) 0 := by
  have hs := (Real.hasDerivAt_sin (0 : ℝ))
  have hc := (Real.hasDerivAt_cos (0 : ℝ))
  by_cases hi : k = i
  · subst k
    convert! (hc.smul_const (sphereCoordinate i)).sub
        (hs.smul_const (sphereCoordinate j)) using 1 <;>
      simp [rotatedCoordinate, rotation_apply, hij, pderiv_X, sphereEval_X]
    rfl
  · by_cases hj : k = j
    · subst k
      convert! (hs.smul_const (sphereCoordinate i)).add
          (hc.smul_const (sphereCoordinate j)) using 1 <;>
        simp [rotatedCoordinate, rotation_apply, hij.symm, pderiv_X, sphereEval_X]
      rfl
    · simpa [rotatedCoordinate, rotation_apply, hi, hj, Ne.symm hi, Ne.symm hj,
        pderiv_X] using hasDerivAt_const (0 : ℝ) (sphereCoordinate k)

lemma rotationAction_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (p : Poly) :
    HasDerivAt (fun t => rotationAction i j t p) (sphereEval (rotation i j p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [rotationAction, rotation_apply] using
      hasDerivAt_const (0 : ℝ) (algebraMap ℝ C(Sphere, ℝ) a)
  | add p q hp hq =>
    convert! hp.add hq using 1 <;> simp only [map_add]
    rfl
  | mul_X p k hp =>
    have hk : HasDerivAt (fun t => rotationAction i j t (X k))
        (sphereEval (rotation i j (X k))) 0 :=
      by simpa only [rotationAction, aeval_X] using
        rotatedCoordinate_hasDerivAt_zero i j hij k
    convert! hp.mul hk using 1
    · funext t; exact map_mul (rotationAction i j t) p (X k)
    · rw [Derivation.leibniz, map_add]
      simp only [smul_eq_mul, map_mul, rotationAction_zero]
      ring

open scoped Manifold ContDiff Topology
open Set

lemma rotationGenerator_apply (i j k : Fin 3) (x : Ambient) :
    rotationGenerator i j x k = (if k = j then x i else 0) - (if k = i then x j else 0) := rfl

attribute [local instance] cksLocalInst_1853

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

def polynomialExtension (p : Poly) (x : Ambient) : ℝ := aeval (fun i => x i) p

lemma polynomialExtension_smooth (p : Poly) : ContDiff ℝ ∞ (polynomialExtension p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    convert! (contDiff_const : ContDiff ℝ ∞ (fun _ : Ambient => a)) using 1
    funext x; simp [polynomialExtension]
  | add p q hp hq =>
    convert! hp.add hq using 1
    funext x; exact map_add (aeval (fun i => x i)) p q
  | mul_X p k hp =>
    convert! hp.mul (EuclideanSpace.proj k).contDiff using 1
    funext x; simp [polynomialExtension]

lemma polynomialExtension_on_sphere (p : Poly) (x : Sphere) :
    polynomialExtension p x = sphereEval p x := by
  have h : aeval (fun i => (x : Ambient) i) =
      (ContinuousMap.evalAlgHom ℝ ℝ x).comp sphereEval := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [sphereEval, sphereCoordinate]
    rfl
  exact congrArg (fun h : Poly →ₐ[ℝ] ℝ => h p) h

lemma radialExtension_pos_smul (f : Sphere → ℝ) (x : Ambient) {a : ℝ} (ha : 0 < a) :
    radialExtension f (a • x) = radialExtension f x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  rw [radialExtension, dite_eq_left (smul_ne_zero ha.ne' hx), radialExtension, dite_eq_left hx]
  congr 1
  apply Subtype.ext
  simp only [normalizeSphere, norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_inv_rev,
    smul_smul]
  congr 1
  field_simp

lemma radialExtension_isometry (f : Sphere → ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (x : Ambient) (hx : x ≠ 0) :
    radialExtension f (e x) = f (sphereHome e (normalizeSphere ⟨x, hx⟩)) := by
  rw [radialExtension, dite_eq_left (by simpa using e.injective.ne hx)]
  congr 1
  apply Subtype.ext
  simp [normalizeSphere, sphereHome]

lemma polynomial_sphere_smooth (p : Poly) : SmoothSphere (sphereEval p) := by
  have h := (polynomialExtension_smooth p).contMDiff.comp (contMDiff_coe_sphere (n := 2))
  convert! h using 1
  funext x
  exact (polynomialExtension_on_sphere p x).symm

lemma radialExtension_fderiv_self {f : Sphere → ℝ} (hf : SmoothSphere f)
    {x : Ambient} (hx : x ≠ 0) : fderiv ℝ (radialExtension f) x x = 0 := by
  have hd := ((radialExtension_smooth hf).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension f) (fderiv ℝ (radialExtension f) x) ((1 : ℝ) • x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have he : (fun s : ℝ => radialExtension f (s • x)) =ᶠ[nhds 1]
      (fun _ => radialExtension f x) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact radialExtension_pos_smul f x hs
  have h2 := (hasDerivAt_const (1 : ℝ) (radialExtension f x)).congr_of_eventuallyEq he
  simpa using h1.unique h2

lemma smoothRotation_radial_polynomial (p : Poly) (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j (radialExtension (sphereEval p)) x =
      radialExtension (sphereEval (rotation i j p)) x := by
  by_cases hij : i = j
  · subst j
    have hg : rotationGenerator i i x = 0 := by ext k; simp [rotationGenerator_apply]
    simp [smoothRotation, hg, rotation_apply, radialExtension]
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension (sphereEval p))
      (fderiv ℝ (radialExtension (sphereEval p)) x) (planeRotation i j hij 0 x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) (planeRotation_hasDerivAt i j hij x 0)
  let y : Sphere := normalizeSphere ⟨x, hx⟩
  have h2 := (ContinuousMap.evalCLM (R := ℝ) y).hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he : (fun t => radialExtension (sphereEval p) (planeRotation i j hij t x)) =
      fun t => rotationAction i j t p y := by
    funext t
    rw [rotationAction_apply i j hij]
    exact radialExtension_isometry _ _ _ hx
  change HasDerivAt (fun s => radialExtension (sphereEval p) (planeRotation i j hij s x)) _ 0 at h1
  rw [he] at h1
  have h := h1.unique h2
  simpa [smoothRotation, radialExtension, hx, y] using h

lemma rotationGenerator_decomposition (x v : Ambient) :
    ‖x‖ ^ 2 • v = (∑ i : Fin 3, ∑ j : Fin 3, (x i * v j) • rotationGenerator i j x) +
      (∑ i : Fin 3, x i * v i) • x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Fin.sum_univ_three, rotationGenerator_apply] <;> ring

lemma radial_polynomial_fderiv (p : Poly) {x : Ambient} (hx : x ≠ 0) (v : Ambient) :
    fderiv ℝ (radialExtension (sphereEval p)) x v =
      ∑ i : Fin 3, ∑ j : Fin 3, (x i * v j / ‖x‖ ^ 2) *
        radialExtension (sphereEval (rotation i j p)) x := by
  have h := congrArg (fderiv ℝ (radialExtension (sphereEval p)) x)
    (rotationGenerator_decomposition x v)
  simp only [map_add, map_sum, map_smul, radialExtension_fderiv_self (polynomial_sphere_smooth p) hx,
    smul_eq_mul] at h
  have hrot (i j : Fin 3) : fderiv ℝ (radialExtension (sphereEval p)) x (rotationGenerator i j x) =
      radialExtension (sphereEval (rotation i j p)) x := smoothRotation_radial_polynomial p i j hx
  simp only [hrot] at h
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).mpr
  simpa [mul_comm, mul_zero] using h

end
end CKSSphericalHarmonics

end

noncomputable section
namespace CKSSpectralHeat
noncomputable section
open Set Filter Real
open scoped Topology ContDiff

lemma eigenvalue_ge_six (n : ℕ) : 6 ≤ eigenvalue n := by
  unfold eigenvalue
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith
lemma eigenvalue_pos (n : ℕ) : 0 < eigenvalue n := by linarith [eigenvalue_ge_six n]

lemma kernel_smooth : ContDiff ℝ ∞ kernel := by unfold kernel; fun_prop

lemma kernel_nonneg_time {t : ℝ} (ht : 0 ≤ t) : kernel t = exp (-t) := by
  simp [kernel, smoothTransition.one_of_one_le (show 1 ≤ t + 1 by linarith)]

lemma kernel_zero {t : ℝ} (ht : t ≤ -1) : kernel t = 0 := by
  simp [kernel, smoothTransition.zero_of_nonpos (show t + 1 ≤ 0 by linarith)]

lemma kernel_derivative_bounded (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, ‖iteratedDeriv b kernel t‖ ≤ C := by
  have hc : Continuous (iteratedDeriv b kernel) :=
    kernel_smooth.continuous_iteratedDeriv b (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro t
  by_cases htlo : t < -2
  · have heq : kernel =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds (show t < -1 by linarith)] with x hx
      exact kernel_zero hx.le
    rw [heq.iteratedDeriv_eq b]
    simp [le_trans zero_le_one (le_max_right C 1)]
  by_cases hthi : 1 < t
  · have heq : kernel =ᶠ[𝓝 t] (fun x => exp (-1 * x)) := by
      filter_upwards [Ioi_mem_nhds (show 0 < t by linarith)] with x hx
      simpa using kernel_nonneg_time hx.le
    rw [heq.iteratedDeriv_eq b, iteratedDeriv_exp_const_mul]
    have he : exp (-t) ≤ 1 := exp_le_one_iff.2 (by linarith)
    calc
      ‖(-1 : ℝ) ^ b * exp (-1 * t)‖ = exp (-t) := by
        rw [norm_mul, norm_pow]
        simp [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      _ ≤ 1 := he
      _ ≤ max C 1 := le_max_right _ _
  · exact (hC t ⟨not_lt.mp htlo, not_lt.mp hthi⟩).trans (le_max_left _ _)

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def Rapid (coeff : ℕ → B) : Prop :=
  ∀ b : ℕ, Summable (fun n => eigenvalue n ^ b * ‖coeff n‖)

def inverseCoeff (coeff : ℕ → B) (n : ℕ) : B :=
  (1 - eigenvalue n / 2)⁻¹ • coeff n

lemma inverse_denominator_bound (n : ℕ) : |(1 - eigenvalue n / 2)⁻¹| ≤ 1 / 2 := by
  have he := eigenvalue_ge_six n
  have hd : 2 ≤ |1 - eigenvalue n / 2| := by
    rw [abs_of_neg (by linarith)]
    linarith
  rw [abs_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd

omit [CompleteSpace B] in
lemma inverseCoeff_rapid [CompleteSpace B] (coeff : ℕ → B) (h : Rapid coeff) : Rapid (inverseCoeff coeff) := by
  intro b
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (eigenvalue_pos n).le _) (norm_nonneg _))
    _ ((h b).mul_left (1 / 2))
  intro n
  rw [inverseCoeff, norm_smul, Real.norm_eq_abs]
  calc
    eigenvalue n ^ b * (|(1 - eigenvalue n / 2)⁻¹| * ‖coeff n‖) ≤
      eigenvalue n ^ b * ((1 / 2) * ‖coeff n‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (inverse_denominator_bound n) (norm_nonneg _))
          (pow_nonneg (eigenvalue_pos n).le _)
    _ = (1 / 2) * (eigenvalue n ^ b * ‖coeff n‖) := by ring

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

end
end CKSSpectralHeat

end

end OAI
end

section
namespace OAI


noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

lemma U_open : IsOpen U := isClosed_singleton.isOpen_compl

attribute [local instance] CKSLorentz.two_atLeastTwo

lemma partial_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : Ix) :
    ContDiffOn ℝ ∞ (pd i F) U :=
  (hF.fderiv_of_isOpen U_open (by simp)).clm_apply contDiffOn_const

lemma partial_partial {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (i j : Ix) :
    pd i (pd j F) x = fderiv ℝ (fderiv ℝ F) x (e i) (e j) := by
  have hd := ((hF.fderiv_of_isOpen (m := ∞) U_open (by simp)).contDiffAt
    (U_open.mem_nhds hx)).differentiableAt (by simp)
  unfold pd
  rw [fderiv_clm_apply hd (differentiableAt_const (e j))]
  simp

lemma partial_comm {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U)
    (i j : Ix) : pd i (pd j F) x = pd j (pd i F) x := by
  rw [partial_partial hF hx, partial_partial hF hx]
  exact ((hF.contDiffAt (U_open.mem_nhds hx)).isSymmSndFDerivAt (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using (ENat.LEInfty.out (m := 2)))).eq _ _

lemma smooth_diff {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ F x := (hF.contDiffAt (U_open.mem_nhds hx)).differentiableAt (by simp)

lemma pd_add {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y + G y) x = pd k F x + pd k G x := by
  simp only [pd, fderiv_fun_add hF hG, add_apply]

lemma pd_mul {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y * G y) x = pd k F x * G x + F x * pd k G x := by
  rw [pd, fderiv_fun_mul hF hG]
  simp only [add_apply, smul_apply, smul_eq_mul, pd]
  ring

lemma coordinate_smooth (i : Ix) : ContDiffOn ℝ ∞ (fun x : E => x i) U :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).contDiff.contDiffOn

lemma proj_smooth (i j : Ix) : ContDiffOn ℝ ∞ (fun x : E => proj (fun a => x a) i j) U :=
  contDiffOn_const.sub ((coordinate_smooth i).mul (coordinate_smooth j))

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma radialExtension_norm_bound (f : C(Sphere, ℝ)) (x : Ambient) :
    ‖radialExtension f x‖ ≤ ‖f‖ := by
  by_cases hx : x ≠ 0
  · rw [radialExtension, dite_eq_left hx]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp [radialExtension, hx]

def angularField (i j : Fin 3) (x : Ambient) : Ambient →L[ℝ] ℝ :=
  (x i / ‖x‖ ^ 2) • EuclideanSpace.proj j

lemma angularField_smooth (i j : Fin 3) : ContDiffOn ℝ ∞ (angularField i j) puncturedSpace := by
  have hn : ContDiffOn ℝ ∞ (fun x : Ambient => ‖x‖) puncturedSpace := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.contDiffOn.div (hn.pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul contDiffOn_const

lemma radial_polynomial_hasFDerivAt (p : Poly) {x : Ambient} (hx : x ≠ 0) :
    HasFDerivAt (radialExtension (sphereEval p))
      (∑ i : Fin 3, ∑ j : Fin 3,
        radialExtension (sphereEval (rotation i j p)) x • angularField i j x) x := by
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  convert! hd.hasFDerivAt using 1
  ext v
  rw [radial_polynomial_fderiv p hx v]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    angularField, EuclideanSpace.proj, PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma temporalJet_hasDerivAt (b n : ℕ) (t : ℝ) :
    HasDerivAt (temporalJet b n) (temporalJet (b + 1) n t) t := by
  have hk := (CKSSpectralHeat.kernel_smooth.differentiable_iteratedDeriv b
    (by exact_mod_cast (ENat.natCast_lt_top b))).differentiableAt (x := CKSSpectralHeat.eigenvalue n * t) |>.hasDerivAt
  have h := (hk.comp t ((hasDerivAt_id t).const_mul (CKSSpectralHeat.eigenvalue n))).const_mul
    (CKSSpectralHeat.eigenvalue n ^ b)
  convert! h using 1
  simp only [temporalJet, iteratedDeriv_succ, pow_succ]
  ring

lemma temporalJet_bound (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t,
    ‖temporalJet b n t‖ ≤ C * CKSSpectralHeat.eigenvalue n ^ b := by
  obtain ⟨C, hC, hb⟩ := CKSSpectralHeat.kernel_derivative_bounded b
  refine ⟨C, hC, fun n t => ?_⟩
  rw [temporalJet, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (CKSSpectralHeat.eigenvalue_pos n)]
  nlinarith [mul_le_mul_of_nonneg_left (hb (CKSSpectralHeat.eigenvalue n * t))
    (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le b)]

def heatDomain : Set SpaceTime := {z | z.2 ≠ 0}

lemma heatDomain_open : IsOpen heatDomain :=
  isOpen_ne_fun continuous_snd continuous_const

def heatField : Option (Fin 3 × Fin 3) → SpaceTime → SpaceTime →L[ℝ] ℝ
  | none, _ => ContinuousLinearMap.fst ℝ ℝ Ambient
  | some ij, z => (angularField ij.1 ij.2 z.2).comp (ContinuousLinearMap.snd ℝ ℝ Ambient)

lemma heatField_smooth (o : Option (Fin 3 × Fin 3)) : ContDiffOn ℝ ∞ (heatField o) heatDomain := by
  cases o with
  | none => exact contDiffOn_const
  | some ij =>
    exact ((angularField_smooth ij.1 ij.2).comp contDiffOn_snd
      (fun z hz => hz)).clm_comp contDiffOn_const

def heatNext (a : HeatJet) : Option (Fin 3 × Fin 3) → HeatJet
  | none => (a.1 + 1, a.2)
  | some ij => (a.1, ij :: a.2)

lemma heatTerm_derivative_identity (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime) :
    (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) =
    temporalJet a.1 n z.1 •
      ((∑ i : Fin 3, ∑ j : Fin 3,
        radialExtension (sphereEval (rotation i j (rotationWord a.2 (p n)))) z.2 •
          angularField i j z.2).comp (ContinuousLinearMap.snd ℝ ℝ Ambient)) +
    radialExtension (sphereEval (rotationWord a.2 (p n))) z.2 •
      ((ContinuousLinearMap.toSpanSingleton ℝ (temporalJet (a.1 + 1) n z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ Ambient)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [Fintype.sum_option, Fintype.sum_prod_type, heatTerm, heatNext, heatField,
    rotationWord, sum_apply, smul_apply,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  exact add_comm _ _

lemma heatTerm_hasFDerivAt (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime)
    (hz : z ∈ heatDomain) :
    HasFDerivAt (heatTerm p a n)
      (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) z := by
  have ht := (temporalJet_hasDerivAt a.1 n z.1).hasFDerivAt.comp z
    (ContinuousLinearMap.fst ℝ ℝ Ambient).hasFDerivAt
  have hx := (radial_polynomial_hasFDerivAt (rotationWord a.2 (p n)) hz).comp z
    (ContinuousLinearMap.snd ℝ ℝ Ambient).hasFDerivAt
  rw [heatTerm_derivative_identity]
  convert! ht.mul hx using 1

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSDifferentialSeries
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
variable {s : Set E} (hs : IsOpen s)
variable (A : J → E → E →L[ℝ] ℝ) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) s)
variable (next : I → J → I) (F : I → ℕ → E → ℝ)
variable (hF : ∀ i n x, x ∈ s → HasFDerivAt (F i n)
  (∑ j, F (next i j) n x • A j x) x)
variable (bound : ∀ i, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n x, x ∈ s → ‖F i n x‖ ≤ u n)

def series (i : I) (x : E) : ℝ := ∑' n, F i n x

include bound

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma series_summable [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : I) {x : E} (hx : x ∈ s) : Summable (fun n => F i n x) := by
  obtain ⟨u, hu, hb⟩ := bound i
  exact Summable.of_norm_bounded hu (fun n => hb n x hx)

include hF

lemma series_continuous (i : I) : ContinuousOn (series F i) s := by
  obtain ⟨u, hu, hb⟩ := bound i
  exact continuousOn_tsum (fun n x hx => (hF i n x hx).continuousAt.continuousWithinAt) hu hb

include hs hA

lemma series_hasFDerivAt (i : I) {x : E} (hx : x ∈ s) :
    HasFDerivAt (series F i) (∑ j, series F (next i j) x • A j x) x := by
  have bounds := bound
  choose u hu hb using bounds
  let K : ℝ := (∑ j, ‖A j x‖) + 1
  have hc : ContinuousAt (fun y => ∑ j, ‖A j y‖) x := by
    exact (continuousOn_finsetSum _ (fun j _ =>
      (hA j).continuousOn.norm)).continuousAt (hs.mem_nhds hx)
  have he : ∀ᶠ y in 𝓝 x, (∑ j, ‖A j y‖) < K :=
    hc.eventually_lt continuousAt_const (by dsimp [K]; linarith)
  have hn : {y | y ∈ s ∧ (∑ j, ‖A j y‖) < K} ∈ 𝓝 x :=
    inter_mem (hs.mem_nhds hx) he
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hn
  have hlocal (j : J) (y : E) (hy : y ∈ Metric.ball x r) : ‖A j y‖ ≤ K := by
    exact (Finset.single_le_sum (fun k _ => norm_nonneg (A k y))
      (Finset.mem_univ j)).trans (hrs hy).2.le
  have hus : Summable (fun n => K * ∑ j, u (next i j) n) :=
    (summable_sum (fun j _ => hu (next i j))).mul_left K
  have hderiv := hasFDerivAt_tsum_of_isPreconnected hus Metric.isOpen_ball
    (convex_ball x r).isPreconnected
    (fun n y hy => hF i n y (hrs hy).1)
    (fun n y hy => (show ‖∑ j, F (next i j) n y • A j y‖ ≤ K * ∑ j, u (next i j) n from by
      calc
        ‖∑ j, F (next i j) n y • A j y‖ ≤ ∑ j, ‖F (next i j) n y • A j y‖ := norm_sum_le _ _
        _ ≤ ∑ j, u (next i j) n * K := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul]
          exact mul_le_mul (hb _ n y (hrs hy).1) (hlocal j y hy) (norm_nonneg _)
            ((norm_nonneg _).trans (hb _ n y (hrs hy).1))
        _ = K * ∑ j, u (next i j) n := by rw [← Finset.sum_mul]; ring))
    (Metric.mem_ball_self hr) (series_summable F bound i hx) (Metric.mem_ball_self hr)
  convert! hderiv using 1
  symm
  rw [Summable.tsum_finsetSum (fun j _ => (series_summable F bound (next i j) hx).smul_const (A j x))]
  apply Finset.sum_congr rfl
  intro j hj
  exact (series_summable F bound (next i j) hx).tsum_smul_const (A j x)

theorem series_contDiff (i : I) : ContDiffOn ℝ ∞ (series F i) s := by
  apply contDiffOn_infty.mpr
  intro N
  induction N generalizing i with
  | zero => exact contDiffOn_zero.mpr (series_continuous A next F hF bound i)
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn).mpr
    refine ⟨by simp, ⟨fun x => ∑ j, series F (next i j) x • A j x, ?_, ?_⟩⟩
    · exact ContDiffOn.sum (fun j _ => (ih (next i j)).smul ((hA j).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤))))
    · intro x hx
      exact (series_hasFDerivAt hs A hA next F hF bound i hx).hasFDerivWithinAt

end
end CKSDifferentialSeries

end

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

lemma heatTerm_bound (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n z, z ∈ heatDomain → ‖heatTerm p a n z‖ ≤ u n := by
  obtain ⟨C, hC, hb⟩ := temporalJet_bound a.1
  refine ⟨fun n => C * (CKSSpectralHeat.eigenvalue n ^ a.1 *
    ‖sphereEval (rotationWord a.2 (p n))‖), (hp a.2 a.1).mul_left C, ?_⟩
  intro n z hz
  dsimp only
  rw [heatTerm, norm_mul, ← mul_assoc]
  exact mul_le_mul (hb n z.1) (radialExtension_norm_bound _ _) (norm_nonneg _)
    (mul_nonneg hC (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le _))

theorem jointHeatSeries_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ContDiffOn ℝ ∞ (jointHeatSeries p a) heatDomain :=
  CKSDifferentialSeries.series_contDiff heatDomain_open heatField heatField_smooth
    heatNext (heatTerm p) (heatTerm_hasFDerivAt p) (heatTerm_bound p hp) a

lemma jointHeatSeries_hasFDerivAt (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {z : SpaceTime} (hz : z ∈ heatDomain) :
    HasFDerivAt (jointHeatSeries p a)
      (∑ o : Option (Fin 3 × Fin 3), jointHeatSeries p (heatNext a o) z • heatField o z) z :=
  CKSDifferentialSeries.series_hasFDerivAt heatDomain_open heatField heatField_smooth
    heatNext (heatTerm p) (heatTerm_hasFDerivAt p) (heatTerm_bound p hp) a hz

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma positive_uIcc {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : uIcc a r ⊆ Ioi 0 := by
  intro s hs
  exact lt_of_lt_of_le (lt_min ha hr) hs.1

lemma positive_interval_integrable {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IntervalIntegrable q volume a r :=
  (hq.mono (positive_uIcc ha hr)).intervalIntegrable

lemma primitive_hasDerivAt {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : HasDerivAt (primitive a q) (q r) r := by
  exact intervalIntegral.integral_hasDerivAt_right (positive_interval_integrable hq ha hr)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hq r hr)
    (hq.continuousAt (isOpen_Ioi.mem_nhds hr))

lemma primitive_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    {a : ℝ} (ha : 0 < a) : ContDiffOn ℝ ∞ (primitive a q) (Ioi 0) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  constructor
  · intro r hr
    exact (primitive_hasDerivAt hq.continuousOn ha hr).differentiableAt.differentiableWithinAt
  · exact hq.congr (fun r hr => (primitive_hasDerivAt hq.continuousOn ha hr).deriv)

lemma paddingDensity_smooth : ContDiffOn ℝ ∞ paddingDensity (Ioi 0) := by
  exact contDiffOn_const.div (contDiffOn_id.mul (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)))
    (fun r hr => mul_ne_zero (ne_of_gt hr) (Real.sqrt_ne_zero'.mpr hr))

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma spatialHeat_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) (t : ℝ) :
    ContDiffOn ℝ ∞ (spatialHeat p a t) puncturedSpace :=
  (jointHeatSeries_smooth p hp a).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma paddingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (paddingWeight R) := by
  unfold paddingWeight
  fun_prop

lemma paddingIntegrand_smooth (R : ℝ) :
    ContDiffOn ℝ ∞ (fun r => paddingWeight R r * paddingDensity r) (Ioi 0) :=
  (paddingWeight_smooth R).contDiffOn.mul paddingDensity_smooth
lemma paddingMass_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (paddingMass R) (Ioi 0) :=
  primitive_smooth (paddingIntegrand_smooth R) hR

lemma heatDensity_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatDensity R) (Ioi 0) := by
  unfold heatDensity
  exact (bendingZeta_smooth R).contDiffOn.div
    ((contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.add ((bendingV_smooth hR).pow 2)))
    (fun r hr => ne_of_gt (mul_pos (mul_pos (by norm_num) hr) (by positivity)))

lemma heatTime_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatTime R) (Ioi 0) :=
  primitive_smooth (heatDensity_smooth hR) (by positivity)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics

inductive HeatGenerated (p : ℕ → Poly) : (ℝ → E → ℝ) → Prop
  | basic (a : HeatJet) : HeatGenerated p (spatialHeat p a)
  | zero : HeatGenerated p (fun _ _ => 0)
  | add {F G} : HeatGenerated p F → HeatGenerated p G →
      HeatGenerated p (fun t x => F t x + G t x)
  | coeff (c : E → ℝ) {F} : ContDiffOn ℝ ∞ c U → HeatGenerated p F →
      HeatGenerated p (fun t x => c x * F t x)
  | congr {F G} : HeatGenerated p F → (∀ t x, x ∈ U → F t x = G t x) →
      HeatGenerated p G

variable {p : ℕ → Poly} (hp : PolynomialRapid p)
include hp

lemma HeatGenerated.joint_smooth {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain := by
  induction hF with
  | basic a => exact jointHeatSeries_smooth p hp a
  | zero => exact contDiffOn_const
  | add _ _ hF hG => exact hF.add hG
  | coeff c hc _ hF =>
    exact (hc.comp contDiffOn_snd (fun z hz => hz)).mul hF
  | congr _ he hF =>
    exact hF.congr (fun z hz => (he z.1 z.2 hz).symm)

lemma HeatGenerated.spatial_smooth {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (t : ℝ) :
    ContDiffOn ℝ ∞ (F t) U :=
  (hF.joint_smooth hp).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

omit hp in
lemma HeatGenerated.sum {J : Type*} (s : Finset J) {F : J → ℝ → E → ℝ}
    (h : ∀ j ∈ s, HeatGenerated p (F j)) :
    HeatGenerated p (fun t x => ∑ j ∈ s, F j t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (HeatGenerated.zero (p := p))
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (mem_insert_self j s)).add (ih (fun k hk => h k (mem_insert_of_mem hk)))

omit hp in
lemma angularCoefficient_smooth (i : Ix) :
    ContDiffOn ℝ ∞ (fun x : E => x i / ‖x‖ ^ 2) U := by
  have hn : ContDiffOn ℝ ∞ (fun x : E => ‖x‖) U := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  exact (coordinate_smooth i).div (hn.pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

lemma pd_spatialHeat (a : HeatJet) (t : ℝ) {x : E} (hx : x ∈ U) (j : Ix) :
    pd j (spatialHeat p a t) x =
      ∑ i : Ix, (x i / ‖x‖ ^ 2) * spatialHeat p (a.1, (i,j) :: a.2) t x := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (spatialHeat p a t) _ x at hd
  rw [pd, hd.fderiv]
  change (∑ o, jointHeatSeries p (heatNext a o) (t,x) • heatField o (t,x)) (0, e j) = _
  simp only [Fintype.sum_option, add_apply,
    _root_.sum_apply, smul_apply, heatField,
    angularField, ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero, zero_add,
    Fintype.sum_prod_type, EuclideanSpace.proj, PiLp.proj_apply, e_apply, heatNext]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply sum_congr rfl
  intro i hi
  exact mul_comm _ _

lemma HeatGenerated.partial {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (j : Ix) :
    HeatGenerated p (fun t x => pd j (F t) x) := by
  induction hF with
  | basic a =>
    apply HeatGenerated.congr (HeatGenerated.sum univ (fun i _ =>
      HeatGenerated.coeff _ (angularCoefficient_smooth i) (HeatGenerated.basic (a.1,(i,j)::a.2))))
    intro t x hx
    exact (pd_spatialHeat hp a t hx j).symm
  | zero => simpa only [pd_const] using (HeatGenerated.zero (p := p))
  | @add F G hF hG ihF ihG =>
    apply HeatGenerated.congr (ihF.add ihG)
    intro t x hx
    exact (pd_add (smooth_diff (hF.spatial_smooth hp t) hx)
      (smooth_diff (hG.spatial_smooth hp t) hx) j).symm
  | @coeff c F hc hF ih =>
    apply HeatGenerated.congr ((HeatGenerated.coeff _ (partial_smooth hc j) hF).add
      (HeatGenerated.coeff _ hc ih))
    intro t x hx
    exact (pd_mul (smooth_diff hc hx) (smooth_diff (hF.spatial_smooth hp t) hx) j).symm
  | @congr F G hF he ih =>
    apply HeatGenerated.congr ih
    intro t x hx
    have he' : F t =ᶠ[𝓝 x] G t := by
      filter_upwards [U_open.mem_nhds hx] with y hy
      exact he t y hy
    exact congrArg (fun A : E →L[ℝ] ℝ => A (e j)) he'.fderiv_eq

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma rotationWord_smul (w : List (Fin 3 × Fin 3)) (c : ℝ) (p : Poly) :
    rotationWord w (c • p) = c • rotationWord w p := by
  induction w with
  | nil => rfl
  | cons ij w ih => simp only [rotationWord, ih, Derivation.map_smul]

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
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma inversePolynomials_rapid (p : ℕ → Poly) (hp : PolynomialRapid p) :
    PolynomialRapid (inversePolynomials p) := by
  intro w b
  have h := CKSSpectralHeat.inverseCoeff_rapid (fun n => sphereEval (rotationWord w (p n))) (hp w) b
  simpa only [inversePolynomials, rotationWord_smul, map_smul, CKSSpectralHeat.inverseCoeff] using h

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

lemma HeatGenerated.neg {p : ℕ → Poly} {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    HeatGenerated p (fun t x => -F t x) := by
  simpa only [neg_one_mul] using HeatGenerated.coeff (fun _ => (-1:ℝ)) contDiffOn_const hF

lemma HeatGenerated.sub {p : ℕ → Poly} {F G : ℝ → E → ℝ}
    (hF : HeatGenerated p F) (hG : HeatGenerated p G) :
    HeatGenerated p (fun t x => F t x - G t x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma heatTensor_generated (p : ℕ → Poly) (hp : PolynomialRapid p) (i j : Ix) :
    HeatGenerated (inversePolynomials p) (fun t x => heatTensor p t x i j) := by
  have hi := inversePolynomials_rapid p hp
  have hH (a b : Ix) : HeatGenerated (inversePolynomials p)
      (fun t x => hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b) :=
    ((HeatGenerated.basic (0,[]) (p := inversePolynomials p)).partial hi b).partial hi a
  change HeatGenerated _ (fun t x =>
    (∑ a, ∑ b, proj (fun c => x c) i a * hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b * proj (fun c => x c) b j) -
    (∑ a, ∑ b, proj (fun c => x c) a b * hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b) / 2 * proj (fun c => x c) i j)
  apply HeatGenerated.sub
  · apply HeatGenerated.congr (HeatGenerated.sum univ (fun a _ => HeatGenerated.sum univ (fun b _ =>
      HeatGenerated.coeff _ ((proj_smooth i a).mul (proj_smooth b j)) (hH a b))))
    intro t x hx
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    ring
  · apply HeatGenerated.congr (HeatGenerated.coeff
      (fun x => proj (fun c => x c) i j / 2) ((proj_smooth i j).div_const 2)
      (HeatGenerated.sum univ (fun a _ => HeatGenerated.sum univ (fun b _ =>
        HeatGenerated.coeff _ (proj_smooth a b) (hH a b)))))
    intro t x hx
    ring

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere
open scoped Topology ContDiff

lemma heatTensor_symmetric_U (p : ℕ → Poly) (hp : PolynomialRapid p)
    (t : ℝ) (x : E) (hx : x ∈ U) (i j : Ix) : heatTensor p t x i j = heatTensor p t x j i :=
  hessTF_symm _ _ (fun a b => partial_comm
    (spatialHeat_smooth _ (inversePolynomials_rapid p hp) _ t) hx a b) i j

lemma canonicalF_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalF f₀ m z.1 z.2) heatDomain :=
  contDiffOn_const.add (jointHeatSeries_smooth _ (smoothDatum_rapid f₀ hf₀) (0,[]))
lemma canonicalT_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (i j : Ix) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalT f₀ z.1 z.2 i j) heatDomain :=
  (heatTensor_generated _ (smoothDatum_rapid f₀ hf₀) i j).joint_smooth
    (inversePolynomials_rapid _ (smoothDatum_rapid f₀ hf₀))

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI




noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def hyperbolicMetric (x Y Z : E) : ℝ :=
  inner ℝ Y Z - inner ℝ x Y * inner ℝ x Z / (1+‖x‖^2)

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
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularProjection_slice (r : ℝ) (θ : Angle) : angularProjection (slice r θ)=θ := by
  ext a
  exact slice_succ r θ a

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

lemma sphereRegion_open (P : SmoothAngularPatch) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (P.sphereRegion W) :=
  P.chart.isOpen_inter_preimage hW

lemma param_chart (P : SmoothAngularPatch) {n : Sphere} (hn : n ∈ P.chart.source) :
    P.param (P.chart n)=(n:E) := congrArg Subtype.val (P.chart.left_inv hn)

end SmoothAngularPatch
end
end CKSLorentz

end










noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

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

end SmoothAngularPatch

end
end CKSLorentz

end












noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry
open CKSAngularGeometry (metricBlock AmbientMat)

def cksReference (σ : Angle → Mat) (y : Point) : AmbientMat :=
  metricBlock (1/(1+(y 0)^2)) 0 ((y 0)^2 • σ (angularProjection y))
end
end CKSLorentz

end









































































noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma actualMetricFirstJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : actualMetricFirstJet G x = actualMetricFirstJet H x := by
  funext i j k
  exact D_congr (h.mono (fun y hy => congrArg (fun q : AmbientMat => q j k) hy)) _

lemma coordinateChristoffel_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : coordinateChristoffel G x = coordinateChristoffel H x := by
  unfold coordinateChristoffel
  rw [h.self_of_nhds,actualMetricFirstJet_congr h]

lemma covariantVector_congr {G H : PhysicalPoint → AmbientMat}
    {W V : PhysicalPoint → PhysicalPoint} {x e : PhysicalPoint}
    (hG : G =ᶠ[𝓝 x] H) (hW : W =ᶠ[𝓝 x] V) :
    covariantVector G e W x = covariantVector H e V x := by
  funext k
  have hd := D_congr (hW.mono (fun y hy => congrFun hy k)) e
  simp only [covariantVector,hW.self_of_nhds,coordinateChristoffel_congr hG,hd]

lemma frameCoefficient_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    frameCoefficient G E x = frameCoefficient H F x := by
  funext i j k
  unfold frameCoefficient
  rw [hG.self_of_nhds,hE.self_of_nhds i,hE.self_of_nhds k,
    covariantVector_congr hG (hE.mono (fun y hy => hy j))]

lemma actualFrameBracket_congr {E F : LocalFrame} {x : PhysicalPoint}
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameBracket E x = actualFrameBracket F x := by
  funext i j k
  unfold actualFrameBracket
  rw [hE.self_of_nhds i,hE.self_of_nhds j,
    D_congr (hE.mono (fun y hy => congrFun (hy j) k)),
    D_congr (hE.mono (fun y hy => congrFun (hy i) k))]

lemma frameBracketCoefficient_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    frameBracketCoefficient G E x = frameBracketCoefficient H F x := by
  funext i j k
  unfold frameBracketCoefficient
  rw [hG.self_of_nhds,hE.self_of_nhds k,actualFrameBracket_congr hE]

lemma actualFrameCurvature_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameCurvature G E x = actualFrameCurvature H F x := by
  have hc : ∀ᶠ y in 𝓝 x, frameCoefficient G E y=frameCoefficient H F y := by
    filter_upwards [hG.eventually_nhds,hE.eventually_nhds] with y hyG hyE
    exact frameCoefficient_congr hyG hyE
  funext i j k l
  unfold actualFrameCurvature
  rw [hE.self_of_nhds i,hE.self_of_nhds j,
    D_congr (hc.mono (fun y hy => congrArg (fun q => q j k l) hy)),
    D_congr (hc.mono (fun y hy => congrArg (fun q => q i k l) hy)),
    hc.self_of_nhds,frameBracketCoefficient_congr hG hE]

lemma actualFrameScalar_congr {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    actualFrameScalar G E x = actualFrameScalar H F x := by
  unfold actualFrameScalar
  rw [actualFrameCurvature_congr hG hE]

lemma coordinateConnectionVector_congr {G H : PhysicalPoint → AmbientMat}
    {x e v : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) :
    coordinateConnectionVector G e v x = coordinateConnectionVector H e v x := by
  unfold coordinateConnectionVector
  rw [coordinateChristoffel_congr hG]

lemma coordinateTensorCovariant_congr {G H K L : PhysicalPoint → AmbientMat}
    {x e v w : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    coordinateTensorCovariant G K e v w x = coordinateTensorCovariant H L e v w x := by
  unfold coordinateTensorCovariant
  have hd (i j) := D_congr (hK.mono (fun y hy => congrArg (fun k : AmbientMat => k i j) hy)) e
  simp only [hK.self_of_nhds,coordinateConnectionVector_congr hG,hd]

lemma coordinateMomentum_congr {G H K L : PhysicalPoint → AmbientMat}
    {x w : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    coordinateMomentum G K x w = coordinateMomentum H L x w := by
  have hc : ∀ i j, coordinateTensorCovariant G K (CKSRealizedRound.basis i)
      (CKSRealizedRound.basis j) w x = coordinateTensorCovariant H L
      (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x :=
    fun _ _ => coordinateTensorCovariant_congr hG hK
  have ht : (fun y => ((G y)⁻¹*K y).trace) =ᶠ[𝓝 x] (fun y => ((H y)⁻¹*L y).trace) := by
    filter_upwards [hG,hK] with y hyG hyK
    rw [hyG,hyK]
  simp only [coordinateMomentum,hG.self_of_nhds,hc,D_congr ht]

lemma momentumCovector_congr {G H K L : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L) :
    momentumCovector G K x = momentumCovector H L x := by
  funext i
  exact coordinateMomentum_congr hG hK

theorem physicalDEC_congr {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame}
    {x : PhysicalPoint} (hG : G =ᶠ[𝓝 x] H) (hK : K =ᶠ[𝓝 x] L)
    (hE : ∀ᶠ y in 𝓝 x, ∀ i, E i y=F i y) :
    physicalDEC G K E x ↔ physicalDEC H L F x := by
  unfold physicalDEC physicalEnergy
  rw [momentumCovector_congr hG hK,actualFrameScalar_congr hG hE,
    hG.self_of_nhds,hK.self_of_nhds]

end
end CKSAngularGeometry

end


















noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma sourceGamma_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceGamma f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mg))).add hf.eg

lemma sourceTangentialK_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceTangentialK f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mK))).add hf.ek

lemma sourceRadialMetric_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceRadialMetric f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact ((contDiffAt_const.div (contDiffAt_const.add (hr.pow 2)) (by positivity)).add
    ((angularLift_diff hf.mr).div (hr.pow 5) (pow_ne_zero _ hy))).add hf.err

lemma sourceRadialK_smoothAt {f : SourceTensorFields} {y : Point} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (sourceRadialK f) y := by
  have hh : ContDiffAt ℝ ∞ (fun z : Point => 1+(z 0)^2) y := by fun_prop
  exact (contDiffAt_const.div hh (by positivity)).add hf.kr

end
end CKSMixedGeometry

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

lemma heatDatum_smooth {M : Sphere → ℝ} (hM : SmoothSphere M) :
    SmoothSphere (heatDatum M hM) := hM.div_const 4

end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

theorem polar_inverse_differentials (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    polarInverse P (polarParam P y) = y ∧
    ContDiffAt ℝ ∞ (polarInverse P) (polarParam P y) ∧
    (fderiv ℝ (polarInverse P) (polarParam P y)).comp (fderiv ℝ (polarParam P) y) =
      ContinuousLinearMap.id ℝ Point ∧
    (fderiv ℝ (polarParam P) y).comp (fderiv ℝ (polarInverse P) (polarParam P y)) =
      ContinuousLinearMap.id ℝ E := by
  refine ⟨polarInverse_param P hr hy,polarInverse_smoothAt_param P hr hy,
    polarInverse_fderiv_left P hr hy,?_⟩
  ext z
  obtain ⟨v,rfl⟩ := polarParam_fderiv_surjective P hr hy z
  have hh := congrArg (fun L : Point →L[ℝ] Point => L v) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hh ⊢
  rw [hh]
end
end CKSLorentz

end




noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators Topology
lemma matrixBilinear_apply (G : Mat) (v w : V) :
    matrixBilinear G v w = ∑ i : Fin 3, ∑ j : Fin 3, G i j * v i * w j := by
  simp [matrixBilinear, mul_assoc]
lemma matrixBilinear_symm {G : Mat} (hG : Matrix.IsHermitian G) (v w : V) :
    matrixBilinear G v w = matrixBilinear G w v := by
  have hs : ∀ i j, G i j = G j i := by
    intro i j
    have h := congrFun (congrFun hG.eq j) i
    change star (G i j) = G j i at h
    simpa only [star_trivial] using h
  simp only [matrixBilinear_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring
lemma matrixBilinear_pos {G : Mat} (hG : Matrix.PosDef G) {v : V} (hv : v ≠ 0) :
    0 < matrixBilinear G v v := by
  have h := hG.dotProduct_mulVec_pos hv
  simpa [matrixBilinear_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using h
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] scalarAtlas

end
end CKSTangentCoefficients

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped BigOperators
lemma bilinear_eq_of_coordinate_basis (B C : Point →L[ℝ] Point →L[ℝ] ℝ)
    (h : ∀ i j, B (basis i) (basis j) = C (basis i) (basis j)) : B = C := by
  ext v w
  rw [← sum_coordinate_basis v,← sum_coordinate_basis w]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,h]
lemma polarLift_components (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (i j : I) :
    polarTensorComponents P (polarLift P F) i j y = F y i j := by
  have hi := congrArg (fun L : Point →L[ℝ] Point => L (basis i)) (polarInverse_fderiv_left P hr hy)
  have hj := congrArg (fun L : Point →L[ℝ] Point => L (basis j)) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hi hj
  change matrixBilinear (F (polarInverse P (polarParam P y)))
    (fderiv ℝ (polarInverse P) (polarParam P y) (fderiv ℝ (polarParam P) y (basis i)))
    (fderiv ℝ (polarInverse P) (polarParam P y) (fderiv ℝ (polarParam P) y (basis j))) = _
  rw [polarInverse_param P hr hy,hi,hj]
  simp [matrixBilinear,basis,Pi.single_apply]
lemma polarTensor_ext (P : SmoothAngularPatch) {A B : SpatialTensor}
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (h : ∀ i j, polarTensorComponents P A i j y = polarTensorComponents P B i j y) :
    A (polarParam P y) = B (polarParam P y) := by
  have hh : (A (polarParam P y)).bilinearComp (fderiv ℝ (polarParam P) y) (fderiv ℝ (polarParam P) y) =
      (B (polarParam P y)).bilinearComp (fderiv ℝ (polarParam P) y) (fderiv ℝ (polarParam P) y) :=
    bilinear_eq_of_coordinate_basis _ _ h
  ext v w
  obtain ⟨v,rfl⟩ := polarParam_fderiv_surjective P hr hy v
  obtain ⟨w,rfl⟩ := polarParam_fderiv_surjective P hr hy w
  exact congrArg (fun L : Point →L[ℝ] Point →L[ℝ] ℝ => L v w) hh

theorem polarLift_reconstruction (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (∀ i j, polarTensorComponents P (polarLift P F) i j y = F y i j) ∧
    (∀ A : SpatialTensor, (∀ i j, polarTensorComponents P A i j y = F y i j) →
      polarLift P F (polarParam P y) = A (polarParam P y)) := by
  refine ⟨polarLift_components P F hr hy,?_⟩
  intro A hA
  apply polarTensor_ext P hr hy
  intro i j
  rw [polarLift_components P F hr hy,hA]
end
end CKSLorentz

end




noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped ContDiff Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.bilNorm
attribute [local instance] OAI.CKSLorentz.bilSpace
attribute [local instance] OAI.CKSLorentz.epNorm
attribute [local instance] OAI.CKSLorentz.epSpace
attribute [local instance] OAI.CKSLorentz.peNorm
attribute [local instance] OAI.CKSLorentz.peSpace
attribute [local instance] OAI.CKSLorentz.eeNorm
attribute [local instance] OAI.CKSLorentz.eeSpace
lemma matrixBilinear_contDiff : ContDiff ℝ ∞ matrixBilinear := by
  unfold matrixBilinear
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((ContinuousLinearMap.proj j : CKSTangentCoefficients.V →L[ℝ] ℝ).contDiff.comp
    (ContinuousLinearMap.proj i : CKSTangentCoefficients.Mat →L[ℝ] CKSTangentCoefficients.V).contDiff).smul contDiff_const
lemma polarLift_smoothAt (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hF : ContDiffAt ℝ ∞ F y) : ContDiffAt ℝ ∞ (polarLift P F) (polarParam P y) := by
  have hi := polarInverse_smoothAt_param P hr hy
  have hFi : ContDiffAt ℝ ∞ F (polarInverse P (polarParam P y)) := by
    rw [polarInverse_param P hr hy]; exact hF
  have hB := matrixBilinear_contDiff.contDiffAt.comp (polarParam P y) (hFi.comp (polarParam P y) hi)
  have hD := hi.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
  have hf1 : ContDiff ℝ ∞ (fun B : E →L[ℝ] Point →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] Point →L[ℝ] ℝ) →L[ℝ] (Point →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E Point ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  have hf2 : ContDiff ℝ ∞ (fun B : E →L[ℝ] E →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  exact hf2.contDiffAt.comp _ ((hf1.contDiffAt.comp _ (hB.clm_comp hD)).clm_comp hD)
lemma polarLift_smooth_positive (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hF : ContDiffAt ℝ ∞ F y) (hp : Matrix.PosDef (F y)) :
    ContDiffAt ℝ ∞ (polarLift P F) (polarParam P y) ∧
    (∀ v w, polarLift P F (polarParam P y) v w = polarLift P F (polarParam P y) w v) ∧
    ∀ v : E, v ≠ 0 → 0 < polarLift P F (polarParam P y) v v := by
  refine ⟨polarLift_smoothAt P F hr hy hF,?_,?_⟩
  · intro v w
    unfold polarLift
    rw [polarInverse_param P hr hy]
    exact matrixBilinear_symm hp.isHermitian _ _
  · intro v hv
    unfold polarLift
    rw [polarInverse_param P hr hy]
    apply matrixBilinear_pos hp
    intro hz
    change fderiv ℝ (polarInverse P) (polarParam P y) v = 0 at hz
    have hh := congrArg (fun L : E →L[ℝ] E => L v) (polar_inverse_differentials P hr hy).2.2.2
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,hz,map_zero] at hh
    exact hv hh.symm
end
end CKSLorentz

end














noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma spatialDirection_val {x : E} (hx : x ≠ 0) : (spatialDirection x : E) = normalizeAmbient x := by
  simp [spatialDirection,hx]
lemma spatialDirection_continuousAt {x : E} (hx : x ≠ 0) : ContinuousAt spatialDirection x := by
  have he : (fun y => (spatialDirection y : E)) =ᶠ[𝓝 x] normalizeAmbient := by
    filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hx] with y hy
    exact spatialDirection_val hy
  have hc : ContinuousAt (fun y => (spatialDirection y : E)) x := (normalizeAmbient_smooth hx).continuousAt.congr_of_eventuallyEq he
  exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hc
lemma spatialDirection_polarParam (P : SmoothAngularPatch) {y : Point} (hr : 0 < y 0) :
    spatialDirection (polarParam P y) = P.chart.symm (angularProjection y) := by
  apply Subtype.ext
  rw [spatialDirection_val (norm_ne_zero_iff.mp (by rw [polarParam_norm P hr.le]; exact hr.ne')),
    normalizeAmbient_polarParam P hr]
  rfl
 theorem polarCone_open (P : SmoothAngularPatch) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (polarCone P W) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.inter_mem
    ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx.1)
    ((spatialDirection_continuousAt hx.1).preimage_mem_nhds ((P.sphereRegion_open hW).mem_nhds hx.2))
lemma polarInverse_direction (P : SmoothAngularPatch) {x : E}
    (hx : x ≠ 0) (hs : spatialDirection x ∈ P.chart.source) :
    polarInverse P x = slice ‖x‖ (P.chart (spatialDirection x)) := by
  unfold polarInverse
  rw [← spatialDirection_val hx,P.extension_eq _ hs]
 theorem polarCone_inverse (P : SmoothAngularPatch) {W : Set Angle} {x : E}
    (hx : x ∈ polarCone P W) :
    0 < (polarInverse P x) 0 ∧ angularProjection (polarInverse P x) ∈ W ∧
    angularProjection (polarInverse P x) ∈ P.chart.target ∧
    polarParam P (polarInverse P x) = x := by
  rw [polarInverse_direction P hx.1 hx.2.1]
  refine ⟨by simpa using norm_pos_iff.mpr hx.1,by
      rw [angularProjection_slice]
      exact hx.2.2,
    by simpa only [angularProjection_slice] using P.chart.map_source hx.2.1,?_⟩
  simp only [polarParam,slice_zero,angularProjection_slice,P.param_chart hx.2.1,
    spatialDirection_val hx.1,normalizeAmbient,smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx.1),one_smul]
 theorem polarCone_param (P : SmoothAngularPatch) {W : Set Angle} {y : Point}
    (hy : angularProjection y ∈ W) (ht : angularProjection y ∈ P.chart.target)
    (hr : 0 < y 0) : polarParam P y ∈ polarCone P W := by
  refine ⟨norm_ne_zero_iff.mp (by rw [polarParam_norm P hr.le]; exact hr.ne'),?_⟩
  rw [spatialDirection_polarParam P hr]
  exact ⟨P.chart.map_target ht,by change P.chart (P.chart.symm (angularProjection y)) ∈ W; rwa [P.chart.right_inv ht]⟩
end
end CKSLorentz

end




noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.globalCollarEeNorm
attribute [local instance] OAI.CKSLorentz.globalCollarEeSpace

lemma polarLift_symmetric (P : SmoothAngularPatch) (F : CKSMixedGeometry.Point → Matrix CKSMixedGeometry.I CKSMixedGeometry.I ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (h : (F y).IsHermitian) : ∀ v w, polarLift P F (polarParam P y) v w = polarLift P F (polarParam P y) w v := by
  intro v w
  unfold polarLift
  rw [polarInverse_param P hr hy]
  exact CKSTangentCoefficients.matrixBilinear_symm h _ _

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Matrix
open CKSAngularGeometry (metricBlock AmbientMat)
lemma cksSourceFields_gamma (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceGamma (cksSourceFields σ A B mr mg mK).base y =
      (y 0)^2 • σ (angularProjection y)+Matrix.of (fun a b : Fin 2 => A a.succ b.succ y) := by
  ext a b
  change (y 0)^2 * σ (angularProjection y) a b + 1/(y 0) * mg a.succ b.succ (angularProjection y) +
    (A a.succ b.succ y - ordinaryLeadingComponent 1 (mg a.succ b.succ) y) = _
  simp only [ordinaryLeadingComponent,pow_one,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply]
  ring
lemma cksSourceFields_tangential (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceTangentialK (cksSourceFields σ A B mr mg mK).base y =
      (y 0)^2 • σ (angularProjection y)+Matrix.of (fun a b : Fin 2 => B a.succ b.succ y) := by
  ext a b
  change (y 0)^2 * σ (angularProjection y) a b + 1/(y 0) * mK a.succ b.succ (angularProjection y) +
    (B a.succ b.succ y - ordinaryLeadingComponent 1 (mK a.succ b.succ) y) = _
  simp only [ordinaryLeadingComponent,pow_one,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply]
  ring
lemma cksSourceFields_radial (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceRadialMetric (cksSourceFields σ A B mr mg mK).base y =
      1/(1+(y 0)^2)+A 0 0 y := by
  simp only [sourceRadialMetric,cksSourceFields,ordinaryLeadingComponent]
  ring
lemma metricBlock_add_perturbation (a : ℝ) (q : Mat) (A : AmbientMat)
    (hA : A.IsHermitian) :
    metricBlock (a+A 0 0) (fun i => A 0 i.succ)
      (q+Matrix.of (fun i k : Fin 2 => A i.succ k.succ)) = metricBlock a 0 q+A := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [metricBlock]
  all_goals exact CKSAngularGeometry.hermitian_real_symmetry hA _ _

theorem cksSourceFields_reconstruct (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point)
    (hA : Matrix.IsHermitian (fun i k => A i k y)) (hB : Matrix.IsHermitian (fun i k => B i k y)) :
    sourceMetric (cksSourceFields σ A B mr mg mK).base y =
      cksReference σ y + Matrix.of (fun i k => A i k y) ∧
    sourceTensor (cksSourceFields σ A B mr mg mK) y =
      cksReference σ y + Matrix.of (fun i k => B i k y) := by
  constructor
  · unfold sourceMetric cksReference
    rw [cksSourceFields_gamma,cksSourceFields_radial]
    exact metricBlock_add_perturbation _ _ _ hA
  · unfold sourceTensor cksReference
    rw [cksSourceFields_tangential]
    exact metricBlock_add_perturbation _ _ _ hB
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
lemma polarParam_fderiv (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (v : Point) :
    fderiv ℝ (polarParam P) y v = v 0 • P.param (angularProjection y) +
      y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) := by
  have hP := (P.param_contDiffAt hy).differentiableAt (by simp)
  have hp := (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).hasFDerivAt (x := y)
  have ha := hP.hasFDerivAt.comp y angularProjection.hasFDerivAt
  have hh := hp.smul ha
  change HasFDerivAt (polarParam P) _ y at hh
  rw [hh.fderiv]
  change y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) + v 0 • P.param (angularProjection y) = _
  exact add_comm _ _
lemma polarParam_fderiv_radial (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    fderiv ℝ (polarParam P) y (basis 0) = P.param (angularProjection y) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis 0) = 0 := by ext a; simp [angularProjection,basis,Fin.succ_ne_zero]
  rw [ha]
  simp [basis]
lemma polarParam_fderiv_angular (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (a : Fin 2) :
    fderiv ℝ (polarParam P) y (basis a.succ) = y 0 • fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis a.succ) = CKSAngularGeometry.basis a := by
    ext b
    simp [angularProjection,basis,CKSAngularGeometry.basis,Pi.single_apply,Fin.succ_inj]
  rw [ha]
  simp [basis,Fin.succ_ne_zero]
lemma hyperbolicField_polar (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (fun i j => polarTensorComponents P hyperbolicField i j y) = cksReference (angularRoundMetric P.param) y := by
  have hn : ‖P.param (angularProjection y)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using P.param_sphere (angularProjection y)
  have hi : inner ℝ (P.param (angularProjection y)) (P.param (angularProjection y)) = 1 := by
    rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have ht := P.param_tangent hy
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis 0))
        (fderiv ℝ (polarParam P) y (basis 0)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy]
      unfold hyperbolicMetric
      rw [polarParam_norm P hr.le]
      simp only [polarParam,real_inner_smul_left,hi,mul_one]
      simp only [cksReference,CKSAngularGeometry.metricBlock]
      change 1 - y 0 * y 0/(1+(y 0)^2) = 1/(1+(y 0)^2)
      have hnz : 1 + (y 0)^2 ≠ 0 := by positivity
      field_simp
      ring
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis 0))
        (fderiv ℝ (polarParam P) y (basis b.succ)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      fin_cases b <;> simp [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,ht,cksReference,CKSAngularGeometry.metricBlock]
  · refine Fin.cases ?_ (fun b => ?_) j
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis a.succ))
        (fderiv ℝ (polarParam P) y (basis 0)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      have hta : inner ℝ (fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a)) (P.param (angularProjection y)) = 0 := by
        rw [real_inner_comm]; exact ht _
      fin_cases a <;> simp_all [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,cksReference,CKSAngularGeometry.metricBlock]
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis a.succ))
        (fderiv ℝ (polarParam P) y (basis b.succ)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_angular P hy,polarParam_fderiv_angular P hy]
      simp only [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,ht,mul_zero,zero_div,sub_zero]
      fin_cases a <;> fin_cases b <;>
        simp [cksReference,CKSAngularGeometry.metricBlock,angularRoundMetric,pow_two,mul_assoc]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry
lemma polarTensorComponents_hermitian (P : SmoothAngularPatch) (A : SpatialTensor)
    (y : CKSMixedGeometry.Point)
    (hA : ∀ v w, A (polarParam P y) v w = A (polarParam P y) w v) :
    Matrix.IsHermitian (fun i j => polarTensorComponents P A i j y) := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  exact hA _ _
lemma polar_sourceSpatial (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    cksReference (angularRoundMetric P.param) y + Matrix.of (fun i j => polarTensorComponents P A i j y) =
      (fun i j => polarTensorComponents P (sourceSpatial A) i j y) := by
  rw [← hyperbolicField_polar P hr hy]
  rfl

theorem spatial_source_reconstruction {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.patch.chart.target)
    (hA : ∀ v w, A (polarParam P.patch y) v w = A (polarParam P.patch y) w v)
    (hB : ∀ v w, B (polarParam P.patch y) v w = B (polarParam P.patch y) w v) :
    sourceMetric P.fields.base y = (fun i j => polarTensorComponents P.patch (sourceSpatial A) i j y) ∧
    sourceTensor P.fields y = (fun i j => polarTensorComponents P.patch (sourceSpatial B) i j y) ∧
    polarLift P.patch (sourceMetric P.fields.base) (polarParam P.patch y) = sourceSpatial A (polarParam P.patch y) ∧
    polarLift P.patch (sourceTensor P.fields) (polarParam P.patch y) = sourceSpatial B (polarParam P.patch y) := by
  obtain ⟨hg,hk⟩ := cksSourceFields_reconstruct (angularRoundMetric P.patch.param)
    (polarTensorComponents P.patch A) (polarTensorComponents P.patch B) P.mr P.mg P.mK y
    (polarTensorComponents_hermitian P.patch A y hA) (polarTensorComponents_hermitian P.patch B y hB)
  have heg : sourceMetric P.fields.base y = (fun i j => polarTensorComponents P.patch (sourceSpatial A) i j y) :=
    hg.trans (polar_sourceSpatial P.patch A hr hy)
  have hek : sourceTensor P.fields y = (fun i j => polarTensorComponents P.patch (sourceSpatial B) i j y) :=
    hk.trans (polar_sourceSpatial P.patch B hr hy)
  refine ⟨heg,hek,?_,?_⟩
  · apply (polarLift_reconstruction P.patch (sourceMetric P.fields.base) hr hy).2
    intro i j
    exact congrArg (fun F : AmbientMat => F i j) heg.symm
  · apply (polarLift_reconstruction P.patch (sourceTensor P.fields) hr hy).2
    intro i j
    exact congrArg (fun F : AmbientMat => F i j) hek.symm
end
end CKSLorentz

end






end OAI
end

section
namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Finset CKSInducedSphere
open scoped RealInnerProductSpace ContDiff

lemma normal_sq {x : E} (hx : x ≠ 0) : ∑ i : Ix, normal x i ^ 2 = 1 := by
  simp only [normal,div_pow,← Finset.sum_div]
  have hs : (∑ i : Ix, x i ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  rw [hs]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

end
end CKSADM

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter MeasureTheory CKSSphericalHarmonics CKSSphericalChart CKSBending CKSInducedSphere
open scoped Topology ContDiff

lemma unitVector_norm {x : E} (hx : x ≠ 0) : ‖unitVector x‖ = 1 := by
  simpa only [unitVector,Metric.mem_sphere,dist_zero_right] using normalize_mem_sphere x hx

lemma unitVector_smooth {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ unitVector x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

lemma cartMass_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (cartMass f₀ m R) x := by
  have hn : ContDiffAt ℝ ∞ (fun x : E => ‖x‖) x := contDiffAt_norm ℝ hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : ContDiffAt ℝ ∞ (fun y : E => heatTime R ‖y‖) x :=
    ((heatTime_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  have hc : ContDiffAt ℝ ∞ (fun y : E => paddingMass R ‖y‖) x :=
    ((paddingMass_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  have hu : unitVector x ≠ 0 := by
    intro hh
    have hq := unitVector_norm hx
    rw [hh,norm_zero] at hq
    norm_num at hq
  have hz : (heatTime R ‖x‖,unitVector x) ∈ heatDomain := hu
  have hh : ContDiffAt ℝ ∞ (fun z : ℝ × E => canonicalF f₀ m z.1 z.2)
      (heatTime R ‖x‖,unitVector x) :=
    (canonicalF_joint f₀ hf₀ m).contDiffAt (heatDomain_open.mem_nhds hz)
  have hcomp := hh.comp x (ht.prodMk (unitVector_smooth hx))
  exact hc.add hcomp

end
end CKSADM

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart
open scoped Topology ContDiff

lemma unitVector_ne {x : E} (hx : x ≠ 0) : unitVector x ≠ 0 := by
  intro hh
  have h := unitVector_norm hx
  simp [hh] at h

end
end CKSADM

end

end OAI
end

section
namespace OAI













noncomputable section
namespace CKSRealizedRound
noncomputable section
open Matrix CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma contDiffAt_normalEntry {v β : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ ∞ v r) (hβ : ContDiffAt ℝ ∞ β r) (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (normalEntry v β) r := by
  exact (hv.derivWithin (m := ∞) (by simp)).add
    (hβ.div (contDiffAt_id.pow 2) (pow_ne_zero _ hr))

lemma contDiffAt_correctionCoeff {v : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ ∞ v r) (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (correctionCoeff v) r := by
  exact (contDiffAt_id.mul ((hv.derivWithin (m := ∞) (by simp)).sub
    (hv.div contDiffAt_id hr))).div (contDiffAt_const.add (hv.pow 2))
      (ne_of_gt (by positivity))

end
end CKSRealizedRound

end



noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma normal_smoothAt {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (normal : E → Fin 3 → ℝ) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact (EuclideanSpace.proj i).contDiff.contDiffAt.div (contDiffAt_norm ℝ hx)
    (norm_ne_zero_iff.mpr hx)
lemma radicand_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (radicand f₀ m R) x := by
  have hn := contDiffAt_norm ℝ hx (n := ∞)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv := ((bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  exact (contDiffAt_const.add (hv.pow 2)).sub
    ((contDiffAt_const.mul (cartMass_smooth f₀ hf₀ m hR hx)).div hn hr.ne')
lemma metric_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (hp : radicand f₀ m R x ≠ 0) :
    ContDiffAt ℝ ∞ (metric f₀ m R) x := by
  have hi := (radicand_smoothAt f₀ hf₀ m hR hx).inv hp
  have hn := normal_smoothAt hx
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ ∞ (fun y => (if i=j then 1 else 0) +
    ((radicand f₀ m R y)⁻¹-1)*(normal y i*normal y j)) x
  exact contDiffAt_const.add ((hi.sub contDiffAt_const).mul
    ((contDiffAt_pi.mp hn i).mul (contDiffAt_pi.mp hn j)))
lemma cartTensorHeat_component_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (i j : Ix) :
    ContDiffAt ℝ ∞ (fun y : E => canonicalT f₀ (heatTime R ‖y‖) (unitVector y) i j) x := by
  have hh : ContDiffAt ℝ ∞ (heatTime R) ‖x‖ :=
    (heatTime_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))
  have ht : ContDiffAt ℝ ∞ (fun y : E => heatTime R ‖y‖) x :=
    hh.comp x (contDiffAt_norm ℝ hx (n:=∞))
  have hz : (heatTime R ‖x‖,unitVector x) ∈ heatDomain := unitVector_ne hx
  have hc : ContDiffAt ℝ ∞ (fun z : ℝ × E => canonicalT f₀ z.1 z.2 i j)
      (heatTime R ‖x‖,unitVector x) :=
    (canonicalT_joint f₀ hf₀ i j).contDiffAt (heatDomain_open.mem_nhds hz)
  exact hc.comp x (ht.prodMk (unitVector_smooth hx))
lemma cartTensorHeat_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => canonicalT f₀ (heatTime R ‖y‖) (unitVector y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact cartTensorHeat_component_smoothAt f₀ hf₀ hR hx i j
lemma tensor_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (hp : radicand f₀ m R x ≠ 0) :
    ContDiffAt ℝ ∞ (tensor f₀ m R) x := by
  have hn := contDiffAt_norm ℝ hx (n:=∞)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv := (bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)
  have hL := (contDiffAt_normalEntry hv (bendingBeta_smooth R).contDiffAt hr.ne').comp x hn
  have hc := (contDiffAt_correctionCoeff hv hr.ne').comp x hn
  have hU := radicand_smoothAt f₀ hf₀ m hR hx
  have hnormal := normal_smoothAt hx
  have hT := cartTensorHeat_smoothAt f₀ hf₀ hR hx
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hi := contDiffAt_pi.mp hnormal i
  have hj := contDiffAt_pi.mp hnormal j
  exact (((hL.div hU hp).mul (hi.mul hj)).add
    (((hv.comp x hn).div hn hr.ne').mul (contDiffAt_const.sub (hi.mul hj)))).add
    ((hc.div (hn.pow 2) (pow_ne_zero _ hr.ne')).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hT i) j))
lemma rankOne_positive {n : Fin 3 → ℝ} (hn : ∑ i, n i^2=1)
    {a : ℝ} (ha : 0<a) : (1+(a-1) • vecMulVec n n : Mat).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.add_apply, Matrix.vecMulVec, mul_comm,
      mul_assoc, Matrix.one_apply, eq_comm]
  · intro v hv
    have hq : 0 < ∑ i, v i^2 := by
      have h := (Matrix.PosDef.one : (1 : Mat).PosDef).dotProduct_mulVec_pos hv
      simpa [dotProduct, pow_two] using h
    have hcs : (∑ i, n i*v i)^2 ≤ ∑ i, v i^2 := by
      simpa only [hn,one_mul] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ n v
    have he : star v ⬝ᵥ ((1+(a-1) • vecMulVec n n : Mat) *ᵥ v) =
        (∑ i, v i^2)+(a-1)*(∑ i, n i*v i)^2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.vecMulVec, Fin.sum_univ_succ, Matrix.one_apply]
      ring
    rw [he]
    by_cases hh : 1 ≤ a
    · have hnn := mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg (∑ i, n i*v i))
      linarith
    · have hnn := mul_nonneg (show 0≤1-a by linarith) (sub_nonneg.mpr hcs)
      have hp := mul_pos ha hq
      nlinarith
lemma metric_positive {f₀ : C(Sphere,ℝ)} {m R : ℝ} {x : E} (hx : x ≠ 0)
    (hp : 0 < radicand f₀ m R x) : (metric f₀ m R x).PosDef :=
  rankOne_positive (normal_sq hx) (inv_pos.mpr hp)
lemma tensor_hermitian (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R : ℝ)
    {x : E} (hx : x ≠ 0) : (tensor f₀ m R x).IsHermitian := by
  have hs := heatTensor_symmetric_U (heatPolynomials f₀) (smoothDatum_rapid f₀ hf₀)
    (heatTime R ‖x‖) (unitVector x) (unitVector_ne hx)
  apply Matrix.IsHermitian.ext
  intro i j
  change tensor f₀ m R x j i = tensor f₀ m R x i j
  simp only [tensor, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, canonicalT, hs j i, mul_comm (normal x j) (normal x i)]
  simp [Matrix.one_apply,eq_comm]
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem constructed_cartesian_outer_regular
    (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : E, 3*R ≤ ‖x‖ →
      ContDiffAt ℝ ∞ (metric f₀ m R) x ∧
      ContDiffAt ℝ ∞ (tensor f₀ m R) x ∧
      (metric f₀ m R x).PosDef ∧ (tensor f₀ m R x).IsHermitian := by
  obtain ⟨R₀,hR₀,hp⟩ := cartesian_radicand_positive f₀ hf₀ m
  refine ⟨R₀,hR₀,?_⟩
  intro R hR x hx
  have h12 : 12 ≤ R := hR₀.trans hR
  have hRp : 0<R := by linarith
  have hxp : x ≠ 0 := norm_pos_iff.mp (by linarith : 0<‖x‖)
  have hpos := hp R hR x hx
  exact ⟨metric_smoothAt f₀ hf₀ m hRp hxp hpos.ne', tensor_smoothAt f₀ hf₀ m hRp hxp hpos.ne',
    metric_positive hxp hpos, tensor_hermitian f₀ hf₀ m R hxp⟩

end
end CKSCartesianOuter

end










































noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients
open scoped ContDiff Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.smrbilNorm
attribute [local instance] OAI.CKSLorentz.smrbilSpace
attribute [local instance] OAI.CKSLorentz.smrepNorm
attribute [local instance] OAI.CKSLorentz.smrepSpace
attribute [local instance] OAI.CKSLorentz.smrpeNorm
attribute [local instance] OAI.CKSLorentz.smrpeSpace
attribute [local instance] OAI.CKSLorentz.smreeNorm
attribute [local instance] OAI.CKSLorentz.smreeSpace
lemma spatialMatrix_contDiffAt {F : E → CKSAngularGeometry.AmbientMat} {x : E} (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (spatialMatrix F) x := by
  have hB := matrixBilinear_contDiff.contDiffAt.comp x hF
  have hf1 : ContDiff ℝ ∞ (fun B : E →L[ℝ] Point →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] Point →L[ℝ] ℝ) →L[ℝ] (Point →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E Point ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  have hf2 : ContDiff ℝ ∞ (fun B : E →L[ℝ] E →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  exact hf2.contDiffAt.comp _ ((hf1.contDiffAt.comp _ (hB.clm_comp contDiffAt_const)).clm_comp contDiffAt_const)
lemma spatialMatrix_symm {F : E → CKSAngularGeometry.AmbientMat} {x : E} (h : (F x).IsHermitian) :
    ∀ v w, spatialMatrix F x v w = spatialMatrix F x w v := by
  intro v w
  exact matrixBilinear_symm h _ _
lemma spatialMatrix_pos {F : E → CKSAngularGeometry.AmbientMat} {x : E} (h : (F x).PosDef) :
    ∀ v : E, v ≠ 0 → 0 < spatialMatrix F x v v := by
  intro v hv
  apply matrixBilinear_pos h
  exact (EuclideanSpace.equiv (Fin 3) ℝ).injective.ne (by simpa using hv)
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularGeometry
open scoped ContDiff Matrix.Norms.Elementwise
lemma metricBlock_smoothAt {a : Point → ℝ} {b : Point → CKSAngularGeometry.Point}
    {q : Point → Mat} {x : Point}
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hq : ContDiffAt ℝ ∞ q x) :
    ContDiffAt ℝ ∞ (fun y => metricBlock (a y) (b y) (q y)) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  refine Fin.cases ?_ (fun c => ?_) i
  · refine Fin.cases ?_ (fun d => ?_) j
    · exact ha
    · fin_cases d <;> simpa [metricBlock] using contDiffAt_pi.mp hb _
  · refine Fin.cases ?_ (fun d => ?_) j
    · fin_cases c <;> simpa [metricBlock] using contDiffAt_pi.mp hb _
    · fin_cases c <;> fin_cases d <;> simpa [metricBlock] using contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
lemma sourceMetric_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) : ContDiffAt ℝ ∞ (sourceMetric f.base) y :=
  metricBlock_smoothAt (sourceRadialMetric_smoothAt hf.base hy) hf.base.b (sourceGamma_smoothAt hf.base hy)
lemma sourceTensor_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) : ContDiffAt ℝ ∞ (sourceTensor f) y :=
  metricBlock_smoothAt (sourceRadialK_smoothAt hf) hf.kb (sourceTangentialK_smoothAt hf.base hy)
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma SourceCollarAtlas.source_spatial_regular {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v)
    {x : E} (hx : q.radius < ‖x‖) :
    ContDiffAt ℝ ∞ (sourceSpatial A) x ∧ ContDiffAt ℝ ∞ (sourceSpatial B) x ∧
    (∀ v w, sourceSpatial A x v w = sourceSpatial A x w v) ∧
    (∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v) ∧
    ∀ v w, sourceSpatial B x v w = sourceSpatial B x w v := by
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (q.radius_pos.trans hx),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  let y := polarInverse (q.patch i).patch x
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hy : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rwa [hyr],hyw⟩
  have hs := q.source_smooth i y hy
  have hgp := polarLift_smooth_positive (q.patch i).patch (sourceMetric (q.patch i).fields.base)
    hy0 hyt (sourceMetric_smoothAt hs hy0.ne') (q.source_positive i y hy)
  have hkt := polarLift_smoothAt (q.patch i).patch (sourceTensor (q.patch i).fields)
    hy0 hyt (sourceTensor_smoothAt hs hy0.ne')
  have hks := polarLift_symmetric (q.patch i).patch (sourceTensor (q.patch i).fields)
    hy0 hyt (metricBlock_hermitian _ _ (q.source_symmetric i y hy))
  rw [hyx] at hgp hkt hks
  have he : ∀ᶠ z in 𝓝 x,
      sourceSpatial A z = polarLift (q.patch i).patch (sourceMetric (q.patch i).fields.base) z ∧
      sourceSpatial B z = polarLift (q.patch i).patch (sourceTensor (q.patch i).fields) z := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx,
      (polarCone_open _ (q.patch i).region_open).mem_nhds hc] with z hz hzc
    obtain ⟨hu,huw,hut,huz⟩ := polarCone_inverse (q.patch i).patch hzc
    have hr := spatial_source_reconstruction (q.patch i) hu hut
      (by rw [huz]; exact hA z hz) (by rw [huz]; exact hB z hz)
    rw [huz] at hr
    exact ⟨hr.2.2.1.symm,hr.2.2.2.symm⟩
  refine ⟨hgp.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
    hkt.congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
  · rw [he.self_of_nhds.1]; exact hgp.2.1
  · rw [he.self_of_nhds.1]; exact hgp.2.2
  · rw [he.self_of_nhds.2]; exact hks
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology

theorem actual_same_end_smooth_replacement {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hmass : q.HasMassAspect M) (m : ℝ) (hcharge : bondiCharge M = (m,0))
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧
      ∀ R ≥ R₀,
        ContDiffOn ℝ ∞ (q.replacementMetric (heatDatum M hM) m R) {x | S < ‖x‖} ∧
        ContDiffOn ℝ ∞ (q.replacementTensor (heatDatum M hM) m R) {x | S < ‖x‖} ∧
        (∀ x, S < ‖x‖ →
          (∀ v w, q.replacementMetric (heatDatum M hM) m R x v w =
            q.replacementMetric (heatDatum M hM) m R x w v) ∧
          (∀ v : E, v ≠ 0 → 0 < q.replacementMetric (heatDatum M hM) m R x v v) ∧
          ∀ v w, q.replacementTensor (heatDatum M hM) m R x v w =
            q.replacementTensor (heatDatum M hM) m R x w v) ∧
        (∀ x, ‖x‖ ≤ R →
          q.replacementMetric (heatDatum M hM) m R x = sourceSpatial A x ∧
          q.replacementTensor (heatDatum M hM) m R x = sourceSpatial B x) ∧
        (∀ x, 3*R < ‖x‖ →
          q.replacementMetric (heatDatum M hM) m R x =
            spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) x ∧
          q.replacementTensor (heatDatum M hM) m R x =
            spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) x) ∧
        ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
          physicalDEC (fun z => fun a b => polarTensorComponents (q.patch i).patch
              (q.replacementMetric (heatDatum M hM) m R) a b z)
            (fun z => fun a b => polarTensorComponents (q.patch i).patch
              (q.replacementTensor (heatDatum M hM) m R) a b z)
            (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) y := by
  obtain ⟨S,R₁,hS,hqS,hS₁,hprep⟩ := q.replacement_localization hM hmass m hcharge hA hB
  obtain ⟨R₂,hR₂,houter⟩ := CKSCartesianOuter.constructed_cartesian_outer_regular
    (heatDatum M hM) (heatDatum_smooth hM) m
  refine ⟨S,max R₁ R₂,hS,hqS,hS₁.trans_le (le_max_left _ _),?_⟩
  intro R hR
  have h1 := (le_max_left R₁ R₂).trans hR
  have h2 := (le_max_right R₁ R₂).trans hR
  have hRp : 0 < R := by linarith
  obtain ⟨hpoint,hlocal⟩ := hprep R h1
  have hrall : ∀ x : E, S < ‖x‖ →
      ContDiffAt ℝ ∞ (q.replacementMetric (heatDatum M hM) m R) x ∧
      ContDiffAt ℝ ∞ (q.replacementTensor (heatDatum M hM) m R) x ∧
      (∀ v w, q.replacementMetric (heatDatum M hM) m R x v w =
        q.replacementMetric (heatDatum M hM) m R x w v) ∧
      (∀ v : E, v ≠ 0 → 0 < q.replacementMetric (heatDatum M hM) m R x v v) ∧
      ∀ v w, q.replacementTensor (heatDatum M hM) m R x v w =
        q.replacementTensor (heatDatum M hM) m R x w v := by
    intro x hx
    by_cases hi : ‖x‖ < R
    · have hs := q.source_spatial_regular hA hB (hqS.trans hx)
      have he : ∀ᶠ z in 𝓝 x,
          q.replacementMetric (heatDatum M hM) m R z = sourceSpatial A z ∧
          q.replacementTensor (heatDatum M hM) m R z = sourceSpatial B z := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hi] with z hz
        simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,ite_eq_left hz.le]
        exact ⟨trivial,trivial⟩
      refine ⟨hs.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
        hs.2.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
      · rw [he.self_of_nhds.1]; exact hs.2.2.1
      · rw [he.self_of_nhds.1]; exact hs.2.2.2.1
      · rw [he.self_of_nhds.2]; exact hs.2.2.2.2
    · by_cases ho : 3*R < ‖x‖
      · obtain ⟨hg,hk,hpos,hks⟩ := houter R h2 x ho.le
        have he : ∀ᶠ z in 𝓝 x,
            q.replacementMetric (heatDatum M hM) m R z =
              spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) z ∧
            q.replacementTensor (heatDatum M hM) m R z =
              spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) z := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ho] with z hz
          simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
            ite_eq_right (by linarith : ¬ ‖z‖ ≤ R),ite_eq_right (not_le.mpr hz)]
          exact ⟨trivial,trivial⟩
        refine ⟨(spatialMatrix_contDiffAt hg).congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
          (spatialMatrix_contDiffAt hk).congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
        · rw [he.self_of_nhds.1]; exact spatialMatrix_symm hpos.isHermitian
        · rw [he.self_of_nhds.1]; exact spatialMatrix_pos hpos
        · rw [he.self_of_nhds.2]; exact spatialMatrix_symm hks
      · have hr : R ≤ ‖x‖ := le_of_not_gt hi
        have ht : ‖x‖ ≤ 3*R := le_of_not_gt ho
        let i := q.localIndex x
        have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
          ⟨norm_pos_iff.mp (hRp.trans_le hr),Classical.choose_spec (q.covers (spatialDirection x))⟩
        obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
        have hyr : (polarInverse (q.patch i).patch x) 0 = ‖x‖ := by simp [polarInverse]
        have hs := (hpoint i (polarInverse (q.patch i).patch x)
          (by rwa [hyr]) (by rwa [hyr]) hyw).1
        have hg := polarLift_smooth_positive (q.patch i).patch _ hy0 hyt hs.metric_smooth hs.metric_positive
        have hk := polarLift_smoothAt (q.patch i).patch _ hy0 hyt hs.tensor_smooth
        have hks := polarLift_symmetric (q.patch i).patch _ hy0 hyt hs.tensor_symmetric
        rw [hyx] at hg hk hks
        have he := hlocal i x hr ht hc
        refine ⟨hg.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
          hk.congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
        · rw [he.self_of_nhds.1]; exact hg.2.1
        · rw [he.self_of_nhds.1]; exact hg.2.2
        · rw [he.self_of_nhds.2]; exact hks
  refine ⟨fun x hx => (hrall x hx).1.contDiffWithinAt,
    fun x hx => (hrall x hx).2.1.contDiffWithinAt,fun x hx => (hrall x hx).2.2,?_,?_,?_⟩
  · intro x hx
    simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,ite_eq_left hx]
    exact ⟨trivial,trivial⟩
  · intro x hx
    simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
      ite_eq_right (by linarith : ¬ ‖x‖ ≤ R),ite_eq_right (not_le.mpr hx)]
    exact ⟨trivial,trivial⟩
  · intro i y hr ht hw
    have hy0 : 0 < y 0 := hRp.trans_le hr
    have hyt := (q.patch i).region_target hw
    have hn := polarParam_norm (q.patch i).patch hy0.le
    have he := hlocal i (polarParam (q.patch i).patch y) (by rwa [hn]) (by rwa [hn])
      (polarCone_param (q.patch i).patch hw hyt hy0)
    have hparam := (polarParam_contDiffAt (q.patch i).patch hyt).continuousAt
    have hcomponents : ∀ᶠ z in 𝓝 y,
        (fun a b => polarTensorComponents (q.patch i).patch
          (q.replacementMetric (heatDatum M hM) m R) a b z) =
          physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields) z ∧
        (fun a b => polarTensorComponents (q.patch i).patch
          (q.replacementTensor (heatDatum M hM) m R) a b z) =
          physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields) z := by
      filter_upwards [hparam.tendsto.eventually he,
        (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hy0,
        angularProjection.continuous.continuousAt.preimage_mem_nhds
          ((q.patch i).patch.chart.open_target.mem_nhds hyt)] with z hz hz0 hzt
      constructor
      · ext a b
        change q.replacementMetric (heatDatum M hM) m R (polarParam (q.patch i).patch z) _ _ = _
        rw [hz.1]
        exact polarLift_components (q.patch i).patch _ hz0 hzt a b
      · ext a b
        change q.replacementTensor (heatDatum M hM) m R (polarParam (q.patch i).patch z) _ _ = _
        rw [hz.2]
        exact polarLift_components (q.patch i).patch _ hz0 hzt a b
    exact (physicalDEC_congr (hcomponents.mono (fun z hz => hz.1))
      (hcomponents.mono (fun z hz => hz.2)) (Eventually.of_forall (fun _ _ => rfl))).mpr
        (hpoint i y hr ht hw).2
end
end CKSLorentz

end































































end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSLorentz.actual_same_end_smooth_replacement.{u_1} := @OAI.CKSLorentz.actual_same_end_smooth_replacement.{u_1}
