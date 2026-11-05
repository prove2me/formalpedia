-- Prove2me | solution 1 for OAI.CKSLorentz.actual_same_end_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:02:14.876721+00:00
-- url     : https://prove2.me/submissions/78a211de-42fd-45d6-9fd8-063098f9c450

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid
import Theorems.Thm_OAI_CKSCartesianOuter_cartesian_radicand_positive
import Theorems.Thm_OAI_CKSCartesianOuter_constructed_cartesian_energy_tail_bound

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

lemma xi_zero {x : ℝ} (hx : 2 ≤ x) : xi x = 0 := by
  simp [xi,Real.smoothTransition.one_of_one_le (show 1 ≤ x-1 by linarith)]
lemma zeta_nonneg (x : ℝ) : 0 ≤ zeta x := Real.smoothTransition.nonneg _

lemma zeta_zero {x : ℝ} (hx : x ≤ 4) : zeta x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma beta_zero {x : ℝ} (hx : 4 ≤ x) : beta x = 0 := by
  simp [beta,Real.smoothTransition.one_of_one_le (show 1 ≤ 2*x-7 by linarith)]

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

lemma bendingV_tail {R r : ℝ} (hR : 0 < R) (hr : 2*R^2 ≤ r) : bendingV R r = 0 := by
  have hx : 2 ≤ r/R^2 := (le_div_iff₀ (sq_pos_of_pos hR)).mpr hr
  simp [bendingV,xi_zero hx]

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

def radiusSq : Poly := ∑ i : Fin 3, X i ^ 2

lemma laplacian_apply (p : Poly) :
    laplacian p = ∑ i : Fin 3, pderiv i (pderiv i p) := by
  simp [laplacian]

def euler : Derivation ℝ Poly Poly := ∑ i : Fin 3, (X i : Poly) • pderiv i

lemma rotation_apply (i j : Fin 3) (p : Poly) :
    rotation i j p = X i * pderiv j p - X j * pderiv i p := by
  simp [rotation, smul_eq_mul]

lemma euler_apply (p : Poly) : euler p = ∑ i : Fin 3, X i * pderiv i p := by
  simp [euler, Fin.sum_univ_three, Derivation.smul_apply, smul_eq_mul]

lemma euler_homogeneous {p : Poly} {n : ℕ} (hp : p.IsHomogeneous n) :
    euler p = (n : ℝ) • p := by
  rw [euler_apply, hp.sum_X_mul_pderiv, Nat.cast_smul_eq_nsmul ℝ]

lemma pderiv_commute (i j : Fin 3) (p : Poly) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp_all [map_add, pderiv_X] <;> ring

lemma laplacian_X_mul (i : Fin 3) (p : Poly) :
    laplacian (X i * p) = X i * laplacian p + 2 * pderiv i p := by
  fin_cases i <;>
    simp [laplacian_apply, Fin.sum_univ_three, map_add, pderiv_X] <;> ring

lemma laplacian_pderiv (i : Fin 3) (p : Poly) :
    laplacian (pderiv i p) = pderiv i (laplacian p) := by
  simp only [laplacian_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pderiv_commute j i p, pderiv_commute j i (pderiv j p)]

lemma laplacian_rotation (i j : Fin 3) (p : Poly) :
    laplacian (rotation i j p) = rotation i j (laplacian p) := by
  rw [rotation_apply, map_sub, laplacian_X_mul, laplacian_X_mul,
    laplacian_pderiv, laplacian_pderiv, rotation_apply, pderiv_commute i j p]
  ring

lemma rotation_homogeneous (i j : Fin 3) {p : Poly} {n : ℕ}
    (hp : p.IsHomogeneous n) : (rotation i j p).IsHomogeneous n := by
  cases n with
  | zero =>
    have hC := totalDegree_eq_zero_iff_eq_C.mp
      ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
    rw [hC, rotation_apply]
    simpa using (isHomogeneous_zero (σ := Fin 3) (R := ℝ) 0)
  | succ n =>
    rw [rotation_apply]
    have hi := (isHomogeneous_X (R := ℝ) i).mul (hp.pderiv (i := j))
    have hj := (isHomogeneous_X (R := ℝ) j).mul (hp.pderiv (i := i))
    simpa [Nat.add_comm] using hi.sub hj

lemma rotation_casimir (p : Poly) :
    rotation 0 1 (rotation 0 1 p) + rotation 0 2 (rotation 0 2 p) +
      rotation 1 2 (rotation 1 2 p) =
      radiusSq * laplacian p - euler (euler p) - euler p := by
  simp [rotation_apply, euler_apply, laplacian_apply, radiusSq,
    Fin.sum_univ_three, map_add, map_sub, pderiv_X]
  ring

theorem harmonic_rotation_eigenvalue {h : Poly} {l : ℕ}
    (hh : h.IsHomogeneous l) (hΔ : laplacian h = 0) :
    rotation 0 1 (rotation 0 1 h) + rotation 0 2 (rotation 0 2 h) +
      rotation 1 2 (rotation 1 2 h) = -((l : ℝ) * ((l : ℝ) + 1)) • h := by
  rw [rotation_casimir, hΔ, euler_homogeneous hh, Derivation.map_smul, euler_homogeneous hh]
  simp only [mul_zero, zero_sub, smul_smul, ← neg_smul, ← sub_smul]
  congr 1
  ring

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

def eigenvalue (l : ℕ) : ℝ := (l : ℝ) * ((l : ℝ) + 1)

lemma rotation_harmonic {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) (i j : Fin 3) :
    (rotation i j p).IsHomogeneous l ∧ laplacian (rotation i j p) = 0 := by
  exact ⟨rotation_homogeneous i j hp, by rw [laplacian_rotation, hΔ, map_zero]⟩

lemma rotationWord_harmonic {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) (w : List (Fin 3 × Fin 3)) :
    (rotationWord w p).IsHomogeneous l ∧ laplacian (rotationWord w p) = 0 := by
  induction w with
  | nil => exact ⟨hp, hΔ⟩
  | cons ij w ih => exact rotation_harmonic ih.1 ih.2 ij.1 ij.2

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

lemma harmonicCoefficientPolynomial_spec (l : ℕ) (f : SphereL2) :
    (harmonicCoefficientPolynomial l f).IsHomogeneous l ∧
    laplacian (harmonicCoefficientPolynomial l f) = 0 ∧
    toL2 (sphereEval (harmonicCoefficientPolynomial l f)) = (harmonicProjection l f : SphereL2) :=
  Classical.choose_spec (harmonicL2_exists_polynomial (harmonicProjection l f))

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

lemma kernel_deriv_nonneg_time (b : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv b kernel t = (-1 : ℝ) ^ b * exp (-t) := by
  have heq : Set.EqOn kernel (fun x : ℝ => exp (-1 * x)) (Ici 0) := by
    intro x hx
    simpa using kernel_nonneg_time hx
  have hk : ContDiffAt ℝ b kernel t := kernel_smooth.contDiffAt.of_le (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  have he : ContDiffAt ℝ b (fun x : ℝ => exp (-1 * x)) t := by fun_prop
  have hid := iteratedDerivWithin_congr (n := b) heq ht
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hk ht,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) he ht] at hid
  rw [iteratedDeriv_exp_const_mul] at hid
  simpa only [neg_one_mul] using hid

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def Rapid (coeff : ℕ → B) : Prop :=
  ∀ b : ℕ, Summable (fun n => eigenvalue n ^ b * ‖coeff n‖)

def term (coeff : ℕ → B) (n : ℕ) (t : ℝ) : B :=
  kernel (eigenvalue n * t) • coeff n

def heat (coeff : ℕ → B) (t : ℝ) : B := ∑' n, term coeff n t

omit [CompleteSpace B] in
lemma term_smooth [CompleteSpace B] (coeff : ℕ → B) (n : ℕ) : ContDiff ℝ ∞ (term coeff n) := by
  unfold term
  exact (kernel_smooth.comp (contDiff_const.mul contDiff_id)).smul contDiff_const

omit [CompleteSpace B] in
lemma term_deriv [CompleteSpace B] (coeff : ℕ → B) (b n : ℕ) (t : ℝ) :
    iteratedDeriv b (term coeff n) t =
      (eigenvalue n ^ b * iteratedDeriv b kernel (eigenvalue n * t)) • coeff n := by
  have hf : ContDiff ℝ b (fun t : ℝ => kernel (eigenvalue n * t)) :=
    (kernel_smooth.comp (contDiff_const.mul contDiff_id)).of_le
      (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  unfold term
  rw [iteratedDeriv_smul_const hf.contDiffAt (coeff n)]
  rw [iteratedDeriv_comp_const_mul (kernel_smooth.of_le
    (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))) (eigenvalue n)]

lemma heat_majorant (coeff : ℕ → B) (h : Rapid coeff) :
    ∃ v : ℕ → ℕ → ℝ, (∀ b, Summable (v b)) ∧
      ∀ b n t, ‖iteratedFDeriv ℝ b (term coeff n) t‖ ≤ v b n := by
  choose C hC hbound using kernel_derivative_bounded
  refine ⟨fun b n => C b * (eigenvalue n ^ b * ‖coeff n‖),
    fun b => (h b).mul_left (C b), ?_⟩
  intro b n t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, term_deriv,
    norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (eigenvalue_pos n)]
  calc
    eigenvalue n ^ b * |iteratedDeriv b kernel (eigenvalue n * t)| * ‖coeff n‖ ≤
        eigenvalue n ^ b * C b * ‖coeff n‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (hbound b _) (pow_nonneg (eigenvalue_pos n).le _)
    _ = C b * (eigenvalue n ^ b * ‖coeff n‖) := by ring

lemma term_deriv_nonneg_time (coeff : ℕ → B) (b n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv b (term coeff n) t =
      ((-eigenvalue n) ^ b * exp (-eigenvalue n * t)) • coeff n := by
  rw [term_deriv, kernel_deriv_nonneg_time b (mul_nonneg (eigenvalue_pos n).le ht)]
  congr 1
  rw [neg_mul]
  ring

lemma heat_deriv (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ) (t : ℝ) :
    iteratedDeriv b (heat coeff) t = ∑' n, iteratedDeriv b (term coeff n) t := by
  obtain ⟨v, hv, hb⟩ := heat_majorant coeff h
  simp_rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
  unfold heat
  rw [iteratedFDeriv_tsum_apply (term_smooth coeff) (fun k _ => hv k)
    (fun k n t _ => hb k n t) (by simp)]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin b) B).symm.toContinuousLinearEquiv.map_tsum

lemma term_decay (coeff : ℕ → B) (b n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖iteratedDeriv b (term coeff n) t‖ ≤
      exp (-6 * t) * (eigenvalue n ^ b * ‖coeff n‖) := by
  rw [term_deriv_nonneg_time coeff b n ht, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_pow, abs_neg, abs_of_pos (eigenvalue_pos n), abs_of_pos (exp_pos _)]
  have he : exp (-eigenvalue n * t) ≤ exp (-6 * t) := by
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr (eigenvalue_ge_six n)) ht]
  calc
    eigenvalue n ^ b * exp (-eigenvalue n * t) * ‖coeff n‖ ≤
      eigenvalue n ^ b * exp (-6 * t) * ‖coeff n‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he
          (pow_nonneg (eigenvalue_pos n).le b)) (norm_nonneg _)
    _ = exp (-6 * t) * (eigenvalue n ^ b * ‖coeff n‖) := by ring

theorem heat_decay (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖iteratedDeriv b (heat coeff) t‖ ≤
      exp (-6 * t) * ∑' n, eigenvalue n ^ b * ‖coeff n‖ := by
  have hm := (h b).mul_left (exp (-6 * t))
  have hn : Summable (fun n => ‖iteratedDeriv b (term coeff n) t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_decay coeff b n ht) hm
  rw [heat_deriv coeff h]
  calc
    ‖∑' n, iteratedDeriv b (term coeff n) t‖ ≤ ∑' n, ‖iteratedDeriv b (term coeff n) t‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, exp (-6 * t) * (eigenvalue n ^ b * ‖coeff n‖) :=
      hn.tsum_le_tsum (fun n => term_decay coeff b n ht) hm
    _ = exp (-6 * t) * ∑' n, eigenvalue n ^ b * ‖coeff n‖ := tsum_mul_left

lemma term_deriv_summable (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ) (t : ℝ) :
    Summable (fun n => iteratedDeriv b (term coeff n) t) := by
  obtain ⟨v, hv, hb⟩ := heat_majorant coeff h
  apply Summable.of_norm_bounded (hv b)
  intro n
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb b n t

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

lemma pd_sub {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y - G y) x = pd k F x - pd k G x := by
  simp only [pd, fderiv_fun_sub hF hG, sub_apply]

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

lemma eigenvalue_shift (n : ℕ) : eigenvalue (n + 2) = CKSSpectralHeat.eigenvalue n := by
  simp only [eigenvalue, CKSSpectralHeat.eigenvalue, Nat.cast_add, Nat.cast_ofNat]
  ring

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
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics (smoothRotation smoothCasimir rotationGenerator)

lemma rotationGenerator_eq (i j : Ix) (x : E) :
    rotationGenerator i j x = x i • e j - x j • e i := by
  ext k
  simp only [CKSSphericalHarmonics.rotationGenerator_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, e_apply]
  split_ifs <;> ring

lemma smoothRotation_pd (i j : Ix) (F : E → ℝ) (x : E) :
    smoothRotation i j F x = x i * pd j F x - x j * pd i F x := by
  rw [smoothRotation, rotationGenerator_eq]
  simp only [map_sub, map_smul, smul_eq_mul, pd]

lemma pd_smoothRotation {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E}
    (hx : x ∈ U) (i j k : Ix) :
    pd k (smoothRotation i j F) x =
      (if k = i then 1 else 0) * pd j F x + x i * hess F x k j -
      ((if k = j then 1 else 0) * pd i F x + x j * hess F x k i) := by
  have he : smoothRotation i j F = fun y => y i * pd j F y - y j * pd i F y := by
    funext y
    exact smoothRotation_pd i j F y
  rw [he]
  erw [pd_sub ((smooth_diff (coordinate_smooth i) hx).fun_mul (smooth_diff (partial_smooth hF j) hx))
    ((smooth_diff (coordinate_smooth j) hx).fun_mul (smooth_diff (partial_smooth hF i) hx)),
    pd_mul (smooth_diff (coordinate_smooth i) hx) (smooth_diff (partial_smooth hF j) hx),
    pd_mul (smooth_diff (coordinate_smooth j) hx) (smooth_diff (partial_smooth hF i) hx)]
  simp only [pd_coordinate, hess]

lemma smoothRotation_square {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E}
    (hx : x ∈ U) (i j : Ix) (hij : i ≠ j) :
    smoothRotation i j (smoothRotation i j F) x =
      x i ^ 2 * hess F x j j - 2 * x i * x j * hess F x i j +
      x j ^ 2 * hess F x i i - x i * grad F x i - x j * grad F x j := by
  rw [smoothRotation_pd, pd_smoothRotation hF hx, pd_smoothRotation hF hx]
  simp only [ite_true, ite_eq_right hij, ite_eq_right (Ne.symm hij), one_mul, zero_mul,
    grad, hess, partial_comm hF hx j i]
  ring

theorem roundLaplacian_eq_Casimir {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {x : E} (hx : ‖x‖ = 1) : roundLaplacian F x = smoothCasimir F x := by
  have hxU : x ∈ U := by intro h; simp [h] at hx
  have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
    simpa only [Fin.sum_univ_three] using unit_sum_sq hx
  have hH (i j : Ix) : hess F x i j = hess F x j i := partial_comm hF hxU i j
  simp only [smoothCasimir, Pi.add_apply, smoothRotation_square hF hxU 0 1 (by decide),
    smoothRotation_square hF hxU 0 2 (by decide), smoothRotation_square hF hxU 1 2 (by decide),
    roundLaplacian, roundLap, tangentTrace, proj, Fin.sum_univ_three]
  norm_num only [show (0 : Ix) ≠ 1 by decide, show (0 : Ix) ≠ 2 by decide,
    show (1 : Ix) ≠ 0 by decide, show (1 : Ix) ≠ 2 by decide,
    show (2 : Ix) ≠ 0 by decide, show (2 : Ix) ≠ 1 by decide,
    ite_true, ite_false]
  rw [hH 1 0, hH 2 0, hH 2 1]
  linear_combination -(hess F x 0 0 + hess F x 1 1 + hess F x 2 2) * hs

end
end CKSInducedSphere

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

lemma jointHeatSeries_summable (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {z : SpaceTime} (hz : z ∈ heatDomain) : Summable (fun n => heatTerm p a n z) :=
  CKSDifferentialSeries.series_summable (heatTerm p) (heatTerm_bound p hp) a hz

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
lemma paddingDensity_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ paddingDensity r := by
  unfold paddingDensity
  positivity

lemma padding_antideriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => -2 / Real.sqrt s) (paddingDensity r) r := by
  have hs := Real.hasDerivAt_sqrt hr.ne'
  have hh := (hasDerivAt_const r (-2:ℝ)).div hs (Real.sqrt_ne_zero'.mpr hr)
  convert! hh using 1
  unfold paddingDensity
  have he := Real.sq_sqrt hr.le
  field_simp
  nlinarith [Real.sqrt_pos.mpr hr]

lemma paddingDensity_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    primitive a paddingDensity r = 2/Real.sqrt a - 2/Real.sqrt r := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => padding_antideriv (positive_uIcc ha hr hs))
    (positive_interval_integrable paddingDensity_smooth.continuousOn ha hr)
  unfold primitive
  rw [hh]
  ring

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

def sphereHeatJet (p : ℕ → Poly) (a : HeatJet) (t : ℝ) : C(Sphere, ℝ) :=
  iteratedDeriv a.1 (CKSSpectralHeat.heat (fun n => sphereEval (rotationWord a.2 (p n)))) t

lemma sphereHeatJet_eq (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) (x : Sphere) :
    sphereHeatJet p a t x = jointHeatSeries p a (t, (x : Ambient)) := by
  rw [sphereHeatJet, CKSSpectralHeat.heat_deriv _ (hp a.2)]
  change (ContinuousMap.evalCLM ℝ x) (∑' n, _) = _
  rw [(ContinuousMap.evalCLM ℝ x).map_tsum
    (CKSSpectralHeat.term_deriv_summable _ (hp a.2) a.1 t)]
  unfold jointHeatSeries
  congr 1
  funext n
  rw [CKSSpectralHeat.term_deriv]
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
    heatTerm, temporalJet, radialExtension_on_sphere]

lemma sphereHeatJet_decay (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖sphereHeatJet p a t‖ ≤ Real.exp (-6 * t) *
      ∑' n, CKSSpectralHeat.eigenvalue n ^ a.1 * ‖sphereEval (rotationWord a.2 (p n))‖ :=
  CKSSpectralHeat.heat_decay _ (hp a.2) a.1 ht

lemma jointHeatSeries_fderiv_tsum (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {z : SpaceTime} (hz : z ∈ heatDomain) (v : SpaceTime) :
    fderiv ℝ (jointHeatSeries p a) z v = ∑' n,
      (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) v := by
  rw [(jointHeatSeries_hasFDerivAt p hp a hz).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Summable.tsum_finsetSum (fun o _ =>
    (jointHeatSeries_summable p hp (heatNext a o) hz).mul_right (heatField o z v))]
  apply Finset.sum_congr rfl
  intro o ho
  exact (tsum_mul_right).symm

lemma heatTerm_directional_rotation (p : ℕ → Poly) (a : HeatJet) (n : ℕ)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) (i j : Fin 3) :
    (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n (t, x) • heatField o (t, x))
      (0, rotationGenerator i j x) = heatTerm p (a.1, (i,j) :: a.2) n (t, x) := by
  rw [heatTerm_derivative_identity]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, zero_mul, mul_zero, add_zero]
  rw [← (radial_polynomial_hasFDerivAt (rotationWord a.2 (p n)) hx).fderiv]
  change temporalJet a.1 n t * smoothRotation i j
    (radialExtension (sphereEval (rotationWord a.2 (p n)))) x = _
  rw [smoothRotation_radial_polynomial _ i j hx]
  rfl

lemma spatialHeat_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) (t : ℝ) :
    ContDiffOn ℝ ∞ (spatialHeat p a t) puncturedSpace :=
  (jointHeatSeries_smooth p hp a).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

lemma spatialHeat_rotation (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) (i j : Fin 3) :
    smoothRotation i j (spatialHeat p a t) x = spatialHeat p (a.1, (i,j) :: a.2) t x := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (spatialHeat p a t) _ x at hd
  rw [smoothRotation, hd.fderiv]
  change (∑ o, jointHeatSeries p (heatNext a o) (t,x) • heatField o (t,x))
    (0, rotationGenerator i j x) = _
  rw [← (jointHeatSeries_hasFDerivAt p hp a hx).fderiv,
    jointHeatSeries_fderiv_tsum p hp a hx]
  simp_rw [heatTerm_directional_rotation p a _ t hx i j]
  rfl

lemma spatialHeat_time_derivative (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) :
    HasDerivAt (fun s => spatialHeat p a s x) (spatialHeat p (a.1+1, a.2) t x) t := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  convert! hd using 1
  simp only [Fintype.sum_option, add_apply,
    sum_apply, smul_apply, heatField,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', map_zero, Finset.sum_const_zero,
    add_zero, smul_eq_mul, mul_one, mul_zero, heatNext, spatialHeat]

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
lemma paddingWeight_nonneg (R r : ℝ) : 0 ≤ paddingWeight R r := Real.smoothTransition.nonneg _
lemma paddingWeight_le_one (R r : ℝ) : paddingWeight R r ≤ 1 := Real.smoothTransition.le_one _
lemma paddingWeight_monotone {R : ℝ} (hR : 0 < R) : Monotone (paddingWeight R) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (sub_le_sub_right ((div_le_div_iff_of_pos_right hR).mpr hxy) _)
lemma paddingWeight_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : paddingWeight R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : r/R ≤ 1 := (div_le_iff₀ hR).mpr (by simpa using hr)
  linarith

lemma paddingIntegrand_smooth (R : ℝ) :
    ContDiffOn ℝ ∞ (fun r => paddingWeight R r * paddingDensity r) (Ioi 0) :=
  (paddingWeight_smooth R).contDiffOn.mul paddingDensity_smooth
lemma paddingMass_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (paddingMass R) (Ioi 0) :=
  primitive_smooth (paddingIntegrand_smooth R) hR

lemma paddingMass_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ R) : paddingMass R r = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [] with s hs
  rw [uIoc_of_ge hr] at hs
  simp only [paddingWeight_zero hR hs.2,zero_mul]
lemma paddingMass_nonneg {R r : ℝ} (hR : 0 < R) (_hr : 0 < r) : 0 ≤ paddingMass R r := by
  by_cases h : r ≤ R
  · rw [paddingMass_initial hR h]
  · apply intervalIntegral.integral_nonneg (le_of_not_ge h)
    intro s hs
    exact mul_nonneg (paddingWeight_nonneg _ _) (paddingDensity_nonneg (hR.trans_le hs.1))

lemma paddingMass_weighted_bound {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    paddingMass R r ≤ paddingWeight R r * (2/Real.sqrt R) := by
  have hrp : 0 < r := hR.trans_le hr
  have hint := positive_interval_integrable (paddingIntegrand_smooth R).continuousOn hR hrp
  have hdint := positive_interval_integrable paddingDensity_smooth.continuousOn hR hrp
  have hh := intervalIntegral.integral_mono_on hr hint (hdint.const_mul (paddingWeight R r))
    (fun s hs => mul_le_mul_of_nonneg_right (paddingWeight_monotone hR hs.2)
      (paddingDensity_nonneg (hR.trans_le hs.1)))
  change paddingMass R r ≤ _ at hh
  rw [intervalIntegral.integral_const_mul] at hh
  change paddingMass R r ≤ paddingWeight R r * primitive R paddingDensity r at hh
  rw [paddingDensity_integral hR hrp] at hh
  have hw := paddingWeight_nonneg R r
  have hd : 0 ≤ 2/Real.sqrt r := by positivity
  nlinarith
lemma paddingMass_bound {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    paddingMass R r ≤ 2/Real.sqrt R := by
  exact (paddingMass_weighted_bound hR hr).trans
    (by have hh := paddingWeight_le_one R r
        have hp : 0 ≤ 2/Real.sqrt R := by positivity
        nlinarith)

lemma heatDensity_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatDensity R) (Ioi 0) := by
  unfold heatDensity
  exact (bendingZeta_smooth R).contDiffOn.div
    ((contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.add ((bendingV_smooth hR).pow 2)))
    (fun r hr => ne_of_gt (mul_pos (mul_pos (by norm_num) hr) (by positivity)))
lemma heatDensity_nonneg {R r : ℝ} (hr : 0 < r) : 0 ≤ heatDensity R r := by
  exact div_nonneg (zeta_nonneg _) (by positivity)
lemma heatTime_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatTime R) (Ioi 0) :=
  primitive_smooth (heatDensity_smooth hR) (by positivity)

lemma heatTime_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ 4*R) : heatTime R r = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [] with s hs
  have hsr : s ≤ 4*R := hs.2.trans (max_le (by linarith) hr)
  have hh : s/R ≤ 4 := (div_le_iff₀ hR).mpr hsr
  simp [heatDensity,bendingZeta,zeta_zero hh]
lemma heatTime_nonneg {R r : ℝ} (hR : 0 < R) (_hr : 0 < r) : 0 ≤ heatTime R r := by
  by_cases h : r ≤ 4*R
  · rw [heatTime_initial hR h]
  · have h3 : 3*R ≤ r := by linarith
    apply intervalIntegral.integral_nonneg h3
    intro s hs
    exact heatDensity_nonneg (by linarith [hs.1])

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

lemma HeatGenerated.temporal_diff {F : ℝ → E → ℝ} (hF : HeatGenerated p F)
    (t : ℝ) {x : E} (hx : x ∈ U) : DifferentiableAt ℝ (fun s => F s x) t := by
  have h := (hF.joint_smooth hp).comp (contDiffOn_id.prodMk contDiffOn_const)
    (s := (Set.univ : Set ℝ)) (fun _ _ => hx)
  exact ((contDiffOn_univ.mp h).differentiable (by simp)).differentiableAt

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

def td (F : ℝ → E → ℝ) (t : ℝ) (x : E) : ℝ := deriv (fun s => F s x) t

lemma HeatGenerated.time {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    HeatGenerated p (td F) := by
  induction hF with
  | basic a =>
    apply HeatGenerated.congr (HeatGenerated.basic (a.1+1,a.2))
    intro t x hx
    exact (spatialHeat_time_derivative p hp a t hx).deriv.symm
  | zero =>
    change HeatGenerated p (fun t x => deriv (fun _ : ℝ => (0 : ℝ)) t)
    simpa only [deriv_const] using (HeatGenerated.zero (p := p))
  | @add F G hF hG ihF ihG =>
    apply HeatGenerated.congr (ihF.add ihG)
    intro t x hx
    exact (deriv_fun_add (hF.temporal_diff hp t hx) (hG.temporal_diff hp t hx)).symm
  | @coeff c F hc hF ih =>
    apply HeatGenerated.congr (HeatGenerated.coeff c hc ih)
    intro t x hx
    exact (deriv_const_mul (c x) (hF.temporal_diff hp t hx)).symm
  | @congr F G hF he ih =>
    apply HeatGenerated.congr ih
    intro t x hx
    unfold td
    congr 1
    funext s
    exact he s x hx

lemma HeatGenerated.decay {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 →
      ‖F t x‖ ≤ C * Real.exp (-6 * t) := by
  induction hF with
  | basic a =>
    let C := ∑' n, CKSSpectralHeat.eigenvalue n ^ a.1 * ‖sphereEval (rotationWord a.2 (p n))‖
    refine ⟨C, tsum_nonneg (fun n => mul_nonneg (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le _) (norm_nonneg _)), ?_⟩
    intro t ht x hx
    let s : Sphere := ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩
    have he : spatialHeat p a t x = sphereHeatJet p a t s := (sphereHeatJet_eq p hp a t s).symm
    rw [he]
    exact ((sphereHeatJet p a t).norm_coe_le_norm s).trans
      (by simpa only [mul_comm, C] using sphereHeatJet_decay p hp a ht)
  | zero =>
    exact ⟨0, le_rfl, by intros; simp⟩
  | @add F G hF hG ihF ihG =>
    obtain ⟨C, hC, hbC⟩ := ihF
    obtain ⟨D, hD, hbD⟩ := ihG
    refine ⟨C+D, add_nonneg hC hD, fun t ht x hx => ?_⟩
    exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hbC t ht x hx) (hbD t ht x hx))
  | @coeff c F hc hF ih =>
    obtain ⟨C, hC, hb⟩ := ih
    let cr := smoothRestriction c hc
    refine ⟨‖cr‖ * C, mul_nonneg (norm_nonneg _) hC, fun t ht x hx => ?_⟩
    let s : Sphere := ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩
    have hc' : ‖c x‖ ≤ ‖cr‖ := cr.norm_coe_le_norm s
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hc' (hb t ht x hx) (norm_nonneg _) (norm_nonneg _)
  | @congr F G hF he ih =>
    obtain ⟨C, hC, hb⟩ := ih
    refine ⟨C, hC, fun t ht x hx => ?_⟩
    rw [← he t x (by intro h; simp [h] at hx)]
    exact hb t ht x hx

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

lemma smoothRotation_congr {F G : Ambient → ℝ} (h : EqOn F G puncturedSpace)
    (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j F x = smoothRotation i j G x := by
  have he : F =ᶠ[𝓝 x] G := by
    filter_upwards [puncturedSpace.isOpen.mem_nhds hx] with y hy
    exact h hy
  rw [smoothRotation, smoothRotation, he.fderiv_eq]

lemma spatialHeat_casimir (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    (t : ℝ) {x : Ambient} (hx : x ≠ 0) :
    smoothCasimir (spatialHeat p a t) x =
      spatialHeat p (a.1, (0,1) :: (0,1) :: a.2) t x +
      spatialHeat p (a.1, (0,2) :: (0,2) :: a.2) t x +
      spatialHeat p (a.1, (1,2) :: (1,2) :: a.2) t x := by
  have h (i j : Fin 3) : smoothRotation i j (smoothRotation i j (spatialHeat p a t)) x =
      spatialHeat p (a.1, (i,j) :: (i,j) :: a.2) t x := by
    rw [smoothRotation_congr (fun y hy => spatialHeat_rotation p hp a t hy i j) i j hx]
    exact spatialHeat_rotation p hp _ t hx i j
  simp only [smoothCasimir, Pi.add_apply]
  rw [h 0 1, h 0 2, h 1 2]

lemma radialExtension_poly_add (p q : Poly) (x : Ambient) :
    radialExtension (sphereEval (p + q)) x =
      radialExtension (sphereEval p) x + radialExtension (sphereEval q) x := by
  by_cases hx : x ≠ 0 <;> simp [radialExtension, hx]

lemma radialExtension_poly_smul (c : ℝ) (p : Poly) (x : Ambient) :
    radialExtension (sphereEval (c • p)) x = c * radialExtension (sphereEval p) x := by
  by_cases hx : x ≠ 0 <;> simp [radialExtension, hx]

lemma rotationWord_smul (w : List (Fin 3 × Fin 3)) (c : ℝ) (p : Poly) :
    rotationWord w (c • p) = c • rotationWord w p := by
  induction w with
  | nil => rfl
  | cons ij w ih => simp only [rotationWord, ih, Derivation.map_smul]

def HighHarmonic (p : ℕ → Poly) : Prop :=
  ∀ n, (p n).IsHomogeneous (n + 2) ∧ laplacian (p n) = 0

lemma heatPolynomials_harmonic (f : C(Sphere, ℝ)) : HighHarmonic (heatPolynomials f) := by
  intro n
  exact ⟨(harmonicCoefficientPolynomial_spec (n+2) (toL2 f)).1,
    (harmonicCoefficientPolynomial_spec (n+2) (toL2 f)).2.1⟩

lemma heatTerm_casimir (p : ℕ → Poly) (hh : HighHarmonic p) (a : HeatJet)
    (n : ℕ) (z : SpaceTime) :
    heatTerm p (a.1, (0,1) :: (0,1) :: a.2) n z +
    heatTerm p (a.1, (0,2) :: (0,2) :: a.2) n z +
    heatTerm p (a.1, (1,2) :: (1,2) :: a.2) n z =
      -CKSSpectralHeat.eigenvalue n * heatTerm p a n z := by
  have he := harmonic_rotation_eigenvalue (rotationWord_harmonic (hh n).1 (hh n).2 a.2).1
    (rotationWord_harmonic (hh n).1 (hh n).2 a.2).2
  have he' := congrArg (fun q => radialExtension (sphereEval q) z.2) he
  simp only [radialExtension_poly_add, radialExtension_poly_smul] at he'
  change _ = -eigenvalue (n+2) * _ at he'
  rw [eigenvalue_shift] at he'
  simp only [heatTerm, rotationWord]
  rw [← mul_add, ← mul_add]
  convert! congrArg (fun v => temporalJet a.1 n z.1 * v) he' using 1
  ring

lemma spatialHeat_casimir_series (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) (t : ℝ) {x : Ambient} (hx : x ≠ 0) :
    smoothCasimir (spatialHeat p a t) x =
      ∑' n, -CKSSpectralHeat.eigenvalue n * heatTerm p a n (t,x) := by
  rw [spatialHeat_casimir p hp a t hx]
  unfold spatialHeat jointHeatSeries
  rw [← (jointHeatSeries_summable p hp _ hx).tsum_add (jointHeatSeries_summable p hp _ hx),
    ← ((jointHeatSeries_summable p hp _ hx).add (jointHeatSeries_summable p hp _ hx)).tsum_add
      (jointHeatSeries_summable p hp _ hx)]
  congr 1
  funext n
  exact heatTerm_casimir p hh a n _

lemma temporalJet_succ_nonneg (b n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    temporalJet (b+1) n t = -CKSSpectralHeat.eigenvalue n * temporalJet b n t := by
  simp only [temporalJet, CKSSpectralHeat.kernel_deriv_nonneg_time _
    (mul_nonneg (CKSSpectralHeat.eigenvalue_pos n).le ht), pow_succ]
  ring

theorem spatialHeat_equation (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) {t : ℝ} (ht : 0 ≤ t)
    {x : Ambient} (hx : x ≠ 0) :
    deriv (fun s => spatialHeat p a s x) t = smoothCasimir (spatialHeat p a t) x := by
  rw [(spatialHeat_time_derivative p hp a t hx).deriv,
    spatialHeat_casimir_series p hp hh a t hx]
  unfold spatialHeat jointHeatSeries
  congr 1
  funext n
  simp only [heatTerm, temporalJet_succ_nonneg _ _ ht]
  ring

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
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

lemma canonicalF_heat (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {t : ℝ} (ht : 0 ≤ t) {x : E} (hx : ‖x‖ = 1) :
    deriv (fun s => canonicalF f₀ m s x) t = roundLaplacian (canonicalF f₀ m t) x := by
  have hp := smoothDatum_rapid f₀ hf₀
  unfold canonicalF
  rw [deriv_const_add,roundLaplacian_const_add,roundLaplacian_eq_Casimir
    (spatialHeat_smooth _ hp _ t) hx]
  exact spatialHeat_equation _ hp (heatPolynomials_harmonic f₀) _ ht (by intro h; simp [h] at hx)

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

lemma generated_uniform {p : ℕ → Poly} (hp : PolynomialRapid p) {F : ℝ → E → ℝ}
    (hF : HeatGenerated p F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 → |F t x| ≤ C := by
  obtain ⟨C,hC,h⟩ := hF.decay hp
  refine ⟨C,hC,fun t ht x hx => ?_⟩
  calc
    |F t x| ≤ C * Real.exp (-6*t) := h t ht x hx
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) hC
    _ = C := mul_one C

theorem canonical_uniform_data (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 →
      |canonicalF f₀ m t x| ≤ |m|+K ∧
      |roundLaplacian (canonicalF f₀ m t) x| ≤ K ∧
      (∀ i : Ix, |pd i (canonicalF f₀ m t) x| ≤ K) ∧
      (∀ i j : Ix, |canonicalT f₀ t x i j| ≤ K) := by
  classical
  let p := heatPolynomials f₀
  have hp : PolynomialRapid p := smoothDatum_rapid f₀ hf₀
  have hi := inversePolynomials_rapid p hp
  have hb : HeatGenerated p (spatialHeat p (0,[])) := HeatGenerated.basic _
  obtain ⟨C₀,hC₀,b₀⟩ := generated_uniform hp hb
  obtain ⟨C₁,hC₁,b₁⟩ := generated_uniform hp (hb.time hp)
  choose C hC bC using (fun i : Ix => generated_uniform hp (hb.partial hp i))
  choose H hH bH using (fun i : Ix × Ix => generated_uniform hi (heatTensor_generated p hp i.1 i.2))
  let K := C₀+C₁+(∑ i : Ix, C i)+(∑ i : Ix × Ix, H i)
  have hsumC : 0 ≤ ∑ i : Ix, C i := sum_nonneg (fun i _ => hC i)
  have hsumH : 0 ≤ ∑ i : Ix × Ix, H i := sum_nonneg (fun i _ => hH i)
  have hc0 : C₀ ≤ K := by dsimp [K]; linarith
  have hc1 : C₁ ≤ K := by dsimp [K]; linarith
  have hc (i : Ix) : C i ≤ K := by
    have hh := single_le_sum (fun j (_ : j ∈ (univ : Finset Ix)) => hC j) (mem_univ i)
    dsimp [K]
    linarith
  have hh (i : Ix × Ix) : H i ≤ K := by
    have hh := single_le_sum (fun j (_ : j ∈ (univ : Finset (Ix × Ix))) => hH j) (mem_univ i)
    dsimp [K]
    linarith
  refine ⟨K,hC₀.trans hc0,?_⟩
  intro t ht x hx
  refine ⟨?_,?_,?_,?_⟩
  · exact (abs_add_le m _).trans (by have hb0 := (b₀ t ht x hx).trans hc0; linarith)
  · rw [← canonicalF_heat f₀ hf₀ m ht hx]
    change |deriv (fun s => m + spatialHeat p (0,[]) s x) t| ≤ K
    rw [deriv_const_add]
    exact (b₁ t ht x hx).trans hc1
  · intro i
    change |pd i (fun y => m + spatialHeat p (0,[]) t y) x| ≤ K
    rw [pd_const_add]
    exact (bC i t ht x hx).trans (hc i)
  · intro i j
    exact (bH (i,j) t ht x hx).trans (hh (i,j))

end
end CKSSphericalChart

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

lemma bendingV_tail_deriv {R r : ℝ} (hR : 0 < R) (hr : 2*R^2 < r) :
    deriv (bendingV R) r = 0 := by
  have hh : bendingV R =ᶠ[𝓝 r] (fun _ => 0) := by
    filter_upwards [eventually_gt_nhds hr] with y hy
    exact bendingV_tail hR hy.le
  rw [hh.deriv_eq]
  exact deriv_const _ _

lemma bendingBeta_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    bendingBeta R r = 0 := by
  apply beta_zero
  exact (le_div_iff₀ (by linarith : 0 < R)).mpr (by nlinarith)

end
end CKSBending

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

def tailSphereMass (f₀ : C(Sphere,ℝ)) (m R r : ℝ) (n : Sphere) : ℝ :=
  paddingMass R r + canonicalF f₀ m (heatTime R r) n

lemma tailSphereMass_bound (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ R r : ℝ, 1 ≤ R → 3*R ≤ r → ∀ n : Sphere,
      |tailSphereMass f₀ m R r n| ≤ B := by
  obtain ⟨K,hK,hbound⟩ := canonical_uniform_data f₀ hf₀ m
  refine ⟨|m|+K+3,by positivity,?_⟩
  intro R r hR hr n
  have hRp : 0 < R := by linarith
  have hrp : 0 < r := by linarith
  have hc := paddingMass_bound hRp (by linarith : R ≤ r)
  have hs : 1 ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt hR
  have ht := heatTime_nonneg hRp hrp
  have hf := (hbound (heatTime R r) ht n (by simp)).1
  have hc' : paddingMass R r ≤ 2 := hc.trans ((div_le_iff₀ (Real.sqrt_pos.mpr hRp)).mpr (by linarith))
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (paddingMass_nonneg hRp hrp)]
  linarith

end
end CKSADM

end

end OAI
end

section
namespace OAI







noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators Topology
lemma matrixBilinear_apply (G : Mat) (v w : V) :
    matrixBilinear G v w = ∑ i : Fin 3, ∑ j : Fin 3, G i j * v i * w j := by
  simp [matrixBilinear, mul_assoc]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] scalarAtlas

end
end CKSTangentCoefficients

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

def metric (b : E → ℝ) (x : E) (i j : Ix) : ℝ :=
  (if i = j then 1 else 0) + b x * normal x i * normal x j

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

def cartB (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : ℝ :=
  (1-2*cartMass f₀ m R x/‖x‖)⁻¹-1

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
lemma cartMass_uniform_bound (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : E, 3*R ≤ ‖x‖ →
      |cartMass f₀ m R x| ≤ B := by
  obtain ⟨B,hB,hbound⟩ := tailSphereMass_bound f₀ hf₀ m
  refine ⟨B,hB,?_⟩
  intro R hR x hx
  have hxp : x ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖x‖)
  let n : Sphere := ⟨unitVector x, by simpa only [Metric.mem_sphere,dist_zero_right] using unitVector_norm hxp⟩
  exact hbound R ‖x‖ hR hx n

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
lemma tensor_tail (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : E} (hx : 2*R^2 < ‖x‖) : tensor f₀ m R x = 0 := by
  have hRp : 0<R := by linarith
  have hv := bendingV_tail hRp hx.le
  have hvp := bendingV_tail_deriv hRp hx
  have hb := bendingBeta_tail hR hx.le
  simp [tensor,normalEntry,correctionCoeff,hv,hvp,hb]
lemma metric_tail (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 0<R)
    {x : E} (hx : 2*R^2 ≤ ‖x‖) : metric f₀ m R x = CKSADM.metric (cartB f₀ m R) x := by
  have hv := bendingV_tail hR hx
  ext i j
  simp only [metric,radicand,hv,zero_pow (by decide : (2:ℕ)≠0),add_zero,
    CKSADM.metric,cartB,Matrix.add_apply,Matrix.one_apply,Matrix.smul_apply,
    Matrix.vecMulVec_apply,smul_eq_mul]
  ring

end
end CKSCartesianOuter

end



















noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : physicalMetricJet G x = physicalMetricJet H x := by
  have hc (i j) : (fun y => G y i j) =ᶠ[𝓝 x] (fun y => H y i j) :=
    h.mono fun _ hh => congrFun (congrFun hh i) j
  have hd (a i j) : D (CKSRealizedRound.basis a) (fun y => G y i j) =ᶠ[𝓝 x]
      D (CKSRealizedRound.basis a) (fun y => H y i j) :=
    (hc i j).eventually_nhds.mono fun _ hh => D_congr hh _
  unfold physicalMetricJet
  congr 1
  · exact congrArg Inv.inv h.self_of_nhds
  · funext a i j
    exact D_congr (hc i j) _
  · funext a b i j
    exact D_congr (hd b i j) _
lemma physicalTensorJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : physicalTensorJet G x = physicalTensorJet H x := by
  have hc (i j) : (fun y => G y i j) =ᶠ[𝓝 x] (fun y => H y i j) :=
    h.mono fun _ hh => congrFun (congrFun hh i) j
  unfold physicalTensorJet
  congr 1
  · exact h.self_of_nhds
  · funext a i j
    exact D_congr (hc i j) _

end
end CKSAngularGeometry

end





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

lemma ContinuousMetricJetAt.energy {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).energy (k y)) x := by
  have hs := h.scalar
  have ht := h.trace hk
  have hn := h.normSq hk
  unfold CKSRound.MetricJet.energy
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
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSTangentCoefficients CKSCartesianOuter CKSInducedSphere CKSSphericalChart
open scoped BigOperators
lemma spatialMatrix_apply (F : E → AmbientMat) (x v w : E) :
    spatialMatrix F x v w = pair (F x) v w := by
  have hh := matrixBilinear_apply (fun i j => F x i j) (fun i => v i) (fun i => w i)
  change spatialMatrix F x v w = _ at hh
  rw [hh]
  simp only [pair,Fin.sum_univ_three]
  ring

end
end CKSLorentz

end

















noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry
open scoped BigOperators

lemma spatialCoefficients_spatialMatrix (F : E → AmbientMat) :
    spatialCoefficients (spatialMatrix F) = fun y => F (CKSCartesianOuter.toPoint.symm y) := by
  funext y i j
  unfold spatialCoefficients
  rw [spatialMatrix_apply]
  simp [CKSSphericalChart.pair,CKSMixedGeometry.basis,ite_mul,mul_ite]
end
end CKSLorentz

end






















noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped Topology ContDiff
lemma spatialCartesian_spatialMatrix (F : E → AmbientMat) :
    spatialCartesian (spatialMatrix F) = F := by
  funext x
  simp only [spatialCartesian,spatialCoefficients_spatialMatrix,
    ContinuousLinearEquiv.symm_apply_apply]
lemma spatialCartesian_congr_at {A B : SpatialTensor} {x : E} (h : A x = B x) :
    spatialCartesian A x = spatialCartesian B x := by
  unfold spatialCartesian spatialCoefficients
  simp only [ContinuousLinearEquiv.symm_apply_apply,h]
  rfl
lemma SourceCollarAtlas.replacement_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : E} (hx : 2*R^2 < ‖x‖) :
    spatialCartesian (q.replacementMetric f₀ m R) x = CKSADM.metric (cartB f₀ m R) x ∧
    q.replacementTensor f₀ m R x = 0 := by
  have hr : ¬ ‖x‖ ≤ R := by nlinarith
  have ht : ¬ ‖x‖ ≤ 3*R := by nlinarith
  have hg : q.replacementMetric f₀ m R x = spatialMatrix (CKSCartesianOuter.metric f₀ m R) x := by
    simp [SourceCollarAtlas.replacementMetric,hr,ht]
  have hk : q.replacementTensor f₀ m R x = spatialMatrix (CKSCartesianOuter.tensor f₀ m R) x := by
    simp [SourceCollarAtlas.replacementTensor,hr,ht]
  refine ⟨?_,?_⟩
  · rw [spatialCartesian_congr_at hg,spatialCartesian_spatialMatrix]
    exact CKSCartesianOuter.metric_tail f₀ m (by linarith) hx.le
  · rw [hk]
    ext v w
    rw [spatialMatrix_apply,CKSCartesianOuter.tensor_tail f₀ m hR hx]
    simp [CKSSphericalChart.pair]

end
end CKSLorentz

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
def direction (x : E) : Fin 3 → ℝ := fun i => x i / ‖x‖
def tailMetric (F : E → ℝ) (x : E) : Mat :=
  1 + ((1-2*F x/‖x‖)⁻¹-1) • Matrix.vecMulVec (direction x) (direction x)
def density (F : E → ℝ) (x : E) : ℝ := Real.sqrt (tailMetric F x).det

end
end CKSTailVolume

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set
lemma direction_sq_sum {x : E} (hx : x ≠ 0) : ∑ i, direction x i ^ 2 = 1 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [direction,div_pow,← Finset.sum_div]
  rw [← EuclideanSpace.real_norm_sq_eq x]
  exact div_self (pow_ne_zero _ hn)
lemma det_rank_one (n : Fin 3 → ℝ) (b : ℝ) :
    (1 + b • vecMulVec n n : Mat).det = 1 + b * ∑ i, n i^2 := by
  have he : (b • vecMulVec n n : Mat) =
      replicateCol Unit (b • n) * replicateRow Unit n := by
    ext i j
    simp [Matrix.mul_apply,Matrix.vecMulVec,Matrix.replicateCol,Matrix.replicateRow,mul_assoc]
  rw [he,det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct,Pi.smul_apply,smul_eq_mul]
  simp_rw [show ∀ i, n i * (b * n i) = b * n i^2 by intro i; ring,Finset.mul_sum]
lemma tailMetric_det {x : E} (hx : x ≠ 0) (F : E → ℝ) :
    (tailMetric F x).det = (1-2*F x/‖x‖)⁻¹ := by
  rw [tailMetric,det_rank_one,direction_sq_sum hx]
  ring

theorem tail_density_bound {F : E → ℝ} {M L : ℝ} (_hM : 0 ≤ M) (hL : 0 < L)
    (hML : 4*M ≤ L) (hF : ∀ x ∈ tailRegion L, |F x| ≤ M) :
    ∀ x ∈ tailRegion L, (tailMetric F x).det = (1-2*F x/‖x‖)⁻¹ ∧
      0 ≤ density F x ∧ density F x ≤ Real.sqrt 2 := by
  intro x hx
  have hLx : L < ‖x‖ := hx
  have hr : 0 < ‖x‖ := hL.trans hLx
  have hdet := tailMetric_det (norm_pos_iff.mp hr) F
  refine ⟨hdet,Real.sqrt_nonneg _,?_⟩
  unfold density
  rw [hdet]
  apply Real.sqrt_le_sqrt
  have hfx : F x ≤ M := (le_abs_self _).trans (hF x hx)
  have hhalf : 1/2 ≤ 1-2*F x/‖x‖ := by
    have hdiv : 2*F x/‖x‖ ≤ 1/2 := (div_le_iff₀ hr).mpr (by linarith)
    linarith
  apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1-2*F x/‖x‖)).mpr
  linarith
end
end CKSTailVolume

end

noncomputable section
namespace CKSTailVolume
noncomputable section
open Matrix MeasureTheory Set
open scoped ENNReal
lemma rate_le_japanese {r : ℝ} (hr : 1 ≤ r) :
    1/(r^3*Real.sqrt r) ≤ (2:ℝ)^(7/2:ℝ)*(1+r)^(-(7/2:ℝ)) := by
  have hp : 0 < r := zero_lt_one.trans_le hr
  have he : 1/(r^3*Real.sqrt r) = r^(-(7/2:ℝ)) := by
    rw [Real.rpow_neg hp.le,show (7/2:ℝ) = (3:ℝ)+1/2 by norm_num,
      Real.rpow_add hp,← Real.sqrt_eq_rpow]
    norm_num
  rw [he]
  calc
    _ ≤ ((1+r)/2)^(-(7/2:ℝ)) := Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      simp only [div_inv_eq_mul,mul_comm]
lemma tailRegion_measurable (L : ℝ) : MeasurableSet (tailRegion L) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet

end
end CKSTailVolume

end





noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM CKSBending Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma spatialCoefficients_congr {P Q : SpatialTensor} {x : E} (h : P =ᶠ[𝓝 x] Q) :
    spatialCoefficients P =ᶠ[𝓝 (CKSCartesianOuter.toPoint x)] spatialCoefficients Q := by
  have hh := CKSCartesianOuter.toPoint.symm.continuous.continuousAt.eventually
    (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ h)
  filter_upwards [hh] with y hy
  ext i j
  change P (CKSCartesianOuter.toPoint.symm y) _ _ = Q (CKSCartesianOuter.toPoint.symm y) _ _
  rw [hy]
lemma spatialEnergy_congr {A B C D : SpatialTensor} {x : E}
    (hA : A =ᶠ[𝓝 x] C) (hB : B =ᶠ[𝓝 x] D) : spatialEnergy A B x = spatialEnergy C D x := by
  unfold spatialEnergy
  rw [physicalMetricJet_congr (spatialCoefficients_congr hA),physicalTensorJet_congr (spatialCoefficients_congr hB)]
lemma SourceCollarAtlas.replacement_outer_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {x : E} (hx : 3*R < ‖x‖) :
    ∀ᶠ z in 𝓝 x,
      q.replacementMetric f₀ m R z = spatialMatrix (CKSCartesianOuter.metric f₀ m R) z ∧
      q.replacementTensor f₀ m R z = spatialMatrix (CKSCartesianOuter.tensor f₀ m R) z := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with z hz
  simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
    ite_eq_right (by linarith : ¬ ‖z‖ ≤ R),ite_eq_right (not_le.mpr hz)]
  exact ⟨trivial,trivial⟩
lemma SourceCollarAtlas.replacement_outer_energy {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {x : E} (hx : 3*R < ‖x‖) :
    spatialEnergy (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R) x =
      (physicalMetricJet (CKSCartesianOuter.physicalMetric f₀ m R) (CKSCartesianOuter.toPoint x)).energy
        (physicalTensorJet (CKSCartesianOuter.physicalTensor f₀ m R) (CKSCartesianOuter.toPoint x)) := by
  have h := q.replacement_outer_eventually f₀ m hR hx
  rw [spatialEnergy_congr (h.mono fun _ hh => hh.1) (h.mono fun _ hh => hh.2)]
  unfold spatialEnergy
  rw [spatialCoefficients_spatialMatrix,spatialCoefficients_spatialMatrix]
  rfl
lemma SourceCollarAtlas.replacement_momentum_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : E} (hx : 2*R^2 < ‖x‖) :
    spatialMomentum (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R) x = 0 := by
  have hk : q.replacementTensor f₀ m R =ᶠ[𝓝 x] 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with z hz
    exact (q.replacement_tail f₀ m hR hz).2
  unfold spatialMomentum
  rw [physicalTensorJet_congr (spatialCoefficients_congr hk)]
  ext i
  simp [CKSRound.MetricJet.momentum,CKSRound.MetricJet.tensorDivergence,CKSRound.MetricJet.dTrace,
    physicalTensorJet,spatialCoefficients,CKSCalculus.D]
lemma SourceCollarAtlas.replacement_density_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R)
    {x : E} (hx : 2*R^2 < ‖x‖) :
    Real.sqrt (spatialCartesian (q.replacementMetric f₀ m R) x).det =
      CKSTailVolume.density (cartMass f₀ m R) x := by
  rw [(q.replacement_tail f₀ m hR hx).1]
  have he : CKSADM.metric (cartB f₀ m R) x = CKSTailVolume.tailMetric (cartMass f₀ m R) x := by
    ext i j
    simp only [CKSADM.metric,cartB,normal,CKSTailVolume.tailMetric,CKSTailVolume.direction,
      Matrix.add_apply,Matrix.one_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    ring
  rw [he]
  rfl

lemma SourceCollarAtlas.replacement_energy_continuousAt {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 0 ≤ R)
    {x : E} (hx : 3*R < ‖x‖)
    (hg : ContDiffAt ℝ ∞ (CKSCartesianOuter.metric f₀ m R) x)
    (hk : ContDiffAt ℝ ∞ (CKSCartesianOuter.tensor f₀ m R) x)
    (hp : (CKSCartesianOuter.metric f₀ m R x).PosDef) :
    ContinuousAt (spatialEnergy (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R)) x := by
  have hgg : ContDiffAt ℝ ∞ (CKSCartesianOuter.physicalMetric f₀ m R) (CKSCartesianOuter.toPoint x) :=
    (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ hg).comp _ CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt
  have hkk : ContDiffAt ℝ ∞ (CKSCartesianOuter.physicalTensor f₀ m R) (CKSCartesianOuter.toPoint x) :=
    (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ hk).comp _ CKSCartesianOuter.toPoint.symm.contDiff.contDiffAt
  have hdet : (CKSCartesianOuter.physicalMetric f₀ m R (CKSCartesianOuter.toPoint x)).det ≠ 0 := by
    simpa [CKSCartesianOuter.physicalMetric] using hp.det_pos.ne'
  have hc := ((physicalMetricJet_continuousAt hgg hdet).energy (physicalTensorJet_continuousAt hkk)).comp
    CKSCartesianOuter.toPoint.continuous.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with z hz
  exact q.replacement_outer_energy f₀ m hR hz
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry CKSInducedSphere CKSSphericalHarmonics CKSADM Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

theorem actual_same_end_tail_integrable {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R ≥ R₀, ∃ L : ℝ, 2*R^2 ≤ L ∧
      IntegrableOn (spatialEnergy (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R))
        (CKSTailVolume.tailRegion L) (spatialVolume (q.replacementMetric f₀ m R)) ∧
      ∀ x : E, 2*R^2 < ‖x‖ →
        spatialMomentum (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R) x = 0 := by
  obtain ⟨R₁,C,hR₁,hC,hbound⟩ := CKSCartesianOuter.constructed_cartesian_energy_tail_bound f₀ hf₀ m
  obtain ⟨R₂,hR₂,hreg⟩ := CKSCartesianOuter.constructed_cartesian_outer_regular f₀ hf₀ m
  obtain ⟨M,hM,hF⟩ := CKSCartesianOuter.cartMass_uniform_bound f₀ hf₀ m
  refine ⟨max R₁ R₂,hR₁.trans (le_max_left _ _),?_⟩
  intro R hR
  have h1 : R₁ ≤ R := (le_max_left _ _).trans hR
  have h2 : R₂ ≤ R := (le_max_right _ _).trans hR
  have hR12 : 12 ≤ R := hR₁.trans h1
  have hRp : 0 ≤ R := by linarith
  let L := max (2*R^2) (4*M+1)
  have hL : 1 ≤ L := le_trans (by linarith) (le_max_right _ _)
  have hML : 4*M ≤ L := le_trans (by linarith) (le_max_right _ _)
  have hRL : 2*R^2 ≤ L := le_max_left _ _
  let κ := spatialEnergy (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R)
  have hr (x : E) (hx : x ∈ CKSTailVolume.tailRegion L) : 2*R^2 < ‖x‖ := hRL.trans_lt hx
  have hr3 (x : E) (hx : x ∈ CKSTailVolume.tailRegion L) : 3*R < ‖x‖ := by
    have hh := hr x hx
    nlinarith
  have hκ : ∀ x ∈ CKSTailVolume.tailRegion L, |κ x| ≤ C/(‖x‖^3*Real.sqrt ‖x‖) := by
    intro x hx
    dsimp [κ]
    rw [q.replacement_outer_energy f₀ m hRp (hr3 x hx)]
    exact hbound R h1 x (hr x hx)
  have hcont : ContinuousOn κ (CKSTailVolume.tailRegion L) := by
    intro x hx
    obtain ⟨hg,hk,hp,hs⟩ := hreg R h2 x (hr3 x hx).le
    exact (q.replacement_energy_continuousAt f₀ m hRp (hr3 x hx) hg hk hp).continuousWithinAt
  have hdx : IntegrableOn κ (CKSTailVolume.tailRegion L) volume := by
    have hh : Integrable (fun x : E => (1+‖x‖)^(-(7/2:ℝ))) volume :=
      integrable_one_add_norm (by norm_num [E,finrank_euclideanSpace])
    apply ((hh.const_mul (C*(2:ℝ)^(7/2:ℝ))).integrableOn).mono'
      (hcont.aestronglyMeasurable (CKSTailVolume.tailRegion_measurable L))
    filter_upwards [self_mem_ae_restrict (CKSTailVolume.tailRegion_measurable L)] with x hx
    rw [Real.norm_eq_abs]
    calc
      _ ≤ C/(‖x‖^3*Real.sqrt ‖x‖) := hκ x hx
      _ = C * (1/(‖x‖^3*Real.sqrt ‖x‖)) := by ring
      _ ≤ C * ((2:ℝ)^(7/2:ℝ)*(1+‖x‖)^(-(7/2:ℝ))) :=
        mul_le_mul_of_nonneg_left (CKSTailVolume.rate_le_japanese (hL.trans hx.le)) hC
      _ = _ := by ring
  have hden := CKSTailVolume.tail_density_bound hM.le (zero_lt_one.trans_le hL) hML
    (fun x hx => hF R (by linarith : 1 ≤ R) x (hr3 x hx).le)
  have hμ : (spatialVolume (q.replacementMetric f₀ m R)).restrict (CKSTailVolume.tailRegion L) ≤
      ENNReal.ofReal (Real.sqrt 2) • volume.restrict (CKSTailVolume.tailRegion L) := by
    rw [spatialVolume,restrict_withDensity (CKSTailVolume.tailRegion_measurable L),← withDensity_const]
    apply withDensity_mono
    filter_upwards [self_mem_ae_restrict (CKSTailVolume.tailRegion_measurable L)] with x hx
    apply ENNReal.ofReal_le_ofReal
    rw [q.replacement_density_tail f₀ m hR12 (hr x hx)]
    exact (hden x hx).2.2
  exact ⟨L,hRL,(hdx.smul_measure ENNReal.ofReal_ne_top).mono_measure hμ,
    fun x hx => q.replacement_momentum_tail f₀ m hR12 hx⟩
end
end CKSLorentz

end



























end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSLorentz.actual_same_end_tail_integrable.{u_1} := @OAI.CKSLorentz.actual_same_end_tail_integrable.{u_1}
