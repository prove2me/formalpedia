-- Prove2me | solution 1 for OAI.CKSSphericalChart.outer_uniform_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:58:34.653195+00:00
-- url     : https://prove2.me/submissions/ae2c9c39-19e9-4846-bb13-4e876c27d1d7

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]

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

lemma zeta_nonneg (x : ℝ) : 0 ≤ zeta x := Real.smoothTransition.nonneg _

lemma zeta_zero {x : ℝ} (hx : x ≤ 4) : zeta x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma bendingV_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (bendingV R) (Ioi 0) := by
  unfold bendingV
  have hc : ContDiffOn ℝ ∞ (fun r : ℝ => phi (r/R)) (Ioi 0) :=
    phi_smooth.comp (contDiffOn_id.div_const R) (fun r hr => div_pos hr hR)
  exact (contDiffOn_id.mul hc).mul
    ((xi_smooth.comp (contDiff_id.div_const (R^2))).contDiffOn)
lemma bendingZeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingZeta R) :=
  zeta_smooth.comp (contDiff_id.div_const R)

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

lemma expand_vec (x : E) : x = ∑ i : Ix, x i • e i := by
  ext j
  simp [e_apply]

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

lemma fderiv_expand (F : E → ℝ) (x v : E) : fderiv ℝ F x v = ∑ i, v i * grad F x i := by
  conv_lhs => rw [expand_vec v]
  simp only [map_sum, map_smul, smul_eq_mul, grad, pd]

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
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
open scoped Topology ContDiff

lemma thetaFrame_smooth : ContDiff ℝ ∞ thetaFrame := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [thetaFrame] <;> fun_prop
lemma phiUnit_smooth : ContDiff ℝ ∞ phiUnit := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> dsimp [phiUnit] <;> fun_prop
lemma phiFrame_smooth : ContDiff ℝ ∞ phiFrame := by
  unfold phiFrame
  exact ((coord 1).contDiff.sin).smul phiUnit_smooth
lemma chartVector_smooth (i : Ix) : ContDiff ℝ ∞ (chartVector i) := by
  fin_cases i
  · exact contDiff_const
  · exact thetaFrame_smooth
  · exact phiFrame_smooth

lemma angular_chain {F : E → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F (sphereParam x)) (i : Ix) :
    D (basis i) (fun y => F (sphereParam y)) x =
      ∑ k : Ix, chartVector i x k * grad F (sphereParam x) k := by
  unfold D
  change fderiv ℝ (F ∘ sphereParam) x (basis i) = _
  rw [fderiv_comp x hF (sphereParam_smooth.differentiable (by simp) x)]
  change fderiv ℝ F (sphereParam x) (fderiv ℝ sphereParam x (basis i)) = _
  rw [fderiv_sphereParam, CKSInducedSphere.fderiv_expand]

end
end CKSSphericalChart

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
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix)
open scoped Topology ContDiff

lemma D_line {F : Point → ℝ} {x : Point} (hF : DifferentiableAt ℝ F x) (v : Point) :
    D v F x = deriv (fun s : ℝ => F (x + s • v)) 0 := by
  have hd : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x using 1
    simp
  have hf : HasFDerivAt F (fderiv ℝ F x) (x + (0:ℝ) • v) := by simpa using hF.hasFDerivAt
  have hh := hf.comp_hasDerivAt 0 hd
  simpa only [zero_smul,add_zero,D,Function.comp_def] using hh.deriv.symm

lemma D_line_congr {F G : Point → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (v : Point)
    (he : ∀ s : ℝ, F (x+s•v) = G (x+s•v)) : D v F x = D v G x := by
  rw [D_line hF,D_line hG]
  congr 1
  funext s
  exact he s

lemma angular_line_radial (x : Point) (k : Ix) (hk : k ≠ 0) (s : ℝ) :
    (x+s•basis k) 0 = x 0 := by
  simp [basis,Ne.symm hk]

lemma angular_first_congr_leaf {F G : Point → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (he : ∀ y : Point, y 0 = x 0 → F y = G y) (k : Ix) (hk : k ≠ 0) :
    D (basis k) F x = D (basis k) G x := by
  apply D_line_congr hF hG
  intro s
  exact he _ (angular_line_radial x k hk s)

lemma angular_second_congr_leaf {F G : Point → ℝ} {x : Point}
    (hF : ∀ y : Point, y 0 = x 0 → ContDiffAt ℝ 2 F y)
    (hG : ∀ y : Point, y 0 = x 0 → ContDiffAt ℝ 2 G y)
    (he : ∀ y : Point, y 0 = x 0 → F y = G y)
    (i j : Ix) (hi : i ≠ 0) (hj : j ≠ 0) :
    D (basis j) (D (basis i) F) x = D (basis j) (D (basis i) G) x := by
  have hFd := (CKSCalculus.contDiffAt_D (hF x rfl) (m := 1) (by norm_num) (basis i)).differentiableAt (by norm_num)
  have hGd := (CKSCalculus.contDiffAt_D (hG x rfl) (m := 1) (by norm_num) (basis i)).differentiableAt (by norm_num)
  apply D_line_congr hFd hGd
  intro s
  have hy := angular_line_radial x j hj s
  apply angular_first_congr_leaf ((hF _ hy).differentiableAt (by norm_num))
    ((hG _ hy).differentiableAt (by norm_num)) _ i hi
  intro z hz
  exact he z (hz.trans hy)

end
end CKSSphericalChart

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
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence)
open scoped Topology ContDiff

lemma D_neg (v : Point) (f : Point → ℝ) (x : Point) :
    D v (fun y => -f y) x = -D v f x := by simp [D, fderiv_fun_neg]

def equator (x : Point) : E := WithLp.toLp 2 ![Real.cos (x 2),Real.sin (x 2),0]

lemma theta_theta (x : Point) : fderiv ℝ thetaFrame x (basis 1) = -sphereParam x := by
  ext j
  rw [component_fderiv (thetaFrame_smooth.differentiable (by simp) x)]
  have hd1 : DifferentiableAt ℝ (fun y : Point => y 1) x := (coord 1).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [thetaFrame,sphereParam]
  all_goals
    simp only [D_mul _ hd1.cos hd2.cos, D_mul _ hd1.cos hd2.sin,
      D_sin _ hd1,D_sin _ hd2,D_cos _ hd1,D_cos _ hd2,dc, D_neg,
      Fin.reduceEq,ite_true,ite_false]
    ring

lemma unit_phi (x : Point) : fderiv ℝ phiUnit x (basis 2) = -equator x := by
  ext j
  rw [component_fderiv (phiUnit_smooth.differentiable (by simp) x)]
  have hd2 : DifferentiableAt ℝ (fun y : Point => y 2) x := (coord 2).differentiableAt
  have dc (a b : Ix) : D (basis a) (fun y : Point => y b) x = if b = a then 1 else 0 := D_coord a b x
  fin_cases j <;> dsimp [phiUnit,equator]
  all_goals
    simp only [D_neg, D_sin _ hd2,D_cos _ hd2,dc,D_const, ite_true]
    ring

lemma equator_decomposition (x : Point) : equator x =
    Real.sin (x 1) • sphereParam x + Real.cos (x 1) • thetaFrame x := by
  ext i
  fin_cases i <;> dsimp [equator,sphereParam,thetaFrame]
  · linear_combination -Real.cos (x 2) * (Real.sin_sq_add_cos_sq (x 1))
  · linear_combination -Real.sin (x 2) * (Real.sin_sq_add_cos_sq (x 1))
  · ring

lemma projected_frame (x : Point) (i j : Ix) :
    proj (fun k => sphereParam x k) i j =
      thetaFrame x i * thetaFrame x j + phiUnit x i * phiUnit x j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [proj,sphereParam,thetaFrame,phiUnit,Fin.reduceEq]
  all_goals ring_nf <;> simp only [Real.sin_sq] <;> ring

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
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound
open CKSInducedSphere (E Ix e grad hess pd proj roundLaplacian sphereGradient tensorDivergence U)
open scoped Topology ContDiff

lemma sphereParam_mem (x : Point) : sphereParam x ∈ U := by
  intro h
  have hn := sphereParam_norm x
  simp [h] at hn

lemma second_eval {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {n : E} (hn : n ∈ U)
    (v w : E) : fderiv ℝ (fderiv ℝ F) n v w =
      ∑ i : Ix, ∑ j : Ix, v i * w j * hess F n i j := by
  conv_lhs => rw [CKSInducedSphere.expand_vec v, CKSInducedSphere.expand_vec w]
  simp only [map_sum,map_smul, _root_.sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum, hess, CKSInducedSphere.partial_partial hF hn]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

lemma angular_first {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : Ix) :
    (D (basis i) (fun y => F (sphereParam y))) =
      fun y => fderiv ℝ F (sphereParam y) (chartVector i y) := by
  funext x
  rw [angular_chain (CKSInducedSphere.smooth_diff hF (sphereParam_mem x)),
    CKSInducedSphere.fderiv_expand]

lemma angular_second {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (x : Point) (i j : Ix) :
    D (basis j) (D (basis i) (fun y => F (sphereParam y))) x =
      fderiv ℝ F (sphereParam x) (fderiv ℝ (chartVector i) x (basis j)) +
      fderiv ℝ (fderiv ℝ F) (sphereParam x) (chartVector j x) (chartVector i x) := by
  have hFd := hF.fderiv_of_isOpen (m := ∞) CKSInducedSphere.U_open (by simp)
  have hFc := hFd.comp_contDiff sphereParam_smooth sphereParam_mem
  have hf := CKSInducedSphere.smooth_diff hF (sphereParam_mem x)
  have hfd := (hFd.contDiffAt (CKSInducedSphere.U_open.mem_nhds (sphereParam_mem x))).differentiableAt (by simp)
  rw [angular_first hF]
  unfold D
  change fderiv ℝ (fun y => ((fderiv ℝ F) ∘ sphereParam) y (chartVector i y)) x (basis j) = _
  rw [fderiv_clm_apply (hFc.differentiable (by simp) x)
    ((chartVector_smooth i).differentiable (by simp) x)]
  change fderiv ℝ F (sphereParam x) (fderiv ℝ (chartVector i) x (basis j)) +
    fderiv ℝ ((fderiv ℝ F) ∘ sphereParam) x (basis j) (chartVector i x) = _
  rw [fderiv_comp x hfd (sphereParam_smooth.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply,fderiv_sphereParam]

lemma phi_phi (x : Point) : fderiv ℝ phiFrame x (basis 2) =
    -(Real.sin (x 1) • equator x) := by
  unfold phiFrame
  rw [fderiv_fun_smul (show DifferentiableAt ℝ (fun y : Point => Real.sin (y 1)) x from
      ((coord 1).differentiableAt).sin) (phiUnit_smooth.differentiable (by simp) x)]
  have hz : fderiv ℝ (fun y : Point => Real.sin (y 1)) x (basis 2) = 0 := by
    change D (basis 2) (fun y : Point => Real.sin (y 1)) x = 0
    rw [D_sin _ (show DifferentiableAt ℝ (fun y : Point => y 1) x from (coord 1).differentiableAt)]
    change Real.cos (x 1) * D (basis 2) (coord 1) x = 0
    rw [D_coord]
    rw [ite_eq_right (show (1 : Ix) ≠ 2 by decide)]
    ring
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, unit_phi, hz, zero_smul, add_zero, smul_neg]

lemma laplacian_frame {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (x : Point) :
    roundLaplacian F (sphereParam x) =
      fderiv ℝ (fderiv ℝ F) (sphereParam x) (thetaFrame x) (thetaFrame x) +
      fderiv ℝ (fderiv ℝ F) (sphereParam x) (phiUnit x) (phiUnit x) -
      2 * fderiv ℝ F (sphereParam x) (sphereParam x) := by
  rw [second_eval hF (sphereParam_mem x), second_eval hF (sphereParam_mem x),
    CKSInducedSphere.fderiv_expand]
  unfold roundLaplacian CKSInducedSphere.roundLap CKSInducedSphere.tangentTrace
  simp only [projected_frame,add_mul,sum_add_distrib]

theorem angular_laplacian {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (x : Point)
    (hs : Real.sin (x 1) ≠ 0) :
    D (basis 1) (D (basis 1) (fun y => F (sphereParam y))) x +
      Real.cos (x 1) / Real.sin (x 1) * D (basis 1) (fun y => F (sphereParam y)) x +
      D (basis 2) (D (basis 2) (fun y => F (sphereParam y))) x / Real.sin (x 1)^2 =
      roundLaplacian F (sphereParam x) := by
  rw [angular_second hF, angular_second hF, angular_first hF, laplacian_frame hF]
  change fderiv ℝ F (sphereParam x) (fderiv ℝ thetaFrame x (basis 1)) +
    fderiv ℝ (fderiv ℝ F) (sphereParam x) (thetaFrame x) (thetaFrame x) +
    Real.cos (x 1)/Real.sin (x 1) * fderiv ℝ F (sphereParam x) (thetaFrame x) +
    (fderiv ℝ F (sphereParam x) (fderiv ℝ phiFrame x (basis 2)) +
    fderiv ℝ (fderiv ℝ F) (sphereParam x) (phiFrame x) (phiFrame x)) / Real.sin (x 1)^2 = _
  rw [theta_theta,phi_phi,equator_decomposition]
  simp only [phiFrame,map_neg,map_add,map_smul,smul_apply,smul_eq_mul]
  field_simp
  ring

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
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics
open CKSInducedSphere (E Ix Mat U)
open scoped Topology ContDiff

lemma positiveChart_open : IsOpen positiveChart := isOpen_lt continuous_const (coord 0).continuous

lemma joint_slice {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain) (t : ℝ) :
    ContDiffOn ℝ ∞ (F t) U := by
  exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => hx)

lemma radius_comp_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun x : Point => q (x 0)) positiveChart :=
  hq.comp (coord 0).contDiff.contDiffOn (fun _ hx => hx)

lemma joint_chart_smooth {F : ℝ → E → ℝ} {t : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun x : Point => F (t (x 0)) (sphereParam x)) positiveChart :=
  hF.comp ((radius_comp_smooth ht).prodMk sphereParam_smooth.contDiffOn)
    (fun x _ => sphereParam_mem x)

lemma chartMass_smooth {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0)) :
    ContDiffOn ℝ ∞ (chartMass F t c) positiveChart :=
  (radius_comp_smooth hc).add (joint_chart_smooth hF ht)

lemma chartMass_laplace {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (hs : Real.sin (x 1) ≠ 0) :
    (massJet (chartMass F t c) x).laplace (Real.sin (x 1)) (Real.cos (x 1)) =
      CKSInducedSphere.roundLaplacian (F (t (x 0))) (sphereParam x) := by
  let G : E → ℝ := fun y => c (x 0) + F (t (x 0)) y
  have hG : ContDiffOn ℝ ∞ G U := contDiffOn_const.add (joint_slice hF _)
  have hGchart := hG.comp_contDiff sphereParam_smooth sphereParam_mem
  have hfull := chartMass_smooth hF ht hc
  have he : ∀ y : Point, y 0 = x 0 → chartMass F t c y = G (sphereParam y) := by
    intro y hy
    simp only [chartMass,G,hy]
  have hf2 (y : Point) (hy : y 0 = x 0) : ContDiffAt ℝ 2 (chartMass F t c) y :=
    (hfull.contDiffAt (positiveChart_open.mem_nhds (by change 0 < y 0; rw [hy]; exact hx))).of_le ((ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hg2 (y : Point) (_hy : y 0 = x 0) : ContDiffAt ℝ 2 (fun z => G (sphereParam z)) y :=
    hGchart.contDiffAt.of_le ((ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have h11 := angular_second_congr_leaf hf2 hg2 he (1:Ix) 1 (by decide) (by decide)
  have h22 := angular_second_congr_leaf hf2 hg2 he (2:Ix) 2 (by decide) (by decide)
  have h1 := angular_first_congr_leaf ((hf2 x rfl).differentiableAt (by norm_num))
    (hGchart.differentiable (by simp) x) he (1:Ix) (by decide)
  change D (basis 1) (D (basis 1) (chartMass F t c)) x +
    Real.cos (x 1)/Real.sin (x 1)*D (basis 1) (chartMass F t c) x +
    D (basis 2) (D (basis 2) (chartMass F t c)) x / Real.sin (x 1)^2 = _
  rw [h11,h22,h1]
  simp only [Function.comp_def]
  rw [angular_laplacian hG x hs]
  exact CKSInducedSphere.roundLaplacian_const_add _ _ _

lemma chartMass_first {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : x ∈ positiveChart) (i : Ix) (hi : i ≠ 0) :
    D (basis i) (chartMass F t c) x =
      D (basis i) (fun y => F (t (x 0)) (sphereParam y)) x := by
  have hfull := (chartMass_smooth hF ht hc).contDiffAt (positiveChart_open.mem_nhds hx)
  have hfixed := (joint_slice hF (t (x 0))).comp_contDiff sphereParam_smooth sphereParam_mem
  have he := angular_first_congr_leaf (hfull.differentiableAt (by simp))
    ((contDiff_const.add hfixed).differentiable (by simp) x)
    (G := fun y => c (x 0) + F (t (x 0)) (sphereParam y))
    (by intro y hy; simp only [chartMass,hy]) i hi
  simpa only [D, fderiv_const_add] using he

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
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere
open scoped Topology ContDiff

lemma canonicalF_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalF f₀ m z.1 z.2) heatDomain :=
  contDiffOn_const.add (jointHeatSeries_smooth _ (smoothDatum_rapid f₀ hf₀) (0,[]))

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

lemma thetaFrame_component (x : Point) (i : Ix) : |thetaFrame x i| ≤ 1 := by
  fin_cases i
  · exact (abs_mul _ _).trans_le
      ((mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans
        (Real.abs_cos_le_one _))
  · exact (abs_mul _ _).trans_le
      ((mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans
        (Real.abs_sin_le_one _))
  · simpa [thetaFrame] using Real.abs_sin_le_one (x 1)
lemma phiUnit_component (x : Point) (i : Ix) : |phiUnit x i| ≤ 1 := by
  fin_cases i
  · simpa [phiUnit] using Real.abs_sin_le_one (x 2)
  · simpa [phiUnit] using Real.abs_cos_le_one (x 2)
  · simp [phiUnit]

lemma fderiv_bound {F : E → ℝ} {y v : E} {K : ℝ}
    (hK : 0 ≤ K) (hF : ∀ i : Ix, |pd i F y| ≤ K) (hv : ∀ i : Ix, |v i| ≤ 1) :
    |fderiv ℝ F y v| ≤ 3*K := by
  rw [CKSInducedSphere.fderiv_expand]
  calc
    _ ≤ ∑ i : Ix, |v i * grad F y i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Ix, K := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul]
      simpa only [grad, mul_comm] using
        (mul_le_mul (hF i) (hv i) (abs_nonneg _) hK).trans_eq (mul_one K)
    _ = 3*K := by simp

lemma pair_bound {T : CKSInducedSphere.Mat} {v w : E} {K : ℝ}
    (hK : 0 ≤ K) (hT : ∀ i j : Ix, |T i j| ≤ K)
    (hv : ∀ i : Ix, |v i| ≤ 1) (hw : ∀ i : Ix, |w i| ≤ 1) :
    |pair T v w| ≤ 9*K := by
  unfold pair
  calc
    _ ≤ ∑ i : Ix, |∑ j : Ix, v i * w j * T i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Ix, ∑ j : Ix, |v i * w j * T i j| := sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Ix, ∑ _j : Ix, K := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [abs_mul,abs_mul]
      have hh : |v i| * |w j| ≤ 1 :=
        (mul_le_of_le_one_left (abs_nonneg _) (hv i)).trans (hw j)
      simpa only [mul_comm] using
        (mul_le_mul (hT i j) hh (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK).trans_eq
          (mul_one K)
    _ = 9*K := by simp; ring

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
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

lemma chartMass_angular_components {F : ℝ → E → ℝ} {t c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (ht : ContDiffOn ℝ ∞ t (Ioi 0)) (hc : ContDiffOn ℝ ∞ c (Ioi 0))
    {x : Point} (hx : 0 < x 0) (hs : Real.sin (x 1) ≠ 0) :
    (D (basis 1) (chartMass F t c) x = fderiv ℝ (F (t (x 0))) (sphereParam x) (thetaFrame x)) ∧
    (D (basis 2) (chartMass F t c) x / Real.sin (x 1) = fderiv ℝ (F (t (x 0))) (sphereParam x) (phiUnit x)) := by
  rw [chartMass_first hF ht hc hx 1 (by decide),chartMass_first hF ht hc hx 2 (by decide),
    angular_first (joint_slice hF _) 1,angular_first (joint_slice hF _) 2]
  simp [chartVector,phiFrame,hs]

lemma paddingMass_le_two {R r : ℝ} (hR : 1 ≤ R) (hr : R ≤ r) : paddingMass R r ≤ 2 := by
  have hRp : 0 < R := by linarith
  have hs : 1 ≤ Real.sqrt R := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hR)
  exact (paddingMass_bound hRp hr).trans ((div_le_iff₀ (Real.sqrt_pos.mpr hRp)).mpr (by linarith))

theorem outer_uniform_bounds (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ M B T : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ 0 ≤ T ∧
    ∀ R : ℝ, 12 ≤ R → ∀ x : Point, 3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
      |outerMass f₀ m R x| ≤ M ∧
      |(massJet (outerMass f₀ m R) x).laplace (Real.sin (x 1)) (Real.cos (x 1))| ≤ B ∧
      ‖sphereGrad (massJet (outerMass f₀ m R) x) (Real.sin (x 1))‖ ≤ B ∧
      outerA f₀ R x ^ 2 + (outerPhi f₀ R x / Real.sin (x 1))^2 ≤ T^2 := by
  obtain ⟨K,hK,h⟩ := canonical_uniform_data f₀ hf₀ m
  refine ⟨|m|+K+2,6*K,18*K,by positivity,by positivity,by positivity,?_⟩
  intro R hR x hr hs
  have hRp : 0 < R := by linarith
  have hrp : 0 < x 0 := by linarith
  obtain ⟨hm,hΔ,hg,hT⟩ := h (heatTime R (x 0)) (heatTime_nonneg hRp hrp) (sphereParam x) (sphereParam_norm x)
  have hf := canonicalF_joint f₀ hf₀ m
  have ht := heatTime_smooth hRp
  have hc := paddingMass_smooth hRp
  have hparts := chartMass_angular_components hf ht hc hrp hs
  have htheta : |D (basis 1) (outerMass f₀ m R) x| ≤ 3*K := by
    rw [show D (basis 1) (outerMass f₀ m R) x = _ from hparts.1]
    exact fderiv_bound hK hg (thetaFrame_component x)
  have hphi : |D (basis 2) (outerMass f₀ m R) x / Real.sin (x 1)| ≤ 3*K := by
    rw [show D (basis 2) (outerMass f₀ m R) x / Real.sin (x 1) = _ from hparts.2]
    exact fderiv_bound hK hg (phiUnit_component x)
  have ha : |outerA f₀ R x| ≤ 9*K := pair_bound hK hT (thetaFrame_component x) (thetaFrame_component x)
  have hb : |outerPhi f₀ R x / Real.sin (x 1)| ≤ 9*K := by
    change |(Real.sin (x 1) * pair _ (thetaFrame x) (phiUnit x)) / Real.sin (x 1)| ≤ _
    rw [mul_div_cancel_left₀ _ hs]
    exact pair_bound hK hT (thetaFrame_component x) (phiUnit_component x)
  refine ⟨?_,?_,?_,?_⟩
  · have hc0 := paddingMass_nonneg hRp hrp
    have hc2 := paddingMass_le_two (by linarith : 1 ≤ R) (by linarith : R ≤ x 0)
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hc0]; linarith)
  · change |(massJet (chartMass (canonicalF f₀ m) (heatTime R) (paddingMass R)) x).laplace _ _| ≤ _
    rw [chartMass_laplace hf ht hc hrp hs]
    linarith
  · have ht2 := pow_le_pow_left₀ (abs_nonneg _) htheta 2
    have hp2 := pow_le_pow_left₀ (abs_nonneg _) hphi 2
    rw [sq_abs] at ht2 hp2
    have he : ‖sphereGrad (massJet (outerMass f₀ m R) x) (Real.sin (x 1))‖^2 =
        (D (basis 1) (outerMass f₀ m R) x)^2 + (D (basis 2) (outerMass f₀ m R) x / Real.sin (x 1))^2 := by
      simp [sphereGrad,massJet,WithLp.prod_norm_sq_eq_of_L2,Real.norm_eq_abs, ← abs_div]
    nlinarith [norm_nonneg (sphereGrad (massJet (outerMass f₀ m R) x) (Real.sin (x 1)))]
  · have ha2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
    have hb2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at ha2 hb2
    nlinarith [sq_nonneg K]

end
end CKSSphericalChart

end

end OAI
end

theorem solution : type_of% @OAI.CKSSphericalChart.outer_uniform_bounds := @OAI.CKSSphericalChart.outer_uniform_bounds
