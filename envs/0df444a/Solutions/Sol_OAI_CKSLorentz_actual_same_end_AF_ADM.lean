-- Prove2me | solution 1 for OAI.CKSLorentz.actual_same_end_AF_ADM
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:25:42.426414+00:00
-- url     : https://prove2.me/submissions/d1f3bcd0-4c11-4356-8d29-fd9aaf89dfd4

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid

set_option linter.all false

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

lemma xi_zero {x : ℝ} (hx : 2 ≤ x) : xi x = 0 := by
  simp [xi,Real.smoothTransition.one_of_one_le (show 1 ≤ x-1 by linarith)]
lemma zeta_nonneg (x : ℝ) : 0 ≤ zeta x := Real.smoothTransition.nonneg _

lemma zeta_zero {x : ℝ} (hx : x ≤ 4) : zeta x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
lemma zeta_one {x : ℝ} (hx : 5 ≤ x) : zeta x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

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

lemma sphereIntegral_apply (f : C(Sphere, ℝ)) :
    sphereIntegral f = ∫ x, f x ∂surfaceMeasure := by
  change inner ℝ (toL2 1) (toL2 f) = _
  rw [toL2, MeasureTheory.ContinuousMap.inner_toLp]
  simp

lemma sphereIntegral_rotationAction (i j : Fin 3) (hij : i ≠ j) (t : ℝ) (p : Poly) :
    sphereIntegral (rotationAction i j t p) = sphereIntegral (sphereEval p) := by
  rw [sphereIntegral_apply, sphereIntegral_apply]
  simp only [rotationAction_apply i j hij]
  exact (sphereHome_measurePreserving (planeRotation i j hij t)).integral_comp
    (sphereHome (planeRotation i j hij t)).measurableEmbedding (sphereEval p)

theorem sphereIntegral_rotation (i j : Fin 3) (hij : i ≠ j) (p : Poly) :
    sphereIntegral (sphereEval (rotation i j p)) = 0 := by
  have hd := sphereIntegral.hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he : (fun t => sphereIntegral (rotationAction i j t p)) =
      fun _ => sphereIntegral (sphereEval p) := by
    funext t
    exact sphereIntegral_rotationAction i j hij t p
  change HasDerivAt (fun t => sphereIntegral (rotationAction i j t p)) _ 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 _)

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

lemma sphereEval_C (a : ℝ) : sphereEval (C a) = a • (1 : C(Sphere, ℝ)) := by
  ext x
  simp [sphereEval]

lemma sphereIntegral_constant (a : ℝ) : sphereIntegral (sphereEval (C a)) = a * sphereArea := by
  rw [sphereEval_C, map_smul]
  rfl

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
lemma paddingWeight_one {R r : ℝ} (hR : 0 < R) (hr : 2*R ≤ r) : paddingWeight R r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : 2 ≤ r/R := (le_div_iff₀ hR).mpr hr
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

lemma harmonic_sphereIntegral_zero {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) (hl : l ≠ 0) : sphereIntegral (sphereEval p) = 0 := by
  have he := congrArg (fun q => sphereIntegral (sphereEval q)) (harmonic_rotation_eigenvalue hp hΔ)
  simp only [map_add, map_smul, sphereIntegral_rotation 0 1 (by decide), sphereIntegral_rotation 0 2 (by decide),
    sphereIntegral_rotation 1 2 (by decide), smul_eq_mul, add_zero] at he
  have hc : -((l : ℝ) * ((l : ℝ) + 1)) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (Nat.cast_ne_zero.mpr hl) (by positivity))
  exact (mul_eq_zero.mp he.symm).resolve_left hc

lemma sphereHeatJet_mean_zero (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) (t : ℝ) : sphereIntegral (sphereHeatJet p a t) = 0 := by
  rw [sphereHeatJet, CKSSpectralHeat.heat_deriv _ (hp a.2),
    sphereIntegral.map_tsum (CKSSpectralHeat.term_deriv_summable _ (hp a.2) a.1 t)]
  have hz (n : ℕ) : sphereIntegral (sphereEval (rotationWord a.2 (p n))) = 0 :=
    harmonic_sphereIntegral_zero (rotationWord_harmonic (hh n).1 (hh n).2 a.2).1
      (rotationWord_harmonic (hh n).1 (hh n).2 a.2).2 (by omega)
  simp only [CKSSpectralHeat.term_deriv, map_smul, hz, smul_zero, tsum_zero]

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

lemma joint_slice {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain) (t : ℝ) :
    ContDiffOn ℝ ∞ (F t) U := by
  exact hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun x hx => hx)

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

lemma primitive_add {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    primitive a q r = primitive a q b + primitive b q r := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    (positive_interval_integrable hq ha hb) (positive_interval_integrable hq hb hr)).symm

lemma heatDensity_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    heatDensity R r = 1/(2*r) := by
  have hRp : 0 < R := by linarith
  have hz : 5 ≤ r/R := (le_div_iff₀ hRp).mpr (by nlinarith)
  simp [heatDensity,bendingV_tail hRp hr,bendingZeta,zeta_one hz]

lemma heatTime_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    heatTime R r = heatTime R (2*R^2) + (Real.log r - Real.log (2*R^2))/2 := by
  have hRp : 0 < R := by linarith
  have ha : 0 < 2*R^2 := by positivity
  have hrp := ha.trans_le hr
  change primitive (3*R) (heatDensity R) r = _
  rw [primitive_add (heatDensity_smooth hRp).continuousOn (by positivity) ha hrp]
  congr 1
  have he : primitive (2*R^2) (heatDensity R) r = primitive (2*R^2) (fun s => 1/(2*s)) r := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact heatDensity_tail hR ((uIcc_of_le hr ▸ hs).1)
  rw [he]
  have hh : primitive (2*R^2) (fun s : ℝ => 1/(2*s)) r =
      Real.log r / 2 - Real.log (2*R^2)/2 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s hs
      convert! (Real.hasDerivAt_log (ne_of_gt (positive_uIcc ha hrp hs))).div_const 2 using 1
      ring
    · apply positive_interval_integrable _ ha hrp
      exact (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
        (fun s hs => ne_of_gt (mul_pos (by norm_num) hs)))
  rw [hh]
  ring

lemma paddingMass_tail {R r : ℝ} (hR : 0 < R) (hr : 2*R ≤ r) :
    paddingMass R r = paddingMass R (2*R) + 2/Real.sqrt (2*R) - 2/Real.sqrt r := by
  have ha : 0 < 2*R := by positivity
  have hrp := ha.trans_le hr
  change primitive R (fun s => paddingWeight R s * paddingDensity s) r = _
  rw [primitive_add (paddingIntegrand_smooth R).continuousOn hR ha hrp]
  have he : primitive (2*R) (fun s => paddingWeight R s * paddingDensity s) r =
      primitive (2*R) paddingDensity r := by
    apply intervalIntegral.integral_congr
    intro s hs
    change paddingWeight R s * paddingDensity s = paddingDensity s
    rw [paddingWeight_one hR ((uIcc_of_le hr ▸ hs).1),one_mul]
  rw [he,paddingDensity_integral ha hrp]
  change paddingMass R (2*R) + _ = _
  ring

lemma paddingCharge_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (paddingMass R) atTop (𝓝 (paddingCharge R)) := by
  have hs : Tendsto (fun r : ℝ => 2/Real.sqrt r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hh : Tendsto (fun r : ℝ => paddingCharge R - 2/Real.sqrt r) atTop (𝓝 (paddingCharge R)) := by
    simpa using (tendsto_const_nhds (x := paddingCharge R)).sub hs
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2*R)] with r hr
  symm
  simpa [paddingCharge] using paddingMass_tail hR hr

lemma paddingCharge_bounds {R : ℝ} (hR : 0 < R) :
    0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R := by
  have hh := paddingCharge_limit hR
  constructor
  · apply ge_of_tendsto hh
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact paddingMass_nonneg hR hr
  · apply le_of_tendsto hh
    filter_upwards [eventually_ge_atTop R] with r hr
    exact paddingMass_bound hR hr

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
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart
open scoped Topology ContDiff

lemma eventually_norm_ge (R : ℝ) : ∀ᶠ x : E in spatialInfinity, R ≤ ‖x‖ :=
  Filter.eventually_comap.mpr ((eventually_ge_atTop R).mono (fun _radius hr _point hx => hx ▸ hr))

lemma eventually_norm_gt (R : ℝ) : ∀ᶠ x : E in spatialInfinity, R < ‖x‖ :=
  Filter.eventually_comap.mpr ((eventually_gt_atTop R).mono (fun _radius hr _point hx => hx ▸ hr))

lemma spatial_eventually_nhds {P : E → Prop} (hP : ∀ᶠ x in spatialInfinity, P x) :
    ∀ᶠ x in spatialInfinity, ∀ᶠ y in 𝓝 x, P y := by
  obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp hP)
  filter_upwards [eventually_norm_gt R] with x hx
  have ho : IsOpen {y : E | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [ho.mem_nhds hx] with y hy
  exact hR ‖y‖ hy.le y rfl

lemma spatial_pd_congr {F G : E → ℝ} (h : F =ᶠ[spatialInfinity] G) (j : Ix) :
    pd j F =ᶠ[spatialInfinity] pd j G := by
  filter_upwards [spatial_eventually_nhds h] with x hx
  exact congrArg (fun L : E →L[ℝ] ℝ => L (e j)) (Filter.EventuallyEq.fderiv_eq hx)

lemma TailRegular.pd {F : E → ℝ} (h : TailRegular F) (j : Ix) : TailRegular (pd j F) := by
  filter_upwards [h] with x hx
  exact (hx.fderiv_right (by simp)).clm_apply contDiffAt_const

lemma TailRegular.mul {F G : E → ℝ} (hF : TailRegular F) (hG : TailRegular G) :
    TailRegular (fun x => F x*G x) := by
  filter_upwards [hF,hG] with x hf hg
  exact hf.mul hg

lemma TailRegular.add {F G : E → ℝ} (hF : TailRegular F) (hG : TailRegular G) :
    TailRegular (fun x => F x+G x) := by
  filter_upwards [hF,hG] with x hf hg
  exact hf.add hg

lemma TailRegular.congr {F G : E → ℝ} (hF : TailRegular F) (he : F =ᶠ[spatialInfinity] G) :
    TailRegular G := by
  filter_upwards [hF,spatial_eventually_nhds he] with x hf he
  exact hf.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)

lemma Decay.congr {F G : E → ℝ} {d : ℝ} (hF : Decay d F) (he : F =ᶠ[spatialInfinity] G) :
    Decay d G := by
  obtain ⟨C,hC,h⟩ := hF
  refine ⟨C,hC,?_⟩
  filter_upwards [h,he] with x hx he
  simpa only [←he] using hx

lemma Decay.zero (d : ℝ) : Decay d (fun _ : E => 0) :=
  ⟨0,le_rfl,Filter.Eventually.of_forall (by intro x; simp)⟩

lemma Decay.const (c : ℝ) : Decay 0 (fun _ : E => c) :=
  ⟨|c|,abs_nonneg c,Filter.Eventually.of_forall (by intro x; simp)⟩

lemma Decay.add {F G : E → ℝ} {d : ℝ} (hF : Decay d F) (hG : Decay d G) :
    Decay d (fun x => F x+G x) := by
  obtain ⟨A,hA,ha⟩ := hF
  obtain ⟨B,hB,hb⟩ := hG
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  filter_upwards [ha,hb] with x hx hy
  exact (abs_add_le _ _).trans ((add_le_add hx hy).trans_eq (by ring))

lemma Decay.mul {F G : E → ℝ} {d e : ℝ} (hF : Decay d F) (hG : Decay e G) :
    Decay (d+e) (fun x => F x*G x) := by
  obtain ⟨A,hA,ha⟩ := hF
  obtain ⟨B,hB,hb⟩ := hG
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  filter_upwards [ha,hb,eventually_norm_gt 0] with x hx hy hr
  rw [abs_mul]
  calc
    |F x| * |G x| ≤ (A*‖x‖^(-d))*(B*‖x‖^(-e)) :=
      mul_le_mul hx hy (abs_nonneg _) (mul_nonneg hA (Real.rpow_nonneg (norm_nonneg _) _))
    _ = A*B*‖x‖^(-(d+e)) := by
      rw [neg_add,Real.rpow_add hr]
      ring

lemma Decay.weaken {F : E → ℝ} {d e : ℝ} (hF : Decay d F) (he : e ≤ d) : Decay e F := by
  obtain ⟨C,hC,h⟩ := hF
  refine ⟨C,hC,?_⟩
  filter_upwards [h,eventually_norm_ge 1] with x hx hr
  exact hx.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr (neg_le_neg he)) hC)

lemma SymbolN.congr {F G : E → ℝ} {n : ℕ} {d : ℝ} (hF : SymbolN n d F)
    (he : F =ᶠ[spatialInfinity] G) : SymbolN n d G := by
  induction n generalizing F G d with
  | zero => exact Decay.congr hF he
  | succ n ih => exact ⟨hF.1.congr he,fun j => ih (hF.2 j) (spatial_pd_congr he j)⟩

lemma SymbolN.zero (n : ℕ) (d : ℝ) : SymbolN n d (fun _ : E => 0) := by
  induction n generalizing d with
  | zero => exact Decay.zero d
  | succ n ih =>
    refine ⟨Decay.zero d,?_⟩
    intro j
    simpa only [show pd j (fun _ : E => (0:ℝ)) = (fun _ => 0) from funext (fun x => pd_const j 0 x)] using ih (d+1)

lemma SymbolN.const (n : ℕ) (c : ℝ) : SymbolN n 0 (fun _ : E => c) := by
  cases n with
  | zero => exact Decay.const c
  | succ n =>
    refine ⟨Decay.const c,?_⟩
    intro j
    simpa only [show pd j (fun _ : E => c) = (fun _ => 0) from funext (fun x => pd_const j c x),zero_add] using SymbolN.zero n 1

lemma SymbolN.weaken {F : E → ℝ} {n : ℕ} {d e : ℝ} (hF : SymbolN n d F)
    (he : e ≤ d) : SymbolN n e F := by
  induction n generalizing F d e with
  | zero => exact Decay.weaken hF he
  | succ n ih => exact ⟨hF.1.weaken he,fun j => ih (hF.2 j) (by linarith)⟩

lemma SymbolN.add {F G : E → ℝ} {n : ℕ} {d : ℝ} (rF : TailRegular F) (rG : TailRegular G)
    (hF : SymbolN n d F) (hG : SymbolN n d G) : SymbolN n d (fun x => F x+G x) := by
  induction n generalizing F G d with
  | zero => exact Decay.add hF hG
  | succ n ih =>
    refine ⟨hF.1.add hG.1,?_⟩
    intro j
    apply (ih (rF.pd j) (rG.pd j) (hF.2 j) (hG.2 j)).congr
    filter_upwards [rF,rG] with x hf hg
    exact (pd_add (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)) j).symm

lemma SymbolN.lower {F : E → ℝ} {n : ℕ} {d : ℝ} (hF : SymbolN (n+1) d F) :
    SymbolN n d F := by
  induction n generalizing F d with
  | zero => exact hF.1
  | succ n ih => exact ⟨hF.1,fun j => ih (hF.2 j)⟩

lemma SymbolN.mul {F G : E → ℝ} {n : ℕ} {d e : ℝ} (rF : TailRegular F) (rG : TailRegular G)
    (hF : SymbolN n d F) (hG : SymbolN n e G) : SymbolN n (d+e) (fun x => F x*G x) := by
  induction n generalizing F G d e with
  | zero => exact Decay.mul hF hG
  | succ n ih =>
    refine ⟨hF.1.mul hG.1,?_⟩
    intro j
    have hF' := hF.lower
    have hG' := hG.lower
    have ha := ih (rF.pd j) rG (hF.2 j) hG'
    have hb := ih rF (rG.pd j) hF' (hG.2 j)
    have hd : d+1+e = d+e+1 := by ring
    have he : d+(e+1) = d+e+1 := by ring
    rw [hd] at ha
    rw [he] at hb
    apply (ha.add ((rF.pd j).mul rG) (rF.mul (rG.pd j)) hb).congr
    filter_upwards [rF,rG] with x hf hg
    exact (pd_mul (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)) j).symm

lemma Symbol.const (c : ℝ) : Symbol 0 (fun _ : E => c) :=
  ⟨Filter.Eventually.of_forall (fun _ => contDiffAt_const),fun n => SymbolN.const n c⟩

lemma Symbol.congr {F G : E → ℝ} {d : ℝ} (hF : Symbol d F)
    (he : F =ᶠ[spatialInfinity] G) : Symbol d G :=
  ⟨hF.1.congr he,fun n => (hF.2 n).congr he⟩

lemma Symbol.add {F G : E → ℝ} {d : ℝ} (hF : Symbol d F) (hG : Symbol d G) :
    Symbol d (fun x => F x+G x) :=
  ⟨hF.1.add hG.1,fun n => (hF.2 n).add hF.1 hG.1 (hG.2 n)⟩

lemma Symbol.mul {F G : E → ℝ} {d e : ℝ} (hF : Symbol d F) (hG : Symbol e G) :
    Symbol (d+e) (fun x => F x*G x) :=
  ⟨hF.1.mul hG.1,fun n => (hF.2 n).mul hF.1 hG.1 (hG.2 n)⟩

lemma Symbol.weaken {F : E → ℝ} {d e : ℝ} (hF : Symbol d F) (he : e ≤ d) : Symbol e F :=
  ⟨hF.1,fun n => (hF.2 n).weaken he⟩

lemma Symbol.const_mul {F : E → ℝ} {d : ℝ} (hF : Symbol d F) (c : ℝ) :
    Symbol d (fun x => c*F x) := by
  simpa only [zero_add] using (Symbol.const c).mul hF

lemma Symbol.neg {F : E → ℝ} {d : ℝ} (hF : Symbol d F) : Symbol d (fun x => -F x) := by
  simpa only [neg_one_mul] using hF.const_mul (-1)

lemma Symbol.sub {F G : E → ℝ} {d : ℝ} (hF : Symbol d F) (hG : Symbol d G) :
    Symbol d (fun x => F x-G x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma pd_inverse {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x) (hne : F x ≠ 0) (j : Ix) :
    pd j (fun y => (F y)⁻¹) x = -(pd j F x)*(F x)⁻¹*(F x)⁻¹ := by
  have hh := (hasFDerivAt_inv' (𝕜 := ℝ) hne).comp x hF.hasFDerivAt
  unfold pd
  erw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  ring

lemma SymbolN.inverse {F : E → ℝ} {n : ℕ} (rF : TailRegular F) (hF : SymbolN n 0 F)
    {c : ℝ} (hc : 0 < c) (hl : ∀ᶠ x in spatialInfinity, c ≤ |F x|) :
    SymbolN n 0 (fun x => (F x)⁻¹) := by
  have hn : ∀ᶠ x in spatialInfinity, F x ≠ 0 := hl.mono (fun _ hx => abs_pos.mp (hc.trans_le hx))
  have ri : TailRegular (fun x => (F x)⁻¹) := by
    filter_upwards [rF,hn] with x hx hn
    exact hx.inv hn
  have hi : Decay 0 (fun x => (F x)⁻¹) := by
    refine ⟨c⁻¹,inv_nonneg.mpr hc.le,?_⟩
    filter_upwards [hl] with x hx
    simp only [abs_inv,neg_zero,Real.rpow_zero,mul_one]
    exact (inv_le_inv₀ (hc.trans_le hx) hc).mpr hx
  induction n with
  | zero => exact hi
  | succ n ih =>
    refine ⟨hi,?_⟩
    intro j
    have hh := ih hF.lower
    have hs := SymbolN.mul ri ri hh hh
    have hd := SymbolN.mul (rF.pd j) (ri.mul ri) (hF.2 j) hs
    have hz := SymbolN.mul (Symbol.const (-1)).1 ((rF.pd j).mul (ri.mul ri))
      (SymbolN.const n (-1)) hd
    simp only [zero_add,add_zero] at hz
    simp only [zero_add]
    apply hz.congr
    filter_upwards [rF,hn] with x hx hn
    rw [pd_inverse (hx.differentiableAt (by simp)) hn]
    ring

lemma Symbol.inverse {F : E → ℝ} (hF : Symbol 0 F) {c : ℝ} (hc : 0 < c)
    (hl : ∀ᶠ x in spatialInfinity, c ≤ |F x|) : Symbol 0 (fun x => (F x)⁻¹) := by
  refine ⟨?_,fun n => SymbolN.inverse hF.1 (hF.2 n) hc hl⟩
  filter_upwards [hF.1,hl] with x hx hl
  exact hx.inv (abs_pos.mp (hc.trans_le hl))

end
end CKSADM

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

lemma surfaceMeasure_real : surfaceMeasure.real univ = 4*Real.pi := by
  rw [← sphereArea_eq_four_pi,sphereArea,sphereIntegral_apply]
  simp

lemma canonicalF_mean (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m t : ℝ) :
    (∫ n : Sphere, canonicalF f₀ m t n ∂surfaceMeasure) = m*(4*Real.pi) := by
  let p := heatPolynomials f₀
  have hp := smoothDatum_rapid f₀ hf₀
  let q : C(Sphere,ℝ) := sphereEval (MvPolynomial.C m) + sphereHeatJet p (0,[]) t
  have he : (fun x : Sphere => canonicalF f₀ m t x) = fun x => q x := by
    funext x
    change m + jointHeatSeries p (0,[]) (t,x) = sphereEval (MvPolynomial.C m) x + sphereHeatJet p (0,[]) t x
    rw [sphereHeatJet_eq p hp]
    simp [sphereEval]
  rw [he,← sphereIntegral_apply]
  change sphereIntegral (sphereEval (MvPolynomial.C m) + sphereHeatJet p (0,[]) t) = _
  rw [map_add,sphereIntegral_constant,sphereHeatJet_mean_zero p hp (heatPolynomials_harmonic f₀),
    add_zero,sphereArea_eq_four_pi]

lemma canonicalF_continuous_sphere (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m t : ℝ) :
    Continuous (fun n : Sphere => canonicalF f₀ m t n) := by
  apply ((joint_slice (canonicalF_joint f₀ hf₀ m) t).continuousOn).comp_continuous continuous_subtype_val
  intro n
  exact ne_of_apply_ne norm (by simp)

def tailSphereMass (f₀ : C(Sphere,ℝ)) (m R r : ℝ) (n : Sphere) : ℝ :=
  paddingMass R r + canonicalF f₀ m (heatTime R r) n

lemma tailSphereMass_continuous (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R r : ℝ) :
    Continuous (tailSphereMass f₀ m R r) :=
  continuous_const.add (canonicalF_continuous_sphere f₀ hf₀ m (heatTime R r))

lemma tailSphereMass_mean (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R r : ℝ) :
    (∫ n, tailSphereMass f₀ m R r n ∂surfaceMeasure) = (m+paddingMass R r)*(4*Real.pi) := by
  unfold tailSphereMass
  rw [integral_add (integrable_const _) ((canonicalF_continuous_sphere f₀ hf₀ m _).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)),integral_const,canonicalF_mean f₀ hf₀ m,
    smul_eq_mul,surfaceMeasure_real]
  ring

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

lemma denominator_lower {F B r : ℝ} (hB : 0 ≤ B) (hF : |F| ≤ B) (hr : 4*B+1 ≤ r) :
    (1:ℝ)/2 ≤ 1-2*F/r := by
  have hrp : 0 < r := by linarith
  have hf := (le_abs_self F).trans hF
  have hh : 2*F/r ≤ (1:ℝ)/2 := (div_le_iff₀ hrp).mpr (by linarith)
  linarith

lemma rational_mass_error {F B r : ℝ} (hB : 0 ≤ B) (hF : |F| ≤ B) (hr : 4*B+1 ≤ r) :
    |F/(1-2*F/r)-F| ≤ 4*B^2/r := by
  have hrp : 0 < r := by linarith
  have hd := denominator_lower hB hF hr
  have hdp : 0 < 1-2*F/r := by linarith
  have hs : F^2 ≤ B^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg F) hB).mpr hF
  have hden : r-2*F ≠ 0 := by have hh := (le_abs_self F).trans hF; linarith
  have he : F/(1-2*F/r)-F = (2*F^2/r)/(1-2*F/r) := by
    apply (eq_div_iff hdp.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hdp.ne']
    field_simp [hrp.ne']
    ring
  rw [he,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hdp).mpr
  have hnn : 0 ≤ 4*B^2/r := by positivity
  have hh := mul_le_mul_of_nonneg_left hd hnn
  calc
    2*F^2/r ≤ 2*B^2/r := div_le_div_of_nonneg_right (by nlinarith) hrp.le
    _ = (4*B^2/r)*((1:ℝ)/2) := by ring
    _ ≤ _ := hh

def reducedEnergy (f₀ : C(Sphere,ℝ)) (m R r : ℝ) : ℝ :=
  (4*Real.pi)⁻¹ * ∫ n : Sphere,
    tailSphereMass f₀ m R r n/(1-2*tailSphereMass f₀ m R r n/r) ∂surfaceMeasure

lemma reducedEnergy_error (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R r B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ n : Sphere, |tailSphereMass f₀ m R r n| ≤ B)
    (hr : 4*B+1 ≤ r) :
    |reducedEnergy f₀ m R r-(m+paddingMass R r)| ≤ 4*B^2/r := by
  let F := tailSphereMass f₀ m R r
  have hf : Continuous F := tailSphereMass_continuous f₀ hf₀ m R r
  have hd : ∀ n : Sphere, 1-2*F n/r ≠ 0 := fun n => ne_of_gt (by
    have hh := denominator_lower hB (hF n) hr; linarith)
  have hq : Continuous (fun n => F n/(1-2*F n/r)) :=
    hf.div (continuous_const.sub ((continuous_const.mul hf).div_const r)) hd
  have hfi : Integrable F surfaceMeasure := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqi : Integrable (fun n => F n/(1-2*F n/r)) surfaceMeasure := hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn := norm_integral_le_of_norm_le_const (μ := surfaceMeasure)
    (f := fun n => F n/(1-2*F n/r)-F n)
    (Filter.Eventually.of_forall (fun n => by simpa only [Real.norm_eq_abs] using rational_mass_error hB (hF n) hr))
  rw [integral_sub hqi hfi,surfaceMeasure_real,Real.norm_eq_abs] at hn
  have hm : (∫ n : Sphere, F n ∂surfaceMeasure) = (m+paddingMass R r)*(4*Real.pi) := tailSphereMass_mean f₀ hf₀ m R r
  rw [hm] at hn
  have hc : 0 < 4*Real.pi := by positivity
  have he : reducedEnergy f₀ m R r-(m+paddingMass R r) =
      (4*Real.pi)⁻¹*((∫ n : Sphere, F n/(1-2*F n/r) ∂surfaceMeasure)-(m+paddingMass R r)*(4*Real.pi)) := by
    unfold reducedEnergy
    dsimp only [F]
    rw [mul_sub]
    congr 1
    field_simp
  rw [he,abs_mul,abs_of_pos (inv_pos.mpr hc)]
  calc
    _ ≤ (4*Real.pi)⁻¹*((4*B^2/r)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hc.le)
    _ = _ := by field_simp

theorem reducedEnergy_limit (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (reducedEnergy f₀ m R) atTop (𝓝 (m+paddingCharge R)) := by
  obtain ⟨B,hB,hbound⟩ := tailSphereMass_bound f₀ hf₀ m
  have herr : Tendsto (fun r => reducedEnergy f₀ m R r-(m+paddingMass R r)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero,Real.norm_eq_abs]
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (g := fun r : ℝ => 4*B^2/r)
    · filter_upwards [eventually_ge_atTop (3*R),eventually_ge_atTop (4*B+1)] with r hr hlarge
      exact reducedEnergy_error f₀ hf₀ m R r B hB.le (hbound R r hR hr) hlarge
    · exact tendsto_const_nhds.div_atTop tendsto_id
  have hmean := (tendsto_const_nhds (x := m)).add (paddingCharge_limit (by linarith : 0 < R))
  have hh := herr.add hmean
  simpa only [sub_add_cancel,zero_add] using hh

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

def energyIntegrand (b : E → ℝ) (x : E) : ℝ :=
  ∑ i : Ix, (∑ j : Ix, (pd j (fun y => metric b y i j) x -
    pd i (fun y => metric b y j j) x)) * normal x i

lemma pd_norm {x : E} (hx : x ≠ 0) (i : Ix) :
    pd i (fun y : E => ‖y‖) x = normal x i := by
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by norm_num)
  have hsq : pd i (fun y : E => ‖y‖^2) x = 2*‖x‖*pd i (fun y : E => ‖y‖) x := by
    rw [pd, (hn.hasFDerivAt.pow 2).fderiv]
    simp [pd]
  have hsq' : pd i (fun y : E => ‖y‖^2) x = 2*x i := by
    rw [pd,fderiv_norm_sq_apply]
    simp [smul_apply, innerSL_apply_apply,e,EuclideanSpace.inner_single_right]
  unfold normal
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).mpr
  nlinarith

lemma normal_diff {x : E} (hx : x ≠ 0) (i : Ix) :
    DifferentiableAt ℝ (fun y => normal y i) x := by
  have hi : DifferentiableAt ℝ (fun y : E => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).differentiableAt
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by norm_num)
  simpa only [normal,div_eq_mul_inv,Pi.inv_apply] using hi.fun_mul (hn.inv (norm_ne_zero_iff.mpr hx))

lemma pd_normal {x : E} (hx : x ≠ 0) (i j : Ix) :
    pd j (fun y => normal y i) x =
      ((if i = j then 1 else 0) - normal x i * normal x j) / ‖x‖ := by
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by norm_num)
  have hi : DifferentiableAt ℝ (fun y : E => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).differentiableAt
  have hh := ((hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn.hasFDerivAt).fderiv
  have hInv : pd j (fun y : E => (‖y‖)⁻¹) x = -(‖x‖^2)⁻¹ * normal x j := by
    unfold pd
    erw [hh]
    simp only [smul_apply,smul_eq_mul]
    change -((‖x‖^2)⁻¹) * pd j (fun y : E => ‖y‖) x = _
    rw [pd_norm hx]
  unfold normal
  simp_rw [div_eq_mul_inv]
  erw [pd_mul hi (hn.inv (norm_ne_zero_iff.mpr hx)),pd_coordinate,hInv]
  unfold normal
  simp only [eq_comm (a := i) (b := j),Pi.inv_apply]
  field_simp [norm_ne_zero_iff.mpr hx]
  split_ifs <;> ring

lemma normal_sq {x : E} (hx : x ≠ 0) : ∑ i : Ix, normal x i ^ 2 = 1 := by
  simp only [normal,div_pow,← Finset.sum_div]
  have hs : (∑ i : Ix, x i ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  rw [hs]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

lemma pd_metric {b : E → ℝ} {x : E} (hb : DifferentiableAt ℝ b x) (hx : x ≠ 0)
    (k i j : Ix) :
    pd k (fun y => metric b y i j) x = pd k b x * normal x i * normal x j +
      b x * (((if i = k then 1 else 0)-normal x i*normal x k)/‖x‖) * normal x j +
      b x * normal x i * (((if j = k then 1 else 0)-normal x j*normal x k)/‖x‖) := by
  have hi := normal_diff hx i
  have hj := normal_diff hx j
  unfold metric
  rw [pd, fderiv_const_add, fderiv_fun_mul (hb.fun_mul hi) hj,
    fderiv_fun_mul hb hi]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change b x * normal x i * pd k (fun y => normal y j) x +
    normal x j * (b x * pd k (fun y => normal y i) x + normal x i * pd k b x) = _
  rw [pd_normal hx,pd_normal hx]
  ring

lemma contracted_flux (b r : ℝ) (n p : Ix → ℝ) (hn : ∑ i, n i^2 = 1) (hr : r ≠ 0) :
    (∑ i : Ix, (∑ j : Ix, (
      (p j*n i*n j+b*((if i=j then 1 else 0)-n i*n j)/r*n j+
        b*n i*((if j=j then 1 else 0)-n j*n j)/r) -
      (p i*n j*n j+b*((if j=i then 1 else 0)-n j*n i)/r*n j+
        b*n j*((if j=i then 1 else 0)-n j*n i)/r))) * n i) = 2*b/r := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at hn ⊢
  norm_num [Ix, Fin.reduceEq] at hn ⊢
  simp only [show ((0:Fin 3) = 2) = False from eq_false (by decide), show ((2:Fin 3) = 0) = False from eq_false (by decide), show ((1:Fin 3) = 2) = False from eq_false (by decide), show ((2:Fin 3) = 1) = False from eq_false (by decide), if_false]
  apply (eq_div_iff hr).mpr
  field_simp
  linear_combination 2*b*hn

theorem energyIntegrand_eq {b : E → ℝ} {x : E} (hb : DifferentiableAt ℝ b x) (hx : x ≠ 0) :
    energyIntegrand b x = 2*b x/‖x‖ := by
  unfold energyIntegrand
  simp_rw [pd_metric hb hx]
  simpa only [mul_div_assoc,ite_true] using contracted_flux (b x) ‖x‖ (normal x) (fun i => pd i b x)
    (normal_sq hx) (norm_ne_zero_iff.mpr hx)

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

lemma norm_radius_sphere {r : ℝ} (hr : 0 < r) (n : Sphere) : ‖r • (n:E)‖ = r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  simp

lemma unitVector_radius {r : ℝ} (hr : 0 < r) (n : Sphere) : unitVector (r • (n:E)) = n := by
  rw [unitVector,norm_radius_sphere hr,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]

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

lemma cartMass_radius (f₀ : C(Sphere,ℝ)) (m R : ℝ) {r : ℝ} (hr : 0 < r) (n : Sphere) :
    cartMass f₀ m R (r • (n:E)) = tailSphereMass f₀ m R r n := by
  simp only [cartMass,norm_radius_sphere hr,unitVector_radius hr,tailSphereMass]

def cartB (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : E) : ℝ :=
  (1-2*cartMass f₀ m R x/‖x‖)⁻¹-1

lemma cartB_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : E} (hx : x ≠ 0)
    (hd : 1-2*cartMass f₀ m R x/‖x‖ ≠ 0) : ContDiffAt ℝ ∞ (cartB f₀ m R) x := by
  have hh := (contDiffAt_const.sub ((contDiffAt_const.mul (cartMass_smooth f₀ hf₀ m hR hx)).div
    (contDiffAt_norm ℝ hx) (norm_ne_zero_iff.mpr hx))).inv hd
  exact hh.sub contDiffAt_const

def surfaceEnergy (f₀ : C(Sphere,ℝ)) (m R r : ℝ) : ℝ :=
  r^2/(16*Real.pi) * ∫ n : Sphere, energyIntegrand (cartB f₀ m R) (r • (n:E)) ∂surfaceMeasure

lemma surfaceEnergy_eq_reduced (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m R r B : ℝ)
    (hR : 0 < R) (hB : 0 ≤ B) (hF : ∀ n : Sphere, |tailSphereMass f₀ m R r n| ≤ B)
    (hr : 4*B+1 ≤ r) : surfaceEnergy f₀ m R r = reducedEnergy f₀ m R r := by
  have hrp : 0 < r := by linarith
  unfold surfaceEnergy reducedEnergy
  rw [← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro n
  have hx : (r • (n:E)) ≠ 0 := smul_ne_zero hrp.ne' (sphere_ne_zero n)
  have hd : 0 < 1-2*cartMass f₀ m R (r • (n:E))/‖r • (n:E)‖ := by
    rw [cartMass_radius f₀ m R hrp,norm_radius_sphere hrp]
    have hh := denominator_lower hB (hF n) hr
    linarith
  dsimp only
  rw [energyIntegrand_eq ((cartB_smooth f₀ hf₀ m hR hx hd.ne').differentiableAt (by simp)) hx]
  simp only [cartB,cartMass_radius f₀ m R hrp,norm_radius_sphere hrp]
  have hd' : 1-2*tailSphereMass f₀ m R r n/r ≠ 0 := by
    simpa only [cartMass_radius f₀ m R hrp,norm_radius_sphere hrp] using hd.ne'
  have hden : r-tailSphereMass f₀ m R r n*2 ≠ 0 := by
    have hh := (le_abs_self _).trans (hF n)
    linarith
  field_simp [hrp.ne',hd',hden]
  ring_nf
  field_simp [hden]
  ring

theorem constructed_ADM_energy (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 1 ≤ R) :
    Tendsto (surfaceEnergy f₀ m R) atTop (𝓝 (m+paddingCharge R)) ∧
      0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R := by
  refine ⟨?_,paddingCharge_bounds (by linarith : 0 < R)⟩
  apply (reducedEnergy_limit f₀ hf₀ m hR).congr'
  obtain ⟨B,hB,hbound⟩ := tailSphereMass_bound f₀ hf₀ m
  filter_upwards [eventually_ge_atTop (3*R),eventually_ge_atTop (4*B+1)] with r hr hlarge
  exact (surfaceEnergy_eq_reduced f₀ hf₀ m R r B (by linarith) hB.le (hbound R r hR hr) hlarge).symm

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

lemma unitVector_component (x : E) (i : Ix) : unitVector x i = normal x i := by
  simp [unitVector,normal,div_eq_mul_inv,mul_comm]

lemma fderiv_unitVector_component {x : E} (hx : x ≠ 0) (j i : Ix) :
    (fderiv ℝ unitVector x (e j)) i =
      ((if i=j then 1 else 0)-unitVector x i*unitVector x j)/‖x‖ := by
  have hh := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).hasFDerivAt.comp x
    ((unitVector_smooth hx).differentiableAt (by simp)).hasFDerivAt
  have he : (fun y : E => unitVector y i) = (fun y => normal y i) := funext (fun y => unitVector_component y i)
  have he' := congrArg (fun L : E →L[ℝ] ℝ => L (e j)) hh.fderiv
  change pd j (fun y => unitVector y i) x = (fderiv ℝ unitVector x (e j)) i at he'
  rw [he] at he'
  have hh' : pd j (fun y => normal y i) x = (fderiv ℝ unitVector x (e j)) i := he'
  rw [← hh',pd_normal hx]
  simp only [unitVector_component]

lemma joint_fderiv_split {F : ℝ → E → ℝ} {t a : ℝ} {n v : E}
    (hF : DifferentiableAt ℝ (fun z : ℝ × E => F z.1 z.2) (t,n)) :
    fderiv ℝ (fun z : ℝ × E => F z.1 z.2) (t,n) (a,v) =
      a*td F t n + ∑ i : Ix, v i*pd i (F t) n := by
  let L := fderiv ℝ (fun z : ℝ × E => F z.1 z.2) (t,n)
  have ht := hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t n))
  have hx := hF.hasFDerivAt.comp n ((hasFDerivAt_const t n).prodMk (hasFDerivAt_id n))
  have ht' : td F t n = L (1,0) := ht.deriv
  have hx' : fderiv ℝ (F t) n v = L (0,v) := by
    erw [hx.fderiv]
    rfl
  change L (a,v) = _
  have hv : (a,v) = a • ((1:ℝ),(0:E)) + (0,v) := by simp
  rw [hv,map_add,map_smul,←ht',←hx',fderiv_expand]
  rfl

def radialHeat (F : ℝ → E → ℝ) (T a d : ℝ) (x : E) : ℝ :=
  ‖x‖ ^ (-d) * F (T+a*Real.log ‖x‖) (unitVector x)

lemma radialHeat_smooth {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (T a d : ℝ) {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (radialHeat F T a d) x := by
  have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hpow : ContDiffAt ℝ ∞ (fun y : E => ‖y‖^(-d)) x := hn.rpow_const_of_ne hr.ne'
  have ht : ContDiffAt ℝ ∞ (fun y : E => T+a*Real.log ‖y‖) x :=
    contDiffAt_const.add (contDiffAt_const.mul (hn.log hr.ne'))
  have hf := hF.contDiffAt (heatDomain_open.mem_nhds (show (T+a*Real.log ‖x‖,unitVector x) ∈ heatDomain from unitVector_ne hx))
  have hc := hf.comp x (ht.prodMk (unitVector_smooth hx))
  exact hpow.mul hc

lemma pd_log_norm {x : E} (hx : x ≠ 0) (j : Ix) :
    pd j (fun y : E => Real.log ‖y‖) x = unitVector x j/‖x‖ := by
  have hn := ((contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E => ‖y‖) x).differentiableAt (by simp)).hasFDerivAt
  rw [pd,(hn.log (norm_ne_zero_iff.mpr hx)).fderiv]
  change ‖x‖⁻¹ * pd j (fun y : E => ‖y‖) x = _
  rw [pd_norm hx,unitVector_component]
  ring

lemma pd_norm_rpow {x : E} (hx : x ≠ 0) (d : ℝ) (j : Ix) :
    pd j (fun y : E => ‖y‖^(-d)) x = ‖x‖^(-(d+1))*(-d*unitVector x j) := by
  have hn := ((contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E => ‖y‖) x).differentiableAt (by simp)).hasFDerivAt
  rw [pd,(hn.rpow_const (p := -d) (Or.inl (norm_ne_zero_iff.mpr hx))).fderiv]
  change (-d*‖x‖^(-d-1))*pd j (fun y : E => ‖y‖) x = _
  rw [pd_norm hx,unitVector_component]
  rw [show -d-1 = -(d+1) by ring]
  ring

lemma pd_heat_pullback {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (T a : ℝ) {x : E} (hx : x ≠ 0) (j : Ix) :
    pd j (fun y => F (T+a*Real.log ‖y‖) (unitVector y)) x =
      (a*unitVector x j*td F (T+a*Real.log ‖x‖) (unitVector x) +
      ∑ i : Ix, ((if i=j then 1 else 0)-unitVector x i*unitVector x j)*
        pd i (F (T+a*Real.log ‖x‖)) (unitVector x))/‖x‖ := by
  let t := T+a*Real.log ‖x‖
  let n := unitVector x
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖) x :=
    (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 _ _).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ (fun y : E => T+a*Real.log ‖y‖) x :=
    (differentiableAt_const T).add ((differentiableAt_const a).fun_mul (hn.log (norm_ne_zero_iff.mpr hx)))
  have hf := (hF.contDiffAt (heatDomain_open.mem_nhds (show (t,n) ∈ heatDomain from unitVector_ne hx))).differentiableAt (by simp)
  have hc := hf.hasFDerivAt.comp x (ht.hasFDerivAt.prodMk ((unitVector_smooth hx).differentiableAt (by simp)).hasFDerivAt)
  unfold pd
  erw [hc.fderiv]
  change fderiv ℝ (fun z : ℝ × E => F z.1 z.2) (t,n)
    (pd j (fun y => T+a*Real.log ‖y‖) x,fderiv ℝ unitVector x (e j)) = _
  rw [joint_fderiv_split hf]
  have ht' : pd j (fun y => T+a*Real.log ‖y‖) x = a*unitVector x j/‖x‖ := by
    rw [pd,fderiv_const_add,fderiv_const_mul (hn.log (norm_ne_zero_iff.mpr hx)) a]
    change a*pd j (fun y : E => Real.log ‖y‖) x = _
    rw [pd_log_norm hx]
    ring
  rw [ht']
  simp_rw [fderiv_unitVector_component hx]
  simp only [t,n]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,← add_div]
  congr 1

def radialNext (F : ℝ → E → ℝ) (a d : ℝ) (j : Ix) (t : ℝ) (n : E) : ℝ :=
  (-d*n j)*F t n + (a*n j)*td F t n +
    ∑ i : Ix, ((if i=j then 1 else 0)-n i*n j)*pd i (F t) n

lemma pd_radialHeat {F : ℝ → E → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain)
    (T a d : ℝ) {x : E} (hx : x ≠ 0) (j : Ix) :
    pd j (radialHeat F T a d) x = radialHeat (radialNext F a d j) T a (d+1) x := by
  have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  have hp := (hn.rpow_const_of_ne (p := -d) (norm_ne_zero_iff.mpr hx)).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ (fun y => F (T+a*Real.log ‖y‖) (unitVector y)) x := by
    have hh := (radialHeat_smooth hF T a 0 hx).differentiableAt (by simp)
    have he : radialHeat F T a 0 = fun y => F (T+a*Real.log ‖y‖) (unitVector y) := by
      funext y
      simp only [radialHeat, neg_zero, Real.rpow_zero, one_mul]
    rw [he] at hh
    exact hh
  unfold radialHeat
  rw [pd_mul hp hf,pd_norm_rpow hx,pd_heat_pullback hF T a hx]
  have hm : ‖x‖^(-d)/‖x‖ = ‖x‖^(-(d+1)) := by
    rw [show -(d+1) = -d-1 by ring,Real.rpow_sub (norm_pos_iff.mpr hx),Real.rpow_one]
  unfold radialNext
  rw [←hm]
  ring

lemma HeatGenerated.radialNext {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (a d : ℝ) (j : Ix) :
    HeatGenerated p (radialNext F a d j) := by
  exact ((HeatGenerated.coeff (fun n => -d*n j) (contDiffOn_const.mul (coordinate_smooth j)) hF).add
    (HeatGenerated.coeff (fun n => a*n j) (contDiffOn_const.mul (coordinate_smooth j)) (hF.time hp))).add
    (HeatGenerated.sum univ (fun i _ => HeatGenerated.coeff
      (fun n => (if i=j then 1 else 0)-n i*n j)
      (contDiffOn_const.sub ((coordinate_smooth i).mul (coordinate_smooth j))) (hF.partial hp i)))

def cartWord : List Ix → (E → ℝ) → E → ℝ
  | [], F => F
  | j::w, F => cartWord w (pd j F)

lemma pd_congr_on {s : Set E} (hs : IsOpen s) {F G : E → ℝ} (he : EqOn F G s) (j : Ix) :
    EqOn (pd j F) (pd j G) s := by
  intro x hx
  exact congrArg (fun L : E →L[ℝ] ℝ => L (e j))
    (Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hs.mem_nhds hx) (fun y hy => he hy)))

lemma cartWord_congr_on {s : Set E} (hs : IsOpen s) {F G : E → ℝ} (he : EqOn F G s) (w : List Ix) :
    EqOn (cartWord w F) (cartWord w G) s := by
  induction w generalizing F G with
  | nil => exact he
  | cons j w ih => exact ih (pd_congr_on hs he j)

theorem radialHeat_word {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (T a d : ℝ) (w : List Ix) :
    ∃ G : ℝ → E → ℝ, HeatGenerated p G ∧
      ∀ x : E, x ≠ 0 → cartWord w (radialHeat F T a d) x =
        radialHeat G T a (d+w.length) x := by
  induction w generalizing F d with
  | nil => exact ⟨F,hF,by intros; simp [cartWord]⟩
  | cons j w ih =>
    obtain ⟨G,hG,he⟩ := ih (HeatGenerated.radialNext hp hF a d j) (d+1)
    refine ⟨G,hG,?_⟩
    intro x hx
    have he' : EqOn (pd j (radialHeat F T a d)) (radialHeat (radialNext F a d j) T a (d+1)) U :=
      fun y hy => pd_radialHeat (hF.joint_smooth hp) T a d hy j
    change cartWord w (pd j (radialHeat F T a d)) x = _
    rw [cartWord_congr_on U_open he' w hx,he x hx]
    congr 1
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

theorem radialHeat_word_decay {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (T a d : ℝ) (w : List Ix) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ≠ 0 → 0 ≤ T+a*Real.log ‖x‖ →
      |cartWord w (radialHeat F T a d) x| ≤
        C*‖x‖^(-(d+w.length))*Real.exp (-6*(T+a*Real.log ‖x‖)) := by
  obtain ⟨G,hG,he⟩ := radialHeat_word hp hF T a d w
  obtain ⟨C,hC,hb⟩ := hG.decay hp
  refine ⟨C,hC,?_⟩
  intro x hx ht
  rw [he x hx,radialHeat,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hh := mul_le_mul_of_nonneg_left (hb _ ht _ (unitVector_norm hx))
    (Real.rpow_nonneg (norm_nonneg x) (-(d+w.length)))
  simpa only [Real.norm_eq_abs,mul_left_comm,mul_assoc] using hh

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

def angularPower (c : E → ℝ) (d : ℝ) (x : E) : ℝ := ‖x‖^(-d)*c (unitVector x)

def angularNext (c : E → ℝ) (d : ℝ) (j : Ix) (n : E) : ℝ :=
  (-d*n j)*c n + ∑ i : Ix, ((if i=j then 1 else 0)-n i*n j)*pd i c n

lemma angularNext_smooth {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) (j : Ix) :
    ContDiffOn ℝ ∞ (angularNext c d j) U := by
  apply ContDiffOn.add
  · exact (contDiffOn_const.mul (coordinate_smooth j)).mul hc
  · apply ContDiffOn.sum
    intro i hi
    exact (contDiffOn_const.sub ((coordinate_smooth i).mul (coordinate_smooth j))).mul
      (partial_smooth hc i)

lemma angularPower_regular {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) :
    TailRegular (angularPower c d) := by
  filter_upwards [eventually_norm_gt 0] with x hx
  have hn : x ≠ 0 := norm_pos_iff.mp hx
  have hh : ContDiffOn ℝ ∞ (fun z : ℝ × E => c z.2) heatDomain :=
    hc.comp contDiffOn_snd (fun z hz => hz)
  exact radialHeat_smooth (F := fun _ y => c y) hh 0 0 d hn

lemma angularPower_decay {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) :
    Decay d (angularPower c d) := by
  let cr := smoothRestriction c hc
  refine ⟨‖cr‖,norm_nonneg _,?_⟩
  filter_upwards [eventually_norm_gt 0] with x hx
  have hn := unitVector_norm (norm_pos_iff.mp hx)
  let s : Sphere := ⟨unitVector x,by simpa [Metric.mem_sphere,dist_zero_right] using hn⟩
  have hh : |c (unitVector x)| ≤ ‖cr‖ := cr.norm_coe_le_norm s
  rw [angularPower,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (norm_nonneg _) _)).trans_eq (mul_comm _ _)

lemma pd_angularPower {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) {x : E} (hx : x ≠ 0) (j : Ix) :
    pd j (angularPower c d) x = angularPower (angularNext c d j) (d+1) x := by
  have hh : ContDiffOn ℝ ∞ (fun z : ℝ × E => c z.2) heatDomain :=
    hc.comp contDiffOn_snd (fun z hz => hz)
  have he := pd_radialHeat (F := fun _ y => c y) hh 0 0 d hx j
  have heq : radialHeat (fun _ y => c y) 0 0 d = angularPower c d := rfl
  rw [heq] at he
  simpa only [radialHeat,radialNext,zero_mul,zero_add,add_zero,angularPower,angularNext] using he

theorem angularPower_symbol {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) :
    Symbol d (angularPower c d) := by
  refine ⟨angularPower_regular hc d,?_⟩
  intro n
  induction n generalizing c d with
  | zero => exact angularPower_decay hc d
  | succ n ih =>
    refine ⟨angularPower_decay hc d,?_⟩
    intro j
    apply (ih (angularNext_smooth hc d j) (d+1)).congr
    filter_upwards [eventually_norm_gt 0] with x hx
    exact (pd_angularPower hc d (norm_pos_iff.mp hx) j).symm

lemma norm_power_symbol (d : ℝ) : Symbol d (fun x : E => ‖x‖^(-d)) := by
  have hh := angularPower_symbol (c := fun _ => 1) contDiffOn_const d
  convert hh using 1
  funext x
  simp [angularPower]

lemma normal_symbol (i : Ix) : Symbol 0 (fun x : E => normal x i) := by
  have hh := angularPower_symbol (coordinate_smooth i) 0
  convert hh using 1
  funext x
  simp [angularPower,unitVector_component]

lemma symbol_of_words {F : E → ℝ} {d : ℝ} (hr : TailRegular F)
    (hw : ∀ w : List Ix, Decay (d+w.length) (cartWord w F)) : Symbol d F := by
  refine ⟨hr,?_⟩
  intro n
  induction n generalizing F d with
  | zero =>
    change Decay d F
    simpa only [cartWord,List.length_nil,Nat.cast_zero,add_zero] using hw []
  | succ n ih =>
    refine ⟨?_,?_⟩
    · simpa only [cartWord,List.length_nil,Nat.cast_zero,add_zero] using hw []
    · intro j
      apply ih (hr.pd j)
      intro w
      convert hw (j::w) using 1 <;> simp only [cartWord,List.length_cons,Nat.cast_add,Nat.cast_one]
      ring

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
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart CKSBending
open scoped Topology ContDiff

lemma log_heat_nonneg (T : ℝ) :
    ∀ᶠ x : E in spatialInfinity, 0 ≤ T+(1/2:ℝ)*Real.log ‖x‖ := by
  filter_upwards [eventually_norm_ge (Real.exp (-2*T)),eventually_norm_gt 0] with x hx hr
  have hlog : -2*T ≤ Real.log ‖x‖ := (Real.le_log_iff_exp_le hr).mpr hx
  linarith

lemma log_heat_exponential {r : ℝ} (hr : 0 < r) (T : ℝ) :
    Real.exp (-6*(T+(1/2:ℝ)*Real.log r)) = Real.exp (-6*T)*r^(-3:ℝ) := by
  rw [Real.rpow_def_of_pos hr,←Real.exp_add]
  congr 1
  ring

theorem radialHeat_symbol {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (T d : ℝ) :
    Symbol (d+3) (radialHeat F T (1/2) d) := by
  apply symbol_of_words
  · filter_upwards [eventually_norm_gt 0] with x hx
    exact radialHeat_smooth (hF.joint_smooth hp) T (1/2) d (norm_pos_iff.mp hx)
  · intro w
    obtain ⟨C,hC,hb⟩ := radialHeat_word_decay hp hF T (1/2) d w
    refine ⟨C*Real.exp (-6*T),mul_nonneg hC (Real.exp_pos _).le,?_⟩
    filter_upwards [eventually_norm_gt 0,log_heat_nonneg T] with x hx ht
    apply (hb x (norm_pos_iff.mp hx) ht).trans_eq
    rw [log_heat_exponential hx T]
    rw [show -(d+3+w.length) = -(d+w.length)+(-3) by ring,Real.rpow_add hx]
    ring

def tailKappa (R : ℝ) : ℝ := heatTime R (2*R^2)-Real.log (2*R^2)/2

def massHeatRemainder (f₀ : C(Sphere,ℝ)) (R : ℝ) : E → ℝ :=
  radialHeat (spatialHeat (heatPolynomials f₀) (0,[])) (tailKappa R) (1/2) 0

lemma massHeatRemainder_symbol (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (R : ℝ) :
    Symbol 3 (massHeatRemainder f₀ R) := by
  simpa only [zero_add,massHeatRemainder] using
    radialHeat_symbol (smoothDatum_rapid f₀ hf₀) (HeatGenerated.basic (0,[])) (tailKappa R) 0

lemma cartMass_tail_formula (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R) :
    cartMass f₀ m R =ᶠ[spatialInfinity] (fun x =>
      m+paddingCharge R-2*‖x‖^(-(1/2:ℝ))+massHeatRemainder f₀ R x) := by
  filter_upwards [eventually_norm_ge (2*R^2)] with x hx
  have hRp : 0 < R := by linarith
  have hx' : 2*R ≤ ‖x‖ := by nlinarith
  have hr : 0 < ‖x‖ := lt_of_lt_of_le (by positivity : 0 < 2*R) hx'
  have ht : heatTime R ‖x‖ = tailKappa R+(1/2:ℝ)*Real.log ‖x‖ := by
    rw [heatTime_tail hR hx,tailKappa]
    ring
  have hp : paddingMass R ‖x‖ = paddingCharge R-2*‖x‖^(-(1/2:ℝ)) := by
    rw [paddingMass_tail hRp hx',paddingCharge,Real.rpow_neg (norm_nonneg _),←Real.sqrt_eq_rpow]
    ring
  simp only [cartMass,ht,hp,canonicalF,massHeatRemainder,radialHeat,
    neg_zero,Real.rpow_zero,one_mul]
  ring

theorem cartMass_symbol (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) : Symbol 0 (cartMass f₀ m R) := by
  have hp := (norm_power_symbol (1/2:ℝ)).const_mul (2:ℝ)
  have hh := massHeatRemainder_symbol f₀ hf₀ R
  apply (((Symbol.const (m+paddingCharge R)).sub (hp.weaken (by norm_num))).add
    (hh.weaken (by norm_num))).congr
  exact (cartMass_tail_formula f₀ m hR).symm

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
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart CKSBending
open scoped Topology ContDiff

theorem rational_coefficient_symbol {F : E → ℝ} (hF : Symbol 0 F) :
    Symbol 1 (fun x => (1-2*F x/‖x‖)⁻¹-1) := by
  let q : E → ℝ := fun x => 2*F x/‖x‖
  have hq : Symbol 1 q := by
    have hh := (hF.const_mul 2).mul (norm_power_symbol 1)
    simpa only [zero_add,Real.rpow_neg_one,div_eq_mul_inv,q] using hh
  have hd : Symbol 0 (fun x => 1-q x) := (Symbol.const 1).sub (hq.weaken (by norm_num))
  obtain ⟨C,hC,hb⟩ := hF.2 0
  have hl : ∀ᶠ x in spatialInfinity, (1:ℝ)/2 ≤ 1-q x := by
    filter_upwards [hb,eventually_norm_ge (4*C+1)] with x hx hr
    have hh : |F x| ≤ C := by simpa only [neg_zero,Real.rpow_zero,mul_one] using hx
    exact denominator_lower hC hh hr
  have hi := hd.inverse (c := (1:ℝ)/2) (by norm_num) (hl.mono (fun x hx => hx.trans (le_abs_self _)))
  have hp := hq.mul hi
  simp only [add_zero] at hp
  apply hp.congr
  filter_upwards [hl] with x hx
  have hne : 1-q x ≠ 0 := by linarith
  change q x*(1-q x)⁻¹ = (1-q x)⁻¹-1
  field_simp
  ring

theorem cartB_symbol (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) : Symbol 1 (cartB f₀ m R) :=
  rational_coefficient_symbol (cartMass_symbol f₀ hf₀ m hR)

theorem constructed_metric_decay (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) (i j : Ix) :
    Symbol 1 (fun x => metric (cartB f₀ m R) x i j-(if i=j then 1 else 0)) := by
  have hh := ((cartB_symbol f₀ hf₀ m hR).mul (normal_symbol i)).mul (normal_symbol j)
  simp only [add_zero] at hh
  convert hh using 1
  funext x
  simp [metric]

end
end CKSADM

end

end OAI
end

section
namespace OAI

















noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise

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
lemma SourceCollarAtlas.replacement_surfaceEnergy_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R r : ℝ} (hR : 12 ≤ R)
    (hr : 2*R^2 < r) :
    spatialADMEnergy (q.replacementMetric f₀ m R) r = surfaceEnergy f₀ m R r := by
  have hrp : 0 < r := lt_of_le_of_lt (by positivity : 0 ≤ 2*R^2) hr
  unfold spatialADMEnergy surfaceEnergy energyIntegrand
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro n
  have hn : 2*R^2 < ‖r • (n:E)‖ := by rwa [norm_radius_sphere hrp]
  have he : (fun y => spatialCartesian (q.replacementMetric f₀ m R) y) =ᶠ[𝓝 (r • (n:E))]
      CKSADM.metric (cartB f₀ m R) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hn] with y hy
    exact (q.replacement_tail f₀ m hR hy).1
  have hd (i j a : Fin 3) : pd a (fun y => spatialCartesian (q.replacementMetric f₀ m R) y i j) (r • (n:E)) =
      pd a (fun y => CKSADM.metric (cartB f₀ m R) y i j) (r • (n:E)) := by
    unfold pd
    have hc : (fun y => spatialCartesian (q.replacementMetric f₀ m R) y i j) =ᶠ[𝓝 (r • (n:E))]
        (fun y => CKSADM.metric (cartB f₀ m R) y i j) :=
      he.mono (fun y hy => congrArg (fun G : AmbientMat => G i j) hy)
    rw [hc.fderiv_eq]
  simp only [hd]
lemma SourceCollarAtlas.replacement_surfaceMomentum_tail {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (m : ℝ) {R r : ℝ} (hR : 12 ≤ R)
    (hr : 2*R^2 < r) :
    spatialADMMomentum (q.replacementMetric f₀ m R) (q.replacementTensor f₀ m R) r = 0 := by
  have hrp : 0 < r := lt_of_le_of_lt (by positivity : 0 ≤ 2*R^2) hr
  have hk (n : Sphere) : spatialCartesian (q.replacementTensor f₀ m R) (r • (n:E)) = 0 := by
    have h := (q.replacement_tail f₀ m hR (x := r • (n:E)) (by rwa [norm_radius_sphere hrp])).2
    unfold spatialCartesian spatialCoefficients
    simp only [ContinuousLinearEquiv.symm_apply_apply,h]
    rfl
  ext i
  simp only [spatialADMMomentum,hk,Matrix.zero_apply,mul_zero,Finset.sum_const_zero,
    zero_mul,sub_zero,integral_zero,Pi.zero_apply]

theorem actual_same_end_AF_ADM {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    (m : ℝ) {R : ℝ} (hR : 12 ≤ R) :
    (∀ x : E, 2*R^2 < ‖x‖ → q.replacementTensor f₀ m R x = 0) ∧
    (∀ i j : Fin 3, Symbol 1 (fun x =>
      spatialCartesian (q.replacementMetric f₀ m R) x i j - (if i=j then 1 else 0))) ∧
    Tendsto (spatialADMEnergy (q.replacementMetric f₀ m R)) atTop (𝓝 (m+paddingCharge R)) ∧
    Tendsto (spatialADMMomentum (q.replacementMetric f₀ m R)
      (q.replacementTensor f₀ m R)) atTop (𝓝 0) ∧
    0 ≤ paddingCharge R ∧ paddingCharge R ≤ 2/Real.sqrt R := by
  obtain ⟨hE,hη0,hη1⟩ := constructed_ADM_energy f₀ hf₀ m (R := R) (by linarith)
  refine ⟨fun x hx => (q.replacement_tail f₀ m hR hx).2,?_,?_,?_,hη0,hη1⟩
  · intro i j
    apply (constructed_metric_decay f₀ hf₀ m hR i j).congr
    filter_upwards [eventually_norm_gt (2*R^2)] with x hx
    rw [(q.replacement_tail f₀ m hR hx).1]
  · apply hE.congr'
    filter_upwards [eventually_gt_atTop (2*R^2)] with r hr
    exact (q.replacement_surfaceEnergy_tail f₀ m hR hr).symm
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (2*R^2)] with r hr
    exact (q.replacement_surfaceMomentum_tail f₀ m hR hr).symm
end
end CKSLorentz

end




































end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSLorentz.actual_same_end_AF_ADM.{u_1} := @OAI.CKSLorentz.actual_same_end_AF_ADM.{u_1}
