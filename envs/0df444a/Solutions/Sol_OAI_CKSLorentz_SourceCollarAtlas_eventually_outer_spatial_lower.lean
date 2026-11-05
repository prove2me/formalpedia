-- Prove2me | solution 1 for OAI.CKSLorentz.SourceCollarAtlas.eventually_outer_spatial_lower
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:16:44.569442+00:00
-- url     : https://prove2.me/submissions/a5eff43e-f6ad-4c57-ade9-40d462a5f952

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

lemma phi_one {x : ℝ} (hx : x ≤ 6) : phi x = 1 := by
  simp [phi,Real.smoothTransition.zero_of_nonpos (show (x-6)/6 ≤ 0 by linarith)]

lemma phi_pos {x : ℝ} (hx : 0 < x) : 0 < phi x := by
  have h0 := Real.smoothTransition.nonneg ((x-6)/6)
  have h1 := Real.smoothTransition.le_one ((x-6)/6)
  have hp : 0 < (x⁻¹)^3 := pow_pos (inv_pos.mpr hx) _
  unfold phi
  by_cases he : Real.smoothTransition ((x-6)/6) = 0
  · simp [he]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr h1) (mul_pos (lt_of_le_of_ne h0 (Ne.symm he)) hp)
lemma phi_le_one {x : ℝ} (hx : 0 < x) : phi x ≤ 1 := by
  by_cases h6 : x ≤ 6
  · rw [phi_one h6]
  · have h1x : 1 ≤ x := by linarith
    have hi : x⁻¹ ≤ 1 := (inv_le_one₀ hx).mpr h1x
    have hp : (x⁻¹)^3 ≤ 1 := by simpa using pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hi 3
    have h0 := Real.smoothTransition.nonneg ((x-6)/6)
    have hprod := mul_le_mul_of_nonneg_left hp h0
    unfold phi
    linarith

lemma xi_nonneg (x : ℝ) : 0 ≤ xi x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma xi_le_one (x : ℝ) : xi x ≤ 1 := by unfold xi; linarith [Real.smoothTransition.nonneg (x-1)]

lemma zeta_nonneg (x : ℝ) : 0 ≤ zeta x := Real.smoothTransition.nonneg _

lemma zeta_zero {x : ℝ} (hx : x ≤ 4) : zeta x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma bendingV_nonneg {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : 0 ≤ bendingV R r :=
  mul_nonneg (mul_nonneg hr.le (phi_pos (div_pos hr hR)).le) (xi_nonneg _)
lemma bendingV_le_radius {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : bendingV R r ≤ r := by
  calc
    _ ≤ r * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left (phi_le_one (div_pos hr hR)) hr.le)
      (xi_le_one _) (xi_nonneg _) (by positivity)
    _ = r := by ring

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

lemma foliationMetric_quadratic (U : ℝ) {γ : Mat} (hγ : γ.IsHermitian) (s : Point)
    (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (foliationMetric U γ s *ᵥ v) =
      (v 0/U)^2+star (fun a : Fin 2 => v a.succ+s a*v 0) ⬝ᵥ
        (γ *ᵥ (fun a : Fin 2 => v a.succ+s a*v 0)) := by
  simp only [foliationMetric,metricBlock,Matrix.of_apply,mulVec,dotProduct,Fin.sum_univ_three,
    Fin.sum_univ_two,star_trivial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons]
  simp only [Fin.succ_zero_eq_one',Fin.succ_one_eq_two']
  rw [hermitian_real_symmetry hγ 0 1]
  ring

theorem foliationMetric_posDef {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.PosDef) (s : Point) :
    (foliationMetric U γ s).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (metricBlock_hermitian _ _ hγ.isHermitian)
  intro v hv
  change 0 < star v ⬝ᵥ (foliationMetric U γ s *ᵥ v)
  rw [foliationMetric_quadratic U hγ.isHermitian s v]
  let y : Point := fun a => v a.succ+s a*v 0
  have hy0 := hγ.posSemidef.dotProduct_mulVec_nonneg y
  by_cases h0 : v 0=0
  · have hy : y ≠ 0 := by
      intro hy
      apply hv
      ext i
      fin_cases i
      · exact h0
      · have hh := congrFun hy 0; simpa [y,h0] using hh
      · have hh := congrFun hy 1; simpa [y,h0] using hh
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (hγ.dotProduct_mulVec_pos hy)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (div_ne_zero h0 hU)) hy0

end
end CKSAngularGeometry

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

lemma heatDensity_nonneg {R r : ℝ} (hr : 0 < r) : 0 ≤ heatDensity R r := by
  exact div_nonneg (zeta_nonneg _) (by positivity)

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
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise

lemma quadratic3_eq_dot (g : AmbientMat) (v : Fin 3 → ℝ) :
    quadratic3 g v=star v ⬝ᵥ (g *ᵥ v) := by
  simp only [quadratic3,dotProduct,mulVec,star_trivial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic3_sub (g h : AmbientMat) (v : Fin 3 → ℝ) :
    quadratic3 (g-h) v=quadratic3 g v-quadratic3 h v := by
  simp only [quadratic3,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma quadratic3_bound {e : AmbientMat} {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖e‖ ≤ δ) (v : Fin 3 → ℝ) :
    |quadratic3 e v| ≤ 3*δ*(∑ i, (v i)^2) := by
  have hentry (i j : Fin 3) : |e i j| ≤ δ := by
    exact ((norm_le_pi_norm (e i) j).trans (norm_le_pi_norm e i)).trans he
  have hv (i j : Fin 3) : |v i| *|v j| ≤ ((v i)^2+(v j)^2)/2 := by
    nlinarith [sq_nonneg (|v i| -|v j|),sq_abs (v i),sq_abs (v j)]
  calc
    |quadratic3 e v| ≤ ∑ i, ∑ j, |e i j*v i*v j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, δ*((v i)^2+(v j)^2)/2 := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [abs_mul,abs_mul]
      calc
        |e i j| *|v i| *|v j| ≤ δ*(|v i| *|v j|) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg _)) (abs_nonneg _)
        _ ≤ δ*((v i)^2+(v j)^2)/2 := by nlinarith [mul_le_mul_of_nonneg_left (hv i j) hδ]
    _ = 3*δ*(∑ i, (v i)^2) := by simp [Fin.sum_univ_three]; ring

lemma quadratic3_error {g h : AmbientMat} {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖g-h‖ ≤ δ)
    (v : Fin 3 → ℝ) : |quadratic3 g v-quadratic3 h v| ≤ 3*δ*(∑ i, (v i)^2) := by
  rw [← quadratic3_sub]
  exact quadratic3_bound hδ he v

theorem metric_lower_from_coefficients {G H : AmbientMat} {δ κ : ℝ}
    (hκ : 0<κ) (hδ : 0 ≤ δ) (hclose : ‖G-H‖ ≤ δ)
    (hbackground : ∀ v, κ*(∑ i : Fin 3, (v i)^2) ≤ quadratic3 H v) :
    ∀ v, (1-3*δ/κ)*quadratic3 H v ≤ quadratic3 G v := by
  intro v
  have hlow := (abs_le.mp (quadratic3_error hδ hclose v)).1
  have hbg := hbackground v
  have hd : κ*(3*δ/κ)=3*δ := by field_simp
  have hh := mul_le_mul_of_nonneg_left hbg (show 0 ≤ 3*δ/κ by positivity)
  have he : (3*δ/κ)*(κ*(∑ i : Fin 3, (v i)^2)) = 3*δ*(∑ i : Fin 3, (v i)^2) := by
    field_simp
  rw [he] at hh
  nlinarith

lemma metric_upper_from_coefficients {g H : AmbientMat} {δ κ : ℝ}
    (hκ : 0<κ) (hδ : 0 ≤ δ) (hclose : ‖g-H‖ ≤ δ)
    (hbackground : ∀ v, κ*(∑ i : Fin 3, (v i)^2) ≤ quadratic3 H v) :
    ∀ v, quadratic3 g v ≤ (1+3*δ/κ)*quadratic3 H v := by
  intro v
  have hupper := (abs_le.mp (quadratic3_error hδ hclose v)).2
  have hbg := hbackground v
  have hd : κ*(3*δ/κ)=3*δ := by field_simp
  have hh := mul_le_mul_of_nonneg_left hbg (show 0 ≤ 3*δ/κ by positivity)
  have he : (3*δ/κ)*(κ*(∑ i : Fin 3, (v i)^2)) = 3*δ*(∑ i : Fin 3, (v i)^2) := by
    field_simp
  rw [he] at hh
  nlinarith

theorem metric_comparison_from_background {G g H : AmbientMat} {δ ε κ : ℝ}
    (hκ : 0<κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hsmall : 3*δ ≤ κ)
    (hGclose : ‖G-H‖ ≤ δ) (hgclose : ‖g-H‖ ≤ ε)
    (hbackground : ∀ v, κ*(∑ i : Fin 3, (v i)^2) ≤ quadratic3 H v) :
    ∀ v, ((1-3*δ/κ)/(1+3*ε/κ))*quadratic3 g v ≤ quadratic3 G v := by
  intro v
  have hlow := metric_lower_from_coefficients hκ hδ hGclose hbackground v
  have hupp := metric_upper_from_coefficients hκ hε hgclose hbackground v
  have hn : 0 ≤ 1-3*δ/κ := sub_nonneg.mpr ((div_le_one hκ).mpr hsmall)
  have hd : 0 < 1+3*ε/κ := by positivity
  have hh := mul_le_mul_of_nonneg_left hupp (div_nonneg hn hd.le)
  have he : (1-3*δ/κ)/(1+3*ε/κ)*((1+3*ε/κ)*quadratic3 H v)=
      (1-3*δ/κ)*quadratic3 H v := by field_simp
  rw [he] at hh
  exact hh.trans hlow

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Set
open scoped Matrix.Norms.Elementwise

lemma quadratic3_vector_smul (g : AmbientMat) (v : Fin 3 → ℝ) (c : ℝ) :
    quadratic3 g (c • v)=c^2*quadratic3 g v := by
  simp only [quadratic3,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma quadratic3_positive {g : AmbientMat} (hg : g.PosDef) {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    0 < quadratic3 g v := by
  rw [quadratic3_eq_dot]
  exact hg.dotProduct_mulVec_pos hv

lemma quadratic3_continuous_euclidean : Continuous (fun p : AmbientMat × EuclideanSpace ℝ (Fin 3) =>
    quadratic3 p.1 p.2) := by
  unfold quadratic3
  fun_prop

theorem compact_positive_quadratic_lower {K : Set AmbientMat} (hK : IsCompact K)
    (hpos : ∀ g ∈ K, g.PosDef) :
    ∃ κ : ℝ, 0<κ ∧ ∀ g ∈ K, ∀ v : Fin 3 → ℝ, κ*(∑ i, (v i)^2) ≤ quadratic3 g v := by
  let S : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere 0 1
  have hS : IsCompact S := isCompact_sphere 0 1
  have hpositive : ∀ p ∈ K ×ˢ S, 0 < quadratic3 p.1 p.2 := by
    intro p hp
    apply quadratic3_positive (hpos p.1 hp.1)
    intro hz
    have he : p.2=0 := by ext i; exact congrFun hz i
    have hn : ‖p.2‖=1 := by simpa only [S,Metric.mem_sphere,dist_zero_right] using hp.2
    simp [he] at hn
  obtain ⟨κ,hκ,hbound⟩ := (hK.prod hS).exists_forall_le' quadratic3_continuous_euclidean.continuousOn hpositive
  refine ⟨κ,hκ,?_⟩
  intro g hg v
  let V : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 v
  have hvnorm : ‖V‖^2=∑ i, (v i)^2 := EuclideanSpace.real_norm_sq_eq V
  by_cases hv : V=0
  · have hz : v=0 := by ext i; exact congrArg (fun q : EuclideanSpace ℝ (Fin 3) => q i) hv
    simp [hz,quadratic3]
  · have hn : ‖V‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hunit : ‖V‖⁻¹ • V ∈ S := by
      simp only [S,Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_norm,inv_mul_cancel₀ hn]
    have hh := hbound (g,‖V‖⁻¹ • V) ⟨hg,hunit⟩
    change κ ≤ quadratic3 g (‖V‖⁻¹ • v) at hh
    rw [quadratic3_vector_smul] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖V‖)
    have he : ‖V‖^2*((‖V‖⁻¹)^2*quadratic3 g v)=quadratic3 g v := by field_simp
    rw [he, hvnorm] at hh'
    simpa only [mul_comm] using hh'

lemma background_positive {q : Mat} (hq : q.PosDef) : (metricBlock 1 0 q).PosDef := by
  have hh := foliationMetric_posDef (U := (1:ℝ)) (by norm_num) hq (0:Point)
  simpa [foliationMetric,Pi.zero_def] using hh

theorem compact_background_lower {K : Set Mat} (hK : IsCompact K) (hpos : ∀ q ∈ K, q.PosDef) :
    ∃ κ : ℝ, 0<κ ∧ ∀ q ∈ K, ∀ v : Fin 3 → ℝ,
      κ*(∑ i, (v i)^2) ≤ quadratic3 (metricBlock 1 0 q) v := by
  have hc : Continuous (fun q : Mat => metricBlock 1 0 q) := by
    unfold metricBlock
    fun_prop
  obtain ⟨κ,hκ,hh⟩ := compact_positive_quadratic_lower (hK.image hc)
    (by rintro _ ⟨q,hq,rfl⟩; exact background_positive (hpos q hq))
  exact ⟨κ,hκ,fun q hq => hh _ ⟨q,hq,rfl⟩⟩

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise

def originalMetricCorrection (z : ℝ) (mg : Mat) (mr : ℝ) (eg : Mat) (err : ℝ) (b : Point) : AmbientMat :=
  metricBlock ((1+z^2)*(mr+z*err)) (fun a => Real.sqrt (1+z^2)*b a) (mg+z • eg)

lemma originalMetricCorrection_bound {B z mr err : ℝ} {mg eg : Mat} {b : Point}
    (hB : 0 ≤ B) (hz : |z| ≤ 1) (hmr : |mr| ≤ B) (herr : |err| ≤ B)
    (hmg : ‖mg‖ ≤ B) (heg : ‖eg‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖originalMetricCorrection z mg mr eg err b‖ ≤ 4*B := by
  have hz2 : z^2 ≤ 1 := by nlinarith [sq_abs z, abs_nonneg z]
  have hs : Real.sqrt (1+z^2) ≤ 2 := by
    have hh := Real.sq_sqrt (show 0 ≤ 1+z^2 by positivity)
    have hh' := Real.sqrt_nonneg (1+z^2)
    nlinarith
  have hr : |(1+z^2)*(mr+z*err)| ≤ 4*B := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ 1+z^2 by positivity)]
    have hh : |mr+z*err| ≤ 2*B := by
      calc |mr+z*err| ≤ |mr|+|z*err| := abs_add_le _ _
           _ = |mr|+|z| * |err| := by rw [abs_mul]
           _ ≤ B+1*B := add_le_add hmr (mul_le_mul hz herr (abs_nonneg _) (by norm_num))
           _ = 2*B := by ring
    exact (mul_le_mul (by linarith : 1+z^2 ≤ 2) hh (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hmix (a : Fin 2) : |Real.sqrt (1+z^2)*b a| ≤ 4*B := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    have ha : |b a| ≤ B := (norm_le_pi_norm b a).trans hb
    nlinarith [mul_le_mul hs ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
  have hleaf (a c : Fin 2) : |mg a c+z*eg a c| ≤ 4*B := by
    have hm : |mg a c| ≤ B := ((norm_le_pi_norm (mg a) c).trans (norm_le_pi_norm mg a)).trans hmg
    have he : |eg a c| ≤ B := ((norm_le_pi_norm (eg a) c).trans (norm_le_pi_norm eg a)).trans heg
    calc |mg a c+z*eg a c| ≤ |mg a c|+|z*eg a c| := abs_add_le _ _
         _ = |mg a c|+|z| * |eg a c| := by rw [abs_mul]
         _ ≤ B+1*B := add_le_add hm (mul_le_mul hz he (abs_nonneg _) (by norm_num))
         _ ≤ 4*B := by linarith
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro j
  fin_cases i <;> fin_cases j <;>
    simpa only [originalMetricCorrection,metricBlock,Matrix.of_apply,Real.norm_eq_abs,
      Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.head_fin_const] using
      (by first | exact hr | exact hmix 0 | exact hmix 1 | exact hleaf 0 0 |
        exact hleaf 0 1 | exact hleaf 1 0 | exact hleaf 1 1)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSAngularGeometry
open scoped Matrix.Norms.Elementwise

lemma ScaledComponentBound.value {f : Point → ℝ} {j q : ℕ} {B : ℝ} {y : Point}
    (h : ScaledComponentBound f j q B y) : |f y| ≤ B/(y 0)^q := by
  exact h [] (Nat.zero_le _)

lemma scaled_value_bound {r v B : ℝ} {n : ℕ} (hr : 0<r) (h : |v| ≤ B/r^n) :
    |r^n*v| ≤ B := by
  rw [abs_mul,abs_of_pos (pow_pos hr n)]
  simpa only [mul_comm] using (le_div_iff₀ (pow_pos hr n)).mp h

lemma originalMetric_factor {f : SourceMassFields} {y : Point} (hy : 0<y 0) :
    radialNormalize (y 0) (sourceMetric f y)-metricBlock 1 0 (f.sigma (angularProjection y)) =
      (1/(y 0))^3 • originalMetricCorrection (1/(y 0)) (f.mg (angularProjection y))
        (f.mr (angularProjection y)) ((y 0)^2 • f.eg y) ((y 0)^6*f.err y) ((y 0)^3 • f.b y) := by
  have hr := hy.ne'
  have hs : Real.sqrt (1+(y 0)^2)=(y 0)*Real.sqrt (1+(1/(y 0))^2) := by
    have he : 1+(y 0)^2=(y 0)^2*(1+(1/(y 0))^2) := by field_simp; ring
    rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hy.le]
  have hsq : Real.sqrt (1+(1/(y 0))^2)^2=1+(1/(y 0))^2 := Real.sq_sqrt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialNormalize,radialScale,sourceMetric,sourceRadialMetric,sourceGamma,
      originalMetricCorrection,metricBlock,Matrix.of_apply,hs]
  all_goals try field_simp
  all_goals try rw [Real.sq_sqrt (show 0 ≤ ((y 0)^2+1)/(y 0)^2 by positivity)]
  all_goals try field_simp
  all_goals ring

theorem originalMetric_error {f : SourceMassFields} {y : Point} {B : ℝ}
    (hy : 1 ≤ y 0) (hB : 0 ≤ B) (hmr : |f.mr (angularProjection y)| ≤ B)
    (hmg : ‖f.mg (angularProjection y)‖ ≤ B) (hb : f.ComponentBounds B y) :
    ‖radialNormalize (y 0) (sourceMetric f y)-metricBlock 1 0 (f.sigma (angularProjection y))‖ ≤
      4*B/(y 0)^3 := by
  have hr : 0<y 0 := zero_lt_one.trans_le hy
  have hz : |1/(y 0)| ≤ 1 := by rw [abs_of_pos (one_div_pos.mpr hr)]; exact (div_le_one hr).mpr hy
  have heg : ‖(y 0)^2 • f.eg y‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
    apply (pi_norm_le_iff_of_nonneg hB).mpr; intro c
    exact scaled_value_bound hr (hb.eg a c).value
  have hbb : ‖(y 0)^3 • f.b y‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr; intro a
    exact scaled_value_bound hr (hb.b a).value
  have herr := scaled_value_bound hr hb.err.value
  rw [originalMetric_factor hr,norm_smul,Real.norm_eq_abs,abs_pow,abs_of_pos (one_div_pos.mpr hr)]
  calc (1/y 0)^3* ‖originalMetricCorrection (1/y 0) (f.mg (angularProjection y))
          (f.mr (angularProjection y)) ((y 0)^2 • f.eg y) ((y 0)^6*f.err y) ((y 0)^3 • f.b y)‖
      ≤ (1/y 0)^3*(4*B) := mul_le_mul_of_nonneg_left
        (originalMetricCorrection_bound hB hz hmr herr hmg heg hbb) (by positivity)
    _ = 4*B/(y 0)^3 := by ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Elementwise

def comparisonFactor (C B κ R : ℝ) : ℝ := (1-3*C/(κ*R^3))/(1+12*B/(κ*R^3))

lemma comparisonFactor_nonneg {C B κ R : ℝ} (hB : 0 ≤ B) (hκ : 0<κ) (hR : 0<R)
    (hsmall : 3*C ≤ κ*R^3) : 0 ≤ comparisonFactor C B κ R := by
  unfold comparisonFactor
  apply div_nonneg
  · exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hsmall)
  · positivity

lemma comparisonFactor_le_one {C B κ R : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hκ : 0<κ) (hR : 0<R) : comparisonFactor C B κ R ≤ 1 := by
  unfold comparisonFactor
  have hd : 0<1+12*B/(κ*R^3) := by positivity
  apply (div_le_one hd).mpr
  have hc : 0 ≤ 3*C/(κ*R^3) := by positivity
  have hb : 0 ≤ 12*B/(κ*R^3) := by positivity
  linarith

lemma comparisonFactor_tendsto (C B κ : ℝ) :
    Tendsto (comparisonFactor C B κ) atTop (𝓝 1) := by
  have hp : Tendsto (fun R : ℝ => R^3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun R : ℝ => (R^3)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hp
  have hc : Tendsto (fun R : ℝ => 3*C/(κ*R^3)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,_root_.mul_inv_rev,mul_zero,zero_mul,mul_assoc,mul_left_comm,mul_comm] using
      (tendsto_const_nhds.mul hz : Tendsto (fun R : ℝ => (3*C/κ)*(R^3)⁻¹) atTop (𝓝 ((3*C/κ)*0)))
  have hb : Tendsto (fun R : ℝ => 12*B/(κ*R^3)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,_root_.mul_inv_rev,mul_zero,zero_mul,mul_assoc,mul_left_comm,mul_comm] using
      (tendsto_const_nhds.mul hz : Tendsto (fun R : ℝ => (12*B/κ)*(R^3)⁻¹) atTop (𝓝 ((12*B/κ)*0)))
  have hone : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hnum : Tendsto (fun R : ℝ => 1-3*C/(κ*R^3)) atTop (𝓝 (1:ℝ)) := by
    simpa only [sub_zero] using hone.sub hc
  have hden : Tendsto (fun R : ℝ => 1+12*B/(κ*R^3)) atTop (𝓝 (1:ℝ)) := by
    simpa only [add_zero] using hone.add hb
  change Tendsto (fun R : ℝ => (1-3*C/(κ*R^3))/(1+12*B/(κ*R^3))) atTop (𝓝 1)
  have h := hnum.div hden (by norm_num : (1:ℝ) ≠ 0)
  rw [div_one] at h
  exact h

lemma uniform_error {C r R : ℝ} (hC : 0 ≤ C) (hR : 0<R) (hr : R ≤ r) : C/r^3 ≤ C/R^3 := by
  exact div_le_div_of_nonneg_left hC (pow_pos hR 3) (pow_le_pow_left₀ hR.le hr 3)

lemma metric_comparison_uniform {G g H : AmbientMat} {C B κ r R : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hκ : 0<κ) (hR : 0<R) (hr : R ≤ r)
    (hsmall : 3*C ≤ κ*R^3)
    (hG : ‖G-H‖ ≤ C/r^3) (hg : ‖g-H‖ ≤ 4*B/r^3)
    (hbg : ∀ v : Fin 3 → ℝ, κ*(∑ i, (v i)^2) ≤ quadratic3 H v) :
    ∀ v, comparisonFactor C B κ R*quadratic3 g v ≤ quadratic3 G v := by
  have hGc := hG.trans (uniform_error hC hR hr)
  have hgc := hg.trans (uniform_error (by positivity : 0 ≤ 4*B) hR hr)
  have hs : 3*(C/R^3) ≤ κ := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (pow_pos hR 3)).mpr hsmall
  have hh := metric_comparison_from_background hκ (by positivity : 0 ≤ C/R^3)
    (by positivity : 0 ≤ 4*B/R^3) hs hGc hgc hbg
  have he : (1-3*(C/R^3)/κ)/(1+3*(4*B/R^3)/κ)=comparisonFactor C B κ R := by
    unfold comparisonFactor
    congr 1 <;> field_simp
    ring
  rwa [he] at hh

lemma quadratic3_radialNormalize (r : ℝ) (g : AmbientMat) (v : Fin 3 → ℝ) :
    quadratic3 (radialNormalize r g) v=quadratic3 g (fun i => radialScale r i*v i) := by
  unfold quadratic3 radialNormalize
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma radialScale_ne_zero {r : ℝ} (hr : r ≠ 0) (i : Fin 3) : radialScale r i ≠ 0 := by
  fin_cases i
  · change Real.sqrt (1+r^2) ≠ 0
    positivity
  · change 1/r ≠ 0
    exact one_div_ne_zero hr
  · change 1/r ≠ 0
    exact one_div_ne_zero hr

lemma radialNormalize_comparison {r c : ℝ} {G g : AmbientMat} (hr : r ≠ 0)
    (h : ∀ v, c*quadratic3 (radialNormalize r g) v ≤ quadratic3 (radialNormalize r G) v) :
    ∀ v, c*quadratic3 g v ≤ quadratic3 G v := by
  intro v
  have hh := h (fun i => v i/radialScale r i)
  rw [quadratic3_radialNormalize,quadratic3_radialNormalize] at hh
  have he : (fun i => radialScale r i*(v i/radialScale r i))=v := by
    funext i
    field_simp [radialScale_ne_zero hr i]
  rwa [he] at hh

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Elementwise

def outerComparisonFactor (M R : ℝ) : ℝ := 1/(1+2*M/R^3)

lemma outerComparisonFactor_pos {M R : ℝ} (hM : 0 ≤ M) (hR : 0<R) :
    0 < outerComparisonFactor M R := by unfold outerComparisonFactor; positivity

lemma outerComparisonFactor_le_one {M R : ℝ} (hM : 0 ≤ M) (hR : 0<R) :
    outerComparisonFactor M R ≤ 1 := by
  unfold outerComparisonFactor
  apply (div_le_one (by positivity)).mpr
  have : 0 ≤ 2*M/R^3 := by positivity
  linarith

lemma outerComparisonFactor_tendsto (M : ℝ) : Tendsto (outerComparisonFactor M) atTop (𝓝 1) := by
  have hp : Tendsto (fun R : ℝ => R^3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun R : ℝ => (R^3)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hp
  have hm : Tendsto (fun R : ℝ => 2*M/R^3) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hz.const_mul (2*M)
  have hd : Tendsto (fun R : ℝ => 1+2*M/R^3) atTop (𝓝 (1:ℝ)) := by
    simpa only [add_zero] using hm.const_add (1:ℝ)
  have hh := hd.inv₀ (by norm_num : (1:ℝ) ≠ 0)
  change Tendsto (fun R : ℝ => 1/(1+2*M/R^3)) atTop (𝓝 1)
  simpa only [one_div,inv_one] using hh

lemma outer_radicand_positive {r F v M : ℝ} (hr : 0<r) (hF : |F| ≤ M) (hsmall : 4*M ≤ r) :
    0 < 1+v^2-2*F/r := by
  have hF' : F ≤ M := (le_abs_self F).trans hF
  have hf : 2*F/r ≤ 1/2 := (div_le_iff₀ hr).mpr (by linarith)
  nlinarith [sq_nonneg v]

lemma outer_radial_coefficient_lower {r R F v M : ℝ}
    (hR : 1 ≤ R) (hr : R ≤ r) (hM : 0 ≤ M) (hF : |F| ≤ M)
    (hv0 : 0 ≤ v) (hv : v ≤ r) (hpos : 0 < 1+v^2-2*F/r) :
    outerComparisonFactor M R ≤ (1+r^2)/(1+v^2-2*F/r) := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hrp : 0<r := hRp.trans_le hr
  have hbase : 0<1+r^2 := by positivity
  have hden : 0<1+2*M/R^3 := by positivity
  have hF' : -M ≤ F := (abs_le.mp hF).1
  have hv2 : v^2 ≤ r^2 := pow_le_pow_left₀ hv0 hv 2
  have hR3 : R^3 ≤ r^3 := pow_le_pow_left₀ hRp.le hr 3
  have hrad : R^3 ≤ r*(1+r^2) := by nlinarith
  have hratio : 2*M/r ≤ (1+r^2)*(2*M/R^3) := by
    apply (div_le_iff₀ hrp).mpr
    have he : (1+r^2)*(2*M/R^3)*r=(2*M)*(r*(1+r^2))/R^3 := by ring
    rw [he]
    apply (le_div_iff₀ (pow_pos hRp 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrad (show 0 ≤ 2*M by positivity)]
  have hupper : 1+v^2-2*F/r ≤ (1+r^2)*(1+2*M/R^3) := by
    have hFdiv : -(2*F/r) ≤ 2*M/r := by
      simpa only [neg_div] using div_le_div_of_nonneg_right (show -(2*F) ≤ 2*M by linarith) hrp.le
    nlinarith
  unfold outerComparisonFactor
  apply (div_le_div_iff₀ hden hpos).mpr
  nlinarith

lemma radialNormalize_round {r u : ℝ} (hr : r ≠ 0) (q : Mat) :
    radialNormalize r (foliationMetric u (r^2 • q) 0)=metricBlock ((1+r^2)/u^2) 0 q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialNormalize,radialScale,foliationMetric,metricBlock,Matrix.of_apply,Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring_nf
  all_goals rw [Real.sq_sqrt (show 0 ≤ 1+r^2 by positivity)]
  all_goals ring

lemma quadratic3_block_diagonal (a : ℝ) (q : Mat) (v : Fin 3 → ℝ) :
    quadratic3 (metricBlock a 0 q) v=a*(v 0)^2+
      (star (fun i : Fin 2 => v i.succ)) ⬝ᵥ (q *ᵥ (fun i => v i.succ)) := by
  simp [quadratic3,metricBlock,Matrix.of_apply,dotProduct,mulVec,Fin.sum_univ_three,Fin.sum_univ_two]
  ring

lemma outer_metric_lower {r R F v M : ℝ} {q : Mat}
    (hR : 1 ≤ R) (hr : R ≤ r) (hM : 0 ≤ M) (hF : |F| ≤ M)
    (hv0 : 0 ≤ v) (hv : v ≤ r) (hpos : 0 < 1+v^2-2*F/r) (hq : q.PosDef) :
    ∀ w : Fin 3 → ℝ,
    outerComparisonFactor M R*quadratic3 (metricBlock 1 0 q) w ≤
      quadratic3 (radialNormalize r (foliationMetric (Real.sqrt (1+v^2-2*F/r)) (r^2 • q) 0)) w := by
  have hrp : 0<r := (zero_lt_one.trans_le hR).trans_le hr
  have hc := outerComparisonFactor_le_one hM (zero_lt_one.trans_le hR)
  have hrad := outer_radial_coefficient_lower hR hr hM hF hv0 hv hpos
  intro w
  rw [radialNormalize_round hrp.ne',Real.sq_sqrt hpos.le,quadratic3_block_diagonal,quadratic3_block_diagonal]
  have hq0 := hq.posSemidef.dotProduct_mulVec_nonneg (fun i : Fin 2 => w i.succ)
  nlinarith [mul_le_mul_of_nonneg_right hrad (sq_nonneg (w 0)),
    mul_le_mul_of_nonneg_right hc hq0]

end
end CKSAngularGeometry

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
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma spatialDirection_val {x : E} (hx : x ≠ 0) : (spatialDirection x : E) = normalizeAmbient x := by
  simp [spatialDirection,hx]

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

end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

lemma slice_exp_log_projection {y : CKSMixedGeometry.Point} (hy : 0 < y 0) :
    slice (Real.exp (Real.log (y 0))) (angularProjection y) = y := by
  rw [Real.exp_log hy,slice_projection]
lemma logRadiusChart_slice_exp (ρ : ℝ) (a : Angle) :
    logRadiusChart (slice ρ a) = slice (Real.exp ρ) a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart,Fin.succ_ne_zero]

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
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixThreeJets_value_bound {q : Point → Mat} {x : Point} {B : ℝ}
    (hB : 0 ≤ B) (hq : ‖matrixThreeJets q x‖ ≤ B) : ‖q x‖ ≤ B := by
  apply (pi_norm_le_iff_of_nonneg hB).mpr; intro i
  apply (pi_norm_le_iff_of_nonneg hB).mpr; intro j
  exact (norm_fst_le ((matrixThreeJets q x i j).1)).trans
    ((norm_fst_le (matrixThreeJets q x i j)).trans
      ((Matrix.norm_entry_le_entrywise_sup_norm (matrixThreeJets q x)).trans hq))

lemma actualScalarJet_value_bound {q : Point → ℝ} {x : Point} {B : ℝ}
    (hq : ‖actualScalarJet q x‖ ≤ B) : |q x| ≤ B :=
  (norm_fst_le (actualScalarJet q x)).trans hq

end
end CKSMixedGeometry

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

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma polarLift_quadratic (P : SmoothAngularPatch) (F : CKSMixedGeometry.Point → AmbientMat)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (v : E) :
    polarLift P F (polarParam P y) v v = quadratic3 (F y) (fderiv ℝ (polarInverse P) (polarParam P y) v) := by
  unfold polarLift
  rw [polarInverse_param P hr hy]
  change CKSTangentCoefficients.matrixBilinear (F y)
    (fderiv ℝ (polarInverse P) (polarParam P y) v)
    (fderiv ℝ (polarInverse P) (polarParam P y) v) = _
  exact CKSTangentCoefficients.matrixBilinear_apply _ _ _

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
open Set Filter MeasureTheory CKSSphericalHarmonics CKSSphericalChart CKSBending CKSInducedSphere
open scoped Topology ContDiff

lemma unitVector_norm {x : E} (hx : x ≠ 0) : ‖unitVector x‖ = 1 := by
  simpa only [unitVector,Metric.mem_sphere,dist_zero_right] using normalize_mem_sphere x hx

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
lemma cartMass_uniform_bound (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ R : ℝ, 1 ≤ R → ∀ x : E, 3*R ≤ ‖x‖ →
      |cartMass f₀ m R x| ≤ B := by
  obtain ⟨B,hB,hbound⟩ := tailSphereMass_bound f₀ hf₀ m
  refine ⟨B,hB,?_⟩
  intro R hR x hx
  have hxp : x ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖x‖)
  let n : Sphere := ⟨unitVector x, by simpa only [Metric.mem_sphere,dist_zero_right] using unitVector_norm hxp⟩
  exact hbound R ‖x‖ hR hx n

end
end CKSCartesianOuter

end













noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma pair_add_matrix (A B : AmbientMat) (v w : E) : pair (A+B) v w=pair A v w+pair B v w := by
  simp [pair,mul_add,Finset.sum_add_distrib]
lemma pair_smul_matrix (c : ℝ) (A : AmbientMat) (v w : E) : pair (c • A) v w=c*pair A v w := by
  simp only [pair,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma pair_rankOne (n : Fin 3 → ℝ) (v w : E) :
    pair (vecMulVec n n) v w=(∑ i,n i*v i)*(∑ i,n i*w i) := by
  simp only [pair,Matrix.vecMulVec_apply,Fin.sum_univ_three]
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
lemma euclidean_inner_sum (v w : E) : inner ℝ v w = ∑ i : Fin 3, v i*w i := by
  simp [PiLp.inner_apply,RCLike.inner_apply,mul_comm]
lemma spatialMatrix_radial (a b : ℝ) (n v w : E) :
    pair (b • (1 : AmbientMat) + (a-b) • Matrix.vecMulVec (fun i => n i) (fun i => n i)) v w =
      b * inner ℝ v w + (a-b)*inner ℝ n v*inner ℝ n w := by
  rw [pair_add_matrix,pair_smul_matrix,pair_smul_matrix,pair_one,pair_rankOne]
  simp only [euclidean_inner_sum]
  ring
lemma normal_polarParam (P : SmoothAngularPatch) {y : CKSMixedGeometry.Point} (hr : 0 < y 0) :
    CKSADM.normal (polarParam P y) = fun i => P.param (angularProjection y) i := by
  funext i
  rw [CKSADM.normal,polarParam_norm P hr.le]
  change (y 0 * P.param (angularProjection y) i) / y 0 = _
  field_simp
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
open scoped Matrix.Norms.Elementwise
lemma radial_matrix_polar (P : SmoothAngularPatch) (F : E → AmbientMat) (a b : ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hF : F (polarParam P y) = b • (1:AmbientMat) + (a-b) •
      Matrix.vecMulVec (CKSADM.normal (polarParam P y)) (CKSADM.normal (polarParam P y))) :
    (fun i j => polarTensorComponents P (spatialMatrix F) i j y) =
      CKSAngularGeometry.metricBlock a 0 ((b*(y 0)^2) • angularRoundMetric P.param (angularProjection y)) := by
  have hn : ‖P.param (angularProjection y)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using P.param_sphere (angularProjection y)
  have hi : inner ℝ (P.param (angularProjection y)) (P.param (angularProjection y)) = 1 := by
    rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have ht := P.param_tangent hy
  have happ (i j : Fin 3) : polarTensorComponents P (spatialMatrix F) i j y =
      b * inner ℝ (fderiv ℝ (polarParam P) y (CKSMixedGeometry.basis i))
        (fderiv ℝ (polarParam P) y (CKSMixedGeometry.basis j)) +
      (a-b) * inner ℝ (P.param (angularProjection y)) (fderiv ℝ (polarParam P) y (CKSMixedGeometry.basis i)) *
        inner ℝ (P.param (angularProjection y)) (fderiv ℝ (polarParam P) y (CKSMixedGeometry.basis j)) := by
    change spatialMatrix F (polarParam P y) _ _ = _
    rw [spatialMatrix_apply,hF,normal_polarParam P hr,spatialMatrix_radial]
  ext i j
  rw [happ]
  refine Fin.cases ?_ (fun c => ?_) i
  · refine Fin.cases ?_ (fun d => ?_) j
    · rw [polarParam_fderiv_radial P hy,hi]
      simp [CKSAngularGeometry.metricBlock]
    · rw [polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      fin_cases d <;> simp [CKSAngularGeometry.metricBlock,real_inner_smul_right,ht]
  · refine Fin.cases ?_ (fun d => ?_) j
    · rw [polarParam_fderiv_angular P hy,polarParam_fderiv_radial P hy]
      have htc : inner ℝ (fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis c)) (P.param (angularProjection y)) = 0 := by
        rw [real_inner_comm]; exact ht _
      fin_cases c <;> simp_all [CKSAngularGeometry.metricBlock,real_inner_smul_left,real_inner_smul_right]
    · rw [polarParam_fderiv_angular P hy,polarParam_fderiv_angular P hy]
      simp only [real_inner_smul_left,real_inner_smul_right,ht,mul_zero,add_zero]
      fin_cases c <;> fin_cases d <;>
        simp [CKSAngularGeometry.metricBlock,angularRoundMetric,pow_two,mul_assoc]
end
end CKSLorentz

end
















































noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics CKSBending Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma cartesian_metric_polar_block (P : SmoothAngularPatch) (f₀ : C(Sphere,ℝ)) (m R : ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (fun i j => polarTensorComponents P (spatialMatrix (CKSCartesianOuter.metric f₀ m R)) i j y) =
      metricBlock (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 0
        (y 0^2 • angularRoundMetric P.param (angularProjection y)) := by
  simpa only [one_mul] using radial_matrix_polar P (CKSCartesianOuter.metric f₀ m R)
    (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 1 hr hy (by simp [CKSCartesianOuter.metric])
lemma generic_outer_background_lower (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R ≥ R₀, 0 < l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ (P : SmoothAngularPatch) (y : CKSMixedGeometry.Point),
        3*R ≤ y 0 → angularProjection y ∈ P.chart.target →
        ∀ v : Fin 3 → ℝ,
          l R * quadratic3 (metricBlock 1 0 (angularRoundMetric P.param (angularProjection y))) v ≤
          quadratic3 (radialNormalize (y 0) (fun i j => polarTensorComponents P
            (spatialMatrix (CKSCartesianOuter.metric f₀ m R)) i j y)) v := by
  obtain ⟨M,hM,hbound⟩ := CKSCartesianOuter.cartMass_uniform_bound f₀ hf₀ m
  refine ⟨max 12 (4*M),le_max_left _ _,outerComparisonFactor M,
    outerComparisonFactor_tendsto M,?_,?_⟩
  · intro R hR
    have hRp : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ)<12) ((le_max_left _ _).trans hR)
    exact ⟨outerComparisonFactor_pos hM.le hRp,outerComparisonFactor_le_one hM.le hRp⟩
  intro R hR P y hr hy
  have hR12 : 12 ≤ R := (le_max_left _ _).trans hR
  have hRM : 4*M ≤ R := (le_max_right _ _).trans hR
  have hRp : 0 < R := by linarith
  have hrp : 0 < y 0 := by linarith
  have hmass := hbound R (by linarith) (polarParam P y) (by rwa [polarParam_norm P hrp.le])
  have hp := outer_radicand_positive hrp hmass (by linarith : 4*M ≤ y 0) (v := bendingV R (y 0))
  rw [cartesian_metric_polar_block P f₀ m R hrp hy]
  have he : metricBlock (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 0
      (y 0^2 • angularRoundMetric P.param (angularProjection y)) =
      foliationMetric (Real.sqrt (1+bendingV R (y 0)^2-2*CKSADM.cartMass f₀ m R (polarParam P y)/(y 0)))
        (y 0^2 • angularRoundMetric P.param (angularProjection y)) 0 := by
    rw [foliationMetric]
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero,
      CKSCartesianOuter.radicand,polarParam_norm P hrp.le,Real.sq_sqrt hp.le,one_div]
    rfl
  rw [he]
  exact outer_metric_lower (by linarith) (by linarith) hM.le hmass
    (bendingV_nonneg hRp hrp) (bendingV_le_radius hRp hrp) hp (P.roundMetric_posDef hy)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma SourceCollarAtlas.eventually_outer_local_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ l : ℝ → ℝ,
      Tendsto l atTop (𝓝 1) ∧ (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ i y, 3*R ≤ y 0 → angularProjection y ∈ (q.patch i).region →
        ∀ v : Fin 3 → ℝ,
        l R * quadratic3 (sourceMetric (q.patch i).fields.base y) v ≤
          quadratic3 (fun a b => polarTensorComponents (q.patch i).patch
            (spatialMatrix (CKSCartesianOuter.metric f₀ m R)) a b y) v := by
  obtain ⟨R₁,hR₁,l,hl,hlb,houter⟩ := generic_outer_background_lower f₀ hf₀ m
  let val : CKSMixedGeometry.MatrixThreeJet → CKSAngularGeometry.Mat := fun q i j => (q i j).1.1
  have hv : Continuous val := by unfold val; fun_prop
  obtain ⟨κ,hκ,hlower⟩ := compact_background_lower (q.jetSet_compact.image hv)
    (by rintro _ ⟨d,hd,rfl⟩; exact q.jetSet_positive d hd)
  refine ⟨max R₁ (q.radius+1),hR₁.trans (le_max_left _ _),
    lt_of_lt_of_le (by linarith) (le_max_right _ _),fun R => l R*comparisonFactor 0 q.bound κ R,?_,?_,?_⟩
  · simpa only [mul_one] using hl.mul (comparisonFactor_tendsto 0 q.bound κ)
  · intro R hR
    have h1 := (le_max_left R₁ (q.radius+1)).trans hR
    have hRp : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ)<12) (hR₁.trans h1)
    have hn := comparisonFactor_nonneg q.bound_nonneg hκ hRp
      (by simpa only [mul_zero] using (mul_nonneg hκ.le (pow_nonneg hRp.le 3)) : 3*(0:ℝ) ≤ κ*R^3)
    have ht := comparisonFactor_le_one (le_refl (0:ℝ)) q.bound_nonneg hκ hRp
    exact ⟨mul_nonneg (hlb R h1).1.le hn,
      (mul_le_mul_of_nonneg_left ht (hlb R h1).1.le).trans (by simpa using (hlb R h1).2)⟩
  intro R hR i y hr hw
  have h1 := (le_max_left R₁ (q.radius+1)).trans hR
  have hR12 : 12 ≤ R := hR₁.trans h1
  have hRp : 0 < R := by linarith
  have hrp : 0 < y 0 := by linarith
  have hqr : q.radius < y 0 := by have := (le_max_right R₁ (q.radius+1)).trans hR; linarith
  have hlog : logRadiusChart (slice (Real.log (y 0)) (angularProjection y)) = y :=
    (logRadiusChart_slice_exp _ _).trans (slice_exp_log_projection hrp)
  obtain ⟨hm,hσ,hmg,hmk,hmr,hb⟩ := q.bounds i (angularProjection y) hw (Real.log (y 0))
  have hb' := hb (by rwa [Real.exp_log hrp])
  rw [hlog] at hb'
  have hg0 : ‖(q.patch i).fields.base.mg (angularProjection y)‖ ≤ q.bound := by
    simpa only [angularLift,angularProjection_slice] using
      matrixThreeJets_value_bound (q:=angularLift (q.patch i).fields.base.mg)
        (x:=slice (Real.log (y 0)) (angularProjection y)) q.bound_nonneg hmg
  have hmr0 : |(q.patch i).fields.base.mr (angularProjection y)| ≤ q.bound := by
    simpa only [angularLift,angularProjection_slice] using
      actualScalarJet_value_bound (q:=angularLift (q.patch i).fields.base.mr)
        (x:=slice (Real.log (y 0)) (angularProjection y)) hmr
  have hg := originalMetric_error (f:=(q.patch i).fields.base) (y:=y)
    (by linarith) q.bound_nonneg hmr0 hg0 hb'.base
  have hbase : ∀ v : Fin 3 → ℝ, κ*(∑ j, (v j)^2) ≤
      quadratic3 (metricBlock 1 0 ((q.patch i).fields.base.sigma (angularProjection y))) v := by
    have h := hlower _ ⟨_,hm,rfl⟩
    simpa only [val,CKSMixedGeometry.matrixThreeJets,CKSMixedGeometry.actualThreeJet,CKSMixedGeometry.actualScalarJet,angularLift,angularProjection_slice] using h
  have hcomp := metric_comparison_uniform (C:=0)
    (G:=metricBlock 1 0 ((q.patch i).fields.base.sigma (angularProjection y)))
    (le_refl (0:ℝ)) q.bound_nonneg hκ hRp (by linarith : R ≤ y 0)
    (by simpa only [mul_zero] using (mul_nonneg hκ.le (pow_nonneg hRp.le 3)) : 3*(0:ℝ) ≤ κ*R^3)
    (by simp) hg hbase
  have hout := houter R h1 (q.patch i).patch y hr ((q.patch i).region_target hw)
  apply radialNormalize_comparison hrp.ne'
  intro v
  calc
    (l R*comparisonFactor 0 q.bound κ R)*quadratic3 (radialNormalize (y 0)
        (sourceMetric (q.patch i).fields.base y)) v =
      l R*(comparisonFactor 0 q.bound κ R*quadratic3 (radialNormalize (y 0)
        (sourceMetric (q.patch i).fields.base y)) v) := by ring
    _ ≤ l R*quadratic3 (metricBlock 1 0 ((q.patch i).fields.base.sigma (angularProjection y))) v :=
      mul_le_mul_of_nonneg_left (hcomp v) (hlb R h1).1.le
    _ ≤ _ := hout v
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma polar_spatial_quadratic (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (v : E) :
    A (polarParam P y) v v = quadratic3 (fun i j => polarTensorComponents P A i j y)
      (fderiv ℝ (polarInverse P) (polarParam P y) v) := by
  have he := (polarLift_reconstruction P (fun z i j => polarTensorComponents P A i j z) hr hy).2 A
    (fun _ _ => rfl)
  exact (congrArg (fun a : SpatialBilinear => a v v) he).symm.trans
    (polarLift_quadratic P (fun z i j => polarTensorComponents P A i j z) hr hy v)
lemma SourceCollarAtlas.eventually_outer_spatial_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ l : ℝ → ℝ,
      Tendsto l atTop (𝓝 1) ∧ (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ x : E, 3*R ≤ ‖x‖ → ∀ v : E,
        l R * sourceSpatial A x v v ≤ spatialMatrix (CKSCartesianOuter.metric f₀ m R) x v v := by
  obtain ⟨R₀,hR₀,hq₀,l,hl,hlb,hcomp⟩ := q.eventually_outer_local_lower f₀ hf₀ m
  refine ⟨R₀,hR₀,hq₀,l,hl,hlb,?_⟩
  intro R hR x hx v
  have hRp : 0 < R := lt_of_lt_of_le (by norm_num : (0:ℝ)<12) (hR₀.trans hR)
  have hqx : q.radius < ‖x‖ := lt_of_lt_of_le (hq₀.trans_le hR) (by linarith)
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (by linarith : 0 < ‖x‖),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  let y := polarInverse (q.patch i).patch x
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hrec := spatial_source_reconstruction (q.patch i) hy0 hyt
    (by rw [hyx]; exact hA x hqx) (by rw [hyx]; exact hB x hqx)
  have h := hcomp R hR i y (by rwa [hyr]) hyw
    (fderiv ℝ (polarInverse (q.patch i).patch) x v)
  rw [← hyx,← hrec.2.2.1,polarLift_quadratic _ _ hy0 hyt,
    polar_spatial_quadratic _ _ hy0 hyt]
  simpa only [hyx] using h

end
end CKSLorentz

end
























end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSLorentz.SourceCollarAtlas.eventually_outer_spatial_lower.{u_1} := @OAI.CKSLorentz.SourceCollarAtlas.eventually_outer_spatial_lower.{u_1}
