-- Prove2me | solution 1 for OAI.CKSLorentz.SourceCollarAtlas.eventually_outer_recovery
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:13:41.529384+00:00
-- url     : https://prove2.me/submissions/6ada29d8-0175-4a1a-809a-fec318ca2e18

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid
import Theorems.Thm_OAI_CKSCartesianOuter_cartesian_radicand_positive

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_eq (q : Mat) : inverse q = q⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, ← determinant_eq]
  ext i j
  simp [inverse, div_eq_mul_inv, mul_comm]

end
end CKSAngularGeometry

end

end OAI
end

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

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]

lemma D_pow (e : E) {f : E → ℝ} {x : E} (n : ℕ)
    (hf : DifferentiableAt ℝ f x) :
    D e (fun y => f y ^ n) x = n * f x ^ (n - 1) * D e f x := by
  unfold D
  rw [fderiv_fun_pow n hf]
  simp

end
end CKSCalculus

end



noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound
open scoped Topology ContDiff

lemma D_r_sq (a : Idx) (x : Point) :
    D (basis a) (fun y => y 0 ^ 2) x = (![2 * x 0, 0, 0] : Point) a := by
  change D (basis a) (fun y => coord 0 y ^ 2) x = _
  rw [D_pow _ 2 (coord 0).differentiableAt, D_coord]
  fin_cases a <;> simp [coord]

end
end CKSRealizedRound

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

lemma phi_one {x : ℝ} (hx : x ≤ 6) : phi x = 1 := by
  simp [phi,Real.smoothTransition.zero_of_nonpos (show (x-6)/6 ≤ 0 by linarith)]

lemma xi_one {x : ℝ} (hx : x ≤ 1) : xi x = 1 := by
  simp [xi,Real.smoothTransition.zero_of_nonpos (show x-1 ≤ 0 by linarith)]

lemma zeta_zero {x : ℝ} (hx : x ≤ 4) : zeta x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma beta_one_near {x : ℝ} (hx : x ≤ 7/2) : beta x = 1 := by
  simp [beta,Real.smoothTransition.zero_of_nonpos (show 2*x-7 ≤ 0 by linarith)]

lemma bendingV_initial {R r : ℝ} (hR : 12 ≤ R) (hr : r ≤ 6*R) : bendingV R r = r := by
  have hRp : 0 < R := by linarith
  have hp : r/R ≤ 6 := (div_le_iff₀ hRp).mpr hr
  have hx : r/R^2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr (by nlinarith)
  simp [bendingV,phi_one hp,xi_one hx]

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
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def traceProduct (q p : Mat) : ℝ := ∑ i, ∑ k, q i k*p k i

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
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t := by
  simp [traceProduct,mul_add,Finset.sum_add_distrib]
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p := by
  simp [traceProduct]
  ring

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
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t :=
  CKSAngularGeometry.traceProduct_add q p t
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p :=
  CKSAngularGeometry.traceProduct_smul c q p

end
end CKSMixedGeometry

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

lemma angularProjection_basis_zero : angularProjection (basis 0) = 0 := by
  ext a
  simp [angularProjection,basis]

lemma D_angularLift {f : Angle → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (angularProjection x)) : D (basis 0) (angularLift f) x = 0 := by
  unfold D angularLift
  change (fderiv ℝ (f ∘ angularProjection) x) (basis 0) = 0
  rw [fderiv_comp x hf angularProjection.differentiableAt,angularProjection.fderiv]
  simp only [ContinuousLinearMap.comp_apply,angularProjection_basis_zero,map_zero]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceAspect (f : SourceMassFields) (w : Angle) : ℝ :=
  traceProduct (inverse (f.sigma w)) (f.mg w+(2:ℝ) • f.mK w)+2*f.mr w

lemma source_leading_mass (f : SourceMassFields) : cksLeadingField f.logFields =
    fun y => sourceAspect f (angularProjection y)/4 := by
  funext y
  unfold cksLeadingField SourceMassFields.logFields angularLift sourceAspect
  rw [traceProduct_add,traceProduct_smul]
  ring

end
end CKSMixedGeometry

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

def radialHarmonicSpan (n : ℕ) : Submodule ℝ Poly :=
  Submodule.span ℝ {p | ∃ j l : ℕ, ∃ h : Poly,
    h.IsHomogeneous l ∧ laplacian h = 0 ∧ 2 * j + l = n ∧
      p = radiusSq ^ j * h}

lemma laplacian_apply (p : Poly) :
    laplacian p = ∑ i : Fin 3, pderiv i (pderiv i p) := by
  simp [laplacian]

lemma radiusSq_homogeneous : radiusSq.IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i hi
  exact isHomogeneous_X_pow i 2

lemma pderiv_radiusSq (i : Fin 3) : pderiv i radiusSq = 2 * X i := by
  fin_cases i <;> simp [radiusSq, Fin.sum_univ_three]

lemma laplacian_homogeneous {p : Poly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (laplacian p).IsHomogeneous (n - 2) := by
  rw [laplacian_apply]
  apply IsHomogeneous.sum
  intro i hi
  simpa [Nat.sub_sub] using (hp.pderiv (i := i)).pderiv (i := i)

lemma laplacian_radiusSq_mul (p : Poly) :
    laplacian (radiusSq * p) = radiusSq * laplacian p +
      4 * (∑ i : Fin 3, X i * pderiv i p) + 6 * p := by
  simp only [laplacian_apply, pderiv_mul, pderiv_radiusSq, map_add,
    pderiv_X_self, Derivation.map_natCast, show (2 : Poly) = (2 : ℕ) by rfl]
  simp only [Fin.sum_univ_three]
  ring

lemma laplacian_radiusSq_mul_homogeneous {p : Poly} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    laplacian (radiusSq * p) = radiusSq * laplacian p + (4 * (n : ℝ) + 6) • p := by
  rw [laplacian_radiusSq_mul, hp.sum_X_mul_pderiv]
  simp only [nsmul_eq_mul, smul_eq_C_mul, map_add, map_mul, map_natCast, map_ofNat]
  ring

lemma laplacian_radial_power {h : Poly} {l : ℕ}
    (hh : h.IsHomogeneous l) (hΔ : laplacian h = 0) (j : ℕ) :
    laplacian (radiusSq ^ (j + 1) * h) =
      ((2 * (j : ℝ) + 2) * (2 * (l : ℝ) + 2 * (j : ℝ) + 3)) •
        (radiusSq ^ j * h) := by
  induction j with
  | zero =>
    rw [pow_one, laplacian_radiusSq_mul_homogeneous hh, hΔ]
    simp only [mul_zero, zero_add, pow_zero, one_mul, Nat.cast_zero, add_zero]
    congr 1
    ring
  | succ j ih =>
    have hg := (radiusSq_homogeneous.pow (j + 1)).mul hh
    have hmul : radiusSq * (radiusSq ^ j * h) = radiusSq ^ (j + 1) * h := by ring
    calc
      laplacian (radiusSq ^ (j + 1 + 1) * h) =
          laplacian (radiusSq * (radiusSq ^ (j + 1) * h)) := by congr 1; ring
      _ = radiusSq * laplacian (radiusSq ^ (j + 1) * h) +
          (4 * ((2 * (j + 1) + l : ℕ) : ℝ) + 6) • (radiusSq ^ (j + 1) * h) :=
        laplacian_radiusSq_mul_homogeneous hg
      _ = (((2 * (j : ℝ) + 2) * (2 * (l : ℝ) + 2 * (j : ℝ) + 3)) +
          (4 * ((2 * (j + 1) + l : ℕ) : ℝ) + 6)) •
            (radiusSq ^ (j + 1) * h) := by
        rw [ih, mul_smul_comm, hmul, ← add_smul]
      _ = _ := by congr 1; push_cast; ring

lemma radialHarmonicSpan_le_homogeneous (n : ℕ) :
    radialHarmonicSpan n ≤ homogeneousSubmodule (Fin 3) ℝ n := by
  apply Submodule.span_le.mpr
  rintro p ⟨j, l, h, hh, hΔ, hn, rfl⟩
  change (radiusSq ^ j * h).IsHomogeneous n
  rw [← hn]
  exact (radiusSq_homogeneous.pow j).mul hh

lemma harmonic_mem_radialHarmonicSpan {h : Poly} {n : ℕ}
    (hh : h.IsHomogeneous n) (hΔ : laplacian h = 0) :
    h ∈ radialHarmonicSpan n := by
  apply Submodule.subset_span
  refine ⟨0, n, h, hh, hΔ, by omega, ?_⟩
  simp

lemma radialHarmonicSpan_le_map_laplacian (n : ℕ) :
    radialHarmonicSpan n ≤ (radialHarmonicSpan (n + 2)).map laplacian := by
  apply Submodule.span_le.mpr
  rintro p ⟨j, l, h, hh, hΔ, hn, rfl⟩
  let a : ℝ := (2 * (j : ℝ) + 2) * (2 * (l : ℝ) + 2 * (j : ℝ) + 3)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  refine ⟨a⁻¹ • (radiusSq ^ (j + 1) * h), ?_, ?_⟩
  · apply (radialHarmonicSpan (n + 2)).smul_mem
    apply Submodule.subset_span
    exact ⟨j + 1, l, h, hh, hΔ, by omega, rfl⟩
  · rw [map_smul, laplacian_radial_power hh hΔ, smul_smul]
    change (a⁻¹ * a) • _ = _
    simp [ha]

lemma laplacian_homogeneous_low {p : Poly} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n < 2) : laplacian p = 0 := by
  rw [laplacian_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hd := hp.pderiv (i := i)
  have hdeg : n - 1 = 0 := by omega
  rw [hdeg] at hd
  have hC : pderiv i p = C ((pderiv i p).coeff 0) := by
    apply totalDegree_eq_zero_iff_eq_C.mp
    exact (totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hd
  rw [hC, pderiv_C]

theorem harmonic_radial_decomposition (n : ℕ) :
    homogeneousSubmodule (Fin 3) ℝ n ≤ radialHarmonicSpan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hp
    change p.IsHomogeneous n at hp
    by_cases hn : n < 2
    · exact harmonic_mem_radialHarmonicSpan hp (laplacian_homogeneous_low hp hn)
    · have hlt : n - 2 < n := by omega
      have hpΔ : laplacian p ∈ radialHarmonicSpan (n - 2) :=
        ih (n - 2) hlt (laplacian_homogeneous hp)
      have hpre := radialHarmonicSpan_le_map_laplacian (n - 2) hpΔ
      obtain ⟨q, hq, hqΔ⟩ := hpre
      have hn' : n - 2 + 2 = n := by omega
      rw [hn'] at hq
      have hqhom : q.IsHomogeneous n := radialHarmonicSpan_le_homogeneous n hq
      have hhΔ : laplacian (p - q) = 0 := by rw [map_sub, hqΔ, sub_self]
      have hh := harmonic_mem_radialHarmonicSpan (hp.sub hqhom) hhΔ
      simpa using (radialHarmonicSpan n).add_mem hh hq

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

lemma sphereEval_radiusSq : sphereEval radiusSq = 1 := by
  ext x
  simp only [radiusSq, map_sum, map_pow, sphereEval_X, ContinuousMap.sum_apply,
    ContinuousMap.pow_apply, ContinuousMap.one_apply, sphereCoordinate]
  have hx : ‖x.1‖ = 1 := by simp
  change (∑ i : Fin 3, x.1 i ^ 2) = 1
  simpa [hx] using (EuclideanSpace.real_norm_sq_eq x.1).symm

lemma polynomialRestrictions_separate : sphereEval.range.SeparatesPoints := by
  intro x y hxy
  have hcoord : ∃ i : Fin 3, x.1 i ≠ y.1 i := by
    by_contra! h
    apply hxy
    apply Subtype.ext
    exact PiLp.ext h
  obtain ⟨i, hi⟩ := hcoord
  exact ⟨sphereCoordinate i, ⟨sphereCoordinate i, ⟨X i, sphereEval_X i⟩, rfl⟩, hi⟩

lemma radialRestriction_mem_harmonicSpan (n : ℕ) :
    radialHarmonicSpan n ≤
      (⨆ l : ℕ, harmonicSpace l).comap sphereEval.toLinearMap := by
  apply Submodule.span_le.mpr
  rintro p ⟨j, l, h, hh, hΔ, hn, rfl⟩
  change sphereEval (radiusSq ^ j * h) ∈ ⨆ l : ℕ, harmonicSpace l
  rw [map_mul, map_pow, sphereEval_radiusSq, one_pow, one_mul]
  exact (le_iSup (fun l => harmonicSpace l) l) ⟨h, ⟨hh, hΔ⟩, rfl⟩

lemma polynomialRestriction_mem_harmonicSpan (p : Poly) :
    sphereEval p ∈ ⨆ l : ℕ, harmonicSpace l := by
  rw [← sum_homogeneousComponent p, map_sum]
  apply Submodule.sum_mem
  intro n hn
  exact radialRestriction_mem_harmonicSpan n
    (harmonic_radial_decomposition n (homogeneousComponent_mem n p))

theorem spherical_harmonics_dense :
    (⨆ l : ℕ, harmonicSpace l).topologicalClosure = ⊤ := by
  apply top_unique
  intro f hf
  have h := ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints
    sphereEval.range polynomialRestrictions_separate f
  exact (closure_mono (show (sphereEval.range : Set C(Sphere, ℝ)) ⊆
      ((⨆ l : ℕ, harmonicSpace l : Submodule ℝ C(Sphere, ℝ)) : Set C(Sphere, ℝ)) from by
    rintro g ⟨p, rfl⟩
    exact polynomialRestriction_mem_harmonicSpan p)) h

open MeasureTheory

lemma harmonicProjection_norm_le (l : ℕ) (f : SphereL2) :
    ‖harmonicProjection l f‖ ≤ ‖f‖ :=
  (harmonicL2 l).norm_orthogonalProjectionOnto_apply_le f

theorem spherical_harmonics_L2_dense :
    (⨆ l : ℕ, harmonicL2 l).topologicalClosure = ⊤ := by
  have hmap := Submodule.topologicalClosure_map toL2 (⨆ l : ℕ, harmonicSpace l)
  rw [spherical_harmonics_dense, Submodule.map_top, Submodule.map_iSup] at hmap
  have hclosed := (⨆ l : ℕ, harmonicL2 l).isClosed_topologicalClosure
  have hd : DenseRange toL2 := ContinuousMap.toLp_denseRange ℝ surfaceMeasure ℝ (by norm_num)
  apply top_unique
  intro f hf
  apply closure_minimal (t := ((⨆ l : ℕ, harmonicL2 l).topologicalClosure : Set SphereL2))
    (s := Set.range toL2) ?_ hclosed (hd f)
  rintro g ⟨c, rfl⟩
  exact hmap ⟨c, rfl⟩

lemma toL2_injective : Function.Injective toL2 :=
  ContinuousMap.toLp_injective surfaceMeasure

def harmonicContinuousEquiv (l : ℕ) : harmonicSpace l ≃ₗ[ℝ] harmonicL2 l :=
  Submodule.equivMapOfInjective toL2.toLinearMap toL2_injective (harmonicSpace l)

def harmonicCoefficient (l : ℕ) : SphereL2 →L[ℝ] C(Sphere, ℝ) :=
  (harmonicSpace l).subtypeL.comp
    ((harmonicContinuousEquiv l).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (harmonicProjection l))

lemma harmonicCoefficient_mem (l : ℕ) (f : SphereL2) :
    harmonicCoefficient l f ∈ harmonicSpace l :=
  ((harmonicContinuousEquiv l).symm (harmonicProjection l f)).property

lemma toL2_harmonicCoefficient (l : ℕ) (f : SphereL2) :
    toL2 (harmonicCoefficient l f) = (harmonicProjection l f : SphereL2) := by
  exact congrArg Subtype.val
    ((harmonicContinuousEquiv l).apply_symm_apply (harmonicProjection l f))

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

lemma inner_sphereEval (p q : Poly) :
    inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval q)) =
      sphereIntegral (sphereEval (p * q)) := by
  rw [sphereIntegral_apply]
  change inner ℝ (ContinuousMap.toLp 2 surfaceMeasure ℝ (sphereEval p))
    (ContinuousMap.toLp 2 surfaceMeasure ℝ (sphereEval q)) = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  simp [map_mul, mul_comm]

theorem rotation_skew_adjoint (i j : Fin 3) (hij : i ≠ j) (p q : Poly) :
    inner ℝ (toL2 (sphereEval (rotation i j p))) (toL2 (sphereEval q)) =
      -inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval (rotation i j q))) := by
  have h := sphereIntegral_rotation i j hij (p * q)
  rw [Derivation.leibniz] at h
  simp only [smul_eq_mul, map_add] at h
  rw [inner_sphereEval, inner_sphereEval]
  rw [mul_comm q] at h
  linarith

def angularLaplacian : Poly →ₗ[ℝ] Poly :=
  ((rotation 0 1).toLinearMap.comp (rotation 0 1).toLinearMap) +
  ((rotation 0 2).toLinearMap.comp (rotation 0 2).toLinearMap) +
  ((rotation 1 2).toLinearMap.comp (rotation 1 2).toLinearMap)

lemma angularLaplacian_apply (p : Poly) :
    angularLaplacian p = rotation 0 1 (rotation 0 1 p) +
      rotation 0 2 (rotation 0 2 p) + rotation 1 2 (rotation 1 2 p) := rfl

lemma rotation_square_symmetric (i j : Fin 3) (hij : i ≠ j) (p q : Poly) :
    inner ℝ (toL2 (sphereEval (rotation i j (rotation i j p)))) (toL2 (sphereEval q)) =
      inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval (rotation i j (rotation i j q)))) := by
  rw [rotation_skew_adjoint i j hij, rotation_skew_adjoint i j hij, neg_neg]

lemma angularLaplacian_symmetric (p q : Poly) :
    inner ℝ (toL2 (sphereEval (angularLaplacian p))) (toL2 (sphereEval q)) =
      inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval (angularLaplacian q))) := by
  simp only [angularLaplacian_apply, map_add, inner_add_left, inner_add_right]
  rw [rotation_square_symmetric 0 1 (by decide),
    rotation_square_symmetric 0 2 (by decide), rotation_square_symmetric 1 2 (by decide)]

def eigenvalue (l : ℕ) : ℝ := (l : ℝ) * ((l : ℝ) + 1)

lemma eigenvalue_injective : Function.Injective eigenvalue := by
  intro l m h
  apply Nat.cast_injective (R := ℝ)
  have hl : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  change (l : ℝ) * ((l : ℝ) + 1) = (m : ℝ) * ((m : ℝ) + 1) at h
  rcases lt_trichotomy (l : ℝ) (m : ℝ) with hlt | heq | hgt
  · nlinarith
  · exact heq
  · nlinarith

lemma different_harmonics_inner_zero {l m : ℕ} (hlm : l ≠ m) {p q : Poly}
    (hp : p.IsHomogeneous l) (hΔp : laplacian p = 0)
    (hq : q.IsHomogeneous m) (hΔq : laplacian q = 0) :
    inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval q)) = 0 := by
  have h := angularLaplacian_symmetric p q
  rw [angularLaplacian_apply, harmonic_rotation_eigenvalue hp hΔp,
    angularLaplacian_apply, harmonic_rotation_eigenvalue hq hΔq] at h
  simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial] at h
  have he : eigenvalue l ≠ eigenvalue m := fun e => hlm (eigenvalue_injective e)
  have hz : (eigenvalue l - eigenvalue m) *
      inner ℝ (toL2 (sphereEval p)) (toL2 (sphereEval q)) = 0 := by
    dsimp [eigenvalue]
    linarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)

theorem harmonicL2_orthogonal {l m : ℕ} (hlm : l ≠ m) :
    (harmonicL2 l).IsOrtho (harmonicL2 m) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro f ⟨cf, ⟨p, ⟨hp, hΔp⟩, rfl⟩, rfl⟩
    g ⟨cg, ⟨q, ⟨hq, hΔq⟩, rfl⟩, rfl⟩
  exact different_harmonics_inner_zero hlm hp hΔp hq hΔq

lemma harmonicL2_orthogonalFamily :
    OrthogonalFamily ℝ (fun l => harmonicL2 l) (fun l => (harmonicL2 l).subtypeₗᵢ) := by
  intro l m hlm f g
  exact (harmonicL2_orthogonal hlm).inner_eq f.property g.property

theorem harmonicHilbertSum :
    IsHilbertSum ℝ (fun l => harmonicL2 l) (fun l => (harmonicL2 l).subtypeₗᵢ) :=
  IsHilbertSum.mkInternal harmonicL2 harmonicL2_orthogonalFamily
    (by rw [spherical_harmonics_L2_dense])

lemma harmonicProjection_other {l m : ℕ} (hlm : l ≠ m) (f : harmonicL2 m) :
    harmonicProjection l (f : SphereL2) = 0 := by
  apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
  exact (harmonicL2_orthogonal hlm).symm f.property

lemma harmonicHilbertSum_coefficient (f : SphereL2) (l : ℕ) :
    harmonicHilbertSum.linearIsometryEquiv f l = harmonicProjection l f := by
  let w := harmonicHilbertSum.linearIsometryEquiv f
  have hs : HasSum (fun m => ((w m : harmonicL2 m) : SphereL2)) f := by
    simpa [w] using harmonicHilbertSum.hasSum_linearIsometryEquiv_symm w
  have hsp := (harmonicProjection l).hasSum hs
  have hr : (fun m => harmonicProjection l (w m : SphereL2)) =
      fun m => if m = l then w l else 0 := by
    funext m
    split_ifs with hml
    · subst m
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    · exact harmonicProjection_other (Ne.symm hml) (w m)
  rw [hr] at hsp
  exact (hasSum_ite_eq l (w l)).unique hsp

theorem harmonicProjections_hasSum (f : SphereL2) :
    HasSum (fun l => (harmonicProjection l f : SphereL2)) f := by
  have hs := harmonicHilbertSum.hasSum_linearIsometryEquiv_symm
    (harmonicHilbertSum.linearIsometryEquiv f)
  convert! hs using 1
  · funext l
    simp only [harmonicHilbertSum_coefficient]
    rfl
  · exact (harmonicHilbertSum.linearIsometryEquiv.symm_apply_apply f).symm

lemma rotation_harmonic {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) (i j : Fin 3) :
    (rotation i j p).IsHomogeneous l ∧ laplacian (rotation i j p) = 0 := by
  exact ⟨rotation_homogeneous i j hp, by rw [laplacian_rotation, hΔ, map_zero]⟩

lemma rotational_energy {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) :
    ‖toL2 (sphereEval (rotation 0 1 p))‖ ^ 2 +
      ‖toL2 (sphereEval (rotation 0 2 p))‖ ^ 2 +
      ‖toL2 (sphereEval (rotation 1 2 p))‖ ^ 2 =
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
  have h := congrArg (fun q : Poly => inner ℝ (toL2 (sphereEval q)) (toL2 (sphereEval p)))
    (harmonic_rotation_eigenvalue hp hΔ)
  simp only [map_add, map_smul, inner_add_left, inner_smul_left, conj_trivial] at h
  rw [rotation_skew_adjoint 0 1 (by decide), rotation_skew_adjoint 0 2 (by decide),
    rotation_skew_adjoint 1 2 (by decide)] at h
  simp only [real_inner_self_eq_norm_sq] at h
  unfold eigenvalue
  linarith

lemma eigenvalue_nonneg (l : ℕ) : 0 ≤ eigenvalue l := by unfold eigenvalue; positivity
lemma eigenvalue_pos {l : ℕ} (hl : l ≠ 0) : 0 < eigenvalue l := by
  have : 0 < (l : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)
  unfold eigenvalue
  positivity

lemma rotation_norm_le {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) (i j : Fin 3) :
    ‖toL2 (sphereEval (rotation i j p))‖ ≤
      Real.sqrt (eigenvalue l) * ‖toL2 (sphereEval p)‖ := by
  have he := rotational_energy hp hΔ
  have hs := Real.sq_sqrt (eigenvalue_nonneg l)
  have hsq : ‖toL2 (sphereEval (rotation i j p))‖ ^ 2 ≤
      eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
    have hn01 := sq_nonneg ‖toL2 (sphereEval (rotation 0 1 p))‖
    have hn02 := sq_nonneg ‖toL2 (sphereEval (rotation 0 2 p))‖
    have hn12 := sq_nonneg ‖toL2 (sphereEval (rotation 1 2 p))‖
    have hrev : ∀ a b : Fin 3, rotation a b p = -rotation b a p := by
      intro a b; simp only [rotation_apply]; ring
    have hdiag : ∀ a : Fin 3, rotation a a p = 0 := by
      intro a; simp [rotation_apply]
    have h01 : ‖toL2 (sphereEval (rotation 0 1 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by linarith
    have h02 : ‖toL2 (sphereEval (rotation 0 2 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by linarith
    have h12 : ‖toL2 (sphereEval (rotation 1 2 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by linarith
    have h10 : ‖toL2 (sphereEval (rotation 1 0 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
      rw [hrev 1 0, map_neg, map_neg, norm_neg]; exact h01
    have h20 : ‖toL2 (sphereEval (rotation 2 0 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
      rw [hrev 2 0, map_neg, map_neg, norm_neg]; exact h02
    have h21 : ‖toL2 (sphereEval (rotation 2 1 p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
      rw [hrev 2 1, map_neg, map_neg, norm_neg]; exact h12
    have hdd (a : Fin 3) : ‖toL2 (sphereEval (rotation a a p))‖ ^ 2 ≤
        eigenvalue l * ‖toL2 (sphereEval p)‖ ^ 2 := by
      simp only [hdiag, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (eigenvalue_nonneg l) (sq_nonneg _)
    fin_cases i <;> fin_cases j
    · exact hdd _
    · convert! h01 using 1
    · convert! h02 using 1
    · convert! h10 using 1
    · exact hdd _
    · convert! h12 using 1
    · convert! h20 using 1
    · convert! h21 using 1
    · exact hdd _
  have hn : 0 ≤ Real.sqrt (eigenvalue l) * ‖toL2 (sphereEval p)‖ := by positivity
  nlinarith only [hsq, hs, hn, norm_nonneg (toL2 (sphereEval (rotation i j p)))]

lemma sphereEval_rotation_of_zero {p : Poly} (hp : sphereEval p = 0)
    (i j : Fin 3) (hij : i ≠ j) : sphereEval (rotation i j p) = 0 := by
  have hd := rotationAction_hasDerivAt_zero i j hij p
  have he : (fun t => rotationAction i j t p) = fun _ => 0 := by
    funext t
    ext x
    rw [rotationAction_apply i j hij, hp]
    rfl
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 0)

lemma harmonicSpace_zero_constant (f : C(Sphere, ℝ)) (hf : f ∈ harmonicSpace 0) :
    ∃ c : ℝ, f = c • (1 : C(Sphere, ℝ)) := by
  obtain ⟨p, ⟨hp, _⟩, rfl⟩ := hf
  have hC := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)
  refine ⟨constantCoeff p, ?_⟩
  rw [hC]
  ext x
  simp [sphereEval]

lemma angular_kernel_constant {p : Poly} (hp : sphereEval (angularLaplacian p) = 0) :
    ∃ c : ℝ, sphereEval p = c • (1 : C(Sphere, ℝ)) := by
  have hproj : ∀ l : ℕ, l ≠ 0 → harmonicProjection l (toL2 (sphereEval p)) = 0 := by
    intro l hl
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    rw [Submodule.mem_orthogonal]
    rintro f ⟨cf, ⟨q, ⟨hq, hΔq⟩, rfl⟩, rfl⟩
    have h := angularLaplacian_symmetric q p
    rw [angularLaplacian_apply, harmonic_rotation_eigenvalue hq hΔq, hp] at h
    simp only [map_smul, map_zero, inner_zero_right, inner_smul_left, conj_trivial] at h
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (eigenvalue_pos hl).ne')
  have hs := harmonicProjections_hasSum (toL2 (sphereEval p))
  have he : (fun l => (harmonicProjection l (toL2 (sphereEval p)) : SphereL2)) =
      fun l => if l = 0 then (harmonicProjection 0 (toL2 (sphereEval p)) : SphereL2) else 0 := by
    funext l
    split_ifs with hl
    · subst l; rfl
    · rw [hproj l hl]; rfl
  rw [he] at hs
  have hh := hs.unique (hasSum_ite_eq 0 _)
  obtain ⟨c, hc⟩ := harmonicSpace_zero_constant
    (harmonicCoefficient 0 (toL2 (sphereEval p))) (harmonicCoefficient_mem _ _)
  refine ⟨c, toL2_injective ?_⟩
  rw [hh, ← toL2_harmonicCoefficient, hc]

abbrev HarmonicBasisIndex (l : ℕ) := Fin (Module.finrank ℝ (harmonicL2 l))
def harmonicBasis (l : ℕ) := stdOrthonormalBasis ℝ (harmonicL2 l)

def harmonicBasisPolynomial (l : ℕ) (a : HarmonicBasisIndex l) : Poly :=
  Classical.choose (harmonicL2_exists_polynomial (harmonicBasis l a))

lemma harmonicBasisPolynomial_spec (l : ℕ) (a : HarmonicBasisIndex l) :
    (harmonicBasisPolynomial l a).IsHomogeneous l ∧
      laplacian (harmonicBasisPolynomial l a) = 0 ∧
      toL2 (sphereEval (harmonicBasisPolynomial l a)) = harmonicBasis l a :=
  Classical.choose_spec (harmonicL2_exists_polynomial (harmonicBasis l a))

lemma harmonic_polynomial_basis_expansion {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    sphereEval p = ∑ a : HarmonicBasisIndex l,
      inner ℝ (harmonicBasis l a : SphereL2) (toL2 (sphereEval p)) •
        sphereEval (harmonicBasisPolynomial l a) := by
  apply toL2_injective
  simp only [map_sum, map_smul, (harmonicBasisPolynomial_spec _ _).2.2]
  let v : harmonicL2 l := ⟨toL2 (sphereEval p), ⟨sphereEval p, ⟨p, ⟨hp, hΔ⟩, rfl⟩, rfl⟩⟩
  have ht := (congrArg (fun w : harmonicL2 l => (w : SphereL2))
      ((harmonicBasis l).sum_repr' v)).symm
  simp only [Submodule.coe_sum, Submodule.coe_smul] at ht
  convert! ht using 1

def harmonicKernelPolynomial (l : ℕ) : Poly :=
  ∑ a : HarmonicBasisIndex l, harmonicBasisPolynomial l a * harmonicBasisPolynomial l a

lemma harmonicKernel_rotation (l : ℕ) (i j : Fin 3) (hij : i ≠ j) :
    sphereEval (rotation i j (harmonicKernelPolynomial l)) = 0 := by
  ext x
  let p := harmonicBasisPolynomial l
  let z : HarmonicBasisIndex l → ℝ := fun a => sphereEval (p a) x
  let c : HarmonicBasisIndex l → HarmonicBasisIndex l → ℝ := fun a b =>
    inner ℝ (toL2 (sphereEval (p b))) (toL2 (sphereEval (rotation i j (p a))))
  have hskew (a b) : c a b = -c b a := by
    dsimp only [c]
    rw [real_inner_comm, rotation_skew_adjoint i j hij]
  have he (a) : sphereEval (rotation i j (p a)) x = ∑ b, c a b * z b := by
    have hp := harmonicBasisPolynomial_spec l a
    have hr := rotation_harmonic hp.1 hp.2.1 i j
    have hh := congrArg (fun f : C(Sphere, ℝ) => f x)
      (harmonic_polynomial_basis_expansion hr.1 hr.2)
    simpa only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      c, z, p, (harmonicBasisPolynomial_spec _ _).2.2] using hh
  have hs : (∑ a, ∑ b, c a b * z a * z b) = 0 := by
    have hh : (∑ a, ∑ b, c a b * z a * z b) = -(∑ a, ∑ b, c a b * z a * z b) := by
      calc
        (∑ a, ∑ b, c a b * z a * z b) = ∑ a, ∑ b, c b a * z b * z a :=
          Finset.sum_comm
        _ = -(∑ a, ∑ b, c a b * z a * z b) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          rw [hskew b a]
          ring
    linarith
  calc
    sphereEval (rotation i j (harmonicKernelPolynomial l)) x =
        ∑ a, 2 * ((∑ b, c a b * z b) * z a) := by
      simp only [harmonicKernelPolynomial, map_sum, Derivation.leibniz, smul_eq_mul,
        map_add, map_mul, ContinuousMap.sum_apply, ContinuousMap.add_apply,
        ContinuousMap.mul_apply]
      apply Finset.sum_congr rfl
      intro a ha
      change z a * sphereEval (rotation i j (p a)) x +
        z a * sphereEval (rotation i j (p a)) x = _
      rw [he]
      ring
    _ = 2 * ∑ a, ∑ b, c a b * z a * z b := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = 0 := by rw [hs]; ring

lemma sphereArea_pos : 0 < sphereArea := by
  have hn : toL2 1 ≠ 0 := by
    intro h
    have h' : (1 : C(Sphere, ℝ)) = 0 := toL2_injective (h.trans (map_zero toL2).symm)
    have hx : (Metric.sphere (0 : Ambient) 1).Nonempty :=
      (NormedSpace.sphere_nonempty.mpr (by norm_num))
    obtain ⟨x, hx⟩ := hx
    exact one_ne_zero (congrArg (fun f : C(Sphere, ℝ) => f ⟨x, hx⟩) h')
  have hh : sphereArea = ‖toL2 1‖ ^ 2 := by
    have h := inner_sphereEval 1 1
    simpa only [map_one, one_mul, real_inner_self_eq_norm_sq, sphereArea] using h.symm
  rw [hh]
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

lemma harmonicKernel_integral (l : ℕ) :
    sphereIntegral (sphereEval (harmonicKernelPolynomial l)) =
      (Module.finrank ℝ (harmonicL2 l) : ℝ) := by
  simp only [harmonicKernelPolynomial, map_sum, ← inner_sphereEval,
    (harmonicBasisPolynomial_spec _ _).2.2]
  have he (a : HarmonicBasisIndex l) : ‖(harmonicBasis l a : SphereL2)‖ = 1 := by
    change ‖harmonicBasis l a‖ = 1
    exact (harmonicBasis l).norm_eq_one a
  simp only [real_inner_self_eq_norm_sq, he, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma harmonicKernel_constant (l : ℕ) :
    sphereEval (harmonicKernelPolynomial l) =
      ((Module.finrank ℝ (harmonicL2 l) : ℝ) / sphereArea) • (1 : C(Sphere, ℝ)) := by
  have hz : sphereEval (angularLaplacian (harmonicKernelPolynomial l)) = 0 := by
    simp only [angularLaplacian_apply, map_add,
      sphereEval_rotation_of_zero (harmonicKernel_rotation l 0 1 (by decide)) 0 1 (by decide),
      sphereEval_rotation_of_zero (harmonicKernel_rotation l 0 2 (by decide)) 0 2 (by decide),
      sphereEval_rotation_of_zero (harmonicKernel_rotation l 1 2 (by decide)) 1 2 (by decide),
      add_zero]
  obtain ⟨c, hc⟩ := angular_kernel_constant hz
  have hi := harmonicKernel_integral l
  rw [hc, map_smul] at hi
  change c * sphereArea = _ at hi
  rw [hc, ← hi, mul_div_cancel_right₀ _ sphereArea_pos.ne']

lemma harmonic_coefficients_sq_sum {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    (∑ a : HarmonicBasisIndex l,
      (inner ℝ (harmonicBasis l a : SphereL2) (toL2 (sphereEval p))) ^ 2) =
      ‖toL2 (sphereEval p)‖ ^ 2 := by
  let v : harmonicL2 l := ⟨toL2 (sphereEval p), ⟨sphereEval p, ⟨p, ⟨hp, hΔ⟩, rfl⟩, rfl⟩⟩
  convert! (harmonicBasis l).sum_sq_inner_right v using 1

lemma harmonic_sup_norm_le {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    ‖sphereEval p‖ ≤ Real.sqrt ((Module.finrank ℝ (harmonicL2 l) : ℝ) / sphereArea) *
      ‖toL2 (sphereEval p)‖ := by
  have hpos : 0 ≤ (Module.finrank ℝ (harmonicL2 l) : ℝ) / sphereArea :=
    div_nonneg (Nat.cast_nonneg _) sphereArea_pos.le
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  have hf := congrArg (fun f : C(Sphere, ℝ) => f x)
    (harmonic_polynomial_basis_expansion hp hΔ)
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul] at hf
  have hk := congrArg (fun f : C(Sphere, ℝ) => f x) (harmonicKernel_constant l)
  simp only [harmonicKernelPolynomial, map_sum, map_mul, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    smul_eq_mul, mul_one] at hk
  simp only [← pow_two] at hk
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (HarmonicBasisIndex l))
    (fun a => inner ℝ (harmonicBasis l a : SphereL2) (toL2 (sphereEval p)))
    (fun a => sphereEval (harmonicBasisPolynomial l a) x)
  rw [← hf, harmonic_coefficients_sq_sum hp hΔ, hk] at hc
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hpos, Real.norm_eq_abs, sq_abs]
  nlinarith only [hc]

def boundedExponentEquiv (l : ℕ) :
    {d : Fin 3 →₀ ℕ // ∀ i, d i ≤ l} ≃ (Fin 3 → Fin (l+1)) where
  toFun d i := ⟨d.1 i, Nat.lt_succ_of_le (d.2 i)⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val),
    fun i => Nat.le_of_lt_succ (a i).isLt⟩
  left_inv d := by ext i; rfl
  right_inv a := by funext i; rfl

lemma restrictDegree_finrank (l : ℕ) :
    Module.finrank ℝ (restrictDegree (Fin 3) ℝ l) = (l+1)^3 := by
  let b := (basisRestrictSupport ℝ {d : Fin 3 →₀ ℕ | ∀ i, d i ≤ l}).reindex
    (boundedExponentEquiv l)
  have h := Module.finrank_eq_card_basis b
  simp only [Fintype.card_fun, Fintype.card_fin] at h
  convert! h using 1

lemma harmonic_dimension_le (l : ℕ) :
    Module.finrank ℝ (harmonicL2 l) ≤ (l+1)^3 := by
  calc
    Module.finrank ℝ (harmonicL2 l) ≤ Module.finrank ℝ (harmonicSpace l) :=
      Submodule.finrank_map_le _ _
    _ ≤ Module.finrank ℝ (harmonicPolynomials l) := Submodule.finrank_map_le _ _
    _ ≤ Module.finrank ℝ (restrictDegree (Fin 3) ℝ l) := by
      apply Submodule.finrank_mono
      intro p hp
      apply restrictTotalDegree_le_restrictDegree (Fin 3) ℝ l
      exact (mem_restrictTotalDegree _ _ _).mpr hp.1.totalDegree_le
    _ = (l+1)^3 := restrictDegree_finrank l

lemma harmonic_sup_norm_polynomial {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    ‖sphereEval p‖ ≤ (sphereArea⁻¹ + 1) * ((l : ℝ) + 1)^2 * ‖toL2 (sphereEval p)‖ := by
  apply (harmonic_sup_norm_le hp hΔ).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have ha : 0 ≤ sphereArea⁻¹ := inv_nonneg.mpr sphereArea_pos.le
  have hl : 1 ≤ (l : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) l; linarith
  have hd : (Module.finrank ℝ (harmonicL2 l) : ℝ) ≤ ((l : ℝ)+1)^3 := by
    exact_mod_cast harmonic_dimension_le l
  have hm : (Module.finrank ℝ (harmonicL2 l) : ℝ) / sphereArea ≤
      ((sphereArea⁻¹+1) * ((l : ℝ)+1)^2)^2 := by
    have h1 : ((l : ℝ)+1)^3 ≤ (((l : ℝ)+1)^2)^2 := by nlinarith
    have h2 : sphereArea⁻¹ ≤ (sphereArea⁻¹+1)^2 := by nlinarith
    calc
      _ = (Module.finrank ℝ (harmonicL2 l) : ℝ) * sphereArea⁻¹ := div_eq_mul_inv _ _
      _ ≤ ((l : ℝ)+1)^3 * sphereArea⁻¹ := mul_le_mul_of_nonneg_right hd ha
      _ ≤ (((l : ℝ)+1)^2)^2 * (sphereArea⁻¹+1)^2 :=
        mul_le_mul h1 h2 ha (by positivity)
      _ = _ := by ring
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hm⟩

lemma rotationWord_harmonic {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) (w : List (Fin 3 × Fin 3)) :
    (rotationWord w p).IsHomogeneous l ∧ laplacian (rotationWord w p) = 0 := by
  induction w with
  | nil => exact ⟨hp, hΔ⟩
  | cons ij w ih => exact rotation_harmonic ih.1 ih.2 ij.1 ij.2

lemma rotationWord_L2_norm_le {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) (w : List (Fin 3 × Fin 3)) :
    ‖toL2 (sphereEval (rotationWord w p))‖ ≤
      Real.sqrt (eigenvalue l) ^ w.length * ‖toL2 (sphereEval p)‖ := by
  induction w with
  | nil => simp [rotationWord]
  | cons ij w ih =>
    have hh := rotationWord_harmonic hp hΔ w
    calc
      _ ≤ Real.sqrt (eigenvalue l) * ‖toL2 (sphereEval (rotationWord w p))‖ :=
        rotation_norm_le hh.1 hh.2 ij.1 ij.2
      _ ≤ Real.sqrt (eigenvalue l) *
          (Real.sqrt (eigenvalue l) ^ w.length * ‖toL2 (sphereEval p)‖) :=
        mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg _)
      _ = _ := by simp [List.length_cons, pow_succ]; ring

lemma rotationWord_sup_norm_le {l : ℕ} {p : Poly}
    (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) (w : List (Fin 3 × Fin 3)) :
    ‖sphereEval (rotationWord w p)‖ ≤
      (sphereArea⁻¹+1) * ((l : ℝ)+1)^(w.length+2) * ‖toL2 (sphereEval p)‖ := by
  have hh := rotationWord_harmonic hp hΔ w
  have hr : Real.sqrt (eigenvalue l) ≤ (l : ℝ)+1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    unfold eigenvalue
    have := Nat.cast_nonneg (α := ℝ) l
    nlinarith
  calc
    _ ≤ (sphereArea⁻¹+1) * ((l : ℝ)+1)^2 *
        ‖toL2 (sphereEval (rotationWord w p))‖ := harmonic_sup_norm_polynomial hh.1 hh.2
    _ ≤ (sphereArea⁻¹+1) * ((l : ℝ)+1)^2 *
        (Real.sqrt (eigenvalue l)^w.length * ‖toL2 (sphereEval p)‖) :=
      mul_le_mul_of_nonneg_left (rotationWord_L2_norm_le hp hΔ w) (by
        have := sphereArea_pos; positivity)
    _ ≤ (sphereArea⁻¹+1) * ((l : ℝ)+1)^2 *
        (((l : ℝ)+1)^w.length * ‖toL2 (sphereEval p)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by have := sphereArea_pos; positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) hr _) (norm_nonneg _)
    _ = _ := by rw [pow_add]; ring

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

lemma polynomialExtension_restriction (p : Poly) :
    smoothRestriction (polynomialExtension p) (polynomialExtension_smooth p).contDiffOn = sphereEval p := by
  ext x
  exact polynomialExtension_on_sphere p x

lemma smoothRotation_restriction_eq {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    {p : Poly} (he : smoothRestriction F hF = sphereEval p)
    (i j : Fin 3) (hij : i ≠ j) :
    smoothRestriction (smoothRotation i j F) (smoothRotation_smooth hF i j) = sphereEval (rotation i j p) := by
  ext x
  have h1 := smoothRotation_orbit_derivative hF i j hij x 0
  have h2 := (ContinuousMap.evalCLM (R := ℝ) x).hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he' : (fun t => F (planeRotation i j hij t (x : Ambient))) =
      fun t => rotationAction i j t p x := by
    funext t
    rw [rotationAction_apply i j hij]
    exact congrArg (fun f : C(Sphere, ℝ) => f (sphereHome (planeRotation i j hij t) x)) he
  rw [he'] at h1
  have h := h1.unique h2
  simpa [smoothRestriction] using h

lemma smoothCasimir_smooth {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    ContDiffOn ℝ ∞ (smoothCasimir F) puncturedSpace :=
  ((smoothRotation_smooth (smoothRotation_smooth hF 0 1) 0 1).add
    (smoothRotation_smooth (smoothRotation_smooth hF 0 2) 0 2)).add
    (smoothRotation_smooth (smoothRotation_smooth hF 1 2) 1 2)

lemma smoothRestriction_casimir {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF) =
      smoothRestriction (smoothRotation 0 1 (smoothRotation 0 1 F)) (smoothRotation_smooth (smoothRotation_smooth hF 0 1) 0 1) +
      smoothRestriction (smoothRotation 0 2 (smoothRotation 0 2 F)) (smoothRotation_smooth (smoothRotation_smooth hF 0 2) 0 2) +
      smoothRestriction (smoothRotation 1 2 (smoothRotation 1 2 F)) (smoothRotation_smooth (smoothRotation_smooth hF 1 2) 1 2) := rfl

lemma smoothCasimir_restriction_eq {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    {p : Poly} (he : smoothRestriction F hF = sphereEval p) :
    smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF) = sphereEval (angularLaplacian p) := by
  rw [smoothRestriction_casimir hF]
  rw [smoothRotation_restriction_eq _ (smoothRotation_restriction_eq hF he 0 1 (by decide)) 0 1 (by decide),
      smoothRotation_restriction_eq _ (smoothRotation_restriction_eq hF he 0 2 (by decide)) 0 2 (by decide),
      smoothRotation_restriction_eq _ (smoothRotation_restriction_eq hF he 1 2 (by decide)) 1 2 (by decide)]
  simp [angularLaplacian_apply]

lemma smoothRotation_square_symmetric {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace)
    (i j : Fin 3) (hij : i ≠ j) :
    inner ℝ (toL2 (smoothRestriction (smoothRotation i j (smoothRotation i j F))
      (smoothRotation_smooth (smoothRotation_smooth hF i j) i j))) (toL2 (smoothRestriction G hG)) =
    inner ℝ (toL2 (smoothRestriction F hF))
      (toL2 (smoothRestriction (smoothRotation i j (smoothRotation i j G))
        (smoothRotation_smooth (smoothRotation_smooth hG i j) i j))) := by
  rw [smoothRotation_skew_adjoint (smoothRotation_smooth hF i j) hG i j hij,
    smoothRotation_skew_adjoint hF (smoothRotation_smooth hG i j) i j hij, neg_neg]

lemma smoothCasimir_symmetric {F G : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (hG : ContDiffOn ℝ ∞ G puncturedSpace) :
    inner ℝ (toL2 (smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF))) (toL2 (smoothRestriction G hG)) =
    inner ℝ (toL2 (smoothRestriction F hF)) (toL2 (smoothRestriction (smoothCasimir G) (smoothCasimir_smooth hG))) := by
  rw [smoothRestriction_casimir hF, smoothRestriction_casimir hG]
  simp only [map_add, inner_add_left, inner_add_right]
  rw [smoothRotation_square_symmetric hF hG 0 1 (by decide),
    smoothRotation_square_symmetric hF hG 0 2 (by decide),
    smoothRotation_square_symmetric hF hG 1 2 (by decide)]

lemma smooth_harmonic_pairing {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l) (hΔ : laplacian p = 0) :
    inner ℝ (toL2 (smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF))) (toL2 (sphereEval p)) =
      -(eigenvalue l) * inner ℝ (toL2 (smoothRestriction F hF)) (toL2 (sphereEval p)) := by
  have he := smoothCasimir_symmetric hF (polynomialExtension_smooth p).contDiffOn
  rw [polynomialExtension_restriction,
    smoothCasimir_restriction_eq _ (polynomialExtension_restriction p),
    angularLaplacian_apply, harmonic_rotation_eigenvalue hp hΔ] at he
  simpa only [map_smul, inner_smul_right, eigenvalue] using he

lemma harmonicProjection_smoothCasimir {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (l : ℕ) :
    harmonicProjection l (toL2 (smoothRestriction (smoothCasimir F) (smoothCasimir_smooth hF))) =
      -(eigenvalue l) • harmonicProjection l (toL2 (smoothRestriction F hF)) := by
  apply ext_inner_right ℝ
  intro v
  have hv := harmonicL2_exists_polynomial v
  obtain ⟨p, hp, hΔ, he⟩ := hv
  have h := smooth_harmonic_pairing hF hp hΔ
  have hproj (f : SphereL2) :
      inner ℝ (harmonicProjection l f : SphereL2) (v : SphereL2) =
        inner ℝ f (v : SphereL2) :=
    (harmonicL2 l).inner_orthogonalProjectionOnto_eq_of_mem_right v f
  simp only [Submodule.coe_inner, Submodule.coe_smul]
  rw [real_inner_smul_left, hproj, hproj]
  simpa only [he] using h

def smoothCasimirIterate : ℕ → (Ambient → ℝ) → (Ambient → ℝ)
  | 0, F => F
  | N + 1, F => smoothCasimir (smoothCasimirIterate N F)

lemma smoothCasimirIterate_smooth {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    (N : ℕ) : ContDiffOn ℝ ∞ (smoothCasimirIterate N F) puncturedSpace := by
  induction N with
  | zero => exact hF
  | succ N ih => exact smoothCasimir_smooth ih

lemma harmonicProjection_smoothCasimirIterate {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (l N : ℕ) :
    harmonicProjection l (toL2 (smoothRestriction (smoothCasimirIterate N F)
      (smoothCasimirIterate_smooth hF N))) =
      (-(eigenvalue l)) ^ N • harmonicProjection l (toL2 (smoothRestriction F hF)) := by
  induction N with
  | zero => simp [smoothCasimirIterate]
  | succ N ih =>
    change harmonicProjection l (toL2 (smoothRestriction (smoothCasimir (smoothCasimirIterate N F))
      (smoothCasimir_smooth (smoothCasimirIterate_smooth hF N)))) = _
    rw [harmonicProjection_smoothCasimir (smoothCasimirIterate_smooth hF N), ih, smul_smul, pow_succ']

theorem harmonicProjection_rapid_L2 {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (l N : ℕ) :
    eigenvalue l ^ N * ‖harmonicProjection l (toL2 (smoothRestriction F hF))‖ ≤
      ‖toL2 (smoothRestriction (smoothCasimirIterate N F) (smoothCasimirIterate_smooth hF N))‖ := by
  have h := harmonicProjection_norm_le l
    (toL2 (smoothRestriction (smoothCasimirIterate N F) (smoothCasimirIterate_smooth hF N)))
  rw [harmonicProjection_smoothCasimirIterate hF, norm_smul, norm_pow,
    norm_neg, Real.norm_eq_abs, abs_of_nonneg (eigenvalue_nonneg l)] at h
  exact h

lemma harmonicCoefficientPolynomial_spec (l : ℕ) (f : SphereL2) :
    (harmonicCoefficientPolynomial l f).IsHomogeneous l ∧
    laplacian (harmonicCoefficientPolynomial l f) = 0 ∧
    toL2 (sphereEval (harmonicCoefficientPolynomial l f)) = (harmonicProjection l f : SphereL2) :=
  Classical.choose_spec (harmonicL2_exists_polynomial (harmonicProjection l f))

lemma harmonicCoefficientPolynomial_restriction (l : ℕ) (f : SphereL2) :
    sphereEval (harmonicCoefficientPolynomial l f) = harmonicCoefficient l f := by
  apply toL2_injective
  rw [(harmonicCoefficientPolynomial_spec l f).2.2, toL2_harmonicCoefficient]

def rotatedHarmonicCoefficient (w : List (Fin 3 × Fin 3)) (l : ℕ) (f : SphereL2) : C(Sphere, ℝ) :=
  sphereEval (rotationWord w (harmonicCoefficientPolynomial l f))

lemma rotatedHarmonicCoefficient_nil (l : ℕ) (f : SphereL2) :
    rotatedHarmonicCoefficient [] l f = harmonicCoefficient l f :=
  harmonicCoefficientPolynomial_restriction l f

lemma rotatedHarmonicCoefficient_bound (w : List (Fin 3 × Fin 3)) (l : ℕ) (f : SphereL2) :
    ‖rotatedHarmonicCoefficient w l f‖ ≤
      (sphereArea⁻¹ + 1) * ((l : ℝ) + 1) ^ (w.length + 2) * ‖harmonicProjection l f‖ := by
  obtain ⟨hp, hΔ, he⟩ := harmonicCoefficientPolynomial_spec l f
  have h := rotationWord_sup_norm_le hp hΔ w
  rw [he] at h
  exact h

lemma eigenvalue_ge_degree {l : ℕ} (hl : 1 ≤ l) : (l : ℝ) + 1 ≤ eigenvalue l := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  unfold eigenvalue
  nlinarith

lemma rotatedHarmonicCoefficient_pseries_bound {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (w : List (Fin 3 × Fin 3)) (b : ℕ)
    {l : ℕ} (hl : 2 ≤ l) :
    eigenvalue l ^ b * ‖rotatedHarmonicCoefficient w l (toL2 (smoothRestriction F hF))‖ ≤
      ((sphereArea⁻¹ + 1) * ‖toL2 (smoothRestriction (smoothCasimirIterate (b + w.length + 4) F)
        (smoothCasimirIterate_smooth hF _))‖) / ((l : ℝ) + 1) ^ 2 := by
  have hx : 0 < (l : ℝ) + 1 := by positivity
  have hC : 0 ≤ sphereArea⁻¹ + 1 := by
    have := sphereArea_pos
    positivity
  have he : eigenvalue l ^ b * ((l : ℝ) + 1) ^ (w.length + 4) ≤
      eigenvalue l ^ (b + w.length + 4) := by
    rw [show b + w.length + 4 = b + (w.length + 4) by omega,
      pow_add (eigenvalue l) b (w.length + 4)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx.le (eigenvalue_ge_degree (by omega)) _) (pow_nonneg (eigenvalue_nonneg l) b)
  apply (le_div_iff₀ (pow_pos hx 2)).mpr
  calc
    (eigenvalue l ^ b * ‖rotatedHarmonicCoefficient w l (toL2 (smoothRestriction F hF))‖) *
        ((l : ℝ) + 1) ^ 2 ≤
      (eigenvalue l ^ b * ((sphereArea⁻¹ + 1) * ((l : ℝ) + 1) ^ (w.length + 2) *
        ‖harmonicProjection l (toL2 (smoothRestriction F hF))‖)) * ((l : ℝ) + 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rotatedHarmonicCoefficient_bound w l _)
          (pow_nonneg (eigenvalue_nonneg l) b)) (sq_nonneg _)
    _ = (sphereArea⁻¹ + 1) * ((eigenvalue l ^ b * ((l : ℝ) + 1) ^ (w.length + 4)) *
        ‖harmonicProjection l (toL2 (smoothRestriction F hF))‖) := by
      simp only [pow_add]
      ring
    _ ≤ (sphereArea⁻¹ + 1) * (eigenvalue l ^ (b + w.length + 4) *
        ‖harmonicProjection l (toL2 (smoothRestriction F hF))‖) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (norm_nonneg _)) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonicProjection_rapid_L2 hF l _) hC

theorem rotatedHarmonicCoefficient_rapid {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) (w : List (Fin 3 × Fin 3)) (b : ℕ) :
    Summable (fun n : ℕ => eigenvalue (n + 2) ^ b *
      ‖rotatedHarmonicCoefficient w (n + 2) (toL2 (smoothRestriction F hF))‖) := by
  let C := (sphereArea⁻¹ + 1) * ‖toL2 (smoothRestriction (smoothCasimirIterate (b + w.length + 4) F)
    (smoothCasimirIterate_smooth hF _))‖
  have hp : Summable (fun n : ℕ => C / ((n : ℝ) + 3) ^ 2) := by
    have h := (summable_nat_add_iff 3).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
    convert! h.mul_left C using 1
    funext n
    simp [Nat.cast_add, div_eq_mul_inv]
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (eigenvalue_nonneg _) _) (norm_nonneg _)) _ hp
  intro n
  convert! rotatedHarmonicCoefficient_pseries_bound hF w b (l := n + 2) (by omega) using 1
  norm_num [C, Nat.cast_add, add_assoc]

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

omit [CompleteSpace B] in
lemma heat_eq_series [CompleteSpace B] (coeff : ℕ → B) {t : ℝ} (ht : 0 ≤ t) :
    heat coeff t = ∑' n, exp (-eigenvalue n * t) • coeff n := by
  unfold heat term
  congr 1
  funext n
  rw [kernel_nonneg_time (mul_nonneg (eigenvalue_pos n).le ht)]
  simp

lemma heat_initial (coeff : ℕ → B) : heat coeff 0 = ∑' n, coeff n := by
  rw [heat_eq_series coeff le_rfl]
  simp

lemma heat_deriv (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ) (t : ℝ) :
    iteratedDeriv b (heat coeff) t = ∑' n, iteratedDeriv b (term coeff n) t := by
  obtain ⟨v, hv, hb⟩ := heat_majorant coeff h
  simp_rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply]
  unfold heat
  rw [iteratedFDeriv_tsum_apply (term_smooth coeff) (fun k _ => hv k)
    (fun k n t _ => hb k n t) (by simp)]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin b) B).symm.toContinuousLinearEquiv.map_tsum

lemma term_deriv_summable (coeff : ℕ → B) (h : Rapid coeff) (b : ℕ) (t : ℝ) :
    Summable (fun n => iteratedDeriv b (term coeff n) t) := by
  obtain ⟨v, hv, hb⟩ := heat_majorant coeff h
  apply Summable.of_norm_bounded (hv b)
  intro n
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb b n t

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

end
end CKSSpectralHeat

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
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma smooth_harmonicCoefficients_summable {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    Summable (fun l => harmonicCoefficient l (toL2 (smoothRestriction F hF))) := by
  have h := rotatedHarmonicCoefficient_rapid hF [] 0
  simp only [pow_zero, one_mul, rotatedHarmonicCoefficient_nil] at h
  exact (summable_nat_add_iff 2).mp h.of_norm

theorem smooth_harmonicCoefficients_tsum {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) :
    (∑' l, harmonicCoefficient l (toL2 (smoothRestriction F hF))) = smoothRestriction F hF := by
  apply toL2_injective
  rw [toL2.map_tsum (smooth_harmonicCoefficients_summable hF)]
  simp_rw [toL2_harmonicCoefficient]
  exact (harmonicProjections_hasSum _).tsum_eq

lemma sphereEval_C (a : ℝ) : sphereEval (C a) = a • (1 : C(Sphere, ℝ)) := by
  ext x
  simp [sphereEval]

lemma sphereIntegral_constant (a : ℝ) : sphereIntegral (sphereEval (C a)) = a * sphereArea := by
  rw [sphereEval_C, map_smul]
  rfl

lemma harmonicProjection_zero_of_mean_zero (f : C(Sphere, ℝ)) (hf : sphereIntegral f = 0) :
    harmonicProjection 0 (toL2 f) = 0 := by
  apply ext_inner_right ℝ
  intro v
  obtain ⟨p, hp, hΔ, he⟩ := harmonicL2_exists_polynomial v
  have hpC : p = C (p.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous _).mpr hp)
  simp only [harmonicProjection, inner_zero_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← he, inner_toL2, hpC, sphereEval_C]
  rw [mul_smul_comm, mul_one, map_smul, hf, smul_zero]

lemma first_moments_pairing_zero (f : C(Sphere, ℝ))
    (hf : ∀ i : Fin 3, sphereIntegral (f * sphereCoordinate i) = 0)
    {p : Poly} (hp : p.IsHomogeneous 1) : sphereIntegral (f * sphereEval p) = 0 := by
  have hm : p ∈ Submodule.span ℝ (Set.range (X : Fin 3 → Poly)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hp
  clear hp
  induction hm using Submodule.span_induction with
  | mem p hp => obtain ⟨i, rfl⟩ := hp; simpa only [sphereEval_X] using hf i
  | zero => simp
  | add p q hp hq ihp ihq => simp [map_add, mul_add, ihp, ihq]
  | smul a p hp ihp => simp [map_smul, ihp]

lemma harmonicProjection_one_of_first_moments (f : C(Sphere, ℝ))
    (hf : ∀ i : Fin 3, sphereIntegral (f * sphereCoordinate i) = 0) :
    harmonicProjection 1 (toL2 f) = 0 := by
  apply ext_inner_right ℝ
  intro v
  obtain ⟨p, hp, hΔ, he⟩ := harmonicL2_exists_polynomial v
  simp only [harmonicProjection, inner_zero_left,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← he, inner_toL2]
  exact first_moments_pairing_zero f hf hp

lemma harmonicCoefficient_zero_of_mean (f : C(Sphere, ℝ)) {m : ℝ}
    (hf : sphereIntegral f = m * sphereArea) :
    harmonicCoefficient 0 (toL2 f) = sphereEval (C m) := by
  have hm : toL2 (sphereEval (C m)) ∈ harmonicL2 0 := by
    exact ⟨sphereEval (C m), ⟨C m, ⟨isHomogeneous_C (Fin 3) m, by simp [laplacian_apply]⟩, rfl⟩, rfl⟩
  have h := harmonicProjection_zero_of_mean_zero (f - sphereEval (C m)) (by
    rw [map_sub, hf, sphereIntegral_constant, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at h
  apply toL2_injective
  rw [toL2_harmonicCoefficient, h]
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨toL2 (sphereEval (C m)), hm⟩ : harmonicL2 0))

lemma harmonicCoefficient_one_of_first_moments (f : C(Sphere, ℝ))
    (hf : ∀ i : Fin 3, sphereIntegral (f * sphereCoordinate i) = 0) :
    harmonicCoefficient 1 (toL2 f) = 0 := by
  apply toL2_injective
  rw [toL2_harmonicCoefficient, harmonicProjection_one_of_first_moments f hf, map_zero]
  rfl

lemma smooth_high_harmonics_initial {F : Ambient → ℝ}
    (hF : ContDiffOn ℝ ∞ F puncturedSpace) {m : ℝ}
    (hbal : Balanced (smoothRestriction F hF) m) :
    sphereEval (C m) + (∑' n, harmonicCoefficient (n + 2) (toL2 (smoothRestriction F hF))) =
      smoothRestriction F hF := by
  have h := (smooth_harmonicCoefficients_summable hF).sum_add_tsum_nat_add 2
  rw [smooth_harmonicCoefficients_tsum hF] at h
  simpa [Finset.sum_range_succ, harmonicCoefficient_zero_of_mean _ hbal.1,
    harmonicCoefficient_one_of_first_moments _ hbal.2] using h

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

lemma sphereHeatJet_initial {F : Ambient → ℝ} (hF : ContDiffOn ℝ ∞ F puncturedSpace)
    {m : ℝ} (hb : Balanced (smoothRestriction F hF) m) :
    sphereEval (C m) + sphereHeatJet (heatPolynomials (smoothRestriction F hF)) (0, []) 0 =
      smoothRestriction F hF := by
  simpa only [sphereHeatJet, iteratedDeriv_zero, rotationWord, heatPolynomials,
    harmonicCoefficientPolynomial_restriction, CKSSpectralHeat.heat_initial] using
    smooth_high_harmonics_initial hF hb

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

lemma paddingWeight_one {R r : ℝ} (hR : 0 < R) (hr : 2*R ≤ r) : paddingWeight R r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : 2 ≤ r/R := (le_div_iff₀ hR).mpr hr
  linarith

lemma heatTime_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ 4*R) : heatTime R r = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [] with s hs
  have hsr : s ≤ 4*R := hs.2.trans (max_le (by linarith) hr)
  have hh : s/R ≤ 4 := (div_le_iff₀ hR).mpr hsr
  simp [heatDensity,bendingZeta,zeta_zero hh]

end
end CKSBending

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

lemma roundingWeight_one {R r : ℝ} (hR : 0 < R) (hr : 3*R ≤ r) : roundingWeight R r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h := (le_div_iff₀ hR).mpr hr
  linarith

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
open Set Filter Finset MeasureTheory
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

lemma radial_restriction (f : C(Sphere,ℝ)) (hf : SmoothSphere f) :
    smoothRestriction (radialExtension f) (radialExtension_smooth hf) = f := by
  ext x
  exact radialExtension_on_sphere f x

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
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

lemma canonicalF_initial (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) (hb : Balanced f₀ m)
    (x : Sphere) : canonicalF f₀ m 0 x = f₀ x := by
  have hp := smoothDatum_rapid f₀ hf₀
  have h := sphereHeatJet_initial (radialExtension_smooth hf₀)
    (m := m) (by rwa [radial_restriction f₀ hf₀])
  rw [radial_restriction f₀ hf₀] at h
  have he := congrArg (fun q : C(Sphere,ℝ) => q x) h
  change sphereEval (MvPolynomial.C m) x + sphereHeatJet (heatPolynomials f₀) (0,[]) 0 x = f₀ x at he
  have hc : sphereEval (MvPolynomial.C m) x = m := by simp [sphereEval]
  rw [hc,sphereHeatJet_eq _ hp] at he
  exact he

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI








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
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Matrix.Norms.Elementwise
lemma SmoothAngularPatch.roundMetric_contDiffAt (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : ContDiffAt ℝ ∞ (angularRoundMetric P.param) θ := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact ContDiffAt.inner ℝ
    (((P.param_contDiffAt hθ).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
    (((P.param_contDiffAt hθ).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
end
end CKSLorentz

end






































noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_smul (γ A : Mat) (c : ℝ) :
    leafTensorTrace γ (c • A) = c*leafTensorTrace γ A := by
  simp [leafTensorTrace]

lemma leafTensorTrace_self {γ : Mat} (hp : γ.PosDef) : leafTensorTrace γ γ = 2 := by
  rw [leafTensorTrace, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')]
  norm_num

end
end CKSAngularGeometry

end



























noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma radiusLogPoint_exp {x : PhysicalPoint} (hr : 0 < x 0) :
    Real.exp (radiusLogPoint x 0)=x 0 := by simp [radiusLogPoint,Real.exp_log hr]

lemma radialExpansion_congr {γ δ : PhysicalPoint → Mat} {s t : PhysicalPoint → Point}
    {x : PhysicalPoint} (hq : γ =ᶠ[𝓝 x] δ) (hs : s =ᶠ[𝓝 x] t) :
    radialExpansion γ s x=radialExpansion δ t x := by
  have hqD (i a b) := D_congr (hq.mono (fun y hy => congrArg (fun q : Mat => q a b) hy))
    (CKSRealizedRound.basis i)
  have hsD (i a) := D_congr (hs.mono (fun y hy => congrFun hy a)) (CKSRealizedRound.basis i)
  have hd : leafRadialRate γ s x=leafRadialRate δ t x := by
    funext a b
    simp only [leafRadialRate,hq.self_of_nhds,hs.self_of_nhds,hqD,hsD]
  unfold radialExpansion
  rw [hq.self_of_nhds,hd]

end
end CKSAngularGeometry

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

lemma rawCharge_integrable {M : Sphere → ℝ} (hM : SmoothSphere M) :
    Integrable (fun n => M n • nullDirection n) surfaceMeasure :=
  (hM.continuous.smul nullDirection_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma rawCharge_test {M : Sphere → ℝ} (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge M) = ∫ n : Sphere, M n * L (nullDirection n) ∂surfaceMeasure := by
  rw [rawCharge, ← L.integral_comp_comm (rawCharge_integrable hM)]
  simp only [map_smul, smul_eq_mul]

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
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

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

lemma norm_radius_sphere {r : ℝ} (hr : 0 < r) (n : Sphere) : ‖r • (n:E)‖ = r := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  simp

lemma unitVector_radius {r : ℝ} (hr : 0 < r) (n : Sphere) : unitVector (r • (n:E)) = n := by
  rw [unitVector,norm_radius_sphere hr,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]

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
namespace CKSAngularSlice
noncomputable section
open CKSBending Set
open scoped ContDiff

lemma collar_fields_final {R : ℝ} (hR : 0<R) (f : LogCollarData) {y : MP}
    (hy : 3*R ≤ Real.exp (y 0)) :
    collarQ R f y=f.sigma y ∧ collarShift R f y=0 ∧ collarT R f y=1 ∧
    collarLb R f y=1 ∧ collarL R f y=1+1/Real.exp (y 0)^2 ∧
    collarF R f y=f.fstar y+paddingMass R (Real.exp (y 0)) ∧ collarEtaDivR R f y=0 := by
  have he := roundingWeight_one hR hy
  have hw := paddingWeight_one hR ((by linarith : 2*R ≤ 3*R).trans hy)
  simp [collarQ,collarShift,collarT,collarLb,collarL,collarF,collarEtaDivR,radialLift,he,hw]

end
end CKSAngularSlice

end

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Matrix Set Filter CKSCalculus CKSRealizedRound CKSAngularGeometry CKSAngularSlice CKSBending
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma final_collar_fields {R : ℝ} {f : LogCollarData} {x : CKSRealizedRound.Point}
    (hR : 0 < R) (hr : 3*R ≤ x 0) :
    physicalCollarGamma R f x=x 0^2 • f.sigma (radiusLogPoint x) ∧
    physicalCollarShift R f x=0 ∧ physicalCollarT R f x=1 ∧
    physicalCollarF R f x=f.fstar (radiusLogPoint x)+paddingMass R (x 0) ∧
    physicalCollarL R f x=1+1/x 0^2 ∧ physicalCollarEta R f x=0 ∧
    physicalCollarRawTau R f x=0 := by
  have hrp : 0 < x 0 := by linarith
  have h := collar_fields_final hR f (y := radiusLogPoint x) (by simpa [radiusLogPoint_exp hrp] using hr)
  simp only [radiusLogPoint_exp hrp] at h
  refine ⟨?_,h.2.1,h.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.1,?_,?_⟩
  · exact congrArg (fun q => x 0^2 • q) h.1
  · unfold physicalCollarEta
    rw [h.2.2.2.2.2.2,smul_zero]
  · simp only [physicalCollarRawTau,roundingWeight_one hR hr,sub_self,mul_zero,zero_smul]

lemma bendingV_deriv_initial {R r : ℝ} (hR : 12 ≤ R) (hr : r < 6*R) :
    deriv (bendingV R) r=1 := by
  have h : bendingV R =ᶠ[𝓝 r] (fun s : ℝ => s) := by
    filter_upwards [Iio_mem_nhds hr] with s hs
    exact bendingV_initial hR hs.le
  rw [h.deriv_eq]
  simp

end
end CKSSphericalChart

end



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSCalculus Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma angular_round_leafRadialRate (P : SmoothAngularPatch) {x : CKSMixedGeometry.Point}
    (hx : angularProjection x ∈ P.chart.target) :
    leafRadialRate (fun y => y 0^2 • angularRoundMetric P.param (angularProjection y)) (fun _ => 0) x =
      (2*x 0) • angularRoundMetric P.param (angularProjection x) := by
  have hσ := P.roundMetric_contDiffAt hx
  have hD (a b : Fin 2) :
      D (CKSRealizedRound.basis 0) (fun y : CKSMixedGeometry.Point =>
        (y 0^2 • angularRoundMetric P.param (angularProjection y)) a b) x =
        2*x 0*angularRoundMetric P.param (angularProjection x) a b := by
    have ha := (contDiffAt_pi.mp (contDiffAt_pi.mp hσ a) b).differentiableAt (by simp)
    change D (CKSRealizedRound.basis 0) (fun y : CKSMixedGeometry.Point =>
      y 0^2 * (angularLift (fun θ => angularRoundMetric P.param θ a b)) y) x = _
    have hp := D_mul (CKSRealizedRound.basis 0)
      (show DifferentiableAt ℝ (fun y : CKSMixedGeometry.Point => y 0^2) x by fun_prop)
      (ha.comp x angularProjection.differentiableAt)
    change D (CKSRealizedRound.basis 0) (fun y : CKSMixedGeometry.Point =>
      y 0^2 * (angularLift (fun θ => angularRoundMetric P.param θ a b)) y) x = _ at hp
    rw [hp]
    have haD : D (CKSRealizedRound.basis 0)
        ((fun θ => angularRoundMetric P.param θ a b) ∘ angularProjection) x = 0 := D_angularLift ha
    rw [haD,CKSRealizedRound.D_r_sq]
    simp only [mul_zero,zero_add,Fin.isValue,Matrix.cons_val_zero,Function.comp_apply]
    ring
  ext a b
  simp only [leafRadialRate,Pi.zero_apply,D_const,zero_mul,mul_zero,add_zero,
    Finset.sum_const_zero,sub_zero,Matrix.smul_apply,smul_eq_mul]
  exact hD a b
lemma angular_round_radialExpansion (P : SmoothAngularPatch) {x : CKSMixedGeometry.Point}
    (hr : x 0 ≠ 0) (hx : angularProjection x ∈ P.chart.target) :
    radialExpansion (fun y => y 0^2 • angularRoundMetric P.param (angularProjection y)) (fun _ => 0) x=1 := by
  have hscale : (2*x 0) • angularRoundMetric P.param (angularProjection x) =
      (2/x 0) • (x 0^2 • angularRoundMetric P.param (angularProjection x)) := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [radialExpansion,angular_round_leafRadialRate P hx,hscale,leafTensorTrace_smul,
    leafTensorTrace_self ((P.roundMetric_posDef hx).smul (sq_pos_of_ne_zero hr))]
  field_simp
  ring
lemma final_angular_collar_radialExpansion (P : SmoothAngularPatch) {R : ℝ}
    {f : LogCollarData} {x : CKSMixedGeometry.Point} (hR : 0 < R) (hr : 3*R < x 0)
    (hx : angularProjection x ∈ P.chart.target)
    (hσ : ∀ᶠ y in 𝓝 x, f.sigma (radiusLogPoint y)=angularRoundMetric P.param (angularProjection y)) :
    radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) x=1 := by
  have hn : ∀ᶠ z in 𝓝 x, 3*R < z 0 :=
    (show ContinuousAt (fun z : CKSMixedGeometry.Point => z 0) x from (continuous_apply 0).continuousAt).eventually (Ioi_mem_nhds hr)
  have hfields : ∀ᶠ y in 𝓝 x,
      physicalCollarGamma R f y=y 0^2 • angularRoundMetric P.param (angularProjection y) ∧
      physicalCollarShift R f y=0 := by
    filter_upwards [hn,hσ] with y hyr hyσ
    obtain ⟨hγ,hs,-⟩ := CKSSphericalChart.final_collar_fields (f := f) hR hyr.le
    exact ⟨by rw [hγ,hyσ],hs⟩
  rw [radialExpansion_congr (hfields.mono (fun _ h => h.1)) (hfields.mono (fun _ h => h.2))]
  exact angular_round_radialExpansion P (by linarith) hx
end
end CKSLorentz

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
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
  CKSADM CKSBending CKSSphericalHarmonics CKSInducedSphere
open CKSRealizedRound (correctionCoeff)
open scoped Matrix.Norms.Elementwise
lemma cartMass_polar_initial (P : SmoothAngularPatch) (f₀ : C(Sphere,ℝ))
    (hf₀ : SmoothSphere f₀) (m : ℝ) (hbal : Balanced f₀ m) {R : ℝ} (hR : 0 < R)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (ht : y 0 ≤ 4*R) :
    cartMass f₀ m R (polarParam P y) = paddingMass R (y 0) + f₀ (P.chart.symm (angularProjection y)) := by
  rw [cartMass,polarParam_norm P hr.le,heatTime_initial hR ht]
  have hu : unitVector (polarParam P y) = (P.chart.symm (angularProjection y) : E) :=
    unitVector_radius hr (P.chart.symm (angularProjection y))
  rw [hu]
  congr 1
  exact canonicalF_initial f₀ hf₀ m hbal _
lemma outer_tensor_initial_matrix (f₀ : C(Sphere,ℝ)) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) {x : E} (hr : 0 < ‖x‖) (ht : ‖x‖ < (7/2)*R) :
    CKSCartesianOuter.tensor f₀ m R x =
      (1 : AmbientMat) + ((1+1/‖x‖^2)/CKSCartesianOuter.radicand f₀ m R x-1) •
        Matrix.vecMulVec (normal x) (normal x) := by
  have hRp : 0 < R := by linarith
  have hv := bendingV_initial hR (by linarith : ‖x‖ ≤ 6*R)
  have hdv := bendingV_deriv_initial hR (by linarith : ‖x‖ < 6*R)
  have hβ : bendingBeta R ‖x‖=1 := beta_one_near ((div_le_iff₀ hRp).mpr ht.le)
  have hcor : correctionCoeff (bendingV R) ‖x‖=0 := by
    simp [correctionCoeff,hv,hdv,hr.ne']
  rw [CKSCartesianOuter.tensor,hcor,hv]
  simp only [zero_div,zero_smul,add_zero,div_self hr.ne',one_smul]
  unfold CKSRealizedRound.normalEntry
  rw [hdv,hβ]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalChart CKSCartesianOuter
  CKSSphericalHarmonics CKSBending Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma collar_outer_blocks (P : SmoothAngularPatch) (f : LogCollarData)
    (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) (hbal : Balanced f₀ m)
    {R : ℝ} (hR : 12 ≤ R) {y : CKSMixedGeometry.Point}
    (hr : 3*R < y 0) (hr' : y 0 < (7/2)*R) (hy : angularProjection y ∈ P.chart.target)
    (hσ : ∀ᶠ z in 𝓝 y, f.sigma (radiusLogPoint z)=angularRoundMetric P.param (angularProjection z))
    (hf : f.fstar (radiusLogPoint y)=f₀ (P.chart.symm (angularProjection y)))
    (hp : 0 < CKSCartesianOuter.radicand f₀ m R (polarParam P y)) :
    physicalCollarMetric R f y = metricBlock
      (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 0
      ((y 0)^2 • angularRoundMetric P.param (angularProjection y)) ∧
    physicalCollarTensor R f y = metricBlock
      ((1+1/(y 0)^2)/CKSCartesianOuter.radicand f₀ m R (polarParam P y)) 0
      ((y 0)^2 • angularRoundMetric P.param (angularProjection y)) := by
  have hRp : 0 < R := by linarith
  have hrp : 0 < y 0 := by linarith
  have hv := bendingV_initial hR (by linarith : y 0 ≤ 6*R)
  obtain ⟨hγ,hs,ht,hF,hL,hη,hτ⟩ := final_collar_fields (f := f) hRp hr.le
  rw [hσ.self_of_nhds] at hγ
  have hFm : physicalCollarF R f y = CKSADM.cartMass f₀ m R (polarParam P y) := by
    rw [hF,hf,cartMass_polar_initial P f₀ hf₀ m hbal hRp hrp (by linarith)]
    ring
  have hU : physicalCollarU R f y = Real.sqrt (CKSCartesianOuter.radicand f₀ m R (polarParam P y)) := by
    rw [physicalCollarU,radialMassLapse,final_angular_collar_radialExpansion P hRp hr hy hσ]
    simp only [div_one,radialMassRadical,ht,hFm,mul_one,CKSCartesianOuter.radicand,
      polarParam_norm P hrp.le,hv]
  have hU2 : (physicalCollarU R f y)^2=CKSCartesianOuter.radicand f₀ m R (polarParam P y) := by
    rw [hU,Real.sq_sqrt hp.le]
  have hT : physicalCollarTangential R f y=y 0^2 • angularRoundMetric P.param (angularProjection y) := by
    simp [physicalCollarTangential,radialTangential,ht,hγ,hτ,leafTensorTraceFree,leafTensorTrace]
  constructor
  · simp only [physicalCollarMetric,foliationMetric,hU2,hγ,hs,one_div]
    simp
    rfl
  · simp [physicalCollarTensor,foliationTensor,hU2,hL,hη,hT,hs]
    rfl
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Filter
open scoped Topology ContDiff

theorem physical_collar_outer_spatial_overlap (f₀ : C(Sphere,ℝ))
    (hf₀ : SmoothSphere f₀) (m : ℝ) (hbal : Balanced f₀ m) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R ≥ R₀, ∀ (P : SmoothAngularPatch) (f : LogCollarData)
      (y : CKSMixedGeometry.Point), 3*R < y 0 → y 0 < (7/2)*R →
      angularProjection y ∈ P.chart.target →
      (∀ᶠ z in 𝓝 y, f.sigma (radiusLogPoint z) = angularRoundMetric P.param (angularProjection z)) →
      f.fstar (radiusLogPoint y) = f₀ (P.chart.symm (angularProjection y)) →
      polarLift P (physicalCollarMetric R f) (polarParam P y) =
        spatialMatrix (CKSCartesianOuter.metric f₀ m R) (polarParam P y) ∧
      polarLift P (physicalCollarTensor R f) (polarParam P y) =
        spatialMatrix (CKSCartesianOuter.tensor f₀ m R) (polarParam P y) := by
  obtain ⟨R₀,hR₀,hpos⟩ := CKSCartesianOuter.cartesian_radicand_positive f₀ hf₀ m
  refine ⟨R₀,hR₀,?_⟩
  intro R hR P f y hr ht hy hσ hf
  have h12 := hR₀.trans hR
  have hrp : 0 < y 0 := by linarith
  have hn := polarParam_norm P hrp.le
  have hp := hpos R hR (polarParam P y) (by rw [hn]; exact hr.le)
  have hb := collar_outer_blocks P f f₀ hf₀ m hbal h12 hr ht hy hσ hf hp
  constructor
  · apply (polarLift_reconstruction P (physicalCollarMetric R f) hrp hy).2
    have hlocal := radial_matrix_polar P (CKSCartesianOuter.metric f₀ m R)
      (CKSCartesianOuter.radicand f₀ m R (polarParam P y))⁻¹ 1 hrp hy
      (by simp only [CKSCartesianOuter.metric,one_smul])
    simp only [one_mul] at hlocal
    intro i j
    exact congrArg (fun M : AmbientMat => M i j) (hlocal.trans hb.1.symm)
  · apply (polarLift_reconstruction P (physicalCollarTensor R f) hrp hy).2
    have hmat := outer_tensor_initial_matrix f₀ m h12
      (by rw [hn]; exact hrp) (by rw [hn]; exact ht)
    rw [hn] at hmat
    have hlocal := radial_matrix_polar P (CKSCartesianOuter.tensor f₀ m R)
      ((1+1/(y 0)^2)/CKSCartesianOuter.radicand f₀ m R (polarParam P y)) 1 hrp hy
      (by simpa only [one_smul] using hmat)
    simp only [one_mul] at hlocal
    intro i j
    exact congrArg (fun M : AmbientMat => M i j) (hlocal.trans hb.2.symm)
end
end CKSLorentz

end



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma CollarSourcePatch.aspect_eq {A B : SpatialTensor} (P : CollarSourcePatch A B) (θ : Angle) :
    sourceAspect P.fields.base θ = cksChartMassAspect P.patch.param P.mr P.mg P.mK θ := by
  unfold sourceAspect cksChartMassAspect angularMetricTrace
  rw [inverse_eq]
  simp only [CollarSourcePatch.fields,spatialSourceFields,cksSourceFields,CKSMixedGeometry.traceProduct,
    Matrix.trace,Matrix.diag]
  rfl
lemma SourceCollarAtlas.fstar_mass {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hm : q.HasMassAspect M) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : angularProjection y ∈ (q.patch i).region) :
    (sourceCollarData (q.patch i).fields.logFields).fstar (radiusLogPoint y) =
      heatDatum M hM ((q.patch i).patch.chart.symm (angularProjection y)) := by
  change cksLeadingField (q.patch i).fields.base.logFields (radiusLogPoint y) = _
  rw [source_leading_mass]
  change sourceAspect (q.patch i).fields.base (angularProjection y)/4 = _
  rw [(q.patch i).aspect_eq,hm i _ hy]
  rfl
lemma SourceCollarAtlas.eventually_outer_recovery {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hm : q.HasMassAspect M) (m : ℝ) (hc : bondiCharge M = (m,0)) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R ≥ R₀, ∀ i x,
      3*R < ‖x‖ → ‖x‖ < (7/2)*R → x ∈ polarCone (q.patch i).patch (q.patch i).region →
      (q.patch i).metric R x = spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) x ∧
      (q.patch i).tensor R x = spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) x := by
  obtain ⟨R₀,hR₀,hrec⟩ := physical_collar_outer_spatial_overlap (heatDatum M hM)
    (heatDatum_smooth hM) m (heatDatum_balanced hM hc)
  refine ⟨R₀,hR₀,?_⟩
  intro R hR i x hr ht hx
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hx
  have hyr : (polarInverse (q.patch i).patch x) 0 = ‖x‖ := by simp [polarInverse]
  have hh := hrec R hR (q.patch i).patch (sourceCollarData (q.patch i).fields.logFields)
    (polarInverse (q.patch i).patch x) (by rwa [hyr]) (by rwa [hyr]) hyt
    (Eventually.of_forall (fun z => rfl)) (q.fstar_mass hM hm i hyw)
  rw [hyx] at hh
  exact hh
end
end CKSLorentz

end




































































end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSLorentz.SourceCollarAtlas.eventually_outer_recovery.{u_1} := @OAI.CKSLorentz.SourceCollarAtlas.eventually_outer_recovery.{u_1}
