-- Prove2me | solution 1 for MaGoldfarbFPC.Convergence.theorem4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T13:16:06.497398+00:00
-- url     : https://prove2.me/submissions/424180f6-5bb9-48ff-b115-39feca20d8c5

/-
SPDX-License-Identifier: Apache-2.0
Full native fixed-point matrix-shrinkage convergence theorem.
Mathematical source: S. Ma, D. Goldfarb, L. Chen,
Fixed point and Bregman iterative methods for matrix rank minimization,
arXiv:0905.1643v2, Theorem 4, printed pp. 8–12.
The proof freshly constructs a polar dual certificate for the literal Mathlib
singular-value sum, derives the actual SVD-shrink subgradient inequality,
and proves minimizer existence and whole-run convergence by quantitative Fejer
monotonicity and a joint cluster of consecutive iterates.
No accepted proof implementation is copied. All native assumptions are unchanged.
-/
import Mathlib
import Definitions.Def_MaGoldfarbFPC_Convergence_Basic

-- BEGIN Foundation
open scoped BigOperators InnerProductSpace Topology
open Filter Topology Set Matrix

namespace MatrixFPCProof
open CaiCandesShen.Convergence MaGoldfarbFPC.Convergence
end MatrixFPCProof
-- END Foundation

-- BEGIN Spectral
open scoped BigOperators InnerProductSpace
open Matrix
namespace MatrixFPCProof
open CaiCandesShen.Convergence

abbrev EV (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev spectralIndex (n : ℕ) := Fin (Module.finrank ℝ (EV n))
noncomputable def gramBasis {m n : ℕ} (X : Mat m n) :
    OrthonormalBasis (spectralIndex n) ℝ (EV n) :=
  (Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
noncomputable def sigma {m n : ℕ} (X : Mat m n) (i : spectralIndex n) : ℝ :=
  Real.sqrt ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues rfl i)

lemma sigma_nonneg {m n : ℕ} (X : Mat m n) (i : spectralIndex n) : 0 ≤ sigma X i :=
  Real.sqrt_nonneg _
lemma sigma_sq {m n : ℕ} (X : Mat m n) (i : spectralIndex n) :
    sigma X i ^ 2 = (Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues rfl i := by
  exact Real.sq_sqrt ((Matrix.toEuclideanLin X).isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i)

lemma nuclear_eq_sum {m n : ℕ} (X : Mat m n) : nuclearNorm X = ∑ i, sigma X i := by
  classical
  unfold nuclearNorm LinearMap.singularValues
  rw [Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  rfl

lemma gram_inner {m n : ℕ} (X : Mat m n) (i j : spectralIndex n) :
    ⟪Matrix.toEuclideanLin X (gramBasis X i), Matrix.toEuclideanLin X (gramBasis X j)⟫_ℝ =
      if i = j then sigma X j ^ 2 else 0 := by
  rw [← LinearMap.adjoint_inner_right]
  change ⟪gramBasis X i, ((Matrix.toEuclideanLin X).adjoint.comp
    (Matrix.toEuclideanLin X)) (gramBasis X j)⟫_ℝ = _
  rw [show ((Matrix.toEuclideanLin X).adjoint.comp (Matrix.toEuclideanLin X)) (gramBasis X j) =
      ((Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.eigenvalues rfl j) • gramBasis X j from
      (Matrix.toEuclideanLin X).isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl j]
  rw [inner_smul_right, orthonormal_iff_ite.mp (gramBasis X).orthonormal, sigma_sq]
  split_ifs <;> simp_all

lemma frobInner_eq_basis {m n : ℕ} (X Y : Mat m n)
    (b : OrthonormalBasis (spectralIndex n) ℝ (EV n)) :
    frobInner X Y = ∑ i, ⟪Matrix.toEuclideanLin X (b i), Matrix.toEuclideanLin Y (b i)⟫_ℝ := by
  classical
  have h1 := LinearMap.trace_eq_sum_inner
    ((Matrix.toEuclideanLin X).adjoint.comp (Matrix.toEuclideanLin Y)) b
  have h2 := LinearMap.trace_eq_sum_inner
    ((Matrix.toEuclideanLin X).adjoint.comp (Matrix.toEuclideanLin Y)) (EuclideanSpace.basisFun (Fin n) ℝ)
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right] at h1 h2
  rw [← h1, h2]
  have happ (A : Mat m n) (j : Fin n) :
      Matrix.toEuclideanLin A (EuclideanSpace.basisFun (Fin n) ℝ j) =
        WithLp.toLp 2 (fun i => A i j) := by
    ext i
    simp [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply ]
  simp only [happ, frobInner, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma frob_sq_eq_sigma {m n : ℕ} (X : Mat m n) :
    frobNorm X ^ 2 = ∑ i, sigma X i ^ 2 := by
  rw [frobNorm, Real.sq_sqrt]
  · rw [frobInner_eq_basis X X (gramBasis X)]
    apply Finset.sum_congr rfl
    intro i _
    have hh := gram_inner X i i
    simpa using hh
  · unfold frobInner
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

end MatrixFPCProof
-- END Spectral

-- BEGIN Polar
open scoped BigOperators InnerProductSpace
open Matrix
namespace MatrixFPCProof
open CaiCandesShen.Convergence

noncomputable def leftVector {m n : ℕ} (X : Mat m n) (i : spectralIndex n) : EV m :=
  (sigma X i)⁻¹ • Matrix.toEuclideanLin X (gramBasis X i)

lemma left_inner {m n : ℕ} (X : Mat m n) (i j : spectralIndex n) :
    ⟪leftVector X i, leftVector X j⟫_ℝ =
      if i = j then (if sigma X i = 0 then 0 else 1) else 0 := by
  classical
  simp only [leftVector, real_inner_smul_left, real_inner_smul_right, gram_inner]
  by_cases hij : i = j
  · subst j
    by_cases h : sigma X i = 0
    · simp [h]
    · simp only [ite_true, if_neg h]
      field_simp
  · simp [hij]

lemma image_eq_sigma_left {m n : ℕ} (X : Mat m n) (i : spectralIndex n) :
    Matrix.toEuclideanLin X (gramBasis X i) = sigma X i • leftVector X i := by
  by_cases h : sigma X i = 0
  · have hh := gram_inner X i i
    simp only [ite_true, h, zero_pow (by decide : 2 ≠ 0)] at hh
    have hz : Matrix.toEuclideanLin X (gramBasis X i) = 0 := inner_self_eq_zero.mp hh
    simp [h, hz]
  · simp [leftVector, smul_smul, h]

lemma left_norm_le {m n : ℕ} (X : Mat m n) (i : spectralIndex n) : ‖leftVector X i‖ ≤ 1 := by
  have hh := left_inner X i i
  simp only [ite_true, real_inner_self_eq_norm_sq] at hh
  split_ifs at hh <;> nlinarith [norm_nonneg (leftVector X i)]

noncomputable def polarMap {m n : ℕ} (X : Mat m n) : EV n →ₗ[ℝ] EV m where
  toFun z := ∑ i, ⟪gramBasis X i,z⟫_ℝ • leftVector X i
  map_add' a b := by simp [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' a z := by simp [inner_smul_right, mul_smul, Finset.smul_sum]

lemma polar_apply_basis {m n : ℕ} (X : Mat m n) (i : spectralIndex n) :
    polarMap X (gramBasis X i) = leftVector X i := by
  classical
  simp [polarMap, orthonormal_iff_ite.mp (gramBasis X).orthonormal]

lemma polar_contracts {m n : ℕ} (X : Mat m n) (z : EV n) : ‖polarMap X z‖ ≤ ‖z‖ := by
  classical
  have heq : ‖polarMap X z‖ ^ 2 =
      ∑ i, ⟪gramBasis X i,z⟫_ℝ ^ 2 * (if sigma X i = 0 then 0 else 1) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [polarMap, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, left_inner]
    simp [mul_ite, pow_two]
  have hle : ‖polarMap X z‖ ^ 2 ≤ ∑ i, ‖⟪gramBasis X i,z⟫_ℝ‖ ^ 2 := by
    rw [heq]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp [sq_nonneg]
  rw [(gramBasis X).sum_sq_norm_inner_right] at hle
  nlinarith [norm_nonneg (polarMap X z), norm_nonneg z]

def IsContraction {m n : ℕ} (Z : Mat m n) : Prop :=
  ∀ z : EV n, ‖Matrix.toEuclideanLin Z z‖ ≤ ‖z‖

noncomputable def polarMatrix {m n : ℕ} (X : Mat m n) : Mat m n :=
  Matrix.toEuclideanLin.symm (polarMap X)

lemma polarMatrix_contracts {m n : ℕ} (X : Mat m n) : IsContraction (polarMatrix X) := by
  intro z
  simpa [polarMatrix] using polar_contracts X z

lemma contraction_pairing_le {m n : ℕ} (X Z : Mat m n) (hz : IsContraction Z) :
    frobInner Z X ≤ nuclearNorm X := by
  rw [frobInner_eq_basis Z X (gramBasis X), nuclear_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [image_eq_sigma_left, real_inner_smul_right]
  have hzi : ‖Matrix.toEuclideanLin Z (gramBasis X i)‖ ≤ 1 := by
    simpa using hz (gramBasis X i)
  have hi := real_inner_le_norm (Matrix.toEuclideanLin Z (gramBasis X i)) (leftVector X i)
  have hu := left_norm_le X i
  have hprod := mul_le_mul hzi hu (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hp : ⟪Matrix.toEuclideanLin Z (gramBasis X i),leftVector X i⟫_ℝ ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hp (sigma_nonneg X i)]

lemma polar_attains {m n : ℕ} (X : Mat m n) : frobInner (polarMatrix X) X = nuclearNorm X := by
  rw [frobInner_eq_basis _ X (gramBasis X), nuclear_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [polarMatrix, LinearEquiv.apply_symm_apply, polar_apply_basis, image_eq_sigma_left,
    real_inner_smul_right, left_inner, ite_true]
  by_cases h : sigma X i = 0 <;> simp [h]

end MatrixFPCProof
-- END Polar

-- BEGIN Nuclear
open scoped BigOperators InnerProductSpace
open Matrix
namespace MatrixFPCProof
open CaiCandesShen.Convergence

lemma frobInner_add_right {m n : ℕ} (Z X Y : Mat m n) :
    frobInner Z (X+Y) = frobInner Z X + frobInner Z Y := by
  simp [frobInner, mul_add, Finset.sum_add_distrib]
lemma frobInner_smul_right {m n : ℕ} (Z X : Mat m n) (a : ℝ) :
    frobInner Z (a • X) = a * frobInner Z X := by
  simp [frobInner, Finset.mul_sum, mul_left_comm]
lemma frobInner_neg_left {m n : ℕ} (Z X : Mat m n) : frobInner (-Z) X = -frobInner Z X := by
  simp [frobInner, Finset.sum_neg_distrib]
lemma contraction_neg {m n : ℕ} (Z : Mat m n) (hz : IsContraction Z) : IsContraction (-Z) := by
  intro z
  simpa using hz z
lemma abs_pairing_le {m n : ℕ} (X Z : Mat m n) (hz : IsContraction Z) :
    |frobInner Z X| ≤ nuclearNorm X := by
  apply abs_le.mpr
  constructor
  · have hh := contraction_pairing_le X (-Z) (contraction_neg Z hz)
    rw [frobInner_neg_left] at hh
    linarith
  · exact contraction_pairing_le X Z hz
lemma nuclear_nonneg {m n : ℕ} (X : Mat m n) : 0 ≤ nuclearNorm X := by
  rw [nuclear_eq_sum]
  exact Finset.sum_nonneg fun i _ => sigma_nonneg X i
lemma nuclear_add_le {m n : ℕ} (X Y : Mat m n) :
    nuclearNorm (X+Y) ≤ nuclearNorm X + nuclearNorm Y := by
  rw [← polar_attains (X+Y), frobInner_add_right]
  exact add_le_add (contraction_pairing_le X _ (polarMatrix_contracts _))
    (contraction_pairing_le Y _ (polarMatrix_contracts _))
lemma nuclear_smul_le {m n : ℕ} (a : ℝ) (X : Mat m n) :
    nuclearNorm (a • X) ≤ |a| * nuclearNorm X := by
  rw [← polar_attains (a • X), frobInner_smul_right]
  calc
    a * frobInner (polarMatrix (a • X)) X ≤ |a * frobInner (polarMatrix (a • X)) X| := le_abs_self _
    _ = |a| * |frobInner (polarMatrix (a • X)) X| := abs_mul _ _
    _ ≤ |a| * nuclearNorm X := mul_le_mul_of_nonneg_left
      (abs_pairing_le X _ (polarMatrix_contracts _)) (abs_nonneg _)
lemma nuclear_zero {m n : ℕ} : nuclearNorm (0 : Mat m n) = 0 := by
  have hh := nuclear_smul_le (0:ℝ) (0:Mat m n)
  simp only [zero_smul, abs_zero, zero_mul] at hh
  exact le_antisymm hh (nuclear_nonneg _)
lemma nuclear_smul {m n : ℕ} (a : ℝ) (X : Mat m n) :
    nuclearNorm (a • X) = |a| * nuclearNorm X := by
  apply le_antisymm (nuclear_smul_le a X)
  by_cases ha : a = 0
  · simp [ha, nuclear_zero]
  · have hh := nuclear_smul_le a⁻¹ (a • X)
    simp only [smul_smul, inv_mul_cancel₀ ha, one_smul, abs_inv] at hh
    have hp := mul_le_mul_of_nonneg_left hh (abs_nonneg a)
    simpa [mul_assoc, abs_ne_zero.mpr ha] using hp
lemma frob_le_nuclear {m n : ℕ} (X : Mat m n) : frobNorm X ≤ nuclearNorm X := by
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ)
    (f:=sigma X) (fun i _ => sigma_nonneg X i)
  rw [← frob_sq_eq_sigma, ← nuclear_eq_sum] at hh
  nlinarith [nuclear_nonneg X]
lemma nuclear_le_frob {m n : ℕ} (X : Mat m n) :
    nuclearNorm X ≤ Real.sqrt n * frobNorm X := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (spectralIndex n))
    (sigma X) (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  have hd : Module.finrank ℝ (EV n) = n := by simp [EV]
  simp only [spectralIndex, Fintype.card_fin, hd] at hh
  rw [← nuclear_eq_sum, ← frob_sq_eq_sigma] at hh
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hn : 0 ≤ frobNorm X := Real.sqrt_nonneg _
  have hp : 0 ≤ Real.sqrt n * frobNorm X := mul_nonneg (Real.sqrt_nonneg _) hn
  nlinarith [sq_nonneg (nuclearNorm X - Real.sqrt n * frobNorm X)]

end MatrixFPCProof
-- END Nuclear

-- BEGIN SVDGeometry
open scoped BigOperators InnerProductSpace
open Matrix
namespace MatrixFPCProof
open CaiCandesShen.Convergence

noncomputable def col {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ) (i : Fin r) : EV m :=
  WithLp.toLp 2 (fun j => U j i)
def factors {m n r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ) (a : Fin r → ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ) : Mat m n := fun i j => ∑ k, a k * U i k * V j k
lemma factors_eq {m n r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ) (a : Fin r → ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ) : factors U a V = U * diagonal a * Vᵀ := by
  ext i j
  change (∑ k, a k * U i k * V j k) = ∑ k, (U * diagonal a) i k * V j k
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro k _
  ring
lemma col_orthonormal {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ) (hU : Uᵀ * U = 1) :
    Orthonormal ℝ (col U) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hh := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M i j) hU
  simpa [col, PiLp.inner_apply, RCLike.inner_apply, Matrix.mul_apply, Matrix.one_apply,
    mul_comm] using hh
lemma factors_apply {m n r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ) (a : Fin r → ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ) (z : EV n) :
    Matrix.toEuclideanLin (factors U a V) z = ∑ i, (a i * ⟪col V i,z⟫_ℝ) • col U i := by
  ext j
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, factors, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, col, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring
lemma factors_pairing {m n r : ℕ} (Q : Mat m n) (U : Matrix (Fin m) (Fin r) ℝ)
    (a : Fin r → ℝ) (V : Matrix (Fin n) (Fin r) ℝ) :
    frobInner Q (factors U a V) = ∑ i, a i * ⟪Matrix.toEuclideanLin Q (col V i),col U i⟫_ℝ := by
  classical
  simp only [frobInner, factors, col, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  simp only [Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ k, Q i j * (a k * U i k * V j k)) =
        ∑ i, ∑ k, ∑ j, Q i j * (a k * U i k * V j k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, Q i j * (a k * U i k * V j k) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma factors_contracts {m n r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ*U=1) (hV : Vᵀ*V=1)
    (c : Fin r → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) : IsContraction (factors U c V) := by
  intro z
  have hu := col_orthonormal U hU
  have hv := col_orthonormal V hV
  have hh := hu.inner_sum (fun i => c i * ⟪col V i,z⟫_ℝ)
    (fun i => c i * ⟪col V i,z⟫_ℝ) Finset.univ
  simp only [conj_trivial, real_inner_self_eq_norm_sq, ← pow_two] at hh
  have hb := hv.sum_inner_products_le (s:=Finset.univ) z
  simp only [Real.norm_eq_abs, sq_abs] at hb
  have hle : ∑ i, (c i * ⟪col V i,z⟫_ℝ)^2 ≤ ∑ i, ⟪col V i,z⟫_ℝ^2 := by
    apply Finset.sum_le_sum
    intro i _
    have hci := hc i
    nlinarith [sq_nonneg (⟪col V i,z⟫_ℝ), mul_nonneg (sq_nonneg (⟪col V i,z⟫_ℝ))
      (show 0 ≤ 1-c i^2 by nlinarith)]
  rw [factors_apply]
  nlinarith [norm_nonneg (∑ i, (c i * ⟪col V i,z⟫_ℝ) • col U i), norm_nonneg z]

lemma factors_pairing_le {m n r : ℕ} (Q : Mat m n) (hQ : IsContraction Q)
    (U : Matrix (Fin m) (Fin r) ℝ) (V : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ*U=1) (hV : Vᵀ*V=1) (a : Fin r → ℝ) (ha : ∀ i,0≤a i) :
    frobInner Q (factors U a V) ≤ ∑ i,a i := by
  rw [factors_pairing]
  apply Finset.sum_le_sum
  intro i _
  have hu := (col_orthonormal U hU).norm_eq_one i
  have hv := (col_orthonormal V hV).norm_eq_one i
  have hq := hQ (col V i)
  have hi := real_inner_le_norm (Matrix.toEuclideanLin Q (col V i)) (col U i)
  rw [hu, mul_one] at hi
  rw [hv] at hq
  have hp := mul_le_mul_of_nonneg_left (hi.trans hq) (ha i)
  simpa using hp

lemma factors_nuclear_le {m n r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ*U=1) (hV : Vᵀ*V=1)
    (a : Fin r → ℝ) (ha : ∀ i,0≤a i) : nuclearNorm (factors U a V) ≤ ∑ i,a i := by
  rw [← polar_attains (factors U a V)]
  exact factors_pairing_le _ (polarMatrix_contracts _) U V hU hV a ha
end MatrixFPCProof
-- END SVDGeometry

-- BEGIN ShrinkCertificate
open scoped BigOperators InnerProductSpace
open Matrix
namespace MatrixFPCProof
open CaiCandesShen.Convergence

lemma factors_apply_col {m n r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ) (hV : Vᵀ*V=1) (c : Fin r → ℝ) (i : Fin r) :
    Matrix.toEuclideanLin (factors U c V) (col V i) = c i • col U i := by
  classical
  rw [factors_apply]
  simp [orthonormal_iff_ite.mp (col_orthonormal V hV)]

lemma factors_pairing_self {m n r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (V : Matrix (Fin n) (Fin r) ℝ) (hU : Uᵀ*U=1) (hV : Vᵀ*V=1)
    (c a : Fin r → ℝ) : frobInner (factors U c V) (factors U a V) = ∑ i,a i*c i := by
  rw [factors_pairing]
  apply Finset.sum_congr rfl
  intro i _
  rw [factors_apply_col U V hV, real_inner_smul_left]
  simp [(col_orthonormal U hU).norm_eq_one i]

lemma shrink_scalar {s ν : ℝ} (hs : 0 < s) (hν : 0 < ν) :
    (0 ≤ min (s/ν) 1 ∧ min (s/ν) 1 ≤ 1) ∧
    s-max (s-ν) 0 = ν*min (s/ν) 1 ∧
    max (s-ν) 0 * min (s/ν) 1 = max (s-ν) 0 := by
  constructor
  · exact ⟨le_min (by positivity) (by norm_num), min_le_right _ _⟩
  by_cases h : s ≤ ν
  · have hd : s/ν ≤ 1 := (div_le_one hν).mpr h
    simp only [min_eq_left hd, max_eq_right (by linarith : s-ν≤0), sub_zero, zero_mul]
    constructor
    · field_simp
    · trivial
  · have hd : 1 ≤ s/ν := (le_div_iff₀ hν).mpr (by linarith)
    have hm : max (s-ν) 0 = s-ν := max_eq_left (by linarith)
    simp only [min_eq_right hd, hm, mul_one]
    constructor
    · ring
    · trivial

lemma shrink_subgradient {m n : ℕ} (ν : ℝ) (hν : 0 < ν) (Y X : Mat m n)
    (h : IsShrink ν Y X) (Z : Mat m n) :
    ν*nuclearNorm X + frobInner (Y-X) (Z-X) ≤ ν*nuclearNorm Z := by
  classical
  obtain ⟨r,U,s,V,⟨hU,hV,hs,hY⟩,hX⟩ := h
  let a : Fin r → ℝ := fun i => max (s i-ν) 0
  let c : Fin r → ℝ := fun i => min (s i/ν) 1
  have hxc : X = factors U a V := by simpa only [factors_eq] using hX
  have hyc : Y = factors U s V := by simpa only [factors_eq] using hY
  have hscalar (i : Fin r) := shrink_scalar (hs i) hν
  have hc : IsContraction (factors U c V) :=
    factors_contracts U V hU hV c (fun i => (hscalar i).1)
  have hdiff : Y-X = ν • factors U c V := by
    rw [hxc,hyc]
    ext i j
    simp only [factors, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hh := (hscalar k).2.1
    dsimp [a,c]
    calc
      s k * U i k * V j k - max (s k - ν) 0 * U i k * V j k =
        (s k - max (s k-ν) 0) * U i k * V j k := by ring
      _ = (ν * min (s k/ν) 1) * U i k * V j k := by rw [hh]
      _ = ν * (min (s k/ν) 1 * U i k * V j k) := by ring
  have hatt : frobInner (factors U c V) X = nuclearNorm X := by
    have he : frobInner (factors U c V) X = ∑ i,a i := by
      rw [hxc, factors_pairing_self U V hU hV]
      apply Finset.sum_congr rfl
      intro i _
      exact (hscalar i).2.2
    apply le_antisymm (contraction_pairing_le X _ hc)
    rw [he,hxc]
    exact factors_nuclear_le U V hU hV a (fun i => le_max_right _ _)
  have hz := contraction_pairing_le Z _ hc
  have he : frobInner (Y-X) (Z-X) = ν * (frobInner (factors U c V) Z-nuclearNorm X) := by
    rw [hdiff]
    have hlin (Q B C : Mat m n) : frobInner (ν • Q) (B-C) =
        ν*(frobInner Q B-frobInner Q C) := by
      simp [frobInner, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    rw [hlin,hatt]
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hz hν.le]
end MatrixFPCProof
-- END ShrinkCertificate

-- BEGIN Geometry
open scoped BigOperators InnerProductSpace Topology
open Filter Topology Set

namespace MatrixFPCProof
open CaiCandesShen.Convergence MaGoldfarbFPC.Convergence

abbrev MSpace (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

def flat {m n : ℕ} (X : Mat m n) : MSpace m n :=
  WithLp.toLp 2 (fun ij => X ij.1 ij.2)

def unflat {m n : ℕ} (x : MSpace m n) : Mat m n :=
  fun i j => x (i, j)

@[simp] theorem unflat_flat {m n : ℕ} (X : Mat m n) : unflat (flat X) = X := rfl
@[simp] theorem flat_unflat {m n : ℕ} (x : MSpace m n) : flat (unflat x) = x := rfl

def flatEquiv (m n : ℕ) : Mat m n ≃ₗ[ℝ] MSpace m n where
  toFun := flat
  invFun := unflat
  left_inv := unflat_flat
  right_inv := flat_unflat
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem flat_zero {m n : ℕ} : flat (0 : Mat m n) = 0 := rfl
@[simp] theorem flat_add {m n : ℕ} (X Y : Mat m n) :
    flat (X + Y) = flat X + flat Y := rfl
@[simp] theorem flat_sub {m n : ℕ} (X Y : Mat m n) :
    flat (X - Y) = flat X - flat Y := rfl
@[simp] theorem flat_smul {m n : ℕ} (a : ℝ) (X : Mat m n) :
    flat (a • X) = a • flat X := rfl
@[simp] theorem unflat_zero {m n : ℕ} : unflat (0 : MSpace m n) = 0 := rfl
@[simp] theorem unflat_add {m n : ℕ} (x y : MSpace m n) :
    unflat (x + y) = unflat x + unflat y := rfl
@[simp] theorem unflat_sub {m n : ℕ} (x y : MSpace m n) :
    unflat (x - y) = unflat x - unflat y := rfl
@[simp] theorem unflat_smul {m n : ℕ} (a : ℝ) (x : MSpace m n) :
    unflat (a • x) = a • unflat x := rfl

theorem flat_inner {m n : ℕ} (X Y : Mat m n) :
    ⟪flat X, flat Y⟫_ℝ = frobInner X Y := by
  simp [PiLp.inner_apply, flat, frobInner, Fintype.sum_prod_type, mul_comm]

theorem flat_norm {m n : ℕ} (X : Mat m n) : ‖flat X‖ = frobNorm X := by
  rw [frobNorm, ← flat_inner, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem unflat_inner {m n : ℕ} (x y : MSpace m n) :
    frobInner (unflat x) (unflat y) = ⟪x, y⟫_ℝ :=
  (flat_inner (unflat x) (unflat y)).symm

theorem unflat_norm {m n : ℕ} (x : MSpace m n) : frobNorm (unflat x) = ‖x‖ :=
  (flat_norm (unflat x)).symm

noncomputable def measurement {m n p : ℕ} (Aop : Fin p → Mat m n) :
    MSpace m n →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => ⟪flat (Aop i), x⟫_ℝ)
      map_add' := by intro x y; ext i; simp [inner_add_right]
      map_smul' := by intro a x; ext i; simp [inner_smul_right] }

@[simp] theorem measurement_apply {m n p : ℕ} (Aop : Fin p → Mat m n)
    (x : MSpace m n) (i : Fin p) :
    measurement Aop x i = ⟪flat (Aop i), x⟫_ℝ := rfl

theorem measurement_flat {m n p : ℕ} (Aop : Fin p → Mat m n) (X : Mat m n) :
    measurement Aop (flat X) = WithLp.toLp 2 (applyA Aop X) := by
  ext i
  exact flat_inner (Aop i) X

theorem flat_adjA {m n p : ℕ} (Aop : Fin p → Mat m n)
    (y : EuclideanSpace ℝ (Fin p)) :
    flat (adjA Aop y) = (measurement Aop).adjoint y := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left]
  change ⟪flatEquiv m n (∑ i, y i • Aop i), x⟫_ℝ = _
  rw [map_sum]
  change ⟪∑ i, y i • flat (Aop i), x⟫_ℝ = ⟪y, measurement Aop x⟫_ℝ
  simp [sum_inner, PiLp.inner_apply, inner_smul_left, mul_comm]

theorem measurement_opNorm {m n p : ℕ} (Aop : Fin p → Mat m n) :
    opNormA Aop = ‖measurement Aop‖ := by
  have hnorm (X : Mat m n) : ‖measurement Aop (flat X)‖ =
      Real.sqrt (∑ i, applyA Aop X i ^ 2) := by
    rw [measurement_flat, EuclideanSpace.norm_eq]
    simp
  unfold opNormA
  rw [← (measurement Aop).sSup_sphere_eq_norm]
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨flat X, ?_, ?_⟩
    · simpa [Metric.mem_sphere, dist_zero_right, flat_norm] using hX
    · exact hnorm X
  · rintro ⟨x, hx, rfl⟩
    refine ⟨unflat x, ?_, ?_⟩
    · simpa [Metric.mem_sphere, dist_zero_right, unflat_norm] using hx
    · exact (hnorm (unflat x)).symm

theorem flat_gradient {m n p : ℕ} (Aop : Fin p → Mat m n) (b : Fin p → ℝ)
    (X : Mat m n) :
    flat (g Aop b X) =
      (measurement Aop).adjoint (measurement Aop (flat X) - WithLp.toLp 2 b) := by
  rw [g, flat_adjA, measurement_flat]
  rfl

theorem sqNorm2_eq_norm_sq {p : ℕ} (v : Fin p → ℝ) :
    sqNorm2 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

end MatrixFPCProof
-- END Geometry

-- BEGIN GenericBasic
open scoped BigOperators InnerProductSpace Topology
open Filter Topology Set

namespace MatrixFPCProof

section Hilbert
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def grad (A : E →L[ℝ] F) (b : F) (x : E) : E := A.adjoint (A x - b)

noncomputable def objective (N : E → ℝ) (μ : ℝ) (A : E →L[ℝ] F) (b : F) (x : E) : ℝ :=
  μ * N x + 1 / 2 * ‖A x - b‖ ^ 2

theorem grad_sub (A : E →L[ℝ] F) (b : F) (x y : E) :
    grad A b x - grad A b y = A.adjoint (A (x - y)) := by
  simp [grad, ← map_sub, sub_sub_sub_cancel_right]

theorem continuous_grad (A : E →L[ℝ] F) (b : F) : Continuous (grad A b) :=
  A.adjoint.continuous.comp (A.continuous.sub continuous_const)

omit [CompleteSpace E] [CompleteSpace F] in
theorem continuous_objective (N : E → ℝ) (hN : Continuous N) (μ : ℝ)
    (A : E →L[ℝ] F) (b : F) : Continuous (objective N μ A b) :=
  (continuous_const.mul hN).add
    (continuous_const.mul ((A.continuous.sub continuous_const).norm.pow 2))

theorem quadratic_expansion (A : E →L[ℝ] F) (b : F) (x d : E) (t : ℝ) :
    1 / 2 * ‖A (x + t • d) - b‖ ^ 2 =
      1 / 2 * ‖A x - b‖ ^ 2 + t * ⟪grad A b x, d⟫_ℝ +
        t ^ 2 / 2 * ‖A d‖ ^ 2 := by
  have he : A (x + t • d) - b = (A x - b) + t • A d := by
    simp [map_add, map_smul, sub_add_eq_add_sub]
  rw [he, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [grad, ContinuousLinearMap.adjoint_inner_left, real_inner_comm (A d)]
  ring

theorem gradient_decrease (A : E →L[ℝ] F) (τ : ℝ) (e : E) :
    ‖e - τ • A.adjoint (A e)‖ ^ 2 ≤
      ‖e‖ ^ 2 - τ * (2 - τ * ‖A‖ ^ 2) * ‖A e‖ ^ 2 := by
  have hv : ‖A.adjoint (A e)‖ ≤ ‖A‖ * ‖A e‖ := by
    simpa using A.adjoint.le_opNorm (A e)
  have hv2 : ‖A.adjoint (A e)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖A e‖ ^ 2 := by
    nlinarith [norm_nonneg (A.adjoint (A e)), norm_nonneg A, norm_nonneg (A e)]
  have hs := mul_le_mul_of_nonneg_left hv2 (sq_nonneg τ)
  rw [norm_sub_sq_real, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith

theorem firm_fejer (A : E →L[ℝ] F) (τ : ℝ) (x y s : E)
    (hi : 0 ≤ ⟪y - s, x - s - τ • A.adjoint (A (x - s)) - (y - s)⟫_ℝ) :
    ‖y - s‖ ^ 2 + ‖x - s - τ • A.adjoint (A (x - s)) - (y - s)‖ ^ 2 +
      τ * (2 - τ * ‖A‖ ^ 2) * ‖A (x - s)‖ ^ 2 ≤ ‖x - s‖ ^ 2 := by
  have hg := gradient_decrease A τ (x - s)
  have he : x - s - τ • A.adjoint (A (x - s)) =
      (y - s) + (x - s - τ • A.adjoint (A (x - s)) - (y - s)) := by abel
  have hn := norm_add_sq_real (y - s)
    (x - s - τ • A.adjoint (A (x - s)) - (y - s))
  rw [← he] at hn
  linarith

end Hilbert
end MatrixFPCProof
-- END GenericBasic

-- BEGIN Minimizer
open scoped BigOperators InnerProductSpace Topology
open Filter Topology Set

namespace MatrixFPCProof

section Hilbert
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

omit [CompleteSpace F] in
theorem exists_minimizer (N : E → ℝ) (hN : Continuous N) (hNlow : ∀ x, ‖x‖ ≤ N x)
    (μ : ℝ) (hμ : 0 < μ) (A : E →L[ℝ] F) (b : F) :
    ∃ s, ∀ z, objective N μ A b s ≤ objective N μ A b z := by
  let R := objective N μ A b 0 / μ + 1
  have hlow (x : E) : μ * ‖x‖ ≤ objective N μ A b x := by
    have hn := mul_le_mul_of_nonneg_left (hNlow x) hμ.le
    dsimp [objective]
    nlinarith [sq_nonneg ‖A x - b‖]
  have hzero : 0 ≤ objective N μ A b 0 := by simpa using hlow 0
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨s, hs, hmin⟩ :=
    (isCompact_closedBall (0 : E) R).exists_isMinOn
      ⟨0, by simpa using hR⟩ (continuous_objective N hN μ A b).continuousOn
  refine ⟨s, fun z => ?_⟩
  by_cases hz : z ∈ Metric.closedBall (0 : E) R
  · exact hmin hz
  · have hnz : R < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hs0 : objective N μ A b s ≤ objective N μ A b 0 :=
      hmin (show (0 : E) ∈ Metric.closedBall 0 R by simpa using hR)
    have hr : μ * R = objective N μ A b 0 + μ := by
      dsimp [R]
      field_simp
    have hzlow := hlow z
    nlinarith

theorem minimizer_stationarity (N : E → ℝ) (hN : ConvexOn ℝ univ N)
    (μ : ℝ) (hμ : 0 < μ) (A : E →L[ℝ] F) (b : F) (s : E)
    (hs : ∀ z, objective N μ A b s ≤ objective N μ A b z) (z : E) :
    -⟪grad A b s, z - s⟫_ℝ ≤ μ * (N z - N s) := by
  let d := z - s
  let C := μ * (N z - N s) + ⟪grad A b s, d⟫_ℝ
  have htbound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      0 ≤ C + t / 2 * ‖A d‖ ^ 2 := by
    have he : s + t • d = (1 - t) • s + t • z := by
      dsimp [d]
      module
    have hconv := hN.2 (mem_univ s) (mem_univ z) (sub_nonneg.mpr ht1) ht.le
      (show 1 - t + t = (1 : ℝ) by ring)
    rw [← he] at hconv
    have hscaled := mul_le_mul_of_nonneg_left hconv hμ.le
    simp only [smul_eq_mul] at hscaled
    have hopt := hs (s + t • d)
    dsimp [objective] at hopt
    rw [quadratic_expansion] at hopt
    have hprod : 0 ≤ t * (C + t / 2 * ‖A d‖ ^ 2) := by
      dsimp [C]
      nlinarith
    exact nonneg_of_mul_nonneg_right hprod ht
  have hlim :
      Tendsto (fun k : ℕ => C + (1 / ((k : ℝ) + 1)) / 2 * ‖A d‖ ^ 2)
        atTop (𝓝 C) := by
    convert tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat.div_const 2).mul_const (‖A d‖ ^ 2))
      using 1; simp
  have hC : 0 ≤ C := ge_of_tendsto' hlim fun k =>
    htbound _ (by positivity) (by
      apply (div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
      nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k])
  dsimp [C, d] at hC
  linarith

theorem stationarity_minimizer (N : E → ℝ) (μ : ℝ) (A : E →L[ℝ] F) (b : F)
    (s : E) (hs : ∀ z, -⟪grad A b s, z - s⟫_ℝ ≤ μ * (N z - N s)) :
    ∀ z, objective N μ A b s ≤ objective N μ A b z := by
  intro z
  have hq := quadratic_expansion A b s (z - s) 1
  simp only [one_smul, add_sub_cancel, one_mul, one_pow] at hq
  have hz := hs z
  dsimp [objective]
  nlinarith [sq_nonneg ‖A (z - s)‖]

end Hilbert
end MatrixFPCProof
-- END Minimizer

-- BEGIN Fejer
open scoped BigOperators InnerProductSpace Topology
open Filter Topology Set

namespace MatrixFPCProof

section Hilbert
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

theorem step_fejer (N : E → ℝ) (hN : ConvexOn ℝ univ N)
    (μ τ : ℝ) (hμ : 0 < μ) (hτ : 0 < τ) (A : E →L[ℝ] F) (b : F)
    (x y s : E) (hs : ∀ z, objective N μ A b s ≤ objective N μ A b z)
    (hstep : ∀ z, τ * μ * N y + ⟪x - τ • grad A b x - y, z - y⟫_ℝ ≤ τ * μ * N z) :
    ‖y - s‖ ^ 2 + ‖x - s - τ • A.adjoint (A (x - s)) - (y - s)‖ ^ 2 +
      τ * (2 - τ * ‖A‖ ^ 2) * ‖A (x - s)‖ ^ 2 ≤ ‖x - s‖ ^ 2 := by
  apply firm_fejer
  have hmin := mul_le_mul_of_nonneg_left
    (minimizer_stationarity N hN μ hμ A b s hs y) hτ.le
  have hst := hstep s
  have he : s - y = -(y - s) := by abel
  rw [he, inner_neg_right, real_inner_comm] at hst
  have hv : A.adjoint (A (x - s)) = grad A b x - grad A b s :=
    (grad_sub A b x s).symm
  rw [hv]
  have he' : x - s - τ • (grad A b x - grad A b s) - (y - s) =
      (x - τ • grad A b x - y) + τ • grad A b s := by module
  rw [he', inner_add_right, inner_smul_right]
  have hcomm := real_inner_comm (grad A b s) (y - s)
  nlinarith

theorem run_distance_antitone (N : E → ℝ) (hN : ConvexOn ℝ univ N)
    (μ τ : ℝ) (hμ : 0 < μ) (hτ : 0 < τ) (A : E →L[ℝ] F)
    (hsize : τ * ‖A‖ ^ 2 < 2) (b : F) (x : ℕ → E) (s : E)
    (hs : ∀ z, objective N μ A b s ≤ objective N μ A b z)
    (hstep : ∀ k z, τ * μ * N (x (k + 1)) +
      ⟪x k - τ • grad A b (x k) - x (k + 1), z - x (k + 1)⟫_ℝ ≤ τ * μ * N z) :
    Antitone (fun k => ‖x k - s‖ ^ 2) := by
  apply antitone_nat_of_succ_le
  intro k
  have hh := step_fejer N hN μ τ hμ hτ A b (x k) (x (k + 1)) s hs (hstep k)
  have hc : 0 ≤ τ * (2 - τ * ‖A‖ ^ 2) := mul_nonneg hτ.le (by linarith)
  nlinarith [sq_nonneg ‖x k - s - τ • A.adjoint (A (x k - s)) - (x (k + 1) - s)‖,
    mul_nonneg hc (sq_nonneg ‖A (x k - s)‖)]

theorem fejer_convergence (N : E → ℝ) (hNcont : Continuous N)
    (hNconv : ConvexOn ℝ univ N) (hNlow : ∀ z, ‖z‖ ≤ N z)
    (μ τ : ℝ) (hμ : 0 < μ) (A : E →L[ℝ] F) (b : F)
    (hτ : 0 < τ) (hsize : τ * ‖A‖ ^ 2 < 2) (x : ℕ → E)
    (hstep : ∀ k z, τ * μ * N (x (k + 1)) +
      ⟪x k - τ • grad A b (x k) - x (k + 1), z - x (k + 1)⟫_ℝ ≤ τ * μ * N z) :
    ∃ q, (∀ z, objective N μ A b q ≤ objective N μ A b z) ∧
      Tendsto (fun k => ‖x k - q‖) atTop (𝓝 0) := by
  obtain ⟨s, hs⟩ := exists_minimizer N hNcont hNlow μ hμ A b
  have hanti := run_distance_antitone N hNconv μ τ hμ hτ A hsize b x s hs hstep
  have hbound (k : ℕ) : x k ∈ Metric.closedBall s ‖x 0 - s‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hanti (Nat.zero_le k))
  obtain ⟨qr, _, φ, hφ, hpairs⟩ :=
    ((isCompact_closedBall s ‖x 0 - s‖).prod (isCompact_closedBall s ‖x 0 - s‖)).tendsto_subseq
      (fun k => show (x k, x (k + 1)) ∈
        Metric.closedBall s ‖x 0 - s‖ ×ˢ Metric.closedBall s ‖x 0 - s‖
        from ⟨hbound k, hbound (k + 1)⟩)
  let q := qr.1
  let r := qr.2
  have hq : Tendsto (fun j => x (φ j)) atTop (𝓝 q) := by
    simpa [Function.comp_def, q] using (continuous_fst.tendsto qr).comp hpairs
  have hr : Tendsto (fun j => x (φ j + 1)) atTop (𝓝 r) := by
    simpa [Function.comp_def, r] using (continuous_snd.tendsto qr).comp hpairs
  have hbdd : BddBelow (range (fun k => ‖x k - s‖ ^ 2)) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩
  have hdist := tendsto_atTop_ciInf hanti hbdd
  have heqQ : (⨅ k, ‖x k - s‖ ^ 2) = ‖q - s‖ ^ 2 :=
    tendsto_nhds_unique (hdist.comp hφ.tendsto_atTop) ((hq.sub_const s).norm.pow 2)
  have heqR : (⨅ k, ‖x k - s‖ ^ 2) = ‖r - s‖ ^ 2 :=
    tendsto_nhds_unique (hdist.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop))
      ((hr.sub_const s).norm.pow 2)
  have hAs := A.continuous.tendsto (q - s) |>.comp (hq.sub_const s)
  have hadj := A.adjoint.continuous.tendsto (A (q - s)) |>.comp hAs
  have hdefect :=
    (((hq.sub_const s).sub (hadj.const_smul τ)).sub (hr.sub_const s)).norm.pow 2
  have hlimineq :
      ‖r - s‖ ^ 2 + ‖q - s - τ • A.adjoint (A (q - s)) - (r - s)‖ ^ 2 +
        τ * (2 - τ * ‖A‖ ^ 2) * ‖A (q - s)‖ ^ 2 ≤ ‖q - s‖ ^ 2 :=
    le_of_tendsto_of_tendsto'
      ((((hr.sub_const s).norm.pow 2).add hdefect).add
        ((hAs.norm.pow 2).const_mul (τ * (2 - τ * ‖A‖ ^ 2))))
      ((hq.sub_const s).norm.pow 2)
      (fun j => step_fejer N hNconv μ τ hμ hτ A b (x (φ j)) (x (φ j + 1)) s hs
        (hstep (φ j)))
  have hc : 0 < τ * (2 - τ * ‖A‖ ^ 2) := mul_pos hτ (by linarith)
  have hAz : ‖A (q - s)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖A (q - s)‖,
      sq_nonneg ‖q - s - τ • A.adjoint (A (q - s)) - (r - s)‖]
  have hA0 : A (q - s) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (A (q - s))]
  have hqr : q = r := by
    have hz : ‖q - s - τ • A.adjoint (A (q - s)) - (r - s)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖q - s - τ • A.adjoint (A (q - s)) - (r - s)‖]
    simp only [hA0, map_zero, smul_zero, sub_zero, sub_sub_sub_cancel_right] at hz
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (q - r)]
  have hrq : Tendsto (fun j => x (φ j + 1)) atTop (𝓝 q) := by simpa [hqr] using hr
  have hgrad := (continuous_grad A b).tendsto q |>.comp hq
  have hstation (z : E) : -⟪grad A b q, z - q⟫_ℝ ≤ μ * (N z - N q) := by
    have hpass :=
      le_of_tendsto'
        (((hNcont.tendsto q |>.comp hrq).const_mul (τ * μ)).add
          (((hq.sub (hgrad.const_smul τ)).sub hrq).inner (tendsto_const_nhds.sub hrq)))
        (fun j => hstep (φ j) z)
    have he : q - τ • grad A b q - q = -(τ • grad A b q) := by abel
    rw [he, inner_neg_left, real_inner_smul_left] at hpass
    have hscaled : τ * (-⟪grad A b q, z - q⟫_ℝ) ≤ τ * (μ * (N z - N q)) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ hτ).mp hscaled
  have hqmin := stationarity_minimizer N μ A b q hstation
  have hantiq := run_distance_antitone N hNconv μ τ hμ hτ A hsize b x q hqmin hstep
  have hbddq : BddBelow (range (fun k => ‖x k - q‖ ^ 2)) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩
  have hdistq := tendsto_atTop_ciInf hantiq hbddq
  have hsub0 : Tendsto (fun j => ‖x (φ j) - q‖ ^ 2) atTop (𝓝 0) := by
    simpa using ((hq.sub_const q).norm.pow 2)
  have hzero : (⨅ k, ‖x k - q‖ ^ 2) = 0 :=
    tendsto_nhds_unique (hdistq.comp hφ.tendsto_atTop) hsub0
  refine ⟨q, hqmin, ?_⟩
  have hsq : Tendsto (fun k => ‖x k - q‖ ^ 2) atTop (𝓝 0) := by
    simpa [hzero] using hdistq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq

end Hilbert
end MatrixFPCProof
-- END Fejer

-- BEGIN NuclearTransport
open scoped BigOperators InnerProductSpace Topology
open Filter Topology Set

namespace MatrixFPCProof
open CaiCandesShen.Convergence MaGoldfarbFPC.Convergence

noncomputable def transportedN {m n : ℕ} (x : MSpace m n) : ℝ := nuclearNorm (unflat x)

theorem transportedN_lower {m n : ℕ} (x : MSpace m n) : ‖x‖ ≤ transportedN x := by
  simpa [transportedN, unflat_norm] using frob_le_nuclear (unflat x)

theorem transportedN_convex (m n : ℕ) : ConvexOn ℝ univ (@transportedN m n) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  dsimp [transportedN]
  calc
    nuclearNorm (a • unflat x + b • unflat y) ≤
        nuclearNorm (a • unflat x) + nuclearNorm (b • unflat y) := nuclear_add_le _ _
    _ = a • nuclearNorm (unflat x) + b • nuclearNorm (unflat y) := by
      rw [nuclear_smul, nuclear_smul, abs_of_nonneg ha, abs_of_nonneg hb]
      rfl

theorem transportedN_continuous (m n : ℕ) : Continuous (@transportedN m n) := by
  have hdiff (x y : MSpace m n) :
      transportedN x - transportedN y ≤ Real.sqrt n * ‖x - y‖ := by
    have htri := nuclear_add_le (unflat (x - y)) (unflat y)
    rw [← unflat_add, sub_add_cancel] at htri
    have hupper := nuclear_le_frob (unflat (x - y))
    rw [unflat_norm] at hupper
    dsimp [transportedN]
    linarith
  have hlip : LipschitzWith ⟨Real.sqrt n, Real.sqrt_nonneg _⟩ (@transportedN m n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    change |transportedN x - transportedN y| ≤ Real.sqrt n * ‖x - y‖
    apply abs_sub_le_iff.mpr
    have hxy := hdiff x y
    have hyx := hdiff y x
    rw [norm_sub_rev] at hyx
    constructor <;> linarith
  exact hlip.continuous

theorem flat_objective {m n p : ℕ} (μ : ℝ) (Aop : Fin p → Mat m n)
    (b : Fin p → ℝ) (X : Mat m n) :
    objective transportedN μ (measurement Aop) (WithLp.toLp 2 b) (flat X) =
      obj μ Aop b X := by
  dsimp [objective, transportedN, obj]
  rw [measurement_flat, sqNorm2_eq_norm_sq]
  rfl

end MatrixFPCProof
-- END NuclearTransport

-- BEGIN NativeRoot
open scoped BigOperators InnerProductSpace Topology

namespace MaGoldfarbFPC.Convergence

open CaiCandesShen.Convergence Filter Topology

/-- Theorem 4, p. 12: for `μ > 0` and `τ ∈ (0, 2/λ_max(AᵀA))`, every sequence `{X^k}`
generated by the fixed point iterations (2.1) from an arbitrary `X⁰` converges in the
Frobenius norm to some optimal solution `X*` of problem (1.8). -/
theorem theorem4 {m n p : ℕ} (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (μ τ : ℝ)
    (hμ : 0 < μ) (hτ : StepRange τ Aop) (X : ℕ → Mat m n)
    (hX : IsFixedPointRun μ τ Aop b X) :
    ∃ Xs : Mat m n, IsOptimal μ Aop b Xs ∧
      Tendsto (fun k => frobNorm (X k - Xs)) atTop (𝓝 0) := by
  let N : MatrixFPCProof.MSpace m n → ℝ := MatrixFPCProof.transportedN
  let A := MatrixFPCProof.measurement Aop
  let b' : EuclideanSpace ℝ (Fin p) := WithLp.toLp 2 b
  let x : ℕ → MatrixFPCProof.MSpace m n := fun k => MatrixFPCProof.flat (X k)
  have hsize : τ * ‖A‖ ^ 2 < 2 := by
    simpa [A, MatrixFPCProof.measurement_opNorm] using hτ.2
  have hstep (k : ℕ) (z : MatrixFPCProof.MSpace m n) :
      τ * μ * N (x (k + 1)) +
        ⟪x k - τ • MatrixFPCProof.grad A b' (x k) - x (k + 1), z - x (k + 1)⟫_ℝ
        ≤ τ * μ * N z := by
    have hh := MatrixFPCProof.shrink_subgradient (τ * μ) (mul_pos hτ.1 hμ) _ _
      (hX k) (MatrixFPCProof.unflat z)
    simpa only [h, ← MatrixFPCProof.flat_inner, MatrixFPCProof.flat_sub,
      MatrixFPCProof.flat_smul, MatrixFPCProof.flat_gradient, MatrixFPCProof.flat_unflat,
      N, x, A, b', MatrixFPCProof.transportedN, MatrixFPCProof.unflat_flat,
      MatrixFPCProof.grad] using hh
  obtain ⟨q, hq, hlim⟩ := MatrixFPCProof.fejer_convergence N
    (MatrixFPCProof.transportedN_continuous m n) (MatrixFPCProof.transportedN_convex m n)
    MatrixFPCProof.transportedN_lower μ τ hμ A b' hτ.1 hsize x hstep
  refine ⟨MatrixFPCProof.unflat q, ?_, ?_⟩
  · intro Z
    have hh := hq (MatrixFPCProof.flat Z)
    change MatrixFPCProof.objective MatrixFPCProof.transportedN μ
      (MatrixFPCProof.measurement Aop) (WithLp.toLp 2 b) q ≤
      MatrixFPCProof.objective MatrixFPCProof.transportedN μ
        (MatrixFPCProof.measurement Aop) (WithLp.toLp 2 b) (MatrixFPCProof.flat Z) at hh
    rw [← MatrixFPCProof.flat_unflat q, MatrixFPCProof.flat_objective,
      MatrixFPCProof.flat_objective] at hh
    exact hh
  · simpa only [x, ← MatrixFPCProof.flat_norm, MatrixFPCProof.flat_sub,
      MatrixFPCProof.flat_unflat] using hlim

end MaGoldfarbFPC.Convergence
-- END NativeRoot

open MaGoldfarbFPC.Convergence CaiCandesShen.Convergence Filter Topology

theorem solution {m n p : ℕ} (Aop : Fin p → Mat m n) (b : Fin p → ℝ) (μ τ : ℝ)
    (hμ : 0 < μ) (hτ : StepRange τ Aop) (X : ℕ → Mat m n)
    (hX : IsFixedPointRun μ τ Aop b X) :
    ∃ Xs : Mat m n, IsOptimal μ Aop b Xs ∧
      Tendsto (fun k => frobNorm (X k - Xs)) atTop (𝓝 0) :=
  MaGoldfarbFPC.Convergence.theorem4 Aop b μ τ hμ hτ X hX
