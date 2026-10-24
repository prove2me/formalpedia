-- Prove2me | solution 1 for KLTNuclear.Oracle.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T18:23:09.100935+00:00
-- url     : https://prove2.me/submissions/74555974-ba20-49e0-8226-99b8f1b9db9a

import Init
import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model
import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

open _root_.MatrixCompletion
namespace Prior
open _root_.MatrixCompletion
namespace Eq11
open _root_.MatrixCompletion
namespace PriorSign
open MatrixCompletion

open scoped Classical BigOperators Matrix

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    spectralNorm (signMatrix S) ≤ 1 := by
  set E := signMatrix S with hE
  have hEntry : ∀ i j, E i j = ∑ k, S.u k i * S.v k j := by
    intro i j
    simp only [hE, signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]
  -- (E *ᵥ x) i = ∑ k, u_k i * c_k  where c_k = ∑ j, v_k j * x_j
  have hmulVec : ∀ (x : Fin n₂ → ℝ) (i : Fin n₁),
      (E *ᵥ x) i = ∑ k, S.u k i * (∑ j, S.v k j * x j) := by
    intro x i
    show (fun j => E i j) ⬝ᵥ x = _
    rw [dotProduct]
    calc ∑ j, E i j * x j
        = ∑ j, ∑ k, (S.u k i * S.v k j) * x j := by
          apply Finset.sum_congr rfl; intro j _; rw [hEntry, Finset.sum_mul]
      _ = ∑ k, ∑ j, (S.u k i * S.v k j) * x j := Finset.sum_comm
      _ = ∑ k, S.u k i * (∑ j, S.v k j * x j) := by
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  -- Squared norm of toEuclideanLin E applied to a Euclidean vector
  have hnormSq : ∀ (x : EuclideanSpace ℝ (Fin n₂)),
      ‖Matrix.toEuclideanLin E x‖ ^ 2
        = ∑ k, (∑ j, S.v k j * x j) ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    have hcoord : ∀ i, (Matrix.toEuclideanLin E x) i = (E *ᵥ (⇑x)) i := by
      intro i
      rfl
    set c : Fin r → ℝ := fun k => ∑ j, S.v k j * x j with hc
    calc ∑ i, (Matrix.toEuclideanLin E x) i ^ 2
        = ∑ i, (∑ k, S.u k i * c k) ^ 2 := by
          apply Finset.sum_congr rfl; intro i _
          rw [hcoord, hmulVec]
      _ = ∑ i, ∑ k, ∑ l, (S.u k i * c k) * (S.u l i * c l) := by
          apply Finset.sum_congr rfl; intro i _
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ k, ∑ l, ∑ i, (S.u k i * c k) * (S.u l i * c l) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_comm]
      _ = ∑ k, ∑ l, (c k * c l) * (∑ i, S.u k i * S.u l i) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro l _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
      _ = ∑ k, ∑ l, (c k * c l) * (if k = l then 1 else 0) := by
          apply Finset.sum_congr rfl; intro k _
          apply Finset.sum_congr rfl; intro l _
          rw [S.u_orthonormal]
      _ = ∑ k, c k ^ 2 := by
          apply Finset.sum_congr rfl; intro k _
          rw [show (∑ l, c k * c l * if k = l then (1:ℝ) else 0)
                = ∑ l, (if k = l then c k * c l else 0) by
            apply Finset.sum_congr rfl; intro l _; split <;> ring]
          rw [Finset.sum_ite_eq Finset.univ k (fun l => c k * c l)]
          simp [sq]
  -- Bessel inequality: ∑ k, c_k² ≤ ∑ j, x_j²  with c_k = ∑ j, v_k j x_j
  have hBessel : ∀ (x : Fin n₂ → ℝ),
      (∑ k, (∑ j, S.v k j * x j) ^ 2) ≤ ∑ j, (x j) ^ 2 := by
    intro x
    set c : Fin r → ℝ := fun k => ∑ j, S.v k j * x j with hc
    -- expand 0 ≤ ∑ j (x_j - ∑_k c_k v_k j)²
    have hnn : (0:ℝ) ≤ ∑ j, (x j - ∑ k, c k * S.v k j) ^ 2 := by
      apply Finset.sum_nonneg; intro j _; positivity
    -- last term: ∑ j (∑ k c_k v_k j)² = ∑ k c_k²
    have hlast : (∑ j, (∑ k, c k * S.v k j) ^ 2) = ∑ k, c k ^ 2 := by
      calc ∑ j, (∑ k, c k * S.v k j) ^ 2
          = ∑ j, ∑ k, ∑ l, (c k * S.v k j) * (c l * S.v l j) := by
            apply Finset.sum_congr rfl; intro j _
            rw [sq, Finset.sum_mul_sum]
        _ = ∑ k, ∑ l, ∑ j, (c k * S.v k j) * (c l * S.v l j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_comm]
        _ = ∑ k, ∑ l, (c k * c l) * (∑ j, S.v k j * S.v l j) := by
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro l _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ = ∑ k, ∑ l, (c k * c l) * (if k = l then 1 else 0) := by
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro l _
            rw [S.v_orthonormal]
        _ = ∑ k, c k ^ 2 := by
            apply Finset.sum_congr rfl; intro k _
            rw [show (∑ l, c k * c l * if k = l then (1:ℝ) else 0)
                  = ∑ l, (if k = l then c k * c l else 0) by
              apply Finset.sum_congr rfl; intro l _; split <;> ring]
            rw [Finset.sum_ite_eq Finset.univ k (fun l => c k * c l)]
            simp [sq]
    -- cross term: ∑ j x_j (∑ k c_k v_k j) = ∑ k c_k²
    have hcross : (∑ j, x j * (∑ k, c k * S.v k j)) = ∑ k, c k ^ 2 := by
      calc ∑ j, x j * (∑ k, c k * S.v k j)
          = ∑ j, ∑ k, c k * (S.v k j * x j) := by
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        _ = ∑ k, c k * (∑ j, S.v k j * x j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum]
        _ = ∑ k, c k ^ 2 := by
            apply Finset.sum_congr rfl; intro k _
            rw [hc]; simp only; rw [sq]
    -- expand the square sum
    have hexpand : (∑ j, (x j - ∑ k, c k * S.v k j) ^ 2)
        = (∑ j, (x j) ^ 2) - 2 * (∑ k, c k ^ 2) + (∑ k, c k ^ 2) := by
      have : (∑ j, (x j - ∑ k, c k * S.v k j) ^ 2)
          = ∑ j, ((x j)^2 - 2 * (x j * (∑ k, c k * S.v k j))
              + (∑ k, c k * S.v k j) ^ 2) := by
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hcross, hlast]
    rw [hexpand] at hnn
    linarith
  -- Combine: ‖toEuclideanLin E x‖ ≤ ‖x‖ for all Euclidean x
  have hbound : ∀ (x : EuclideanSpace ℝ (Fin n₂)),
      ‖Matrix.toEuclideanLin E x‖ ≤ 1 * ‖x‖ := by
    intro x
    rw [one_mul]
    have hsq : ‖Matrix.toEuclideanLin E x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [hnormSq x, EuclideanSpace.real_norm_sq_eq]
      exact hBessel (⇑x)
    have h1 : (0:ℝ) ≤ ‖Matrix.toEuclideanLin E x‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
    nlinarith [hsq, h1, h2]
  -- Conclude on the spectral norm
  show ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin E)‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [LinearMap.coe_toContinuousLinearMap']
  exact hbound x

end PriorSign
#print axioms PriorSign.solution

def sign_matrix_spectral_norm_le_one := @PriorSign.solution

namespace Imported0
/-!
Operator-level SVD reconstruction probe.

For a linear map `T : E →ₗ[ℝ] F` between finite-dimensional real inner product
spaces, we build:
  v_k = eigenvectorBasis of G = adjoint T ∘ₗ T (orthonormal, eigenvalues μ_k ≥ 0)
  σ_k = √μ_k = singularValues T k
  reconstruction  T x = ∑_k σ_k • ⟪v_k, x⟫ • u_k   where u_k = σ_k⁻¹ • T v_k.
We first prove the cleanest invariant form:
  T x = ∑_k ⟪v_k, x⟫ • T v_k   (just sum_repr' + linearity),
then  ‖T v_k‖ = σ_k  and the orthogonality of {T v_k}.
-/

open Module InnerProductSpace LinearMap
open scoped BigOperators

namespace SVDProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev gram (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := adjoint T ∘ₗ T

theorem gram_symm (T : E →ₗ[ℝ] F) : (gram T).IsSymmetric :=
  T.isSymmetric_adjoint_comp_self

theorem gram_pos (T : E →ₗ[ℝ] F) : (gram T).IsPositive :=
  T.isPositive_adjoint_comp_self

-- right singular vectors: orthonormal eigenbasis of G
noncomputable def rsv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) :
    OrthonormalBasis (Fin n) ℝ E :=
  (gram_symm T).eigenvectorBasis hn

noncomputable def evals (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) : Fin n → ℝ :=
  (gram_symm T).eigenvalues hn

theorem evals_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ evals T hn k :=
  (gram_pos T).nonneg_eigenvalues hn k

-- Reconstruction of T from the right singular vectors.
theorem recon (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (x : E) :
    T x = ∑ k, (inner ℝ (rsv T hn k) x) • T (rsv T hn k) := by
  conv_lhs => rw [← (rsv T hn).sum_repr' x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]

-- Key Gram identity: ⟪T v_i, T v_j⟫ = ⟪G v_i, v_j⟫.
theorem inner_Tv (T : E →ₗ[ℝ] F) (a b : E) :
    inner ℝ (T a) (T b) = inner ℝ (gram T a) b := by
  unfold gram
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]

-- ⟪T v_i, T v_j⟫ = μ_i δ_ij.
theorem inner_Tv_eig (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T (rsv T hn i)) (T (rsv T hn j))
      = if i = j then evals T hn i else 0 := by
  rw [inner_Tv]
  unfold gram rsv evals
  rw [show (adjoint T ∘ₗ T) ((gram_symm T).eigenvectorBasis hn i)
        = (gram T) ((gram_symm T).eigenvectorBasis hn i) from rfl]
  rw [(gram_symm T).apply_eigenvectorBasis hn i]
  rw [inner_smul_left]
  rw [orthonormal_iff_ite.mp ((gram_symm T).eigenvectorBasis hn).orthonormal i j]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

noncomputable def sval (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) : ℝ :=
  T.singularValues k

theorem sval_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ sval T hn k := T.singularValues_nonneg k

theorem sval_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    sval T hn k ^ 2 = evals T hn k := by
  unfold sval evals
  rw [T.sq_singularValues_fin hn k]

-- ‖T v_k‖ = σ_k.
theorem norm_Tv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    ‖T (rsv T hn k)‖ = sval T hn k := by
  have h2 : ‖T (rsv T hn k)‖ ^ 2 = sval T hn k ^ 2 := by
    rw [@norm_sq_eq_re_inner ℝ]
    have := inner_Tv_eig T hn k k
    simp only [if_pos rfl] at this
    rw [this, sval_sq]
    simp
  have hnn := sval_nonneg T hn k
  nlinarith [norm_nonneg (T (rsv T hn k)), h2, hnn]

-- T v_k as σ_k times a unit left-singular vector (only meaningful when σ_k>0;
-- when σ_k=0, T v_k = 0).
theorem Tv_zero_of_sval_zero (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n)
    (h : sval T hn k = 0) : T (rsv T hn k) = 0 := by
  have := norm_Tv T hn k
  rw [h] at this
  exact norm_eq_zero.mp this

/-! ## Hilbert–Schmidt inner product, basis-independent. -/

-- ∑_j ⟪S b_j, T b_j⟫ = trace (adjoint S ∘ T), basis-independent.
theorem hsInner_eq_trace {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    (∑ j, inner ℝ (S (b j)) (T (b j))) = (adjoint S ∘ₗ T).trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right S (b j) (T (b j))]

-- Therefore HS inner over the standard basis = HS inner over the eigenbasis.
theorem hsInner_basis_indep {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ (S (b j)) (T (b j)))
      = ∑ k, inner ℝ (S (rsv T hn k)) (T (rsv T hn k)) := by
  rw [hsInner_eq_trace S T b, hsInner_eq_trace S T (rsv T hn)]

/-! ## Operator-level von Neumann trace inequality.
    ∑_j ⟪S b_j, T b_j⟫ ≤ ‖S‖ · ∑_k σ_k(T). -/

theorem vonNeumann_op {ι : Type*} [Fintype ι] (S : E →L[ℝ] F) (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ ((S : E →ₗ[ℝ] F) (b j)) (T (b j))) ≤ ‖S‖ * ∑ k, sval T hn k := by
  rw [hsInner_basis_indep (S : E →ₗ[ℝ] F) T b hn]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  -- ⟪S v_k, T v_k⟫ ≤ ‖S v_k‖ ‖T v_k‖ ≤ ‖S‖ ‖v_k‖ σ_k = ‖S‖ σ_k
  have hSle : ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ ≤ ‖S‖ * ‖(rsv T hn k : E)‖ := S.le_opNorm _
  calc inner ℝ ((S : E →ₗ[ℝ] F) (rsv T hn k)) (T (rsv T hn k))
      ≤ ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ * ‖T (rsv T hn k)‖ := real_inner_le_norm _ _
    _ ≤ (‖S‖ * ‖(rsv T hn k : E)‖) * ‖T (rsv T hn k)‖ := by
          apply mul_le_mul_of_nonneg_right hSle (norm_nonneg _)
    _ = ‖S‖ * sval T hn k := by
          rw [(rsv T hn).orthonormal.1 k, norm_Tv]; ring

end SVDProbe

namespace MatrixCompletion
open scoped Classical BigOperators
open Module InnerProductSpace LinearMap Matrix WithLp SVDProbe

theorem _svd_exists_aux {n1 n2 : Nat} (N : RealMatrix n1 n2) :
    ∃ (r : Nat) (S : SVD N r), True := by
  set T : EuclideanSpace ℝ (Fin n2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n1) :=
    Matrix.toEuclideanLin N with hT
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  set b := rsv T hn with hb
  -- the set of indices with positive singular value
  set P : Finset (Fin n2) := Finset.univ.filter (fun k => 0 < sval T hn k) with hP
  set r : Nat := P.card with hr
  -- equiv between Fin r and P
  set e : Fin r ≃ {x // x ∈ P} := P.equivFin.symm with he
  set idx : Fin r → Fin n2 := fun k => (e k : Fin n2) with hidx
  have hidx_mem : ∀ k, idx k ∈ P := fun k => (e k).2
  have hidx_pos : ∀ k, 0 < sval T hn (idx k) := by
    intro k
    have := hidx_mem k
    rw [hP, Finset.mem_filter] at this
    exact this.2
  have hidx_inj : Function.Injective idx := by
    intro a c h
    apply e.injective
    apply Subtype.ext
    simpa [hidx] using h
  -- definitions of the SVD data
  set sigma : Fin r → ℝ := fun k => sval T hn (idx k) with hsigma
  set vvec : Fin r → (Fin n2 → ℝ) := fun k => ofLp (b (idx k)) with hvvec
  set uvec : Fin r → (Fin n1 → ℝ) := fun k => (sigma k)⁻¹ • ofLp (T (b (idx k))) with huvec
  refine ⟨r, ?_, trivial⟩
  refine
    { sigma := sigma
      u := uvec
      v := vvec
      sigma_pos := ?_
      u_orthonormal := ?_
      v_orthonormal := ?_
      decomp := ?_ }
  · -- sigma_pos
    intro k; exact hidx_pos k
  · -- u_orthonormal
    intro k l
    -- ∑_i u k i * u l i = (σk)⁻¹ (σl)⁻¹ * inner (T (b idx k)) (T (b idx l))
    have hinner : (inner ℝ (T (b (idx k))) (T (b (idx l))) : ℝ)
        = ∑ i, (ofLp (T (b (idx k)))) i * (ofLp (T (b (idx l)))) i := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl; intro i _
      rw [show (inner ℝ ((ofLp (T (b (idx k)))) i) ((ofLp (T (b (idx l)))) i) : ℝ)
            = (ofLp (T (b (idx l)))) i * (ofLp (T (b (idx k)))) i from rfl]
      ring
    have hsum : (∑ i, uvec k i * uvec l i)
        = (sigma k)⁻¹ * (sigma l)⁻¹ * inner ℝ (T (b (idx k))) (T (b (idx l))) := by
      rw [hinner, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      simp only [huvec, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsum, inner_Tv_eig T hn (idx k) (idx l)]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl]
      have hsq : evals T hn (idx k) = sigma k ^ 2 := by
        rw [hsigma]; exact (sval_sq T hn (idx k)).symm
      rw [hsq]
      have hne : sigma k ≠ 0 := ne_of_gt (hidx_pos k)
      field_simp
    · have hne : idx k ≠ idx l := fun h => hkl (hidx_inj h)
      rw [if_neg hne, if_neg hkl]
      ring
  · -- v_orthonormal
    intro k l
    have hinner : (inner ℝ (b (idx k)) (b (idx l)) : ℝ)
        = ∑ j, vvec k j * vvec l j := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl; intro j _
      rw [show (inner ℝ ((ofLp (b (idx k))) j) ((ofLp (b (idx l))) j) : ℝ)
            = (ofLp (b (idx l))) j * (ofLp (b (idx k))) j from rfl]
      simp only [hvvec]; ring
    rw [← hinner, orthonormal_iff_ite.mp b.orthonormal (idx k) (idx l)]
    by_cases hkl : k = l
    · subst hkl; simp
    · have hne : idx k ≠ idx l := fun h => hkl (hidx_inj h)
      rw [if_neg hne, if_neg hkl]
  · -- decomp
    -- First: σ_k • u_k = ofLp (T (b (idx k))) as a Fin n1 → ℝ vector.
    have hsig_u : ∀ k, sigma k • uvec k = ofLp (T (b (idx k))) := by
      intro k
      funext i
      simp only [huvec, Pi.smul_apply, smul_eq_mul]
      have hne : sigma k ≠ 0 := ne_of_gt (hidx_pos k)
      field_simp
    -- Entry of the column N via T applied to basisFun.
    have hNij : ∀ (i : Fin n1) (j : Fin n2),
        N i j = (ofLp (T (EuclideanSpace.basisFun (Fin n2) ℝ j))) i := by
      intro i j
      rw [EuclideanSpace.basisFun_apply]
      rw [hT, Matrix.ofLp_toEuclideanLin_apply]
      simp only [Matrix.mulVec, EuclideanSpace.ofLp_single, dotProduct_single, mul_one]
    -- inner ⟨b k, basisFun j⟩ = (ofLp (b k)) j
    have hinner_bj : ∀ (k : Fin n2) (j : Fin n2),
        (inner ℝ (b k) (EuclideanSpace.basisFun (Fin n2) ℝ j) : ℝ) = (ofLp (b k)) j := by
      intro k j
      rw [PiLp.inner_apply, EuclideanSpace.basisFun_apply]
      rw [show (∑ x, (inner ℝ ((ofLp (b k)) x) ((ofLp (EuclideanSpace.single j (1:ℝ))) x) : ℝ))
            = ∑ x, (ofLp (EuclideanSpace.single j (1:ℝ))) x * (ofLp (b k)) x from
          Finset.sum_congr rfl (fun x _ => rfl)]
      simp only [EuclideanSpace.ofLp_single]
      rw [Finset.sum_eq_single j]
      · simp
      · intro x _ hx; simp [Pi.single_apply, hx]
      · intro h; exact absurd (Finset.mem_univ j) h
    -- The full-domain reconstruction at coordinate i:
    -- (ofLp (T (basisFun j))) i = ∑_{k : Fin n2} (ofLp (b k)) j * (ofLp (T (b k))) i
    have hrecon_coord : ∀ (i : Fin n1) (j : Fin n2),
        (ofLp (T (EuclideanSpace.basisFun (Fin n2) ℝ j))) i
          = ∑ k : Fin n2, (ofLp (b k)) j * (ofLp (T (b k))) i := by
      intro i j
      have hr := recon T hn (EuclideanSpace.basisFun (Fin n2) ℝ j)
      -- hr : T (basisFun j) = ∑ k, ⟨b k, basisFun j⟩ • T (b k)
      have := congrArg (fun (y : EuclideanSpace ℝ (Fin n1)) => (ofLp y) i) hr
      simp only at this
      rw [this]
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [WithLp.ofLp_smul]
      simp only [Pi.smul_apply, smul_eq_mul, hb]
      rw [hinner_bj k j]
    -- Drop the zero terms (k ∉ P) and re-index by idx.
    have hsum_reindex : ∀ (i : Fin n1) (j : Fin n2),
        (∑ k : Fin n2, (ofLp (b k)) j * (ofLp (T (b k))) i)
          = ∑ k : Fin r, (ofLp (b (idx k))) j * (ofLp (T (b (idx k))) i) := by
      intro i j
      -- the full sum equals the sum over P (zero off P), then reindex P by e
      rw [← Finset.sum_subset (Finset.subset_univ P)
          (fun k _ hkP => ?_)]
      · -- ∑_{k ∈ P} f k = ∑_{x : Fin r} f (idx x) via the bijection idx
        symm
        apply Finset.sum_bij (fun (k : Fin r) (_ : k ∈ Finset.univ) => idx k)
        · intro k _; exact hidx_mem k
        · intro a _ c _ h; exact hidx_inj h
        · intro x hx
          refine ⟨(e.symm ⟨x, hx⟩), Finset.mem_univ _, ?_⟩
          simp only [hidx, Equiv.apply_symm_apply]
        · intro k _; rfl
      · -- term vanishes for k ∉ P (σ_k = 0)
        have hsv0 : sval T hn k = 0 := by
          rw [hP, Finset.mem_filter] at hkP
          push_neg at hkP
          have := hkP (Finset.mem_univ k)
          have hnn := sval_nonneg T hn k
          linarith
        have hTbk : T (b k) = 0 := by
          rw [hb]; exact Tv_zero_of_sval_zero T hn k hsv0
        rw [hTbk]
        simp
    -- Now assemble the matrix equality entrywise.
    funext i j
    simp only [hT] at hNij
    rw [hNij i j, hrecon_coord i j, hsum_reindex i j]
    -- RHS: (∑ k, σ_k • vecMulVec (u_k) (v_k)) i j
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    -- σ_k * (u_k i * v_k j) = (ofLp (T (b idx k))) i * (ofLp (b idx k)) j
    have hu : sigma k * uvec k i = (ofLp (T (b (idx k)))) i := by
      have := congrArg (fun (w : Fin n1 → ℝ) => w i) (hsig_u k)
      simpa using this
    rw [show sigma k * (uvec k i * vvec k j) = (sigma k * uvec k i) * vvec k j by ring, hu]
    simp only [hvvec]
    ring


end MatrixCompletion

open MatrixCompletion
theorem solution {n1 n2 : Nat} (N : Matrix (Fin n1) (Fin n2) ℝ) :
    ∃ (r : Nat) (S : SVD N r), True :=
  MatrixCompletion._svd_exists_aux N

end Imported0
def matrix_svd_exists := @Imported0.solution

namespace Imported1
/-!
L1 — `sign_matrix_inner_eq_nuclear_norm`:  `⟨E, M⟩ = ‖M‖_*`  (Candès–Recht 2009, eq.(3.3), p.15).
Easy half (orthonormality):  `⟨E, M⟩ = ∑_k σ_k`.
Deep half (SVD uniqueness):  `∑_k σ_k = nuclearNorm M` (eigenvalue-multiset / charpoly argument).
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace Polynomial WithLp

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace Polynomial WithLp

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- The Gram matrix `Mᵀ * M`. -/
noncomputable abbrev gramMat (M : RealMatrix n1 n2) : Matrix (Fin n2) (Fin n2) ℝ := Mᵀ * M

/-- `Mᵀ M = ∑_k σ_k² • (v_k v_kᵀ)` (using orthonormality of the left vectors `u`). -/
theorem gramMat_eq_sum (S : SVD M r) :
    gramMat M = ∑ k, (S.sigma k ^ 2) • Matrix.vecMulVec (S.v k) (S.v k) := by
  ext a b
  -- entrywise:  (Mᵀ M) a b = ∑_i M i a * M i b
  show (Mᵀ * M) a b = _
  rw [Matrix.mul_apply]
  have hMia : ∀ i a, M i a = ∑ l, S.sigma l * (S.u l i * S.v l a) := by
    intro i a
    have := congrFun (congrFun S.decomp i) a
    rw [this]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  -- RHS entry
  have hRHS : (∑ k, (S.sigma k ^ 2) • Matrix.vecMulVec (S.v k) (S.v k)) a b
      = ∑ k, (S.sigma k ^ 2) * (S.v k a * S.v k b) := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [hRHS]
  -- expand LHS
  have hLHS : (∑ i, Mᵀ a i * M i b) = ∑ i, M i a * M i b := by
    apply Finset.sum_congr rfl; intro i _; rw [Matrix.transpose_apply]
  rw [hLHS]
  calc (∑ i, M i a * M i b)
      = ∑ i, (∑ l, S.sigma l * (S.u l i * S.v l a)) * (∑ m, S.sigma m * (S.u m i * S.v m b)) := by
        apply Finset.sum_congr rfl; intro i _; rw [hMia i a, hMia i b]
    _ = ∑ i, ∑ l, ∑ m,
          (S.sigma l * S.sigma m) * (S.v l a * S.v m b) * (S.u l i * S.u m i) := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl; intro l _
        apply Finset.sum_congr rfl; intro m _
        ring
    _ = ∑ l, ∑ m, (S.sigma l * S.sigma m) * (S.v l a * S.v m b) * (∑ i, S.u l i * S.u m i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum]
    _ = ∑ l, (S.sigma l ^ 2) * (S.v l a * S.v l b) := by
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.sum_eq_single l]
        · rw [S.u_orthonormal l l, if_pos rfl]; ring
        · intro m _ hml
          rw [S.u_orthonormal l m, if_neg (fun h => hml h.symm)]; ring
        · intro h; exact absurd (Finset.mem_univ l) h

/-! ## Operator-level setup. -/

/-- `T = toEuclideanLin M`. -/
noncomputable abbrev Top (M : RealMatrix n1 n2) : EuclideanSpace ℝ (Fin n2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n1) :=
  Matrix.toEuclideanLin M

/-- `G = adjoint T ∘ₗ T`, the Gram operator. -/
noncomputable abbrev Gop (M : RealMatrix n1 n2) : EuclideanSpace ℝ (Fin n2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n2) :=
  LinearMap.adjoint (Top M) ∘ₗ (Top M)

theorem Gop_symm (M : RealMatrix n1 n2) : (Gop M).IsSymmetric :=
  (Top M).isSymmetric_adjoint_comp_self

/-- `G = toEuclideanLin (Mᵀ M)`. -/
theorem Gop_eq_toEuclideanLin (M : RealMatrix n1 n2) :
    Gop M = Matrix.toEuclideanLin (Mᵀ * M) := by
  have hadj : LinearMap.adjoint (Top M) = Matrix.toEuclideanLin Mᵀ := by
    have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (M)
    rw [show Mᵀ = Mᴴ from ?_]
    · exact h.symm
    · ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, hadj]
  -- toEuclideanLin Mᵀ (toEuclideanLin M x) = toEuclideanLin (Mᵀ * M) x
  apply (WithLp.equiv 2 (Fin n2 → ℝ)).injective
  simp only [WithLp.equiv_apply]
  rw [Matrix.ofLp_toEuclideanLin_apply, Matrix.ofLp_toEuclideanLin_apply,
    Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec_mulVec]

/-- The right singular vector `vv k` as a point of Euclidean space. -/
noncomputable def vv (S : SVD M r) (k : Fin r) : EuclideanSpace ℝ (Fin n2) :=
  toLp 2 (S.v k)

theorem vv_ofLp (S : SVD M r) (k : Fin r) : ofLp (vv S k) = S.v k := rfl

/-- Orthonormality of the `vv k` in EuclideanSpace. -/
theorem vv_orthonormal (S : SVD M r) : Orthonormal ℝ (vv S) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [PiLp.inner_apply]
  simp only [vv, WithLp.ofLp_toLp]
  have := S.v_orthonormal k l
  rw [show (∑ x, (inner ℝ (S.v k x) (S.v l x)) ) = ∑ j, S.v k j * S.v l j from
    Finset.sum_congr rfl (fun x _ => by rw [show (inner ℝ (S.v k x) (S.v l x) : ℝ)
      = S.v l x * S.v k x from rfl, mul_comm])]
  rw [this]

/-- The matrix eigenvalue equation `(Mᵀ M) *ᵥ v_k = σ_k² • v_k`. -/
theorem gramMat_mulVec_v (S : SVD M r) (k : Fin r) :
    (Mᵀ * M) *ᵥ S.v k = (S.sigma k ^ 2) • S.v k := by
  have hg : (Mᵀ * M) = ∑ l, (S.sigma l ^ 2) • Matrix.vecMulVec (S.v l) (S.v l) :=
    gramMat_eq_sum S
  rw [hg]
  funext a
  simp only [Matrix.mulVec, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul, dotProduct]
  -- ∑_b (∑_l σ_l² v_l a v_l b) v_k b = σ_k² v_k a
  rw [show (∑ b, (∑ l, S.sigma l ^ 2 * (S.v l a * S.v l b)) * S.v k b)
        = ∑ l, S.sigma l ^ 2 * S.v l a * (∑ b, S.v l b * S.v k b) from ?_]
  · rw [Finset.sum_eq_single k]
    · rw [S.v_orthonormal k k, if_pos rfl]; ring
    · intro l _ hlk
      rw [S.v_orthonormal l k, if_neg hlk]; ring
    · intro h; exact absurd (Finset.mem_univ k) h
  · have step1 : (∑ b, (∑ l, S.sigma l ^ 2 * (S.v l a * S.v l b)) * S.v k b)
          = ∑ b, ∑ l, (S.sigma l ^ 2 * S.v l a) * (S.v l b * S.v k b) := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro l _; ring
    rw [step1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]

/-- Eigenvector equation:  `G (vv k) = σ_k² • vv k`. -/
theorem Gop_vv (S : SVD M r) (k : Fin r) :
    Gop M (vv S k) = (S.sigma k ^ 2) • vv S k := by
  rw [Gop_eq_toEuclideanLin]
  apply (WithLp.equiv 2 (Fin n2 → ℝ)).injective
  simp only [WithLp.equiv_apply]
  rw [Matrix.ofLp_toEuclideanLin_apply, vv_ofLp, WithLp.ofLp_smul, vv_ofLp,
    gramMat_mulVec_v S k]

/-- The real inner `⟪vv_k, x⟫ = ∑_b v_k b · (ofLp x) b`. -/
theorem inner_vv (S : SVD M r) (k : Fin r) (x : EuclideanSpace ℝ (Fin n2)) :
    (inner ℝ (vv S k) x : ℝ) = ∑ b, S.v k b * (ofLp x) b := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro b _
  rw [show (inner ℝ ((ofLp (vv S k)) b) ((ofLp x) b) : ℝ) = (ofLp x) b * (ofLp (vv S k)) b from rfl,
    vv_ofLp]
  ring

/-- Operator form of the Gram operator: `G x = ∑_k σ_k² ⟪vv_k, x⟫ vv_k`. -/
theorem Gop_apply_eq_sum (S : SVD M r) (x : EuclideanSpace ℝ (Fin n2)) :
    Gop M x = ∑ k, (S.sigma k ^ 2 * (inner ℝ (vv S k) x)) • vv S k := by
  rw [Gop_eq_toEuclideanLin]
  apply (WithLp.equiv 2 (Fin n2 → ℝ)).injective
  simp only [WithLp.equiv_apply]
  have hg : (Mᵀ * M) = ∑ l, (S.sigma l ^ 2) • Matrix.vecMulVec (S.v l) (S.v l) :=
    gramMat_eq_sum S
  rw [Matrix.ofLp_toEuclideanLin_apply, hg, WithLp.ofLp_sum]
  funext a
  rw [Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [WithLp.ofLp_smul]
  simp only [Matrix.mulVec, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [inner_vv S k x, vv_ofLp, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro b _
  ring

/-! ## Eigenbasis construction. -/

theorem r_le_n2 (S : SVD M r) : r ≤ n2 := by
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  have hli := (vv_orthonormal S).linearIndependent
  have := hli.fintype_card_le_finrank (M := EuclideanSpace ℝ (Fin n2))
  simpa [hfin] using this

/-- Inclusion `Fin r ↪ Fin n2`. -/
noncomputable def incl (S : SVD M r) : Fin r → Fin n2 := fun k => Fin.castLE (r_le_n2 S) k

theorem incl_injective (S : SVD M r) : Function.Injective (incl S) := by
  intro a b h
  exact Fin.castLE_injective (r_le_n2 S) h

/-- The total extension of `vv` to `Fin n2 → E` (junk `0` off the range). -/
noncomputable def vext (S : SVD M r) : Fin n2 → EuclideanSpace ℝ (Fin n2) :=
  Function.extend (incl S) (vv S) 0

theorem vext_incl (S : SVD M r) (k : Fin r) : vext S (incl S k) = vv S k := by
  unfold vext
  rw [(incl_injective S).extend_apply]

/-- `Fin r ≃ range (incl S)`, used to index the restricted family without
building subtype elements whose membership proof is only type-correct at
default transparency. -/
noncomputable def inclEquiv (S : SVD M r) : Fin r ≃ Set.range (incl S) :=
  Equiv.ofInjective (incl S) (incl_injective S)

theorem vext_restrict_inclEquiv (S : SVD M r) (k : Fin r) :
    (Set.range (incl S)).restrict (vext S) (inclEquiv S k) = vv S k := vext_incl S k

theorem vext_orthonormal_restrict (S : SVD M r) :
    Orthonormal ℝ ((Set.range (incl S)).restrict (vext S)) := by
  rw [orthonormal_iff_ite]
  intro i j
  obtain ⟨ki, rfl⟩ := (inclEquiv S).surjective i
  obtain ⟨kj, rfl⟩ := (inclEquiv S).surjective j
  rw [vext_restrict_inclEquiv, vext_restrict_inclEquiv,
    orthonormal_iff_ite.mp (vv_orthonormal S) ki kj]
  by_cases h : ki = kj
  · subst h; simp
  · rw [if_neg h, if_neg (fun hc => h ((inclEquiv S).injective hc))]

/-- The extended orthonormal basis whose first `r` vectors are the `vv k`. -/
noncomputable def bb (S : SVD M r) : OrthonormalBasis (Fin n2) ℝ (EuclideanSpace ℝ (Fin n2)) :=
  (vext_orthonormal_restrict S).exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin]) |>.choose

theorem bb_spec (S : SVD M r) : ∀ i ∈ Set.range (incl S), bb S i = vext S i :=
  (vext_orthonormal_restrict S).exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin]) |>.choose_spec

theorem bb_incl (S : SVD M r) (k : Fin r) : bb S (incl S k) = vv S k := by
  rw [bb_spec S (incl S k) (Set.mem_range_self k), vext_incl]

/-- The diagonal eigenvalue function: `σ_k²` on `incl k`, `0` elsewhere. -/
noncomputable def dvec (S : SVD M r) : Fin n2 → ℝ :=
  fun i => if h : ∃ k, incl S k = i then S.sigma h.choose ^ 2 else 0

theorem dvec_incl (S : SVD M r) (k : Fin r) : dvec S (incl S k) = S.sigma k ^ 2 := by
  unfold dvec
  have hex : ∃ k', incl S k' = incl S k := ⟨k, rfl⟩
  rw [dif_pos hex]
  have : hex.choose = k := incl_injective S hex.choose_spec
  rw [this]

theorem dvec_not_range (S : SVD M r) (i : Fin n2) (hi : ¬ ∃ k, incl S k = i) :
    dvec S i = 0 := by
  unfold dvec; rw [dif_neg hi]

/-- `bb i` for `i` outside the range of `incl` is orthogonal to every `vv k`. -/
theorem bb_orthogonal_vv (S : SVD M r) (i : Fin n2) (hi : ¬ ∃ k, incl S k = i) (k : Fin r) :
    (inner ℝ (vv S k) (bb S i) : ℝ) = 0 := by
  rw [← bb_incl S k]
  have hne : incl S k ≠ i := fun h => hi ⟨k, h⟩
  have := (bb S).orthonormal
  rw [orthonormal_iff_ite] at this
  rw [this (incl S k) i, if_neg hne]

/-- Key eigen-equation in the extended basis: `G (bb i) = dvec i • bb i`. -/
theorem Gop_bb (S : SVD M r) (i : Fin n2) :
    Gop M (bb S i) = dvec S i • bb S i := by
  by_cases hi : ∃ k, incl S k = i
  · obtain ⟨k, rfl⟩ := hi
    rw [bb_incl, Gop_vv, dvec_incl]
  · -- i outside range: G (bb i) = 0 and dvec i = 0
    rw [dvec_not_range S i hi, zero_smul]
    rw [Gop_apply_eq_sum S]
    apply Finset.sum_eq_zero
    intro k _
    rw [bb_orthogonal_vv S i hi k, mul_zero, zero_smul]

/-! ## Charpoly and the eigenvalue multiset. -/

/-- `G` is diagonal (with diagonal `dvec`) in the basis `bb`. -/
theorem toMatrix_bb_diagonal (S : SVD M r) :
    LinearMap.toMatrix (bb S).toBasis (bb S).toBasis (Gop M) = Matrix.diagonal (dvec S) := by
  ext i j
  rw [LinearMap.toMatrix_apply, (bb S).coe_toBasis, Gop_bb S j, map_smul, Finsupp.smul_apply,
    (bb S).coe_toBasis_repr_apply, (bb S).repr_self, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [EuclideanSpace.single_apply, if_neg h, if_neg h, smul_zero]

/-- `charpoly G = ∏_i (X - C (dvec i))`. -/
theorem charpoly_Gop (S : SVD M r) :
    (Gop M).charpoly = ∏ i, (Polynomial.X - Polynomial.C (dvec S i)) := by
  rw [← (Gop M).charpoly_toMatrix (bb S).toBasis, toMatrix_bb_diagonal S,
    Matrix.charpoly_diagonal]

/-! ## The eigenvalue multiset equals the `dvec` multiset, and the final sum. -/

/-- The multiset of `dvec` values equals the multiset of `G`-eigenvalues. -/
theorem eigenvalues_multiset_eq (S : SVD M r) (hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2) :
    (Finset.univ.val.map ((Gop_symm M).eigenvalues hn))
      = Finset.univ.val.map (dvec S) := by
  -- both equal (charpoly G).roots (as ℝ-multisets, since RCLike.ofReal = id over ℝ)
  have hroots_g := (Gop_symm M).roots_charpoly_eq_eigenvalues hn
  have hcp := charpoly_Gop S
  -- roots of ∏(X - C dvec i)
  have hprod : (∏ i, (Polynomial.X - Polynomial.C (dvec S i)))
      = ((Finset.univ.val.map (dvec S)).map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]
    rw [Finset.prod_eq_multiset_prod]
    rfl
  have hroots_d : (Gop M).charpoly.roots = Finset.univ.val.map (dvec S) := by
    rw [hcp, hprod, Polynomial.roots_multiset_prod_X_sub_C]
  -- combine; ofReal over ℝ is the identity
  rw [hroots_d] at hroots_g
  -- hroots_g : univ.val.map dvec = univ.val.map (ofReal ∘ eigenvalues G)
  rw [hroots_g]
  apply Multiset.map_congr rfl
  intro x _
  simp [Function.comp]

/-- THE TARGET (SVD uniqueness): `∑_k σ_k = nuclearNorm M`. -/
theorem svd_sigma_sum_eq_nuclearNorm (S : SVD M r) :
    ∑ k, S.sigma k = nuclearNorm M := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  set T := Matrix.toEuclideanLin M with hT
  -- Step A: nuclearNorm M = ∑_{i:Fin n2} singularValues T i
  have hnuc : nuclearNorm M = ∑ i : Fin n2, T.singularValues i := by
    unfold nuclearNorm
    rw [← hT]
    rw [Finsupp.sum_of_support_subset T.singularValues
        (s := Finset.range n2) ?_ (fun _ x => x) (by intro _ _; rfl)]
    · rw [Finset.sum_range fun k => T.singularValues k]
    · intro k hk
      rw [Finset.mem_range]
      by_contra hge
      push_neg at hge
      have : T.singularValues k = 0 := by
        apply T.singularValues_of_finrank_le; rw [hn]; exact hge
      rw [Finsupp.mem_support_iff] at hk; exact hk this
  -- Step B: singularValues T i = √(eigenvalues G i)
  have hsv : ∀ i : Fin n2, T.singularValues i = Real.sqrt ((Gop_symm M).eigenvalues hn i) := by
    intro i
    rw [T.singularValues_fin hn i]
  rw [hnuc]
  -- ∑ singularValues T i = ∑ √(eigenvalues G i)
  rw [show (∑ i : Fin n2, T.singularValues i)
      = ∑ i : Fin n2, Real.sqrt ((Gop_symm M).eigenvalues hn i) from
    Finset.sum_congr rfl (fun i _ => hsv i)]
  -- Convert finite sums to multiset sums and use the multiset equality
  have hconv1 : (∑ i : Fin n2, Real.sqrt ((Gop_symm M).eigenvalues hn i))
        = ((Finset.univ.val.map ((Gop_symm M).eigenvalues hn)).map Real.sqrt).sum := by
    rw [Multiset.map_map]; rfl
  have hconv2 : ((Finset.univ.val.map (dvec S)).map Real.sqrt).sum
        = ∑ i : Fin n2, Real.sqrt (dvec S i) := by
    rw [Multiset.map_map]; rfl
  rw [hconv1, eigenvalues_multiset_eq S hn, hconv2]
  -- ∑_{i:Fin n2} √(dvec i) = ∑_k σ_k  (off-range terms vanish, on-range √(σ_k²)=σ_k)
  rw [show (∑ i : Fin n2, Real.sqrt (dvec S i))
        = ∑ k : Fin r, Real.sqrt (dvec S (incl S k)) from ?_]
  · refine (Finset.sum_congr rfl (fun k _ => ?_)).symm
    rw [dvec_incl, Real.sqrt_sq (le_of_lt (S.sigma_pos k))]
  · -- off-range vanish
    rw [← Finset.sum_image (f := fun i => Real.sqrt (dvec S i)) (g := incl S)
      (by intro a _ b _ h; exact incl_injective S h)]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    -- i ∉ image incl univ  ⇒  i ∉ range incl  ⇒  dvec i = 0
    rw [dvec_not_range S i ?_, Real.sqrt_zero]
    rintro ⟨k, rfl⟩
    exact hi (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)



open scoped Classical BigOperators


/-- Reorder a 4-fold finite sum, pulling the inner pair of indices `(k,l)` out. -/
theorem sum4_reorder {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  have hL : (∑ i, ∑ j, ∑ k, ∑ l, f i j k l)
      = ∑ p : α × β, ∑ q : γ × δ, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type' (fun (i : α) (j : β) => ∑ k, ∑ l, f i j k l)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Fintype.sum_prod_type' (fun (k : γ) (l : δ) => f p.1 p.2 k l)]
  have hR : (∑ k, ∑ l, ∑ i, ∑ j, f i j k l)
      = ∑ q : γ × δ, ∑ p : α × β, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type' (fun (k : γ) (l : δ) => ∑ i, ∑ j, f i j k l)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Fintype.sum_prod_type' (fun (i : α) (j : β) => f i j q.1 q.2)]
  rw [hL, hR, Finset.sum_comm]

/-- EASY half of L1: the sign matrix inner product with `M` is the sum of the
SVD singular values, by orthonormality of the singular vectors. -/
theorem signMatrix_inner_eq_sum_sigma (S : SVD M r) :
    matrixInner (signMatrix S) M = ∑ k, S.sigma k := by
  unfold matrixInner
  -- entry-wise SVD expansion of M (real equation, no motive problem)
  have hMij : ∀ i j, M i j = ∑ l, S.sigma l * (S.u l i * S.v l j) := by
    intro i j
    have := congrFun (congrFun S.decomp i) j
    rw [this]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  have hEij : ∀ i j, (signMatrix S) i j = ∑ k, S.u k i * S.v k j := by
    intro i j
    unfold signMatrix
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hentry : ∀ i j,
      (signMatrix S) i j * M i j
        = ∑ k, ∑ l, (S.sigma l) * (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
    intro i j
    rw [hEij i j, hMij i j, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  calc (∑ i, ∑ j, (signMatrix S) i j * M i j)
      = ∑ i, ∑ j, ∑ k, ∑ l, (S.sigma l) * (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hentry i j]
    _ = ∑ k, ∑ l, ∑ i, ∑ j,
          (S.sigma l) * (S.u k i * S.u l i) * (S.v k j * S.v l j) :=
        sum4_reorder (fun i j k l => (S.sigma l) * (S.u k i * S.u l i) * (S.v k j * S.v l j))
    _ = ∑ k, ∑ l, (S.sigma l) *
          ((∑ i, S.u k i * S.u l i) * (∑ j, S.v k j * S.v l j)) := by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ = ∑ k, S.sigma k := by
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_eq_single k]
        · rw [S.u_orthonormal k k, S.v_orthonormal k k]; simp
        · intro l _ hlk
          rw [S.u_orthonormal k l]
          rw [if_neg (fun h => hlk h.symm)]
          ring
        · intro h; exact absurd (Finset.mem_univ k) h

end MatrixCompletion

open MatrixCompletion

/-- L1 — the sign matrix realizes the nuclear norm (Candès–Recht 2009, eq.(3.3)). -/
theorem solution {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    matrixInner (signMatrix S) M = nuclearNorm M := by
  rw [signMatrix_inner_eq_sum_sigma S, svd_sigma_sum_eq_nuclearNorm S]

end Imported1
def sign_matrix_inner_eq_nuclear_norm := @Imported1.solution

namespace Imported2
/-!
C1 — von Neumann / matrix trace-duality inequality:
  `matrixInner A B ≤ spectralNorm A * nuclearNorm B`.

Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2 first inequality
(von Neumann's trace inequality, 1937; see also Mirsky 1975).

Proof outline (built from Mathlib's self-adjoint spectral theorem; the SVD
reconstruction `B = Σ σ_k u_k v_k^T` is NOT available ready-made in this env's
Mathlib, so it is constructed here):
  * `T := toEuclideanLin B`, `G := Tᵀ∘T` symmetric and PSD.
  * `v_k := eigenvectorBasis G` orthonormal, eigenvalues `μ_k ≥ 0`,
    `σ_k = √μ_k = singularValues T k`.
  * `⟪T v_i, T v_j⟫ = ⟪G v_i, v_j⟫ = μ_i δ_ij`, so `‖T v_k‖ = σ_k`.
  * Frobenius inner product = Hilbert–Schmidt inner `∑_j ⟪S e_j, T e_j⟫`,
    which is `trace(Sᵀ∘T)` — basis-independent — hence `= ∑_k ⟪S v_k, T v_k⟫`.
  * `⟪S v_k, T v_k⟫ ≤ ‖S v_k‖·‖T v_k‖ ≤ ‖S‖·1·σ_k`; sum gives `‖S‖·Σσ_k`.
  * `Σ σ_k = nuclearNorm B`, `‖S‖ = spectralNorm A`.
-/

open Module InnerProductSpace LinearMap Matrix
open scoped BigOperators

/-! ### Operator-level SVD reconstruction & von Neumann inequality. -/

namespace SVDProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev gram (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := adjoint T ∘ₗ T

theorem gram_symm (T : E →ₗ[ℝ] F) : (gram T).IsSymmetric :=
  T.isSymmetric_adjoint_comp_self

theorem gram_pos (T : E →ₗ[ℝ] F) : (gram T).IsPositive :=
  T.isPositive_adjoint_comp_self

noncomputable def rsv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) :
    OrthonormalBasis (Fin n) ℝ E :=
  (gram_symm T).eigenvectorBasis hn

noncomputable def evals (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) : Fin n → ℝ :=
  (gram_symm T).eigenvalues hn

theorem evals_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ evals T hn k :=
  (gram_pos T).nonneg_eigenvalues hn k

theorem inner_Tv (T : E →ₗ[ℝ] F) (a b : E) :
    inner ℝ (T a) (T b) = inner ℝ (gram T a) b := by
  unfold gram
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]

theorem inner_Tv_eig (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T (rsv T hn i)) (T (rsv T hn j))
      = if i = j then evals T hn i else 0 := by
  rw [inner_Tv]
  unfold gram rsv evals
  rw [show (adjoint T ∘ₗ T) ((gram_symm T).eigenvectorBasis hn i)
        = (gram T) ((gram_symm T).eigenvectorBasis hn i) from rfl]
  rw [(gram_symm T).apply_eigenvectorBasis hn i]
  rw [inner_smul_left]
  rw [orthonormal_iff_ite.mp ((gram_symm T).eigenvectorBasis hn).orthonormal i j]
  simp only [conj_trivial]
  by_cases h : i = j
  · subst h; rw [if_pos rfl, if_pos rfl, mul_one, RCLike.ofReal_real_eq_id]; rfl
  · rw [if_neg h, if_neg h, mul_zero]

noncomputable def sval (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) : ℝ :=
  T.singularValues k

theorem sval_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ sval T hn k := T.singularValues_nonneg k

theorem sval_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    sval T hn k ^ 2 = evals T hn k := by
  unfold sval evals
  rw [T.sq_singularValues_fin hn k]

theorem norm_Tv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    ‖T (rsv T hn k)‖ = sval T hn k := by
  have heig : inner ℝ (T (rsv T hn k)) (T (rsv T hn k)) = evals T hn k := by
    have h := inner_Tv_eig T hn k k
    rw [if_pos rfl] at h
    exact h
  have h2 : ‖T (rsv T hn k)‖ ^ 2 = sval T hn k ^ 2 := by
    rw [@norm_sq_eq_re_inner ℝ, heig, sval_sq, RCLike.re_to_real]
  have hnn := sval_nonneg T hn k
  nlinarith [norm_nonneg (T (rsv T hn k)), h2, hnn]

theorem hsInner_eq_trace {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    (∑ j, inner ℝ (S (b j)) (T (b j))) = (adjoint S ∘ₗ T).trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right S (b j) (T (b j))]

theorem hsInner_basis_indep {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ (S (b j)) (T (b j)))
      = ∑ k, inner ℝ (S (rsv T hn k)) (T (rsv T hn k)) := by
  rw [hsInner_eq_trace S T b, hsInner_eq_trace S T (rsv T hn)]

theorem vonNeumann_op {ι : Type*} [Fintype ι] (S : E →L[ℝ] F) (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ ((S : E →ₗ[ℝ] F) (b j)) (T (b j))) ≤ ‖S‖ * ∑ k, sval T hn k := by
  rw [hsInner_basis_indep (S : E →ₗ[ℝ] F) T b hn]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hSle : ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ ≤ ‖S‖ * ‖(rsv T hn k : E)‖ := S.le_opNorm _
  calc inner ℝ ((S : E →ₗ[ℝ] F) (rsv T hn k)) (T (rsv T hn k))
      ≤ ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ * ‖T (rsv T hn k)‖ := real_inner_le_norm _ _
    _ ≤ (‖S‖ * ‖(rsv T hn k : E)‖) * ‖T (rsv T hn k)‖ := by
          apply mul_le_mul_of_nonneg_right hSle (norm_nonneg _)
    _ = ‖S‖ * sval T hn k := by
          rw [(rsv T hn).orthonormal.1 k, norm_Tv]; ring

end SVDProbe

/-! ### Matrix specialization to the platform statement. -/

namespace MatrixCompletion

open SVDProbe

variable {n1 n2 : ℕ}

theorem matrixInner_eq_hsInner (A B : RealMatrix n1 n2) :
    matrixInner A B
      = ∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                      ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)) := by
  unfold matrixInner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply]
  simp only [toEuclideanLin_apply]
  have hcol : ∀ (C : RealMatrix n1 n2),
      (C *ᵥ (EuclideanSpace.single j (1:ℝ)).ofLp) i = C i j := by
    intro C
    simp only [Matrix.mulVec, EuclideanSpace.ofLp_single, dotProduct_single, mul_one]
  rw [hcol A, hcol B]
  rw [show (⟪A i j, B i j⟫_ℝ : ℝ) = B i j * (starRingEnd ℝ) (A i j) from RCLike.inner_apply _ _,
      conj_trivial]; ring

theorem nuclearNorm_eq_sum_sval (B : RealMatrix n1 n2)
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2) :
    nuclearNorm B = ∑ k, sval (toEuclideanLin B) hn k := by
  unfold nuclearNorm sval
  set T := toEuclideanLin B
  rw [Finsupp.sum_of_support_subset T.singularValues
      (s := Finset.range n2) ?_ (fun _ x => x) (by intro _ _; rfl)]
  · rw [Finset.sum_range fun k => T.singularValues k]
  · intro k hk
    rw [Finset.mem_range]
    by_contra hge
    push_neg at hge
    have hz : T.singularValues k = 0 := by
      apply T.singularValues_of_finrank_le
      rw [hn]; exact hge
    rw [Finsupp.mem_support_iff] at hk
    exact hk hz

theorem trace_duality_C1 (A B : RealMatrix n1 n2) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  rw [matrixInner_eq_hsInner A B, nuclearNorm_eq_sum_sval B hn]
  show (∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                     ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)))
      ≤ spectralNorm A * ∑ k, sval (toEuclideanLin B) hn k
  unfold _root_.MatrixCompletion.spectralNorm
  exact vonNeumann_op (LinearMap.toContinuousLinearMap (toEuclideanLin A))
    (toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ) hn

end MatrixCompletion

open MatrixCompletion
open scoped BigOperators

/-- C1 — von Neumann / matrix trace-duality inequality.
Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2, first inequality
(von Neumann's trace inequality 1937; Mirsky 1975). -/
theorem matrix_trace_duality_inequality {n₁ n₂ : ℕ} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B :=
  MatrixCompletion.trace_duality_C1 A B

end Imported2
def matrix_trace_duality_inequality := @Imported2.matrix_trace_duality_inequality

namespace Imported3
open MatrixCompletion

theorem solution {n₁ n₂ : ℕ} (N : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ∃ Z : Matrix (Fin n₁) (Fin n₂) ℝ,
      spectralNorm Z ≤ 1 ∧ matrixInner Z N = nuclearNorm N := by
  obtain ⟨r, S, _⟩ := matrix_svd_exists N
  exact ⟨signMatrix S, sign_matrix_spectral_norm_le_one S, sign_matrix_inner_eq_nuclear_norm S⟩

end Imported3
def nuclear_norm_dual_achiever_contraction := @Imported3.solution

namespace Imported4
namespace MatrixCompletion
open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace WithLp

variable {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂}

theorem signMatrix_spectralNorm_le_one_stub (S : SVD M r) :
    spectralNorm (signMatrix S) ≤ 1 :=
  sign_matrix_spectral_norm_le_one S

theorem ker_idem {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i b : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ k : Fin r, u k i * u k b := by
  have e1 : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin N, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; rw [horth k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, u k i * u l b * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then u k i * u l b else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp


theorem left_signMatrix (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold leftSingularProjection signMatrix
  -- signMatrix a j = ∑ l, u l a * v l j
  have hsm : ∀ a : Fin n₁, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) a j
      = ∑ l : Fin r, S.u l a * S.v l j := by
    intro a
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  -- LHS = ∑ a (∑ k u_k i u_k a)(∑ l u_l a v_l j)
  -- = ∑ k u_k i v_k j  (orthonormality of u)
  have hgoal : (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
        = ∑ a : Fin n₁, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j) := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ k : Fin r, ∑ a : Fin n₁, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n₁, S.u k a * S.u l a) := by
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [e2]
    have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n₁, S.u k a * S.u l a))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
      apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
      rw [S.u_orthonormal k l]
    rw [e3]
    apply Finset.sum_congr rfl; intro k _
    have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
        = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
      apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

theorem right_signMatrix (S : SVD M r) :
    rightSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold rightSingularProjection signMatrix
  have hsm : ∀ b : Fin n₂, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) i b
      = ∑ l : Fin r, S.u l i * S.v l b := by
    intro b
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _; rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  have hgoal : (∑ b : Fin n₂, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ b : Fin n₂, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
        = ∑ b : Fin n₂, ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j) := by
      apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ l : Fin r, ∑ b : Fin n₂, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n₂, S.v l b * S.v k b) := by
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e2]
    have e3 : (∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n₂, S.v l b * S.v k b))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (if l = k then 1 else 0) := by
      apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _
      rw [S.v_orthonormal l k]
    rw [e3]
    apply Finset.sum_congr rfl; intro l _
    have : (∑ k : Fin r, S.u l i * S.v k j * (if l = k then 1 else 0))
        = ∑ k : Fin r, (if l = k then S.u l i * S.v k j else 0) := by
      apply Finset.sum_congr rfl; intro k _; by_cases h : l = k <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

/-! ## Matrix projectors PU (n₁×n₁) and PV (n₂×n₂). -/

/-- Orthogonal projector onto the column singular space. -/
noncomputable def PUmat (S : SVD M r) : Matrix (Fin n₁) (Fin n₁) ℝ :=
  ∑ k, Matrix.vecMulVec (S.u k) (S.u k)

/-- Orthogonal projector onto the row singular space. -/
noncomputable def PVmat (S : SVD M r) : Matrix (Fin n₂) (Fin n₂) ℝ :=
  ∑ k, Matrix.vecMulVec (S.v k) (S.v k)

theorem PUmat_apply (S : SVD M r) (i a : Fin n₁) :
    PUmat S i a = ∑ k, S.u k i * S.u k a := by
  unfold PUmat
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _; rw [Matrix.vecMulVec_apply]

theorem PVmat_apply (S : SVD M r) (b j : Fin n₂) :
    PVmat S b j = ∑ k, S.v k b * S.v k j := by
  unfold PVmat
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _; rw [Matrix.vecMulVec_apply]

/-! ## Projector forms of the singular projections. -/

theorem left_eq_PU (S : SVD M r) (X : RealMatrix n₁ n₂) :
    leftSingularProjection S X = PUmat S * X := by
  funext i j
  unfold leftSingularProjection
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply]

theorem right_eq_PV (S : SVD M r) (X : RealMatrix n₁ n₂) :
    rightSingularProjection S X = X * PVmat S := by
  funext i j
  unfold rightSingularProjection
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro b _; rw [PVmat_apply]

theorem two_eq_PU_PV (S : SVD M r) (X : RealMatrix n₁ n₂) :
    twoSidedSingularProjection S X = PUmat S * X * PVmat S := by
  funext i j
  unfold twoSidedSingularProjection
  rw [Matrix.mul_apply]
  -- (PU * X * PV) i j = ∑ b (PU*X) i b * PV b j = ∑ b (∑ a PU i a * X a b) * PV b j
  have hrew : ∀ b : Fin n₂, (PUmat S * X) i b * PVmat S b j
      = (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * X a b)
          * (∑ l : Fin r, S.v l b * S.v l j) := by
    intro b
    rw [Matrix.mul_apply, PVmat_apply]
    congr 1
    apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply]
  rw [Finset.sum_congr rfl (fun b _ => hrew b)]
  -- target: ∑ a ∑ b (∑k u i a) X a b (∑l v b j) = ∑ b (∑ a (∑k u i a) X a b)(∑l v b j)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

/-! ## Idempotence and symmetry of PU, PV. -/

theorem PU_idem (S : SVD M r) : PUmat S * PUmat S = PUmat S := by
  funext i j
  rw [Matrix.mul_apply]
  have : (∑ a : Fin n₁, PUmat S i a * PUmat S a j)
      = ∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.u l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply, PUmat_apply]
  rw [this, ker_idem S.u S.u_orthonormal i j, PUmat_apply]

theorem PV_idem (S : SVD M r) : PVmat S * PVmat S = PVmat S := by
  funext i j
  rw [Matrix.mul_apply]
  have : (∑ a : Fin n₂, PVmat S i a * PVmat S a j)
      = ∑ a : Fin n₂, (∑ k : Fin r, S.v k i * S.v k a) * (∑ l : Fin r, S.v l a * S.v l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [PVmat_apply, PVmat_apply]
  rw [this, ker_idem S.v S.v_orthonormal i j, PVmat_apply]

theorem PU_symm (S : SVD M r) : (PUmat S)ᵀ = PUmat S := by
  funext i j
  rw [Matrix.transpose_apply, PUmat_apply, PUmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

theorem PV_symm (S : SVD M r) : (PVmat S)ᵀ = PVmat S := by
  funext i j
  rw [Matrix.transpose_apply, PVmat_apply, PVmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

/-! ## Factorization of the normal projection: W = (1-PU) Z (1-PV). -/

theorem normalProjection_factor (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z = (1 - PUmat S) * Z * (1 - PVmat S) := by
  unfold normalProjection tangentProjection
  rw [left_eq_PU, right_eq_PV, two_eq_PU_PV]
  -- Z - (PU Z + Z PV - PU Z PV) = (1-PU) Z (1-PV)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  -- LHS = Z - (PU*Z + Z*PV - PU*Z*PV); RHS = (Z - Z*PV) - (PU*Z - PU*Z*PV)
  abel

/-! ## E = signMatrix S obeys PU E = E, E PV = E. -/

theorem PU_signMatrix (S : SVD M r) : PUmat S * signMatrix S = signMatrix S := by
  rw [← left_eq_PU, left_signMatrix]

theorem signMatrix_PV (S : SVD M r) : signMatrix S * PVmat S = signMatrix S := by
  rw [← right_eq_PV, right_signMatrix]

/-! ## Orthogonality crux: Eᵀ * W = 0  and  W * PV = 0. -/

theorem Etrans_W_eq_zero (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    (signMatrix S)ᵀ * normalProjection S Z = 0 := by
  rw [normalProjection_factor]
  -- Eᵀ * (1-PU) * Z * (1-PV) ; Eᵀ * (1-PU) = Eᵀ - Eᵀ PU = Eᵀ - (PU E)ᵀ = Eᵀ - Eᵀ = 0
  have hEt : (signMatrix S)ᵀ * (1 - PUmat S) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have : (signMatrix S)ᵀ * PUmat S = (signMatrix S)ᵀ := by
      have h := PU_signMatrix S
      have h2 : (PUmat S * signMatrix S)ᵀ = (signMatrix S)ᵀ := by rw [h]
      rw [Matrix.transpose_mul, PU_symm] at h2
      exact h2
    rw [this, sub_self]
  calc (signMatrix S)ᵀ * ((1 - PUmat S) * Z * (1 - PVmat S))
      = ((signMatrix S)ᵀ * (1 - PUmat S)) * Z * (1 - PVmat S) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = 0 := by rw [hEt, Matrix.zero_mul, Matrix.zero_mul]

theorem W_PV_eq_zero (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z * PVmat S = 0 := by
  rw [normalProjection_factor]
  have hPV : (1 - PVmat S) * PVmat S = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, PV_idem, sub_self]
  calc (1 - PUmat S) * Z * (1 - PVmat S) * PVmat S
      = (1 - PUmat S) * Z * ((1 - PVmat S) * PVmat S) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hPV, Matrix.mul_zero]

/-! ## E = E PV (already from right_signMatrix). -/

theorem signMatrix_eq_signMatrix_PV (S : SVD M r) :
    signMatrix S = signMatrix S * PVmat S := (signMatrix_PV S).symm

/-! ## Analytic part. -/

/-- ofLp of the Euclidean image is the matrix-vector product. -/
theorem ofLp_image (A : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    ofLp ((toEuclideanLin A) x) = A *ᵥ ofLp x :=
  Matrix.ofLp_toEuclideanLin_apply A x

/-- Euclidean inner product as coordinate sum (for ℝ). -/
theorem eucl_inner_eq_sum {N : ℕ} (a b : EuclideanSpace ℝ (Fin N)) :
    (inner ℝ a b : ℝ) = ∑ i, (ofLp a) i * (ofLp b) i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro i _
  rw [show (⟪a i, b i⟫_ℝ : ℝ) = b i * (starRingEnd ℝ) (a i) from RCLike.inner_apply _ _,
      conj_trivial]; ring

/-- Inner product of two Euclidean images as a coordinate sum of matrix-vector products. -/
theorem inner_image_eq_sum (B C : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (inner ℝ ((toEuclideanLin B) x) ((toEuclideanLin C) x) : ℝ)
      = ∑ i, (B *ᵥ ofLp x) i * (C *ᵥ ofLp x) i := by
  rw [eucl_inner_eq_sum, ofLp_image, ofLp_image]

/-- A bilinear quadratic form `∑ᵢ (B x)ᵢ (C x)ᵢ` expands as `∑_{p,q} (Bᵀ C)_{pq} xₚ x_q`. -/
theorem mulVec_dot_eq_transpose_mul (B C : RealMatrix n₁ n₂) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ p, ∑ q, (Bᵀ * C) p q * x p * x q := by
  have e1 : (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.mulVec, Matrix.mulVec]; rfl
  rw [e1]
  -- expand each product, swap sums to pull i innermost
  have e2 : (∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q))
      = ∑ i, ∑ p, ∑ q, (B i p * C i q) * (x p * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _; ring
  rw [e2, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.transpose_apply]; ring

/-- If `Bᵀ C = 0` then `∑ᵢ (B x)ᵢ (C x)ᵢ = 0`. -/
theorem mulVec_dot_eq_zero_of_transpose_mul_zero (B C : RealMatrix n₁ n₂)
    (h : Bᵀ * C = 0) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i) = 0 := by
  rw [mulVec_dot_eq_transpose_mul, h]
  simp

/-! ## Euclidean norm-squared as a quadratic form. -/

/-- `‖a‖² = ∑ᵢ (ofLp a)ᵢ²`. -/
theorem normSq_eq_sum {N : ℕ} (a : EuclideanSpace ℝ (Fin N)) :
    ‖a‖ ^ 2 = ∑ i, (ofLp a) i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, eucl_inner_eq_sum]
  apply Finset.sum_congr rfl; intro i _; ring

/-- `‖B y‖² = ∑_{p,q} (Bᵀ B)_{pq} yₚ y_q` for the Euclidean image. -/
theorem normSq_image_eq_quad (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ^ 2
      = ∑ p, ∑ q, (Bᵀ * B) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  have : (∑ i, (ofLp ((toEuclideanLin B) y)) i ^ 2)
      = ∑ i, (B *ᵥ ofLp y) i * (B *ᵥ ofLp y) i := by
    apply Finset.sum_congr rfl; intro i _; rw [ofLp_image]; ring
  rw [this, mulVec_dot_eq_transpose_mul]

/-- `‖y‖² = ∑_{p,q} (1)_{pq} yₚ y_q`. -/
theorem normSq_eq_one_quad {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) :
    ‖y‖ ^ 2 = ∑ p, ∑ q, (1 : Matrix (Fin N) (Fin N) ℝ) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq]; ring
  · intro q _ hq; rw [Matrix.one_apply_ne (Ne.symm hq)]; ring
  · intro h; exact absurd (Finset.mem_univ p) h

/-- Pythagorean split for a symmetric idempotent square matrix `P`. -/
theorem pythagoras_split {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin P) y‖ ^ 2 + ‖(toEuclideanLin (1 - P)) y‖ ^ 2 = ‖y‖ ^ 2 := by
  have hPtP : Pᵀ * P = P := by rw [hsymm, hidem]
  have hQtQ : (1 - P)ᵀ * (1 - P) = 1 - P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hidem]
    abel
  rw [normSq_image_eq_quad, hPtP, normSq_image_eq_quad, hQtQ, normSq_eq_one_quad]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases h : p = q
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-! ## Operator-norm bound transport. -/

/-- `‖B y‖ ≤ spectralNorm B · ‖y‖`. -/
theorem norm_image_le (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ≤ spectralNorm B * ‖y‖ := by
  unfold _root_.MatrixCompletion.spectralNorm
  have h := (LinearMap.toContinuousLinearMap (toEuclideanLin B)).le_opNorm y
  simpa using h

/-- Orthogonal projection `1-P` (symmetric idempotent `P`) is a contraction. -/
theorem norm_compl_le {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin (1 - P)) y‖ ≤ ‖y‖ := by
  have hsplit := pythagoras_split P hsymm hidem y
  have hle : ‖(toEuclideanLin (1 - P)) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(toEuclideanLin P) y‖]
  have h1 := norm_nonneg ((toEuclideanLin (1 - P)) y)
  have h2 := norm_nonneg y
  nlinarith [hle, h1, h2]

/-! ## `toEuclideanLin` is multiplicative / additive (transported through `ofLp`). -/

theorem toEuclideanLin_mul_apply {n₀ : ℕ} (A : RealMatrix n₀ n₁) (B : RealMatrix n₁ n₂)
    (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A * B)) x = (toEuclideanLin A) ((toEuclideanLin B) x) := by
  apply ofLp_injective
  rw [ofLp_image, ofLp_image, ofLp_image, Matrix.mulVec_mulVec]

theorem toEuclideanLin_add_apply (A B : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A + B)) x = (toEuclideanLin A) x + (toEuclideanLin B) x := by
  apply ofLp_injective
  rw [ofLp_image]
  rw [show ofLp ((toEuclideanLin A) x + (toEuclideanLin B) x)
        = ofLp ((toEuclideanLin A) x) + ofLp ((toEuclideanLin B) x) from rfl]
  rw [ofLp_image, ofLp_image, Matrix.add_mulVec]

/-! ## The per-vector contraction, then the operator-norm bound. -/

/-- Per-vector sharp contraction: `‖(E + W) x‖ ≤ ‖x‖` in EuclideanSpace. -/
theorem nopb_vector (S : SVD M r) (Z : RealMatrix n₁ n₂) (hZ : spectralNorm Z ≤ 1)
    (x : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin (signMatrix S + normalProjection S Z)) x‖ ≤ ‖x‖ := by
  set E := signMatrix S with hE
  set W := normalProjection S Z with hW
  set Ex := (toEuclideanLin E) x with hEx
  set Wx := (toEuclideanLin W) x with hWx
  -- A x = E x + W x
  have hAx : (toEuclideanLin (E + W)) x = Ex + Wx := toEuclideanLin_add_apply E W x
  -- orthogonality ⟪Ex, Wx⟫ = 0
  have horth : (inner ℝ Ex Wx : ℝ) = 0 := by
    rw [hEx, hWx, inner_image_eq_sum]
    exact mulVec_dot_eq_zero_of_transpose_mul_zero E W (Etrans_W_eq_zero S Z) (ofLp x)
  -- Pythagoras
  have hpyth : ‖Ex + Wx‖ ^ 2 = ‖Ex‖ ^ 2 + ‖Wx‖ ^ 2 := by
    rw [norm_add_sq_real, horth]; ring
  -- ‖Ex‖ ≤ ‖PV x‖
  have hEbound : ‖Ex‖ ≤ ‖(toEuclideanLin (PVmat S)) x‖ := by
    have hsplit : E = E * PVmat S := signMatrix_eq_signMatrix_PV S
    have : Ex = (toEuclideanLin E) ((toEuclideanLin (PVmat S)) x) := by
      rw [hEx]
      conv_lhs => rw [hsplit]
      rw [toEuclideanLin_mul_apply]
    rw [this]
    calc ‖(toEuclideanLin E) ((toEuclideanLin (PVmat S)) x)‖
        ≤ spectralNorm E * ‖(toEuclideanLin (PVmat S)) x‖ := norm_image_le E _
      _ ≤ 1 * ‖(toEuclideanLin (PVmat S)) x‖ := by
          apply mul_le_mul_of_nonneg_right (signMatrix_spectralNorm_le_one_stub S) (norm_nonneg _)
      _ = ‖(toEuclideanLin (PVmat S)) x‖ := one_mul _
  -- ‖Wx‖ ≤ ‖(1-PV) x‖
  have hWbound : ‖Wx‖ ≤ ‖(toEuclideanLin (1 - PVmat S)) x‖ := by
    -- W = (1-PU) Z (1-PV), so W x = (1-PU)(Z((1-PV)x))
    have hWfac : W = (1 - PUmat S) * Z * (1 - PVmat S) := normalProjection_factor S Z
    have hWx2 : Wx = (toEuclideanLin (1 - PUmat S))
        ((toEuclideanLin Z) ((toEuclideanLin (1 - PVmat S)) x)) := by
      rw [hWx, hWfac, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    rw [hWx2]
    have hPUsymm : (PUmat S)ᵀ = PUmat S := PU_symm S
    have hPUidem : PUmat S * PUmat S = PUmat S := PU_idem S
    calc ‖(toEuclideanLin (1 - PUmat S))
            ((toEuclideanLin Z) ((toEuclideanLin (1 - PVmat S)) x))‖
        ≤ ‖(toEuclideanLin Z) ((toEuclideanLin (1 - PVmat S)) x)‖ :=
          norm_compl_le (PUmat S) hPUsymm hPUidem _
      _ ≤ spectralNorm Z * ‖(toEuclideanLin (1 - PVmat S)) x‖ := norm_image_le Z _
      _ ≤ 1 * ‖(toEuclideanLin (1 - PVmat S)) x‖ := by
          apply mul_le_mul_of_nonneg_right hZ (norm_nonneg _)
      _ = ‖(toEuclideanLin (1 - PVmat S)) x‖ := one_mul _
  -- Pythagoras split for PV
  have hPVsplit : ‖(toEuclideanLin (PVmat S)) x‖ ^ 2
      + ‖(toEuclideanLin (1 - PVmat S)) x‖ ^ 2 = ‖x‖ ^ 2 :=
    pythagoras_split (PVmat S) (PV_symm S) (PV_idem S) x
  -- combine
  have hAsq : ‖(toEuclideanLin (E + W)) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hAx, hpyth]
    have h1 : ‖Ex‖ ^ 2 ≤ ‖(toEuclideanLin (PVmat S)) x‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg Ex) hEbound 2
    have h2 : ‖Wx‖ ^ 2 ≤ ‖(toEuclideanLin (1 - PVmat S)) x‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg Wx) hWbound 2
    nlinarith [h1, h2, hPVsplit]
  -- conclude ‖A x‖ ≤ ‖x‖
  have hAnn := norm_nonneg ((toEuclideanLin (E + W)) x)
  have hxnn := norm_nonneg x
  nlinarith [hAsq, hAnn, hxnn]

/-- **nopb** — sign + normal projection contraction:
`spectralNorm (signMatrix S + normalProjection S Z) ≤ 1` when `spectralNorm Z ≤ 1`.
Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2 achiever contraction. -/
theorem nopb {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (Z : Matrix (Fin n₁) (Fin n₂) ℝ) (hZ : spectralNorm Z ≤ 1) :
    spectralNorm (signMatrix S + normalProjection S Z) ≤ 1 := by
  unfold _root_.MatrixCompletion.spectralNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]
  have h := nopb_vector S Z hZ x
  simpa using h


end MatrixCompletion

open MatrixCompletion
theorem solution {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (Z : Matrix (Fin n₁) (Fin n₂) ℝ) (hZ : spectralNorm Z ≤ 1) :
    spectralNorm (signMatrix S + normalProjection S Z) ≤ 1 :=
  MatrixCompletion.nopb S Z hZ

end Imported4
def sign_plus_normal_projection_operator_norm_le_one := @Imported4.solution

namespace Imported5
/-!
L2 reduction — `normal_space_dual_achiever_with_sign_contraction`
(Candès–Recht 2009, arXiv:0805.4471, Lemma 3.2 achiever, p.15).

Reduces to two cited children:
  * `nuclear_norm_dual_achiever_contraction` : ∀ N, ∃ Z, ‖Z‖_op ≤ 1 ∧ ⟨Z,N⟩ = ‖N‖_*.
  * `sign_plus_normal_projection_operator_norm_le_one` :
        ∀ Z, ‖Z‖_op ≤ 1 → ‖E + P_{T⊥}Z‖_op ≤ 1.
The orthogonal-projection algebra (P_{T⊥} idempotent + tangent self-adjoint) is inline.
-/

open MatrixCompletion
open scoped Classical BigOperators

namespace MatrixCompletion

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

-- ===== bring in the proven pieces (copied) =====

theorem ker_idem {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i b : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ k : Fin r, u k i * u k b := by
  have e1 : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin N, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; rw [horth k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, u k i * u l b * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then u k i * u l b else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem left_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X) = leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection
  have : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
      = ∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * X a j := by
    have hL : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
        = ∑ a : Fin n1, (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
              (∑ k : Fin r, S.u k c * S.u k a)) * X a j := by
      have hLeft : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
          = ∑ c : Fin n1, ∑ a : Fin n1,
              (∑ k : Fin r, S.u k i * S.u k c) * (∑ k : Fin r, S.u k c * S.u k a) * X a j := by
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      have hRight : (∑ a : Fin n1, (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
              (∑ k : Fin r, S.u k c * S.u k a)) * X a j)
          = ∑ a : Fin n1, ∑ c : Fin n1,
              (∑ k : Fin r, S.u k i * S.u k c) * (∑ k : Fin r, S.u k c * S.u k a) * X a j := by
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_mul]
      rw [hLeft, hRight, Finset.sum_comm]
    rw [hL]
    apply Finset.sum_congr rfl; intro a _
    rw [ker_idem S.u S.u_orthonormal i a]
  exact this

theorem right_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X) = rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  have hR : (∑ b : Fin n2, (∑ c : Fin n2, X i c * (∑ l : Fin r, S.v l c * S.v l b)) *
              (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ c : Fin n2, X i c * (∑ b : Fin n2,
            (∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
    have hLeft : (∑ b : Fin n2, (∑ c : Fin n2, X i c * (∑ l : Fin r, S.v l c * S.v l b)) *
              (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ b : Fin n2, ∑ c : Fin n2,
            X i c * ((∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro c _; ring
    have hRight : (∑ c : Fin n2, X i c * (∑ b : Fin n2,
            (∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)))
        = ∑ c : Fin n2, ∑ b : Fin n2,
            X i c * ((∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.mul_sum]
    rw [hLeft, hRight, Finset.sum_comm]
  rw [hR]
  apply Finset.sum_congr rfl; intro c _
  rw [ker_idem S.v S.v_orthonormal c j]

theorem two_eq_left_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = leftSingularProjection S (rightSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem two_eq_right_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = rightSingularProjection S (leftSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

theorem left_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B) = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  show (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (A a j + B a j))
      = (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * A a j)
        + (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * B a j)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem left_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B) = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  show (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (A a j - B a j))
      = (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * A a j)
        - (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * B a j)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem right_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B) = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  show (∑ b : Fin n2, (A i b + B i b) * (∑ k : Fin r, S.v k b * S.v k j))
      = (∑ b : Fin n2, A i b * (∑ k : Fin r, S.v k b * S.v k j))
        + (∑ b : Fin n2, B i b * (∑ k : Fin r, S.v k b * S.v k j))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem right_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B) = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  show (∑ b : Fin n2, (A i b - B i b) * (∑ k : Fin r, S.v k b * S.v k j))
      = (∑ b : Fin n2, A i b * (∑ k : Fin r, S.v k b * S.v k j))
        - (∑ b : Fin n2, B i b * (∑ k : Fin r, S.v k b * S.v k j))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem left_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_left_right S X, left_left S (rightSingularProjection S X)]

theorem right_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_right_left S X, right_right S (leftSingularProjection S X)]

theorem left_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (tangentProjection S X) = leftSingularProjection S X := by
  unfold tangentProjection
  rw [left_sub, left_add, left_left, ← two_eq_left_right, left_two]
  abel

theorem right_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (tangentProjection S X) = rightSingularProjection S X := by
  unfold tangentProjection
  rw [right_sub, right_add, right_right, ← two_eq_right_left, right_two]
  abel

theorem two_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (tangentProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_left_right S (tangentProjection S X), right_tangent, ← two_eq_left_right]

theorem tangent_idem {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  conv_lhs => rw [tangentProjection]
  rw [left_tangent, right_tangent, two_tangent]
  rfl

-- ===== self-adjoint + coordinate (copied from Thm file) =====

theorem matrixInner_coordinateMatrix {n1 n2 : Nat} (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _; simp [ha]
  · intro h; simp at h

theorem tangentProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner X (tangentProjection S Y) = matrixInner (tangentProjection S X) Y := by
  unfold matrixInner tangentProjection
  simp only [Matrix.add_apply, Matrix.sub_apply]
  unfold leftSingularProjection rightSingularProjection twoSidedSingularProjection
  have h1 : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j) := by
    have hLn : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2,
            (∑ k, S.u k i * S.u k a) * (X i j * Y a j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    have hRn : (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j)
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2,
            (∑ k, S.u k i * S.u k a) * (X a j * Y i j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hLn, hRn, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have hk : (∑ k, S.u k a * S.u k i) = (∑ k, S.u k i * S.u k a) := by
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hk]
  have h2 : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    apply Finset.sum_congr rfl; intro i _
    have hLn : (∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
        = ∑ j : Fin n2, ∑ b : Fin n2, (∑ l, S.v l b * S.v l j) * (X i j * Y i b) := by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    have hRn : (∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j)
        = ∑ j : Fin n2, ∑ b : Fin n2, (∑ l, S.v l b * S.v l j) * (X i b * Y i j) := by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [hLn, hRn, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    have hk : (∑ l, S.v l j * S.v l b) = (∑ l, S.v l b * S.v l j) := by
      apply Finset.sum_congr rfl; intro l _; ring
    rw [hk]
  have h3 : (∑ i : Fin n1, ∑ j : Fin n2,
        X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))
      = (∑ i : Fin n1, ∑ j : Fin n2,
        (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    have hLn : (∑ i : Fin n1, ∑ j : Fin n2,
          X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))
        = ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X i j * Y a b) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    have hRn : (∑ i : Fin n1, ∑ j : Fin n2,
          (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j)
        = ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X a b * Y i j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [hLn, hRn]
    rw [show (∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X i j * Y a b))
        = ∑ q : (Fin n1 × Fin n2) × (Fin n1 × Fin n2),
            (∑ k, S.u k q.1.1 * S.u k q.2.1) * (∑ l, S.v l q.2.2 * S.v l q.1.2)
              * (X q.1.1 q.1.2 * Y q.2.1 q.2.2) from by
          simp_rw [Fintype.sum_prod_type]]
    rw [show (∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X a b * Y i j))
        = ∑ q : (Fin n1 × Fin n2) × (Fin n1 × Fin n2),
            (∑ k, S.u k q.1.1 * S.u k q.2.1) * (∑ l, S.v l q.2.2 * S.v l q.1.2)
              * (X q.2.1 q.2.2 * Y q.1.1 q.1.2) from by
          simp_rw [Fintype.sum_prod_type]]
    apply Finset.sum_nbij' (i := fun q => (q.2, q.1)) (j := fun q => (q.2, q.1))
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
    · intro p _
      have hku : (∑ k, S.u k p.2.1 * S.u k p.1.1) = (∑ k, S.u k p.1.1 * S.u k p.2.1) := by
        apply Finset.sum_congr rfl; intro k _; ring
      have hlv : (∑ l, S.v l p.1.2 * S.v l p.2.2) = (∑ l, S.v l p.2.2 * S.v l p.1.2) := by
        apply Finset.sum_congr rfl; intro l _; ring
      show _ = _
      simp only
      rw [hku, hlv]
  have hdistL : (∑ i : Fin n1, ∑ j : Fin n2,
        X i j * (((∑ a, (∑ k, S.u k i * S.u k a) * Y a j)
                  + (∑ b, Y i b * (∑ l, S.v l b * S.v l j))
                  - (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))))
      = (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
        + (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
        - (∑ i : Fin n1, ∑ j : Fin n2,
            X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hdistR : (∑ i : Fin n1, ∑ j : Fin n2,
        (((∑ a, (∑ k, S.u k i * S.u k a) * X a j)
                  + (∑ b, X i b * (∑ l, S.v l b * S.v l j))
                  - (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)))) * Y i j)
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j)
        + (∑ i : Fin n1, ∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j)
        - (∑ i : Fin n1, ∑ j : Fin n2,
            (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hdistL, hdistR, h1, h2, h3]

-- ===== norm helpers =====

theorem matrixInner_self {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    matrixInner X X = frobeniusNormSq X := by
  unfold matrixInner frobeniusNormSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem frobeniusNormSq_nonneg {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    0 ≤ frobeniusNormSq X :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem frobeniusNormSq_eq_sq {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    frobeniusNormSq X = frobeniusNorm X ^ 2 := by
  unfold frobeniusNorm
  rw [Real.sq_sqrt (frobeniusNormSq_nonneg X)]

/-- Cauchy–Schwarz, squared form, for the Frobenius inner product. -/
theorem matrixInner_sq_le {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
  have hfold : (∑ i : Fin n1, ∑ j : Fin n2, X i j * Y i j)
        = ∑ q : Fin n1 × Fin n2, X q.1 q.2 * Y q.1 q.2 :=
    (Fintype.sum_prod_type (fun q => X q.1 q.2 * Y q.1 q.2)).symm
  have hfoldX : (∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2)
        = ∑ q : Fin n1 × Fin n2, X q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type (fun q => X q.1 q.2 ^ 2)).symm
  have hfoldY : (∑ i : Fin n1, ∑ j : Fin n2, Y i j ^ 2)
        = ∑ q : Fin n1 × Fin n2, Y q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type (fun q => Y q.1 q.2 ^ 2)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n1 × Fin n2))
      (fun q => X q.1 q.2) (fun q => Y q.1 q.2)
  unfold matrixInner frobeniusNormSq
  rw [hfold, hfoldX, hfoldY]
  exact hcs

/-- The tangent projection is a Frobenius contraction. -/
theorem tangentProjection_contraction {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    frobeniusNormSq (tangentProjection S X) ≤ frobeniusNormSq X := by
  set Y := tangentProjection S X with hY
  -- ‖Y‖² = ⟨Y,Y⟩ = ⟨X, P_T(P_T X)⟩ = ⟨X, Y⟩
  have hself : matrixInner Y Y = matrixInner X Y := by
    -- selfAdjoint: ⟨X, P_T Y⟩ = ⟨P_T X, Y⟩.  With Y = P_T X, P_T Y = P_T(P_T X) = P_T X = Y.
    have hsa := tangentProjection_selfAdjoint S X Y
    rw [hY] at hsa
    rw [tangent_idem] at hsa
    -- hsa : matrixInner X (tangentProjection S X) = matrixInner (tangentProjection S X) (tangentProjection S X)
    rw [hY]
    exact hsa.symm
  have hYY : frobeniusNormSq Y = matrixInner X Y := by
    rw [← matrixInner_self Y, hself]
  -- ⟨X,Y⟩ ≤ ‖X‖‖Y‖ ; so ‖Y‖² ≤ ‖X‖‖Y‖
  have hcs : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y :=
    matrixInner_sq_le X Y
  have hYYnn : 0 ≤ frobeniusNormSq Y := frobeniusNormSq_nonneg Y
  have hXXnn : 0 ≤ frobeniusNormSq X := frobeniusNormSq_nonneg X
  -- from hYY: frobeniusNormSq Y = matrixInner X Y, so (frobeniusNormSq Y)^2 = (matrixInner X Y)^2 ≤ ‖X‖²‖Y‖²
  have hsq : (frobeniusNormSq Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    calc (frobeniusNormSq Y) ^ 2 = (matrixInner X Y) ^ 2 := by rw [hYY]
      _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hcs
  -- conclude frobeniusNormSq Y ≤ frobeniusNormSq X
  rcases eq_or_lt_of_le hYYnn with h0 | hpos
  · rw [← h0]; exact hXXnn
  · -- divide hsq by frobeniusNormSq Y > 0
    have : frobeniusNormSq Y * frobeniusNormSq Y ≤ frobeniusNormSq X * frobeniusNormSq Y := by
      calc frobeniusNormSq Y * frobeniusNormSq Y = (frobeniusNormSq Y) ^ 2 := by ring
        _ ≤ frobeniusNormSq X * frobeniusNormSq Y := hsq
    exact le_of_mul_le_mul_right this hpos

/-- The Parseval contraction: ∑ ⟨X, P_T e_ij⟩² ≤ ‖X‖²_F. -/
theorem tangent_projection_coordinate_parseval_contraction
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    (∑ i : Fin n1, ∑ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j)) ^ 2)
      ≤ frobeniusNormSq X := by
  -- rewrite each term: ⟨X, P_T e_ij⟩ = ⟨P_T X, e_ij⟩ = (P_T X) i j
  have hterm : ∀ i : Fin n1, ∀ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j))
        = tangentProjection S X i j := by
    intro i j
    rw [tangentProjection_selfAdjoint S X (coordinateMatrix i j)]
    rw [matrixInner_coordinateMatrix]
  have hrw : (∑ i : Fin n1, ∑ j : Fin n2,
      matrixInner X (tangentProjection S (coordinateMatrix i j)) ^ 2)
      = ∑ i : Fin n1, ∑ j : Fin n2, tangentProjection S X i j ^ 2 := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hterm i j]
  rw [hrw]
  -- this is frobeniusNormSq (P_T X)
  have heq : (∑ i : Fin n1, ∑ j : Fin n2, tangentProjection S X i j ^ 2)
      = frobeniusNormSq (tangentProjection S X) := rfl
  rw [heq]
  exact tangentProjection_contraction S X


/-- `twoSidedSingularProjection` is additive over subtraction. -/
theorem two_sub' (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j
  show (∑ a : Fin n1, ∑ b : Fin n2,
        (∑ k : Fin r, S.u k i * S.u k a) * (A a b - B a b) * (∑ l : Fin r, S.v l b * S.v l j))
      = (∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k : Fin r, S.u k i * S.u k a) * A a b * (∑ l : Fin r, S.v l b * S.v l j))
        - (∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k : Fin r, S.u k i * S.u k a) * B a b * (∑ l : Fin r, S.v l b * S.v l j))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

/-- `tangentProjection` is additive over subtraction. -/
theorem tangent_sub' (S : SVD M r) (A B : RealMatrix n1 n2) :
    tangentProjection S (A - B) = tangentProjection S A - tangentProjection S B := by
  unfold tangentProjection
  rw [left_sub, right_sub, two_sub']; abel

theorem matrixInner_sub_left' (A B X : RealMatrix n1 n2) :
    matrixInner (A - B) X = matrixInner A X - matrixInner B X := by
  unfold matrixInner
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

theorem matrixInner_sub_right' (X A B : RealMatrix n1 n2) :
    matrixInner X (A - B) = matrixInner X A - matrixInner X B := by
  unfold matrixInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [Matrix.sub_apply]; ring

/-- `normalProjection` is idempotent. -/
theorem normal_idem' (S : SVD M r) (X : RealMatrix n1 n2) :
    normalProjection S (normalProjection S X) = normalProjection S X := by
  unfold normalProjection
  rw [tangent_sub', tangent_idem, sub_self, sub_zero]

end MatrixCompletion

open MatrixCompletion

/-- L2 — normal-space dual achiever with sign-contraction (CR2009 Lemma 3.2 achiever). -/
theorem solution {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    ∃ W : Matrix (Fin n₁) (Fin n₂) ℝ,
      normalProjection S W = W ∧
      spectralNorm (signMatrix S + W) ≤ 1 ∧
      matrixInner W (normalProjection S H) = nuclearNorm (normalProjection S H) := by
  set NH := normalProjection S H with hNH
  obtain ⟨Z, hZop, hZNH⟩ := nuclear_norm_dual_achiever_contraction NH
  refine ⟨normalProjection S Z, normal_idem' S Z,
    sign_plus_normal_projection_operator_norm_le_one S Z hZop, ?_⟩
  have hself : matrixInner (normalProjection S Z) NH
      = matrixInner Z (normalProjection S NH) := by
    unfold normalProjection
    rw [matrixInner_sub_left', matrixInner_sub_right',
      tangentProjection_selfAdjoint S Z NH]
  have hNHidem : normalProjection S NH = NH := by rw [hNH]; exact normal_idem' S H
  rw [hself, hNHidem, hZNH]

end Imported5
def normal_space_dual_achiever_with_sign_contraction := @Imported5.solution

namespace Imported6
/-!
Reduction of node 40a58360 `nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm`
to the trace-duality cores:
  C1 = matrix_trace_duality_inequality   (⟨A,B⟩ ≤ ‖A‖_op ‖B‖_*)
  L1 = sign_matrix_inner_eq_nuclear_norm (⟨E,M⟩ = ‖M‖_*)
  L2 = normal_space_dual_achiever_with_sign_contraction
       (∃ W∈T⊥, ‖E+W‖_op≤1, ⟨W,N_H⟩=‖N_H‖_*).
CR2009 Lemma 3.2 / subgradient characterization (3.4), p.15.
The proved helpers (P_T algebra, M∈T) are inlined; only the three deep cores are imported.
-/

open scoped Classical BigOperators

namespace MatrixCompletion

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

theorem ker_idem {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i b : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ k : Fin r, u k i * u k b := by
  have e1 : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin N, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; rw [horth k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, u k i * u l b * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then u k i * u l b else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem left_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X) = leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection
  have : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
      = ∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * X a j := by
    have hL : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
        = ∑ a : Fin n1, (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
              (∑ k : Fin r, S.u k c * S.u k a)) * X a j := by
      have hLeft : (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
            (∑ a : Fin n1, (∑ k : Fin r, S.u k c * S.u k a) * X a j))
          = ∑ c : Fin n1, ∑ a : Fin n1,
              (∑ k : Fin r, S.u k i * S.u k c) * (∑ k : Fin r, S.u k c * S.u k a) * X a j := by
        apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      have hRight : (∑ a : Fin n1, (∑ c : Fin n1, (∑ k : Fin r, S.u k i * S.u k c) *
              (∑ k : Fin r, S.u k c * S.u k a)) * X a j)
          = ∑ a : Fin n1, ∑ c : Fin n1,
              (∑ k : Fin r, S.u k i * S.u k c) * (∑ k : Fin r, S.u k c * S.u k a) * X a j := by
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_mul]
      rw [hLeft, hRight, Finset.sum_comm]
    rw [hL]
    apply Finset.sum_congr rfl; intro a _
    rw [ker_idem S.u S.u_orthonormal i a]
  exact this

theorem right_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X) = rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  have hR : (∑ b : Fin n2, (∑ c : Fin n2, X i c * (∑ l : Fin r, S.v l c * S.v l b)) *
              (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ c : Fin n2, X i c * (∑ b : Fin n2,
            (∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
    have hLeft : (∑ b : Fin n2, (∑ c : Fin n2, X i c * (∑ l : Fin r, S.v l c * S.v l b)) *
              (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ b : Fin n2, ∑ c : Fin n2,
            X i c * ((∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro c _; ring
    have hRight : (∑ c : Fin n2, X i c * (∑ b : Fin n2,
            (∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)))
        = ∑ c : Fin n2, ∑ b : Fin n2,
            X i c * ((∑ l : Fin r, S.v l c * S.v l b) * (∑ l : Fin r, S.v l b * S.v l j)) := by
      apply Finset.sum_congr rfl; intro c _
      rw [Finset.mul_sum]
    rw [hLeft, hRight, Finset.sum_comm]
  rw [hR]
  apply Finset.sum_congr rfl; intro c _
  rw [ker_idem S.v S.v_orthonormal c j]

theorem two_eq_left_right {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = leftSingularProjection S (rightSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem two_eq_right_left {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X = rightSingularProjection S (leftSingularProjection S X) := by
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

theorem left_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B) = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  show (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (A a j + B a j))
      = (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * A a j)
        + (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * B a j)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem left_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B) = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  show (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (A a j - B a j))
      = (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * A a j)
        - (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * B a j)
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

theorem right_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B) = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  show (∑ b : Fin n2, (A i b + B i b) * (∑ k : Fin r, S.v k b * S.v k j))
      = (∑ b : Fin n2, A i b * (∑ k : Fin r, S.v k b * S.v k j))
        + (∑ b : Fin n2, B i b * (∑ k : Fin r, S.v k b * S.v k j))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem right_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B) = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  show (∑ b : Fin n2, (A i b - B i b) * (∑ k : Fin r, S.v k b * S.v k j))
      = (∑ b : Fin n2, A i b * (∑ k : Fin r, S.v k b * S.v k j))
        - (∑ b : Fin n2, B i b * (∑ k : Fin r, S.v k b * S.v k j))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem left_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_left_right S X, left_left S (rightSingularProjection S X)]

theorem right_two {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_right_left S X, right_right S (leftSingularProjection S X)]

theorem left_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (tangentProjection S X) = leftSingularProjection S X := by
  unfold tangentProjection
  rw [left_sub, left_add, left_left, ← two_eq_left_right, left_two]
  abel

theorem right_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (tangentProjection S X) = rightSingularProjection S X := by
  unfold tangentProjection
  rw [right_sub, right_add, right_right, ← two_eq_right_left, right_two]
  abel

theorem two_tangent {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (tangentProjection S X) = twoSidedSingularProjection S X := by
  rw [two_eq_left_right S (tangentProjection S X), right_tangent, ← two_eq_left_right]

theorem tangent_idem {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  conv_lhs => rw [tangentProjection]
  rw [left_tangent, right_tangent, two_tangent]
  rfl

-- ===== self-adjoint + coordinate (copied from Thm file) =====

theorem matrixInner_coordinateMatrix {n1 n2 : Nat} (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; simp at h
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _; simp [ha]
  · intro h; simp at h

theorem tangentProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner X (tangentProjection S Y) = matrixInner (tangentProjection S X) Y := by
  unfold matrixInner tangentProjection
  simp only [Matrix.add_apply, Matrix.sub_apply]
  unfold leftSingularProjection rightSingularProjection twoSidedSingularProjection
  have h1 : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j) := by
    have hLn : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2,
            (∑ k, S.u k i * S.u k a) * (X i j * Y a j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    have hRn : (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j)
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2,
            (∑ k, S.u k i * S.u k a) * (X a j * Y i j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hLn, hRn, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    have hk : (∑ k, S.u k a * S.u k i) = (∑ k, S.u k i * S.u k a) := by
      apply Finset.sum_congr rfl; intro k _; ring
    rw [hk]
  have h2 : (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    apply Finset.sum_congr rfl; intro i _
    have hLn : (∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
        = ∑ j : Fin n2, ∑ b : Fin n2, (∑ l, S.v l b * S.v l j) * (X i j * Y i b) := by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    have hRn : (∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j)
        = ∑ j : Fin n2, ∑ b : Fin n2, (∑ l, S.v l b * S.v l j) * (X i b * Y i j) := by
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [hLn, hRn, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    have hk : (∑ l, S.v l j * S.v l b) = (∑ l, S.v l b * S.v l j) := by
      apply Finset.sum_congr rfl; intro l _; ring
    rw [hk]
  have h3 : (∑ i : Fin n1, ∑ j : Fin n2,
        X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))
      = (∑ i : Fin n1, ∑ j : Fin n2,
        (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    have hLn : (∑ i : Fin n1, ∑ j : Fin n2,
          X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))
        = ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X i j * Y a b) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    have hRn : (∑ i : Fin n1, ∑ j : Fin n2,
          (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j)
        = ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X a b * Y i j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
    rw [hLn, hRn]
    rw [show (∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X i j * Y a b))
        = ∑ q : (Fin n1 × Fin n2) × (Fin n1 × Fin n2),
            (∑ k, S.u k q.1.1 * S.u k q.2.1) * (∑ l, S.v l q.2.2 * S.v l q.1.2)
              * (X q.1.1 q.1.2 * Y q.2.1 q.2.2) from by
          simp_rw [Fintype.sum_prod_type]]
    rw [show (∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j) * (X a b * Y i j))
        = ∑ q : (Fin n1 × Fin n2) × (Fin n1 × Fin n2),
            (∑ k, S.u k q.1.1 * S.u k q.2.1) * (∑ l, S.v l q.2.2 * S.v l q.1.2)
              * (X q.2.1 q.2.2 * Y q.1.1 q.1.2) from by
          simp_rw [Fintype.sum_prod_type]]
    apply Finset.sum_nbij' (i := fun q => (q.2, q.1)) (j := fun q => (q.2, q.1))
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
    · intro p _
      have hku : (∑ k, S.u k p.2.1 * S.u k p.1.1) = (∑ k, S.u k p.1.1 * S.u k p.2.1) := by
        apply Finset.sum_congr rfl; intro k _; ring
      have hlv : (∑ l, S.v l p.1.2 * S.v l p.2.2) = (∑ l, S.v l p.2.2 * S.v l p.1.2) := by
        apply Finset.sum_congr rfl; intro l _; ring
      show _ = _
      simp only
      rw [hku, hlv]
  have hdistL : (∑ i : Fin n1, ∑ j : Fin n2,
        X i j * (((∑ a, (∑ k, S.u k i * S.u k a) * Y a j)
                  + (∑ b, Y i b * (∑ l, S.v l b * S.v l j))
                  - (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j)))))
      = (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ a, (∑ k, S.u k i * S.u k a) * Y a j))
        + (∑ i : Fin n1, ∑ j : Fin n2, X i j * (∑ b, Y i b * (∑ l, S.v l b * S.v l j)))
        - (∑ i : Fin n1, ∑ j : Fin n2,
            X i j * (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * Y a b * (∑ l, S.v l b * S.v l j))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hdistR : (∑ i : Fin n1, ∑ j : Fin n2,
        (((∑ a, (∑ k, S.u k i * S.u k a) * X a j)
                  + (∑ b, X i b * (∑ l, S.v l b * S.v l j))
                  - (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)))) * Y i j)
      = (∑ i : Fin n1, ∑ j : Fin n2, (∑ a, (∑ k, S.u k i * S.u k a) * X a j) * Y i j)
        + (∑ i : Fin n1, ∑ j : Fin n2, (∑ b, X i b * (∑ l, S.v l b * S.v l j)) * Y i j)
        - (∑ i : Fin n1, ∑ j : Fin n2,
            (∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j)) * Y i j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hdistL, hdistR, h1, h2, h3]

-- ===== norm helpers =====

theorem left_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    leftSingularProjection S (c • X) = c • leftSingularProjection S X := by
  funext i j
  show (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (c * X a j))
      = c * (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * X a j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring

theorem right_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    rightSingularProjection S (c • X) = c • rightSingularProjection S X := by
  funext i j
  show (∑ b : Fin n2, (c * X i b) * (∑ k : Fin r, S.v k b * S.v k j))
      = c * (∑ b : Fin n2, X i b * (∑ k : Fin r, S.v k b * S.v k j))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem two_smul' (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (c • X) = c • twoSidedSingularProjection S X := by
  funext i j
  show (∑ a : Fin n1, ∑ b : Fin n2,
        (∑ k : Fin r, S.u k i * S.u k a) * (c * X a b) * (∑ l : Fin r, S.v l b * S.v l j))
      = c * (∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k : Fin r, S.u k i * S.u k a) * X a b * (∑ l : Fin r, S.v l b * S.v l j))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring

theorem two_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j
  show (∑ a : Fin n1, ∑ b : Fin n2,
        (∑ k : Fin r, S.u k i * S.u k a) * (A a b + B a b) * (∑ l : Fin r, S.v l b * S.v l j))
      = (∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k : Fin r, S.u k i * S.u k a) * A a b * (∑ l : Fin r, S.v l b * S.v l j))
        + (∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k : Fin r, S.u k i * S.u k a) * B a b * (∑ l : Fin r, S.v l b * S.v l j))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; ring

theorem tangent_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    tangentProjection S (A + B) = tangentProjection S A + tangentProjection S B := by
  unfold tangentProjection
  rw [left_add, right_add, two_add]; abel

theorem tangent_smul (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    tangentProjection S (c • X) = c • tangentProjection S X := by
  unfold tangentProjection
  rw [left_smul, right_smul, two_smul']
  rw [smul_sub, smul_add]

theorem matrixInner_add_left (A B X : RealMatrix n1 n2) :
    matrixInner (A + B) X = matrixInner A X + matrixInner B X := by
  unfold matrixInner
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

/-- matrixInner additive in the right argument. -/

theorem matrixInner_add_right (X A B : RealMatrix n1 n2) :
    matrixInner X (A + B) = matrixInner X A + matrixInner X B := by
  unfold matrixInner
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

/-- matrixInner sub in left argument. -/

theorem matrixInner_sub_left (A B X : RealMatrix n1 n2) :
    matrixInner (A - B) X = matrixInner A X - matrixInner B X := by
  unfold matrixInner
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

theorem matrixInner_comm' (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- F1: nuclear norm is nonnegative. -/

theorem nuclearNorm_nonneg (X : RealMatrix n1 n2) : 0 ≤ nuclearNorm X := by
  unfold nuclearNorm
  apply Finset.sum_nonneg
  intro i _
  exact (Matrix.toEuclideanLin X).singularValues_nonneg i

/-- F2: nuclear norm is zero iff the matrix is zero. -/

theorem nuclearNorm_eq_zero_iff (X : RealMatrix n1 n2) :
    nuclearNorm X = 0 ↔ X = 0 := by
  unfold nuclearNorm
  constructor
  · intro h
    -- sum of nonneg = 0 ⇒ all terms zero ⇒ singularValues = 0 ⇒ map = 0 ⇒ X = 0
    have hzero : (Matrix.toEuclideanLin X).singularValues = 0 := by
      ext i
      have hsupp := (Matrix.toEuclideanLin X).singularValues.support
      by_contra hne
      have hpos : 0 < (Matrix.toEuclideanLin X).singularValues i := by
        rcases lt_or_eq_of_le ((Matrix.toEuclideanLin X).singularValues_nonneg i) with h' | h'
        · exact h'
        · exact absurd h'.symm hne
      have : (Matrix.toEuclideanLin X).singularValues i ≤
          (Matrix.toEuclideanLin X).singularValues.sum (fun _ x => x) := by
        rw [Finsupp.sum]
        by_cases hi : i ∈ (Matrix.toEuclideanLin X).singularValues.support
        · exact Finset.single_le_sum
            (fun j _ => (Matrix.toEuclideanLin X).singularValues_nonneg j) hi
        · simp only [Finsupp.mem_support_iff, not_not] at hi
          rw [hi] at hpos; exact absurd hpos (lt_irrefl 0)
      rw [h] at this
      exact absurd (lt_of_lt_of_le hpos this) (lt_irrefl 0)
    have : Matrix.toEuclideanLin X = 0 :=
      (LinearMap.singularValues_eq_zero_iff (T := Matrix.toEuclideanLin X)).mp hzero
    have hX : Matrix.toEuclideanLin X = Matrix.toEuclideanLin 0 := by rw [this]; simp
    exact (Matrix.toEuclideanLin).injective hX
  · intro h; subst h
    simp [LinearMap.singularValues_zero]

theorem left_rank1 (S : SVD M r) (k : Fin r) :
    leftSingularProjection S (Matrix.vecMulVec (S.u k) (S.v k))
      = Matrix.vecMulVec (S.u k) (S.v k) := by
  funext i j
  unfold leftSingularProjection
  simp only [Matrix.vecMulVec_apply]
  -- ∑ a (∑ l u_l i u_l a) (u_k a v_k j) = u_k i v_k j
  have e1 : (∑ a : Fin n1, (∑ l : Fin r, S.u l i * S.u l a) * (S.u k a * S.v k j))
      = ∑ l : Fin r, (S.u l i * S.v k j) * (∑ a : Fin n1, S.u l a * S.u k a) := by
    have step : (∑ a : Fin n1, (∑ l : Fin r, S.u l i * S.u l a) * (S.u k a * S.v k j))
        = ∑ a : Fin n1, ∑ l : Fin r, (S.u l i * S.v k j) * (S.u l a * S.u k a) := by
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
    rw [step, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]
  rw [e1]
  have e2 : (∑ l : Fin r, (S.u l i * S.v k j) * (∑ a : Fin n1, S.u l a * S.u k a))
      = ∑ l : Fin r, (if l = k then S.u l i * S.v k j else 0) := by
    apply Finset.sum_congr rfl; intro l _
    rw [S.u_orthonormal l k]; by_cases h : l = k <;> simp [h]
  rw [e2, Finset.sum_ite_eq']; simp

theorem right_rank1 (S : SVD M r) (k : Fin r) :
    rightSingularProjection S (Matrix.vecMulVec (S.u k) (S.v k))
      = Matrix.vecMulVec (S.u k) (S.v k) := by
  funext i j
  unfold rightSingularProjection
  simp only [Matrix.vecMulVec_apply]
  have e1 : (∑ b : Fin n2, (S.u k i * S.v k b) * (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n2, S.v k b * S.v l b) := by
    have step : (∑ b : Fin n2, (S.u k i * S.v k b) * (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ b : Fin n2, ∑ l : Fin r, (S.u k i * S.v l j) * (S.v k b * S.v l b) := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
    rw [step, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]
  rw [e1]
  have e2 : (∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n2, S.v k b * S.v l b))
      = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _
    rw [S.v_orthonormal k l]; by_cases h : k = l <;> simp [h]
  rw [e2, Finset.sum_ite_eq]; simp

theorem two_rank1 (S : SVD M r) (k : Fin r) :
    twoSidedSingularProjection S (Matrix.vecMulVec (S.u k) (S.v k))
      = Matrix.vecMulVec (S.u k) (S.v k) := by
  rw [two_eq_left_right, right_rank1, left_rank1]

theorem tangent_rank1 (S : SVD M r) (k : Fin r) :
    tangentProjection S (Matrix.vecMulVec (S.u k) (S.v k))
      = Matrix.vecMulVec (S.u k) (S.v k) := by
  unfold tangentProjection
  rw [left_rank1, right_rank1, two_rank1]; abel

/-- `tangentProjection` commutes with finite sums (it is linear). -/

theorem tangent_sum (S : SVD M r) {ι : Type*} (s : Finset ι)
    (f : ι → RealMatrix n1 n2) :
    tangentProjection S (∑ i ∈ s, f i) = ∑ i ∈ s, tangentProjection S (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      -- P_T 0 = 0
      have : tangentProjection S (0 : RealMatrix n1 n2) = 0 := by
        have := tangent_smul S 0 (0 : RealMatrix n1 n2)
        simpa using this
      exact this
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, tangent_add, ih]

theorem tangent_M (S : SVD M r) : tangentProjection S M = M := by
  have harg : tangentProjection S M
      = tangentProjection S (∑ k, S.sigma k • Matrix.vecMulVec (S.u k) (S.v k)) :=
    congrArg (tangentProjection S) S.decomp
  rw [harg, tangent_sum]
  have hsum : (∑ k, tangentProjection S (S.sigma k • Matrix.vecMulVec (S.u k) (S.v k)))
      = ∑ k, S.sigma k • Matrix.vecMulVec (S.u k) (S.v k) := by
    apply Finset.sum_congr rfl; intro k _
    rw [tangent_smul, tangent_rank1 S k]
  rw [hsum, ← S.decomp]

theorem left_signMatrix (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold leftSingularProjection signMatrix
  -- signMatrix a j = ∑ l, u l a * v l j
  have hsm : ∀ a : Fin n1, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) a j
      = ∑ l : Fin r, S.u l a * S.v l j := by
    intro a
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  -- LHS = ∑ a (∑ k u_k i u_k a)(∑ l u_l a v_l j)
  -- = ∑ k u_k i v_k j  (orthonormality of u)
  have hgoal : (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
        = ∑ a : Fin n1, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j) := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ k : Fin r, ∑ a : Fin n1, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n1, S.u k a * S.u l a) := by
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [e2]
    have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n1, S.u k a * S.u l a))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
      apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
      rw [S.u_orthonormal k l]
    rw [e3]
    apply Finset.sum_congr rfl; intro k _
    have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
        = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
      apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

theorem right_signMatrix (S : SVD M r) :
    rightSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold rightSingularProjection signMatrix
  have hsm : ∀ b : Fin n2, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) i b
      = ∑ l : Fin r, S.u l i * S.v l b := by
    intro b
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _; rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  have hgoal : (∑ b : Fin n2, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ b : Fin n2, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
        = ∑ b : Fin n2, ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j) := by
      apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ l : Fin r, ∑ b : Fin n2, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n2, S.v l b * S.v k b) := by
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e2]
    have e3 : (∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n2, S.v l b * S.v k b))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (if l = k then 1 else 0) := by
      apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _
      rw [S.v_orthonormal l k]
    rw [e3]
    apply Finset.sum_congr rfl; intro l _
    have : (∑ k : Fin r, S.u l i * S.v k j * (if l = k then 1 else 0))
        = ∑ k : Fin r, (if l = k then S.u l i * S.v k j else 0) := by
      apply Finset.sum_congr rfl; intro k _; by_cases h : l = k <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

theorem two_signMatrix (S : SVD M r) :
    twoSidedSingularProjection S (signMatrix S) = signMatrix S := by
  -- two = left of (right of signMatrix) = left of signMatrix = signMatrix
  rw [two_eq_left_right, right_signMatrix, left_signMatrix]

end MatrixCompletion

open MatrixCompletion

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    nuclearNorm M +
        matrixInner (signMatrix S) (tangentProjection S H) +
          nuclearNorm (normalProjection S H) ≤
      nuclearNorm (M + H) := by
  set E := signMatrix S with hE
  obtain ⟨W, hWT, hEWnorm, hWNH⟩ := normal_space_dual_achiever_with_sign_contraction S H
  have hC1 := matrix_trace_duality_inequality (E + W) (M + H)
  have hMHnn : 0 ≤ nuclearNorm (M + H) := by
    unfold nuclearNorm
    apply Finset.sum_nonneg
    intro i _
    exact (Matrix.toEuclideanLin (M + H)).singularValues_nonneg i
  have hub : matrixInner (E + W) (M + H) ≤ nuclearNorm (M + H) := by
    calc matrixInner (E + W) (M + H)
        ≤ spectralNorm (E + W) * nuclearNorm (M + H) := hC1
      _ ≤ 1 * nuclearNorm (M + H) := by
            apply mul_le_mul_of_nonneg_right hEWnorm hMHnn
      _ = nuclearNorm (M + H) := one_mul _
  have hexp : matrixInner (E + W) (M + H)
      = matrixInner E M + matrixInner E H + matrixInner W M + matrixInner W H := by
    rw [matrixInner_add_left, matrixInner_add_right, matrixInner_add_right]; ring
  have hEM : matrixInner E M = nuclearNorm M := by
    rw [hE]; exact sign_matrix_inner_eq_nuclear_norm S
  have hEH : matrixInner E H = matrixInner E (tangentProjection S H) := by
    have hEt : tangentProjection S E = E := by
      rw [hE]; unfold tangentProjection; rw [left_signMatrix, right_signMatrix, two_signMatrix]; abel
    calc matrixInner E H = matrixInner (tangentProjection S E) H := by rw [hEt]
      _ = matrixInner E (tangentProjection S H) := (tangentProjection_selfAdjoint S E H).symm
  have hPTW : tangentProjection S W = 0 := by
    have hdef : normalProjection S W = W - tangentProjection S W := rfl
    rw [hdef] at hWT
    exact sub_eq_self.mp hWT
  have hWM : matrixInner W M = 0 := by
    have hPTM : tangentProjection S M = M := tangent_M S
    calc matrixInner W M = matrixInner W (tangentProjection S M) := by rw [hPTM]
      _ = matrixInner (tangentProjection S W) M := (tangentProjection_selfAdjoint S W M)
      _ = matrixInner (0 : RealMatrix n₁ n₂) M := by rw [hPTW]
      _ = 0 := by unfold matrixInner; simp
  have hWH : matrixInner W H = nuclearNorm (normalProjection S H) := by
    have hsplit : H = tangentProjection S H + normalProjection S H := by
      have : normalProjection S H = H - tangentProjection S H := rfl
      rw [this]; abel
    have hWPTH : matrixInner W (tangentProjection S H) = 0 := by
      calc matrixInner W (tangentProjection S H)
          = matrixInner (tangentProjection S W) H := (tangentProjection_selfAdjoint S W H)
        _ = matrixInner (0 : RealMatrix n₁ n₂) H := by rw [hPTW]
        _ = 0 := by unfold matrixInner; simp
    calc matrixInner W H
        = matrixInner W (tangentProjection S H + normalProjection S H) := by rw [← hsplit]
      _ = matrixInner W (tangentProjection S H) + matrixInner W (normalProjection S H) :=
            matrixInner_add_right W _ _
      _ = 0 + matrixInner W (normalProjection S H) := by rw [hWPTH]
      _ = matrixInner W (normalProjection S H) := by rw [zero_add]
      _ = nuclearNorm (normalProjection S H) := hWNH
  rw [hexp, hEM, hEH, hWM, hWH] at hub
  linarith [hub]

end Imported6
def nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm := @Imported6.solution

#print axioms nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm

open MeasureTheory MatrixCompletion
open scoped BigOperators
namespace KLTWork

lemma inner_comm {m k : ℕ} (A B : RealMatrix m k) : matrixInner A B = matrixInner B A := by
  simp [matrixInner, mul_comm]
lemma inner_sub_left {m k : ℕ} (A B D : RealMatrix m k) :
    matrixInner (A - B) D = matrixInner A D - matrixInner B D := by
  simp [matrixInner, sub_mul, Finset.sum_sub_distrib]
lemma inner_sub_right {m k : ℕ} (A B D : RealMatrix m k) :
    matrixInner A (B - D) = matrixInner A B - matrixInner A D := by
  simp [matrixInner, mul_sub, Finset.sum_sub_distrib]
lemma inner_smul_left {m k : ℕ} (c : ℝ) (A B : RealMatrix m k) :
    matrixInner (c • A) B = c * matrixInner A B := by
  simp [matrixInner, Finset.mul_sum, mul_assoc]
lemma inner_sum_left {m k : ℕ} {ι : Type*} [Fintype ι] (A : ι → RealMatrix m k) (B : RealMatrix m k) :
    matrixInner (∑ i, A i) B = ∑ i, matrixInner (A i) B := by
  simp only [matrixInner, Matrix.sum_apply, Finset.sum_mul]
  calc
    (∑ a, ∑ b, ∑ i, A i a b * B a b) = ∑ a, ∑ i, ∑ b, A i a b * B a b := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

open KLTNuclear.Oracle
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n m k : ℕ}
  {X : Fin n → Ω → RealMatrix m k} {Y : Fin n → Ω → ℝ}
lemma inner_memLp (hreg : SampleRegularity P X Y) (A : RealMatrix m k) (i : Fin n) :
    MemLp (fun ω => matrixInner A (X i ω)) 2 P := by
  exact memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun l _ =>
    (hreg.2.2.1 i j l).const_mul (A j l)
lemma inner_product_integrable (hreg : SampleRegularity P X Y) (A B : RealMatrix m k) (i : Fin n) :
    Integrable (fun ω => matrixInner A (X i ω) * matrixInner B (X i ω)) P :=
  (inner_memLp hreg A i).integrable_mul (inner_memLp hreg B i)

lemma centered_entry [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (i : Fin n) (j : Fin m) (l : Fin k) :
    expectYX P X Y i j l = ∫ ω, matrixInner A₀ (X i ω) * X i ω j l ∂P := by
  let g : Ω → Fin m → Fin k → ℝ := fun ω j l => X i ω j l
  have hx : Measurable g := measurable_pi_lambda _ fun a =>
    measurable_pi_lambda _ fun b => hreg.1 i a b
  have hs : MeasurableSpace.comap g inferInstance ≤ ‹MeasurableSpace Ω› := hx.comap_le
  have hx_s : @Measurable Ω (Fin m → Fin k → ℝ)
      (MeasurableSpace.comap g inferInstance) _ g := measurable_iff_comap_le.mpr le_rfl
  have he : @Measurable Ω ℝ (MeasurableSpace.comap g inferInstance) _ (fun ω => X i ω j l) :=
    (measurable_pi_apply l).comp ((measurable_pi_apply j).comp hx_s)
  have hc := condExp_mul_of_stronglyMeasurable_right (μ := P)
    he.stronglyMeasurable (hreg.2.2.2.2 i j l) (hreg.2.2.2.1 i)
  unfold expectYX
  calc
    _ = ∫ ω, P[(fun ω => Y i ω * X i ω j l) | MeasurableSpace.comap g inferInstance] ω ∂P :=
      (integral_condExp hs).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hc, hmodel i] with ω h1 h2
      change P[Y i | MeasurableSpace.comap g inferInstance] ω = matrixInner A₀ (X i ω) at h2
      change P[(fun ω => Y i ω * X i ω j l) | MeasurableSpace.comap g inferInstance] ω =
        P[Y i | MeasurableSpace.comap g inferInstance] ω * X i ω j l at h1
      rw [h2] at h1
      exact h1

lemma l2_square_sub (hreg : SampleRegularity P X Y) (A B : RealMatrix m k) :
    l2NormSq P X (A - B) = l2NormSq P X A - 2 * l2Inner P X A B + l2NormSq P X B := by
  unfold l2NormSq l2Inner
  have hi (i : Fin n) :
      (∫ ω, matrixInner (A-B) (X i ω) * matrixInner (A-B) (X i ω) ∂P) =
      (∫ ω, matrixInner A (X i ω) * matrixInner A (X i ω) ∂P) -
        2 * (∫ ω, matrixInner A (X i ω) * matrixInner B (X i ω) ∂P) +
        (∫ ω, matrixInner B (X i ω) * matrixInner B (X i ω) ∂P) := by
    simp_rw [inner_sub_left]
    have he (ω : Ω) : (matrixInner A (X i ω) - matrixInner B (X i ω)) *
        (matrixInner A (X i ω) - matrixInner B (X i ω)) =
        matrixInner A (X i ω) * matrixInner A (X i ω) -
          2 * (matrixInner A (X i ω) * matrixInner B (X i ω)) +
          matrixInner B (X i ω) * matrixInner B (X i ω) := by ring
    simp_rw [he]
    have hAA := inner_product_integrable hreg A A i
    have hAB := (inner_product_integrable hreg A B i).const_mul 2
    have hBB := inner_product_integrable hreg B B i
    have hsum := integral_add (hAA.sub hAB) hBB
    have hsub := integral_sub hAA hAB
    simp only [Pi.sub_apply] at hsum
    rw [hsum, hsub, integral_const_mul]

  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
lemma integral_inner (F : Ω → RealMatrix m k)
    (hF : ∀ j l, Integrable (fun ω => F ω j l) P) (B : RealMatrix m k) :
    matrixInner (fun j l => ∫ ω, F ω j l ∂P) B = ∫ ω, matrixInner (F ω) B ∂P := by
  unfold matrixInner
  simp_rw [← integral_mul_const]
  symm
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun l _ =>
    (hF j l).mul_const (B j l))]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_finsetSum _ (fun l _ => (hF j l).mul_const (B j l))

lemma centered_inner [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (i : Fin n) (B : RealMatrix m k) :
    matrixInner (expectYX P X Y i) B =
      ∫ ω, matrixInner A₀ (X i ω) * matrixInner B (X i ω) ∂P := by
  have he : expectYX P X Y i = fun j l =>
      ∫ ω, matrixInner A₀ (X i ω) * X i ω j l ∂P := by
    funext j l
    exact centered_entry hreg A₀ hmodel i j l
  rw [he]
  have hi (j : Fin m) (l : Fin k) :
      Integrable (fun ω => matrixInner A₀ (X i ω) * X i ω j l) P :=
    (inner_memLp hreg A₀ i).integrable_mul (hreg.2.2.1 i j l)
  calc
    _ = ∫ ω, matrixInner (matrixInner A₀ (X i ω) • X i ω) B ∂P := by
      simpa only [Matrix.smul_apply, smul_eq_mul] using
        integral_inner (fun ω => matrixInner A₀ (X i ω) • X i ω) hi B
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [inner_smul_left, inner_comm (X i ω) B]

lemma empirical_pairing [IsProbabilityMeasure P] (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m k) (hmodel : TraceRegressionModel P X Y A₀)
    (ω : Ω) (B : RealMatrix m k) :
    matrixInner (empiricalYX X Y ω) B =
      2 * matrixInner (noiseMatrix P X Y ω) B + 2 * l2Inner P X A₀ B := by
  simp only [empiricalYX, noiseMatrix, inner_smul_left, inner_sum_left,
    inner_sub_left, centered_inner hreg A₀ hmodel, l2Inner, Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv, one_mul]
  ring

lemma l2_comm (A B : RealMatrix m k) : l2Inner P X A B = l2Inner P X B A := by
  unfold l2Inner
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext ω
  exact mul_comm _ _
end KLTWork

open MeasureTheory MatrixCompletion KLTNuclear.Oracle KLTWork
namespace ConvexGap
lemma strong_gap_from_chords (a b q : ℝ) (hq : 0 ≤ q)
    (h : ∀ t : ℝ, 0 < t → t < 1 → b ≤ (1-t)*b+t*a-t*(1-t)*q) : b+q ≤ a := by
  by_contra hh
  have hd : 0 < b+q-a := by linarith
  let t := min (1/2 : ℝ) ((b+q-a)/(2*(q+1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hd (by positivity))
  have ht1 : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have htq : t * (2*(q+1)) ≤ b+q-a :=
    (le_div_iff₀ (by positivity : 0 < 2*(q+1))).mp (min_le_right _ _)
  have hh' : 0 ≤ t*(a-b-(1-t)*q) := by nlinarith [h t ht ht1]
  have hh'' := (mul_nonneg_iff_of_pos_left ht).mp hh'
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n m k : ℕ}
  {X : Fin n → Ω → RealMatrix m k} {Y : Fin n → Ω → ℝ}
lemma l2_nonneg (A : RealMatrix m k) : 0 ≤ l2NormSq P X A := by
  unfold l2NormSq l2Inner
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i hi
  exact integral_nonneg fun ω => mul_self_nonneg _

lemma inner_chord (A B D : RealMatrix m k) (t : ℝ) :
    matrixInner ((1-t)•B+t•A) D = (1-t)*matrixInner B D+t*matrixInner A D := by
  simp [matrixInner, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma square_chord (hreg : SampleRegularity P X Y) (A B : RealMatrix m k) (t : ℝ) :
    l2NormSq P X ((1-t)•B+t•A) =
      (1-t)*l2NormSq P X B+t*l2NormSq P X A-t*(1-t)*l2NormSq P X (B-A) := by
  unfold l2NormSq l2Inner
  have hi (i : Fin n) :
      (∫ ω, matrixInner ((1-t)•B+t•A) (X i ω)*matrixInner ((1-t)•B+t•A) (X i ω) ∂P) =
      (1-t)*(∫ ω, matrixInner B (X i ω)*matrixInner B (X i ω) ∂P) +
      t*(∫ ω, matrixInner A (X i ω)*matrixInner A (X i ω) ∂P) -
      t*(1-t)*(∫ ω, matrixInner (B-A) (X i ω)*matrixInner (B-A) (X i ω) ∂P) := by
    have he (ω : Ω) :
        matrixInner ((1-t)•B+t•A) (X i ω)*matrixInner ((1-t)•B+t•A) (X i ω) =
        (1-t)*(matrixInner B (X i ω)*matrixInner B (X i ω)) +
        t*(matrixInner A (X i ω)*matrixInner A (X i ω)) -
        (t*(1-t))*(matrixInner (B-A) (X i ω)*matrixInner (B-A) (X i ω)) := by
      rw [inner_chord,inner_sub_left];ring
    simp_rw [he]
    have hb : Integrable (fun ω => (1-t)*(matrixInner B (X i ω)*matrixInner B (X i ω))) P :=
      (inner_product_integrable hreg B B i).const_mul (1-t)
    have ha : Integrable (fun ω => t*(matrixInner A (X i ω)*matrixInner A (X i ω))) P :=
      (inner_product_integrable hreg A A i).const_mul t
    have hd : Integrable (fun ω => (t*(1-t))*(matrixInner (B-A) (X i ω)*matrixInner (B-A) (X i ω))) P :=
      (inner_product_integrable hreg (B-A) (B-A) i).const_mul (t*(1-t))
    calc _ = (∫ ω, (1-t)*(matrixInner B (X i ω)*matrixInner B (X i ω)) +
        t*(matrixInner A (X i ω)*matrixInner A (X i ω)) ∂P) -
        (∫ ω, (t*(1-t))*(matrixInner (B-A) (X i ω)*matrixInner (B-A) (X i ω)) ∂P) :=
          integral_sub (hb.add ha) hd
      _ = _ := by rw [integral_add hb ha]; simp only [integral_const_mul]
  simp_rw [hi,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  ring
end ConvexGap
#print axioms ConvexGap.square_chord

open _root_.MatrixCompletion KLTWork ConvexGap
open scoped BigOperators
namespace NormConvex
lemma nonneg {m k : ℕ} (A : RealMatrix m k) : 0 ≤ nuclearNorm A := by
  unfold nuclearNorm
  exact Finset.sum_nonneg fun i _ => (Matrix.toEuclideanLin A).singularValues_nonneg i
lemma bound {m k : ℕ} (Z A : RealMatrix m k) (hZ : spectralNorm Z ≤ 1) :
    matrixInner Z A ≤ nuclearNorm A :=
  (matrix_trace_duality_inequality Z A).trans (by simpa using mul_le_mul_of_nonneg_right hZ (nonneg A))
lemma chord {m k : ℕ} (A B : RealMatrix m k) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    nuclearNorm ((1-t)•B+t•A) ≤ (1-t)*nuclearNorm B+t*nuclearNorm A := by
  obtain ⟨Z,hZ,hpair⟩ := nuclear_norm_dual_achiever_contraction ((1-t)•B+t•A)
  rw [← hpair, inner_comm, inner_chord, inner_comm B, inner_comm A]
  exact add_le_add (mul_le_mul_of_nonneg_left (bound Z B hZ) (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left (bound Z A hZ) ht)
end NormConvex
#print axioms NormConvex.chord

open MeasureTheory MatrixCompletion KLTNuclear.Oracle KLTWork ConvexGap
namespace EstimatorGap
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n m k : ℕ}
  {X : Fin n → Ω → RealMatrix m k} {Y : Fin n → Ω → ℝ}
lemma strong (hreg : SampleRegularity P X Y) {𝔸 : Set (RealMatrix m k)}
    (hconv : Convex ℝ 𝔸) {lam : ℝ} (hlam : 0 ≤ lam) (ω : Ω)
    {B : RealMatrix m k} (hB : IsEstimator P X Y lam ω 𝔸 B)
    {A : RealMatrix m k} (hA : A ∈ 𝔸) :
    Ln P X Y lam ω B + l2NormSq P X (B-A) ≤ Ln P X Y lam ω A := by
  apply strong_gap_from_chords _ _ _ (l2_nonneg _)
  intro t ht ht1
  have hc : (1-t)•B+t•A ∈ 𝔸 := hconv hB.1 hA (by linarith) ht.le (by ring)
  have hmin := hB.2 _ hc
  have hnorm := mul_le_mul_of_nonneg_left (NormConvex.chord A B t ht.le ht1.le) hlam
  have hquad := square_chord hreg A B t
  have hlin : matrixInner (empiricalYX X Y ω) ((1-t)•B+t•A) =
      (1-t)*matrixInner (empiricalYX X Y ω) B + t*matrixInner (empiricalYX X Y ω) A := by
    rw [inner_comm, inner_chord, inner_comm B, inner_comm A]
  unfold Ln at *
  rw [hquad,hlin] at hmin
  nlinarith
end EstimatorGap
#print axioms EstimatorGap.strong

namespace PriorTwo
open MatrixCompletion
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000

/-
Self-adjointness (symmetry under the Frobenius inner product) of the tangent
projection `P_T = leftSingularProjection + rightSingularProjection -
twoSidedSingularProjection`:

    ⟨P_T A, B⟩_F = ⟨A, P_T B⟩_F  for all real matrices A, B.

This is the basic orthogonal-projection property the Candès–Recht tangent-space
analysis (arXiv:0805.4471 §3–§4) uses repeatedly: it underlies the
resolution-of-identity `X = ∑_{ab} ⟨P_T(e_ab), X⟩ P_T(e_ab)` for `X ∈ T`, and
the rank-one frame representation of the sampling fluctuation `P_T P_Ω P_T - p P_T`
used in the Rudelson selection lemma (Rudelson 1999, J. Funct. Anal. 164, Thm 1).

Proof: each of the three constituent projections is self-adjoint because its
kernel is symmetric (`∑_k u_k i u_k a` and `∑_l v_l b v_l j`).  The two-sided
projection equals `left ∘ right = right ∘ left`, so its self-adjointness follows
from composing the two self-adjoint factors.  matrixInner is bilinear, so
self-adjointness distributes over the `+`/`-`.  Uses only the SVD orthonormality
data implicitly (in fact only symmetry of the kernels, not orthonormality).
-/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    matrixInner (twoSidedSingularProjection S A) B
      = matrixInner A (twoSidedSingularProjection S B) := by
  -- inline helpers ----------------------------------------------------------
  -- kernel symmetry
  have PuK_symm_inline : ∀ (i a : Fin n1),
      (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    intro i a; apply Finset.sum_congr rfl; intro k _; ring
  have PvK_symm_inline : ∀ (b j : Fin n2),
      (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    intro b j; apply Finset.sum_congr rfl; intro l _; ring
  -- matrixInner bilinearity
  have matrixInner_add_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P + Q) C = matrixInner P C + matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [add_mul]
  have matrixInner_sub_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P - Q) C = matrixInner P C - matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [sub_mul]
  have matrixInner_add_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q + C) = matrixInner P Q + matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_add]
  have matrixInner_sub_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q - C) = matrixInner P Q - matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_sub]
  -- left self-adjoint
  have left_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (leftSingularProjection S P) Q
        = matrixInner P (leftSingularProjection S Q) := by
    intro P Q; unfold matrixInner leftSingularProjection
    rw [show (∑ i, ∑ j, (∑ a, (∑ k, S.u k i * S.u k a) * P a j) * Q i j)
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * P a j * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ a, (∑ k, S.u k i * S.u k a) * Q a j))
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * Q a j * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _; ring]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    rw [PuK_symm_inline i a]; ring
  -- right self-adjoint
  have right_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (rightSingularProjection S P) Q
        = matrixInner P (rightSingularProjection S Q) := by
    intro P Q; unfold matrixInner rightSingularProjection
    rw [show (∑ i, ∑ j, (∑ b, P i b * (∑ l, S.v l b * S.v l j)) * Q i j)
          = ∑ i, ∑ j, ∑ b, P i b * (∑ l, S.v l b * S.v l j) * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ b, Q i b * (∑ l, S.v l b * S.v l j)))
          = ∑ i, ∑ j, ∑ b, Q i b * (∑ l, S.v l b * S.v l j) * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
    apply Finset.sum_congr rfl; intro i _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    rw [PvK_symm_inline b j]; ring
  -- twoSided = left ∘ right and = right ∘ left
  have ts_lr : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = leftSingularProjection S (rightSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ a, (∑ k, S.u k i * S.u k a) * (∑ b, X a b * (∑ l, S.v l b * S.v l j)))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
  have ts_rl : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = rightSingularProjection S (leftSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
                = ∑ b, ∑ a, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
                apply Finset.sum_congr rfl; intro b _
                rw [Finset.sum_mul]]
          rw [Finset.sum_comm]]
  -- twoSided self-adjoint via composition
  have ts_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (twoSidedSingularProjection S P) Q
        = matrixInner P (twoSidedSingularProjection S Q) := by
    intro P Q
    rw [ts_lr, left_sa, right_sa, ← ts_rl]
  exact ts_sa A B

end PriorTwo
#print axioms PriorTwo.solution

open _root_.MatrixCompletion KLTWork
namespace Penalty
open Imported6.MatrixCompletion
lemma normal_sub_self {m k r : ℕ} {A : RealMatrix m k} (S : SVD A r) (B : RealMatrix m k) :
    normalProjection S (B-A) = normalProjection S B := by
  have hs : tangentProjection S (B-A) = tangentProjection S B - tangentProjection S A := by
    rw [sub_eq_add_neg, tangent_add, show -A = (-1:ℝ) • A by simp, tangent_smul]
    simp [sub_eq_add_neg]
  unfold normalProjection
  rw [hs,tangent_M S]
  abel
lemma lower {m k r : ℕ} {A : RealMatrix m k} (S : SVD A r) (B : RealMatrix m k) :
    nuclearNorm A+nuclearNorm (normalProjection S B)-
      nuclearNorm (twoSidedSingularProjection S (B-A)) ≤ nuclearNorm B := by
  have hd := nuclear_norm_lower_bound_by_tangent_sign_and_normal_norm S (B-A)
  rw [normal_sub_self, add_sub_cancel] at hd
  have hp : matrixInner (signMatrix S) (tangentProjection S (B-A)) =
      matrixInner (signMatrix S) (twoSidedSingularProjection S (B-A)) := by
    calc
      matrixInner (signMatrix S) (tangentProjection S (B-A)) =
          matrixInner (twoSidedSingularProjection S (signMatrix S))
            (tangentProjection S (B-A)) := by rw [two_signMatrix]
      _ = matrixInner (signMatrix S) (twoSidedSingularProjection S (tangentProjection S (B-A))) :=
        PriorTwo.solution S _ _
      _ = _ := by rw [two_tangent]
  have hn : spectralNorm (-(signMatrix S)) ≤ 1 := by
    simpa [MatrixCompletion.spectralNorm] using sign_matrix_spectral_norm_le_one S
  have hb := NormConvex.bound (-(signMatrix S)) (twoSidedSingularProjection S (B-A)) hn
  have he : matrixInner (-(signMatrix S)) (twoSidedSingularProjection S (B-A)) =
      -matrixInner (signMatrix S) (twoSidedSingularProjection S (B-A)) := by
    simp [matrixInner, Finset.sum_neg_distrib]
  rw [he] at hb
  rw [hp] at hd
  linarith
end Penalty
#print axioms Penalty.lower

open MeasureTheory MatrixCompletion KLTNuclear.Oracle KLTWork

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (h𝔸 : Convex ℝ 𝔸) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat) :
    ∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
      l2NormSq P X (Ahat - A₀) + l2NormSq P X (Ahat - A) + lam * nuclearNorm (normalProjection S Ahat) ≤
        l2NormSq P X (A - A₀) + lam * nuclearNorm (twoSidedSingularProjection S (Ahat - A)) +
          2 * matrixInner (noiseMatrix P X Y ω) (Ahat - A) := by
  intro A hA r S
  have hg := EstimatorGap.strong hreg h𝔸 hlam.le ω hAhat hA
  have hp := mul_le_mul_of_nonneg_left (Penalty.lower S Ahat) hlam.le
  unfold Ln at hg
  rw [empirical_pairing hreg A₀ hmodel, empirical_pairing hreg A₀ hmodel] at hg
  rw [l2_square_sub hreg Ahat A₀, l2_square_sub hreg A A₀,
    inner_sub_right, l2_comm Ahat A₀, l2_comm A A₀]
  nlinarith
#print axioms solution

end Eq11

namespace OldSharp
namespace PriorIdem

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

namespace MatrixCompletion

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- The column singular kernel collapses: `∑_a K_U(i,a) K_U(a,a') = K_U(i,a')`,
    where `K_U(i,a) = ∑_k u_k i * u_k a`. This is `P_U² = P_U` at kernel level. -/
private lemma KU_collapse (S : SVD M r) (i a' : Fin n1) :
    (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
        (∑ k' : Fin r, S.u k' a * S.u k' a'))
      = ∑ k : Fin r, S.u k i * S.u k a' := by
  calc ∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')
      = ∑ a : Fin n1, ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k a) * (S.u k' a * S.u k' a') := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_mul_sum]
    _ = ∑ k : Fin r, ∑ k' : Fin r, ∑ a : Fin n1,
          (S.u k i * S.u k a) * (S.u k' a * S.u k' a') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k' a') * (∑ a : Fin n1, S.u k a * S.u k' a) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k' a') * (if k = k' then 1 else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [S.u_orthonormal k k']
    _ = ∑ k : Fin r, S.u k i * S.u k a' := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (∑ k' : Fin r, S.u k i * S.u k' a' * if k = k' then 1 else 0)
            = ∑ k' : Fin r, if k = k' then S.u k i * S.u k' a' else 0 from by
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          by_cases h : k = k' <;> simp [h]]
        rw [Finset.sum_ite_eq Finset.univ k (fun k' => S.u k i * S.u k' a')]
        simp

/-- The row singular kernel collapses: `∑_b K_V(b',b) K_V(b,j) = K_V(b',j)`. -/
private lemma KV_collapse (S : SVD M r) (b' j : Fin n2) :
    (∑ b : Fin n2, (∑ k : Fin r, S.v k b' * S.v k b) *
        (∑ k' : Fin r, S.v k' b * S.v k' j))
      = ∑ k : Fin r, S.v k b' * S.v k j := by
  calc ∑ b : Fin n2, (∑ k : Fin r, S.v k b' * S.v k b) *
          (∑ k' : Fin r, S.v k' b * S.v k' j)
      = ∑ b : Fin n2, ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k b) * (S.v k' b * S.v k' j) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.sum_mul_sum]
    _ = ∑ k : Fin r, ∑ k' : Fin r, ∑ b : Fin n2,
          (S.v k b' * S.v k b) * (S.v k' b * S.v k' j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k' j) * (∑ b : Fin n2, S.v k b * S.v k' b) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k' j) * (if k = k' then 1 else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [S.v_orthonormal k k']
    _ = ∑ k : Fin r, S.v k b' * S.v k j := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (∑ k' : Fin r, S.v k b' * S.v k' j * if k = k' then 1 else 0)
            = ∑ k' : Fin r, if k = k' then S.v k b' * S.v k' j else 0 from by
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          by_cases h : k = k' <;> simp [h]]
        rw [Finset.sum_ite_eq Finset.univ k (fun k' => S.v k b' * S.v k' j)]
        simp

/-- `P_U` is idempotent. -/
private lemma left_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X)
      = leftSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection]
  rw [show (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
        ∑ a' : Fin n1, (∑ k' : Fin r, S.u k' a * S.u k' a') * X a' j)
      = ∑ a : Fin n1, ∑ a' : Fin n1,
          ((∑ k : Fin r, S.u k i * S.u k a) *
            (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    ring]
  rw [Finset.sum_comm]
  rw [show (∑ a' : Fin n1, ∑ a : Fin n1,
        ((∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j)
      = ∑ a' : Fin n1, (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j from by
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [KU_collapse S i a']

/-- `P_V` is idempotent. -/
private lemma right_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X)
      = rightSingularProjection S X := by
  funext i j
  simp only [rightSingularProjection]
  rw [show (∑ b : Fin n2, (∑ b' : Fin n2, X i b' * (∑ k : Fin r, S.v k b' * S.v k b)) *
        (∑ k' : Fin r, S.v k' b * S.v k' j))
      = ∑ b' : Fin n2, X i b' * (∑ b : Fin n2,
          (∑ k : Fin r, S.v k b' * S.v k b) * (∑ k' : Fin r, S.v k' b * S.v k' j))
        from by
    rw [show (∑ b : Fin n2, (∑ b' : Fin n2, X i b' * (∑ k : Fin r, S.v k b' * S.v k b)) *
          (∑ k' : Fin r, S.v k' b * S.v k' j))
        = ∑ b : Fin n2, ∑ b' : Fin n2,
            X i b' * ((∑ k : Fin r, S.v k b' * S.v k b) *
              (∑ k' : Fin r, S.v k' b * S.v k' j)) from by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      ring]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  rw [KV_collapse S b' j]

/-- `P_U` and `P_V` commute, and the composite is `twoSided`:
    `P_U (P_V X) = twoSided X`. -/
private lemma left_right_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection]
  -- LHS: ∑ a, KU(i,a) * (∑ b, X a b * KV(b,j))
  -- RHS: ∑ a, ∑ b, KU(i,a) * X a b * KV(b,j)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `P_V (P_U X) = twoSided X` (the other composition order). -/
private lemma right_left_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection]
  -- LHS: ∑ b, (∑ a, KU(i,a) * X a b) * KV(b,j)
  -- RHS: ∑ a, ∑ b, KU(i,a) * X a b * KV(b,j)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

/-- `P_U (twoSided X) = twoSided X`: applying `P_U` again is idempotent. -/
private lemma left_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, twoSidedSingularProjection]
  -- LHS: ∑ a', KU(i,a') * (∑ a ∑ b, KU(a',a) X a b KV(b,j))
  -- RHS: ∑ a ∑ b, KU(i,a) X a b KV(b,j)
  -- collapse over a': coefficient of (X a b * KV(b,j)) is ∑ a' KU(i,a') KU(a',a) = KU(i,a)
  rw [show (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
        ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k' : Fin r, S.u k' a' * S.u k' a) * X a b *
            (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
            (∑ k' : Fin r, S.u k' a' * S.u k' a)) *
            (X a b * (∑ l : Fin r, S.v l b * S.v l j)) from by
    -- First: distribute KU(i,a') over the inner ∑a ∑b and turn LHS into a
    -- fully expanded triple sum over a', a, b.
    rw [show (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
          ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k' : Fin r, S.u k' a' * S.u k' a) * X a b *
              (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ a' : Fin n1, ∑ a : Fin n1, ∑ b : Fin n2,
            ((∑ k : Fin r, S.u k i * S.u k a') *
              (∑ k' : Fin r, S.u k' a' * S.u k' a)) *
              (X a b * (∑ l : Fin r, S.v l b * S.v l j)) from by
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring]
    -- Move ∑ a' innermost: swap a' with a, then a' with b.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [KU_collapse S i a]
  ring

/-- `P_V (twoSided X) = twoSided X`. -/
private lemma right_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [rightSingularProjection, twoSidedSingularProjection]
  -- LHS: ∑ b', (∑ a ∑ b, KU(i,a) X a b KV(b,b')) * KV(b',j)
  -- RHS: ∑ a ∑ b, KU(i,a) X a b KV(b,j)
  rw [show (∑ b' : Fin n2, (∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k : Fin r, S.u k i * S.u k a) * X a b *
            (∑ l : Fin r, S.v l b * S.v l b')) *
        (∑ l' : Fin r, S.v l' b' * S.v l' j))
      = ∑ a : Fin n1, ∑ b : Fin n2,
          ((∑ k : Fin r, S.u k i * S.u k a) * X a b) *
            (∑ b' : Fin n2, (∑ l : Fin r, S.v l b * S.v l b') *
              (∑ l' : Fin r, S.v l' b' * S.v l' j)) from by
    -- First: distribute KV(b',j) over the inner ∑a ∑b and expand to a triple sum.
    rw [show (∑ b' : Fin n2, (∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k : Fin r, S.u k i * S.u k a) * X a b *
              (∑ l : Fin r, S.v l b * S.v l b')) *
          (∑ l' : Fin r, S.v l' b' * S.v l' j))
        = ∑ b' : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            ((∑ k : Fin r, S.u k i * S.u k a) * X a b) *
              ((∑ l : Fin r, S.v l b * S.v l b') *
                (∑ l' : Fin r, S.v l' b' * S.v l' j)) from by
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring]
    -- Move ∑ b' innermost: swap b' with a, then b' with b.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [KV_collapse S b j]

/-- `twoSided = P_U ∘ P_V`. -/
private lemma two_eq_left_right (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X
      = leftSingularProjection S (rightSingularProjection S X) :=
  (left_right_eq_two S X).symm

/-- `twoSided (P_U X) = twoSided X`. -/
private lemma two_left_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_left_eq_two, left_two_eq_two]

/-- `twoSided (P_V X) = twoSided X`. -/
private lemma two_right_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_idem, left_right_eq_two]

/-- `twoSided (twoSided X) = twoSided X`. -/
private lemma two_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_two_eq_two, left_two_eq_two]

/-- `P_U` is additive. -/
private lemma left_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B)
      = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  simp only [leftSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- `P_V` is additive. -/
private lemma right_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B)
      = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  simp only [rightSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `twoSided` is additive. -/
private lemma two_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j
  simp only [twoSidedSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `P_U` respects subtraction. -/
private lemma left_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B)
      = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  simp only [leftSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- `P_V` respects subtraction. -/
private lemma right_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B)
      = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  simp only [rightSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `twoSided` respects subtraction. -/
private lemma two_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j
  simp only [twoSidedSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

end MatrixCompletion

open MatrixCompletion
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  -- tangentProjection S Y = P_U Y + P_V Y - twoSided Y, and P_U, P_V, twoSided are
  -- additive.  Expand the outer projection over the inner +/-, then substitute the
  -- nine composition identities; the result telescopes by `abel`.
  simp only [tangentProjection]
  rw [left_sub, left_add, right_sub, right_add, two_sub, two_add,
    left_idem, right_idem, left_right_eq_two, right_left_eq_two,
    left_two_eq_two, right_two_eq_two,
    two_left_eq_two, two_right_eq_two, two_two_eq_two]
  abel

end PriorIdem
#print axioms PriorIdem.solution

namespace PriorAdj
open MatrixCompletion
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000

/-
Self-adjointness (symmetry under the Frobenius inner product) of the tangent
projection `P_T = leftSingularProjection + rightSingularProjection -
twoSidedSingularProjection`:

    ⟨P_T A, B⟩_F = ⟨A, P_T B⟩_F  for all real matrices A, B.

This is the basic orthogonal-projection property the Candès–Recht tangent-space
analysis (arXiv:0805.4471 §3–§4) uses repeatedly: it underlies the
resolution-of-identity `X = ∑_{ab} ⟨P_T(e_ab), X⟩ P_T(e_ab)` for `X ∈ T`, and
the rank-one frame representation of the sampling fluctuation `P_T P_Ω P_T - p P_T`
used in the Rudelson selection lemma (Rudelson 1999, J. Funct. Anal. 164, Thm 1).

Proof: each of the three constituent projections is self-adjoint because its
kernel is symmetric (`∑_k u_k i u_k a` and `∑_l v_l b v_l j`).  The two-sided
projection equals `left ∘ right = right ∘ left`, so its self-adjointness follows
from composing the two self-adjoint factors.  matrixInner is bilinear, so
self-adjointness distributes over the `+`/`-`.  Uses only the SVD orthonormality
data implicitly (in fact only symmetry of the kernels, not orthonormality).
-/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    matrixInner (tangentProjection S A) B
      = matrixInner A (tangentProjection S B) := by
  -- inline helpers ----------------------------------------------------------
  -- kernel symmetry
  have PuK_symm_inline : ∀ (i a : Fin n1),
      (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    intro i a; apply Finset.sum_congr rfl; intro k _; ring
  have PvK_symm_inline : ∀ (b j : Fin n2),
      (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    intro b j; apply Finset.sum_congr rfl; intro l _; ring
  -- matrixInner bilinearity
  have matrixInner_add_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P + Q) C = matrixInner P C + matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [add_mul]
  have matrixInner_sub_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P - Q) C = matrixInner P C - matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [sub_mul]
  have matrixInner_add_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q + C) = matrixInner P Q + matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_add]
  have matrixInner_sub_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q - C) = matrixInner P Q - matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_sub]
  -- left self-adjoint
  have left_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (leftSingularProjection S P) Q
        = matrixInner P (leftSingularProjection S Q) := by
    intro P Q; unfold matrixInner leftSingularProjection
    rw [show (∑ i, ∑ j, (∑ a, (∑ k, S.u k i * S.u k a) * P a j) * Q i j)
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * P a j * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ a, (∑ k, S.u k i * S.u k a) * Q a j))
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * Q a j * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _; ring]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    rw [PuK_symm_inline i a]; ring
  -- right self-adjoint
  have right_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (rightSingularProjection S P) Q
        = matrixInner P (rightSingularProjection S Q) := by
    intro P Q; unfold matrixInner rightSingularProjection
    rw [show (∑ i, ∑ j, (∑ b, P i b * (∑ l, S.v l b * S.v l j)) * Q i j)
          = ∑ i, ∑ j, ∑ b, P i b * (∑ l, S.v l b * S.v l j) * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ b, Q i b * (∑ l, S.v l b * S.v l j)))
          = ∑ i, ∑ j, ∑ b, Q i b * (∑ l, S.v l b * S.v l j) * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
    apply Finset.sum_congr rfl; intro i _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    rw [PvK_symm_inline b j]; ring
  -- twoSided = left ∘ right and = right ∘ left
  have ts_lr : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = leftSingularProjection S (rightSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ a, (∑ k, S.u k i * S.u k a) * (∑ b, X a b * (∑ l, S.v l b * S.v l j)))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
  have ts_rl : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = rightSingularProjection S (leftSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
                = ∑ b, ∑ a, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
                apply Finset.sum_congr rfl; intro b _
                rw [Finset.sum_mul]]
          rw [Finset.sum_comm]]
  -- twoSided self-adjoint via composition
  have ts_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (twoSidedSingularProjection S P) Q
        = matrixInner P (twoSidedSingularProjection S Q) := by
    intro P Q
    rw [ts_lr, left_sa, right_sa, ← ts_rl]
  -- assemble
  unfold tangentProjection
  rw [matrixInner_sub_left, matrixInner_add_left, left_sa, right_sa, ts_sa,
      matrixInner_sub_right, matrixInner_add_right]

end PriorAdj
#print axioms PriorAdj.solution


/-!
C1 — von Neumann / matrix trace-duality inequality:
  `matrixInner A B ≤ spectralNorm A * nuclearNorm B`.

Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2 first inequality
(von Neumann's trace inequality, 1937; see also Mirsky 1975).

Proof outline (built from Mathlib's self-adjoint spectral theorem; the SVD
reconstruction `B = Σ σ_k u_k v_k^T` is NOT available ready-made in this env's
Mathlib, so it is constructed here):
  * `T := toEuclideanLin B`, `G := Tᵀ∘T` symmetric and PSD.
  * `v_k := eigenvectorBasis G` orthonormal, eigenvalues `μ_k ≥ 0`,
    `σ_k = √μ_k = singularValues T k`.
  * `⟪T v_i, T v_j⟫ = ⟪G v_i, v_j⟫ = μ_i δ_ij`, so `‖T v_k‖ = σ_k`.
  * Frobenius inner product = Hilbert–Schmidt inner `∑_j ⟪S e_j, T e_j⟫`,
    which is `trace(Sᵀ∘T)` — basis-independent — hence `= ∑_k ⟪S v_k, T v_k⟫`.
  * `⟪S v_k, T v_k⟫ ≤ ‖S v_k‖·‖T v_k‖ ≤ ‖S‖·1·σ_k`; sum gives `‖S‖·Σσ_k`.
  * `Σ σ_k = nuclearNorm B`, `‖S‖ = spectralNorm A`.
-/

open Module InnerProductSpace LinearMap Matrix
open scoped BigOperators

/-! ### Operator-level SVD reconstruction & von Neumann inequality. -/

namespace SVDProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev gram (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := adjoint T ∘ₗ T

theorem gram_symm (T : E →ₗ[ℝ] F) : (gram T).IsSymmetric :=
  T.isSymmetric_adjoint_comp_self

theorem gram_pos (T : E →ₗ[ℝ] F) : (gram T).IsPositive :=
  T.isPositive_adjoint_comp_self

noncomputable def rsv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) :
    OrthonormalBasis (Fin n) ℝ E :=
  (gram_symm T).eigenvectorBasis hn

noncomputable def evals (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) : Fin n → ℝ :=
  (gram_symm T).eigenvalues hn

theorem evals_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ evals T hn k :=
  (gram_pos T).nonneg_eigenvalues hn k

theorem inner_Tv (T : E →ₗ[ℝ] F) (a b : E) :
    inner ℝ (T a) (T b) = inner ℝ (gram T a) b := by
  unfold gram
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]

theorem inner_Tv_eig (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T (rsv T hn i)) (T (rsv T hn j))
      = if i = j then evals T hn i else 0 := by
  rw [inner_Tv]
  unfold gram rsv evals
  rw [show (adjoint T ∘ₗ T) ((gram_symm T).eigenvectorBasis hn i)
        = (gram T) ((gram_symm T).eigenvectorBasis hn i) from rfl]
  rw [(gram_symm T).apply_eigenvectorBasis hn i]
  rw [inner_smul_left]
  rw [orthonormal_iff_ite.mp ((gram_symm T).eigenvectorBasis hn).orthonormal i j]
  simp only [conj_trivial]
  by_cases h : i = j
  · subst h; rw [if_pos rfl, if_pos rfl, mul_one, RCLike.ofReal_real_eq_id]; rfl
  · rw [if_neg h, if_neg h, mul_zero]

noncomputable def sval (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) : ℝ :=
  T.singularValues k

theorem sval_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ sval T hn k := T.singularValues_nonneg k

theorem sval_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    sval T hn k ^ 2 = evals T hn k := by
  unfold sval evals
  rw [T.sq_singularValues_fin hn k]

theorem norm_Tv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    ‖T (rsv T hn k)‖ = sval T hn k := by
  have heig : inner ℝ (T (rsv T hn k)) (T (rsv T hn k)) = evals T hn k := by
    have h := inner_Tv_eig T hn k k
    rw [if_pos rfl] at h
    exact h
  have h2 : ‖T (rsv T hn k)‖ ^ 2 = sval T hn k ^ 2 := by
    rw [@norm_sq_eq_re_inner ℝ, heig, sval_sq, RCLike.re_to_real]
  have hnn := sval_nonneg T hn k
  nlinarith [norm_nonneg (T (rsv T hn k)), h2, hnn]

theorem hsInner_eq_trace {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    (∑ j, inner ℝ (S (b j)) (T (b j))) = (adjoint S ∘ₗ T).trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right S (b j) (T (b j))]

theorem hsInner_basis_indep {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ (S (b j)) (T (b j)))
      = ∑ k, inner ℝ (S (rsv T hn k)) (T (rsv T hn k)) := by
  rw [hsInner_eq_trace S T b, hsInner_eq_trace S T (rsv T hn)]

theorem vonNeumann_op {ι : Type*} [Fintype ι] (S : E →L[ℝ] F) (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ ((S : E →ₗ[ℝ] F) (b j)) (T (b j))) ≤ ‖S‖ * ∑ k, sval T hn k := by
  rw [hsInner_basis_indep (S : E →ₗ[ℝ] F) T b hn]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hSle : ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ ≤ ‖S‖ * ‖(rsv T hn k : E)‖ := S.le_opNorm _
  calc inner ℝ ((S : E →ₗ[ℝ] F) (rsv T hn k)) (T (rsv T hn k))
      ≤ ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ * ‖T (rsv T hn k)‖ := real_inner_le_norm _ _
    _ ≤ (‖S‖ * ‖(rsv T hn k : E)‖) * ‖T (rsv T hn k)‖ := by
          apply mul_le_mul_of_nonneg_right hSle (norm_nonneg _)
    _ = ‖S‖ * sval T hn k := by
          rw [(rsv T hn).orthonormal.1 k, norm_Tv]; ring

end SVDProbe

/-! ### Matrix specialization to the platform statement. -/

namespace MatrixCompletion

open SVDProbe

variable {n1 n2 : ℕ}

theorem matrixInner_eq_hsInner (A B : RealMatrix n1 n2) :
    matrixInner A B
      = ∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                      ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)) := by
  unfold matrixInner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply]
  simp only [toEuclideanLin_apply]
  have hcol : ∀ (C : RealMatrix n1 n2),
      (C *ᵥ (EuclideanSpace.single j (1:ℝ)).ofLp) i = C i j := by
    intro C
    simp only [Matrix.mulVec, EuclideanSpace.ofLp_single, dotProduct_single, mul_one]
  rw [hcol A, hcol B]
  rw [show (⟪A i j, B i j⟫_ℝ : ℝ) = B i j * (starRingEnd ℝ) (A i j) from RCLike.inner_apply _ _,
      conj_trivial]; ring

theorem nuclearNorm_eq_sum_sval (B : RealMatrix n1 n2)
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2) :
    nuclearNorm B = ∑ k, sval (toEuclideanLin B) hn k := by
  unfold nuclearNorm sval
  set T := toEuclideanLin B
  rw [Finsupp.sum_of_support_subset T.singularValues
      (s := Finset.range n2) ?_ (fun _ x => x) (by intro _ _; rfl)]
  · rw [Finset.sum_range fun k => T.singularValues k]
  · intro k hk
    rw [Finset.mem_range]
    by_contra hge
    push_neg at hge
    have hz : T.singularValues k = 0 := by
      apply T.singularValues_of_finrank_le
      rw [hn]; exact hge
    rw [Finsupp.mem_support_iff] at hk
    exact hk hz

theorem trace_duality_C1 (A B : RealMatrix n1 n2) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  rw [matrixInner_eq_hsInner A B, nuclearNorm_eq_sum_sval B hn]
  show (∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                     ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)))
      ≤ spectralNorm A * ∑ k, sval (toEuclideanLin B) hn k
  unfold _root_.MatrixCompletion.spectralNorm
  exact vonNeumann_op (LinearMap.toContinuousLinearMap (toEuclideanLin A))
    (toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ) hn

end MatrixCompletion

open MatrixCompletion
open scoped BigOperators

/-- C1 — von Neumann / matrix trace-duality inequality.
Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2, first inequality
(von Neumann's trace inequality 1937; Mirsky 1975). -/
theorem matrix_trace_duality_inequality {n₁ n₂ : ℕ} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B :=
  MatrixCompletion.trace_duality_C1 A B

open MatrixCompletion Module
namespace RectNuclear
-- Generalized from tianyipeng's LRMNucAux to rectangular matrices.
theorem range_rank {m n : ℕ} (X : RealMatrix m n) :
    finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) = X.rank := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]
theorem trace_self {m n : ℕ} (X : RealMatrix m n) :
    ((Matrix.toEuclideanLin X).adjoint ∘ₗ Matrix.toEuclideanLin X).trace ℝ _ =
      frobeniusNormSq X := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  unfold frobeniusNormSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem nuclear_le {m n : ℕ} (X : RealMatrix m n) :
    nuclearNorm X ≤ Real.sqrt (X.rank : ℝ) * frobeniusNorm X := by
  set T := Matrix.toEuclideanLin X
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hsupp := T.support_singularValues
  have hk : finrank ℝ (LinearMap.range T) = X.rank := range_rank X
  rw [hk] at hsupp
  have hnuc : nuclearNorm X = ∑ i ∈ Finset.range X.rank, T.singularValues i := by
    unfold nuclearNorm; rw [Finsupp.sum, hsupp]
  have hkp : X.rank ≤ n := Matrix.rank_le_width X
  have hsq : ∑ i ∈ Finset.range X.rank, T.singularValues i ^ 2 = frobeniusNormSq X := by
    have h1 : ∑ i ∈ Finset.range X.rank, T.singularValues i ^ 2 =
        ∑ i ∈ Finset.range n, T.singularValues i ^ 2 := by
      apply Finset.sum_subset (Finset.range_subset_range.2 hkp)
      intro i _ hi
      have : T.singularValues i = 0 := by
        by_contra hne
        have : i ∈ T.singularValues.support := Finsupp.mem_support_iff.2 hne
        rw [hsupp] at this; exact hi this
      simp [this]
    rw [h1, Finset.sum_range (fun i => T.singularValues i ^ 2)]
    have h2 : ∀ i : Fin n, T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hfin i :=
      fun i => T.sq_singularValues_fin hfin i
    simp_rw [h2]
    rw [← T.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues hfin]
    simp only [RCLike.re_to_real]
    exact trace_self X
  have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.range X.rank) (f := fun i => T.singularValues i)
  rw [Finset.card_range, hsq, ← hnuc] at hCS
  unfold frobeniusNorm
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le hCS
end RectNuclear
#print axioms RectNuclear.nuclear_le

open MatrixCompletion Matrix
open scoped BigOperators
namespace TangentRank
variable {m n r : ℕ} {A : RealMatrix m n}
noncomputable def U (S : SVD A r) : Matrix (Fin m) (Fin r) ℝ := fun i k => S.u k i
noncomputable def V (S : SVD A r) : Matrix (Fin n) (Fin r) ℝ := fun j k => S.v k j
lemma utu (S : SVD A r) : (U S).transpose * U S = 1 := by
  ext k l
  simpa [Matrix.mul_apply,U,Matrix.one_apply] using S.u_orthonormal k l
lemma vtv (S : SVD A r) : (V S).transpose * V S = 1 := by
  ext k l
  simpa [Matrix.mul_apply,V,Matrix.one_apply] using S.v_orthonormal k l
lemma factor (S : SVD A r) : A = U S * Matrix.diagonal S.sigma * (V S).transpose := by
  calc A = ∑ k, S.sigma k • Matrix.vecMulVec (S.u k) (S.v k) := S.decomp
       _ = _ := by
        ext i j
        simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
        change (∑ k, S.sigma k * (S.u k i * S.v k j)) =
          ∑ k, (U S * Matrix.diagonal S.sigma) i k * S.v k j
        simp only [Matrix.mul_diagonal,U]
        apply Finset.sum_congr rfl
        intro k hk
        ring
lemma rank_lower (S : SVD A r) : r ≤ A.rank := by
  classical
  have hd : (U S).transpose * A * V S = Matrix.diagonal S.sigma := by
    calc (U S).transpose * A * V S =
          (U S).transpose * (U S * Matrix.diagonal S.sigma * (V S).transpose) * V S :=
            congrArg (fun X : RealMatrix m n => (U S).transpose * X * V S) (factor S)
         _ = _ := by
          simp only [Matrix.mul_assoc,vtv,Matrix.mul_one]
          rw [← Matrix.mul_assoc,utu,Matrix.one_mul]
  have hr : (Matrix.diagonal S.sigma).rank = r := by
    have hnon : ∀ i, S.sigma i ≠ 0 := fun i => ne_of_gt (S.sigma_pos i)
    simp [Matrix.rank_diagonal,hnon]
  rw [← hr,← hd]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
lemma left_eq (S : SVD A r) (X : RealMatrix m n) :
    leftSingularProjection S X = (U S * (U S).transpose) * X := rfl
lemma right_eq (S : SVD A r) (X : RealMatrix m n) :
    rightSingularProjection S X = X * (V S * (V S).transpose) := rfl
lemma two_eq (S : SVD A r) (X : RealMatrix m n) :
    twoSidedSingularProjection S X = (U S * (U S).transpose) * (X * (V S * (V S).transpose)) := by
  ext i j
  simp only [twoSidedSingularProjection,Matrix.mul_apply,Matrix.transpose_apply,U,V,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring
lemma decomposition (S : SVD A r) (X : RealMatrix m n) :
    tangentProjection S X = ((1 - U S * (U S).transpose) * X * V S) * (V S).transpose +
      U S * ((U S).transpose * X) := by
  rw [tangentProjection,left_eq,right_eq,two_eq]
  simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc]
  abel
lemma rank_add {a b : ℕ} (X Y : RealMatrix a b) : (X+Y).rank ≤ X.rank + Y.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro y ⟨x,rfl⟩
  rw [Matrix.mulVecLin_apply,Matrix.add_mulVec]
  exact Submodule.add_mem_sup ⟨x,rfl⟩ ⟨x,rfl⟩
lemma tangent_rank (S : SVD A r) (X : RealMatrix m n) :
    (tangentProjection S X).rank ≤ 2*A.rank := by
  rw [decomposition]
  have h1 := Matrix.rank_mul_le_left (((1-U S*(U S).transpose)*X)*V S) (V S).transpose
  have h2 := Matrix.rank_le_width (((1-U S*(U S).transpose)*X)*V S)
  have h3 := Matrix.rank_mul_le_left (U S) ((U S).transpose*X)
  have h4 := Matrix.rank_le_width (U S)
  have h5 := rank_add ((((1-U S*(U S).transpose)*X)*V S)*(V S).transpose) (U S*((U S).transpose*X))
  have h6 := rank_lower S
  omega
end TangentRank
#print axioms TangentRank.tangent_rank

open MatrixCompletion
namespace TangentGeometry
lemma energy {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (N : RealMatrix m n) :
    frobeniusNorm (tangentProjection S N)^2 = matrixInner N (tangentProjection S N) := by
  have hnn : 0 ≤ frobeniusNormSq (tangentProjection S N) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [frobeniusNorm,Real.sq_sqrt hnn]
  calc frobeniusNormSq (tangentProjection S N) =
       matrixInner (tangentProjection S N) (tangentProjection S N) := by
        simp [frobeniusNormSq,matrixInner,pow_two]
       _ = matrixInner N (tangentProjection S (tangentProjection S N)) := PriorAdj.solution S N _
       _ = _ := by rw [PriorIdem.solution]
lemma norm_bound {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (N : RealMatrix m n) :
    frobeniusNorm (tangentProjection S N) ≤
      Real.sqrt ((tangentProjection S N).rank : ℝ) * spectralNorm N := by
  have hn : 0 ≤ spectralNorm N := norm_nonneg _
  have hf : 0 ≤ frobeniusNorm (tangentProjection S N) := Real.sqrt_nonneg _
  by_cases hz : frobeniusNorm (tangentProjection S N) = 0
  · rw [hz]; exact mul_nonneg (Real.sqrt_nonneg _) hn
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne hf (Ne.symm hz))).mp
    calc frobeniusNorm (tangentProjection S N) * frobeniusNorm (tangentProjection S N)
        = frobeniusNorm (tangentProjection S N)^2 := by ring
      _ = matrixInner N (tangentProjection S N) := energy S N
      _ ≤ spectralNorm N * nuclearNorm (tangentProjection S N) := matrix_trace_duality_inequality _ _
      _ ≤ spectralNorm N * (Real.sqrt ((tangentProjection S N).rank : ℝ) *
            frobeniusNorm (tangentProjection S N)) := mul_le_mul_of_nonneg_left (RectNuclear.nuclear_le _) hn
      _ = _ := by ring
end TangentGeometry
#print axioms TangentGeometry.norm_bound

open MatrixCompletion

/-- (2.15) and the bound on Λ = 2‖𝒫_A(N)‖₂ (p. 9), for an arbitrary matrix N in place of 𝐌:
𝒫_A(N) = P_{S₁⊥} N P_{S₂} + P_{S₁} N, and
Λ ≤ 2√(rank 𝒫_A(N)) ‖N‖∞ ≤ 2√(2 rank A) ‖N‖∞ ≤ √(2 rank A) λ when λ ≥ 2‖N‖∞. -/
theorem prior_lambda {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂} (S : SVD A r) (N : RealMatrix m₁ m₂) :
    -- (2.15)
    tangentProjection S N =
        (rightSingularProjection S N - twoSidedSingularProjection S N) + leftSingularProjection S N ∧
      2 * frobeniusNorm (tangentProjection S N) ≤
        2 * Real.sqrt ((tangentProjection S N).rank : ℝ) * spectralNorm N ∧
      2 * Real.sqrt ((tangentProjection S N).rank : ℝ) * spectralNorm N ≤
        2 * Real.sqrt (2 * (A.rank : ℝ)) * spectralNorm N ∧
      ∀ lam : ℝ, 2 * spectralNorm N ≤ lam →
        2 * Real.sqrt (2 * (A.rank : ℝ)) * spectralNorm N ≤ Real.sqrt (2 * (A.rank : ℝ)) * lam := by
  have hn : 0 ≤ spectralNorm N := norm_nonneg _
  constructor
  · unfold tangentProjection; abel
  refine ⟨?_,?_,?_⟩
  · have h := TangentGeometry.norm_bound S N
    linarith
  · have hr : ((tangentProjection S N).rank : ℝ) ≤ 2*(A.rank : ℝ) := by
      exact_mod_cast TangentRank.tangent_rank S N
    have h := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hr) hn
    linarith
  · intro lam hlam
    have h := mul_le_mul_of_nonneg_left hlam (Real.sqrt_nonneg (2*(A.rank : ℝ)))
    nlinarith


#print axioms prior_lambda

namespace NormalHelper
open MatrixCompletion
open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace WithLp
variable {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂}
theorem ker_idem {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i b : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ k : Fin r, u k i * u k b := by
  have e1 : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin N, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; rw [horth k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, u k i * u l b * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then u k i * u l b else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp


theorem left_signMatrix (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold leftSingularProjection signMatrix
  -- signMatrix a j = ∑ l, u l a * v l j
  have hsm : ∀ a : Fin n₁, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) a j
      = ∑ l : Fin r, S.u l a * S.v l j := by
    intro a
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  -- LHS = ∑ a (∑ k u_k i u_k a)(∑ l u_l a v_l j)
  -- = ∑ k u_k i v_k j  (orthonormality of u)
  have hgoal : (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
        = ∑ a : Fin n₁, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j) := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ k : Fin r, ∑ a : Fin n₁, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n₁, S.u k a * S.u l a) := by
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [e2]
    have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n₁, S.u k a * S.u l a))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
      apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
      rw [S.u_orthonormal k l]
    rw [e3]
    apply Finset.sum_congr rfl; intro k _
    have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
        = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
      apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

theorem right_signMatrix (S : SVD M r) :
    rightSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold rightSingularProjection signMatrix
  have hsm : ∀ b : Fin n₂, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) i b
      = ∑ l : Fin r, S.u l i * S.v l b := by
    intro b
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _; rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  have hgoal : (∑ b : Fin n₂, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ b : Fin n₂, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
        = ∑ b : Fin n₂, ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j) := by
      apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ l : Fin r, ∑ b : Fin n₂, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n₂, S.v l b * S.v k b) := by
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e2]
    have e3 : (∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n₂, S.v l b * S.v k b))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (if l = k then 1 else 0) := by
      apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _
      rw [S.v_orthonormal l k]
    rw [e3]
    apply Finset.sum_congr rfl; intro l _
    have : (∑ k : Fin r, S.u l i * S.v k j * (if l = k then 1 else 0))
        = ∑ k : Fin r, (if l = k then S.u l i * S.v k j else 0) := by
      apply Finset.sum_congr rfl; intro k _; by_cases h : l = k <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

/-! ## Matrix projectors PU (n₁×n₁) and PV (n₂×n₂). -/

/-- Orthogonal projector onto the column singular space. -/
noncomputable def PUmat (S : SVD M r) : Matrix (Fin n₁) (Fin n₁) ℝ :=
  ∑ k, Matrix.vecMulVec (S.u k) (S.u k)

/-- Orthogonal projector onto the row singular space. -/
noncomputable def PVmat (S : SVD M r) : Matrix (Fin n₂) (Fin n₂) ℝ :=
  ∑ k, Matrix.vecMulVec (S.v k) (S.v k)

theorem PUmat_apply (S : SVD M r) (i a : Fin n₁) :
    PUmat S i a = ∑ k, S.u k i * S.u k a := by
  unfold PUmat
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _; rw [Matrix.vecMulVec_apply]

theorem PVmat_apply (S : SVD M r) (b j : Fin n₂) :
    PVmat S b j = ∑ k, S.v k b * S.v k j := by
  unfold PVmat
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _; rw [Matrix.vecMulVec_apply]

/-! ## Projector forms of the singular projections. -/

theorem left_eq_PU (S : SVD M r) (X : RealMatrix n₁ n₂) :
    leftSingularProjection S X = PUmat S * X := by
  funext i j
  unfold leftSingularProjection
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply]

theorem right_eq_PV (S : SVD M r) (X : RealMatrix n₁ n₂) :
    rightSingularProjection S X = X * PVmat S := by
  funext i j
  unfold rightSingularProjection
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro b _; rw [PVmat_apply]

theorem two_eq_PU_PV (S : SVD M r) (X : RealMatrix n₁ n₂) :
    twoSidedSingularProjection S X = PUmat S * X * PVmat S := by
  funext i j
  unfold twoSidedSingularProjection
  rw [Matrix.mul_apply]
  -- (PU * X * PV) i j = ∑ b (PU*X) i b * PV b j = ∑ b (∑ a PU i a * X a b) * PV b j
  have hrew : ∀ b : Fin n₂, (PUmat S * X) i b * PVmat S b j
      = (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * X a b)
          * (∑ l : Fin r, S.v l b * S.v l j) := by
    intro b
    rw [Matrix.mul_apply, PVmat_apply]
    congr 1
    apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply]
  rw [Finset.sum_congr rfl (fun b _ => hrew b)]
  -- target: ∑ a ∑ b (∑k u i a) X a b (∑l v b j) = ∑ b (∑ a (∑k u i a) X a b)(∑l v b j)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

/-! ## Idempotence and symmetry of PU, PV. -/

theorem PU_idem (S : SVD M r) : PUmat S * PUmat S = PUmat S := by
  funext i j
  rw [Matrix.mul_apply]
  have : (∑ a : Fin n₁, PUmat S i a * PUmat S a j)
      = ∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.u l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply, PUmat_apply]
  rw [this, ker_idem S.u S.u_orthonormal i j, PUmat_apply]

theorem PV_idem (S : SVD M r) : PVmat S * PVmat S = PVmat S := by
  funext i j
  rw [Matrix.mul_apply]
  have : (∑ a : Fin n₂, PVmat S i a * PVmat S a j)
      = ∑ a : Fin n₂, (∑ k : Fin r, S.v k i * S.v k a) * (∑ l : Fin r, S.v l a * S.v l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [PVmat_apply, PVmat_apply]
  rw [this, ker_idem S.v S.v_orthonormal i j, PVmat_apply]

theorem PU_symm (S : SVD M r) : (PUmat S)ᵀ = PUmat S := by
  funext i j
  rw [Matrix.transpose_apply, PUmat_apply, PUmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

theorem PV_symm (S : SVD M r) : (PVmat S)ᵀ = PVmat S := by
  funext i j
  rw [Matrix.transpose_apply, PVmat_apply, PVmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

/-! ## Factorization of the normal projection: W = (1-PU) Z (1-PV). -/

theorem normalProjection_factor (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z = (1 - PUmat S) * Z * (1 - PVmat S) := by
  unfold normalProjection tangentProjection
  rw [left_eq_PU, right_eq_PV, two_eq_PU_PV]
  -- Z - (PU Z + Z PV - PU Z PV) = (1-PU) Z (1-PV)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  -- LHS = Z - (PU*Z + Z*PV - PU*Z*PV); RHS = (Z - Z*PV) - (PU*Z - PU*Z*PV)
  abel

/-! ## E = signMatrix S obeys PU E = E, E PV = E. -/

theorem PU_signMatrix (S : SVD M r) : PUmat S * signMatrix S = signMatrix S := by
  rw [← left_eq_PU, left_signMatrix]

theorem signMatrix_PV (S : SVD M r) : signMatrix S * PVmat S = signMatrix S := by
  rw [← right_eq_PV, right_signMatrix]

/-! ## Orthogonality crux: Eᵀ * W = 0  and  W * PV = 0. -/

theorem Etrans_W_eq_zero (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    (signMatrix S)ᵀ * normalProjection S Z = 0 := by
  rw [normalProjection_factor]
  -- Eᵀ * (1-PU) * Z * (1-PV) ; Eᵀ * (1-PU) = Eᵀ - Eᵀ PU = Eᵀ - (PU E)ᵀ = Eᵀ - Eᵀ = 0
  have hEt : (signMatrix S)ᵀ * (1 - PUmat S) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have : (signMatrix S)ᵀ * PUmat S = (signMatrix S)ᵀ := by
      have h := PU_signMatrix S
      have h2 : (PUmat S * signMatrix S)ᵀ = (signMatrix S)ᵀ := by rw [h]
      rw [Matrix.transpose_mul, PU_symm] at h2
      exact h2
    rw [this, sub_self]
  calc (signMatrix S)ᵀ * ((1 - PUmat S) * Z * (1 - PVmat S))
      = ((signMatrix S)ᵀ * (1 - PUmat S)) * Z * (1 - PVmat S) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = 0 := by rw [hEt, Matrix.zero_mul, Matrix.zero_mul]

theorem W_PV_eq_zero (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z * PVmat S = 0 := by
  rw [normalProjection_factor]
  have hPV : (1 - PVmat S) * PVmat S = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, PV_idem, sub_self]
  calc (1 - PUmat S) * Z * (1 - PVmat S) * PVmat S
      = (1 - PUmat S) * Z * ((1 - PVmat S) * PVmat S) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hPV, Matrix.mul_zero]

/-! ## E = E PV (already from right_signMatrix). -/

theorem signMatrix_eq_signMatrix_PV (S : SVD M r) :
    signMatrix S = signMatrix S * PVmat S := (signMatrix_PV S).symm

/-! ## Analytic part. -/

/-- ofLp of the Euclidean image is the matrix-vector product. -/
theorem ofLp_image (A : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    ofLp ((toEuclideanLin A) x) = A *ᵥ ofLp x :=
  Matrix.ofLp_toEuclideanLin_apply A x

/-- Euclidean inner product as coordinate sum (for ℝ). -/
theorem eucl_inner_eq_sum {N : ℕ} (a b : EuclideanSpace ℝ (Fin N)) :
    (inner ℝ a b : ℝ) = ∑ i, (ofLp a) i * (ofLp b) i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro i _
  rw [show (⟪a i, b i⟫_ℝ : ℝ) = b i * (starRingEnd ℝ) (a i) from RCLike.inner_apply _ _,
      conj_trivial]; ring

/-- Inner product of two Euclidean images as a coordinate sum of matrix-vector products. -/
theorem inner_image_eq_sum (B C : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (inner ℝ ((toEuclideanLin B) x) ((toEuclideanLin C) x) : ℝ)
      = ∑ i, (B *ᵥ ofLp x) i * (C *ᵥ ofLp x) i := by
  rw [eucl_inner_eq_sum, ofLp_image, ofLp_image]

/-- A bilinear quadratic form `∑ᵢ (B x)ᵢ (C x)ᵢ` expands as `∑_{p,q} (Bᵀ C)_{pq} xₚ x_q`. -/
theorem mulVec_dot_eq_transpose_mul (B C : RealMatrix n₁ n₂) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ p, ∑ q, (Bᵀ * C) p q * x p * x q := by
  have e1 : (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.mulVec, Matrix.mulVec]; rfl
  rw [e1]
  -- expand each product, swap sums to pull i innermost
  have e2 : (∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q))
      = ∑ i, ∑ p, ∑ q, (B i p * C i q) * (x p * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _; ring
  rw [e2, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.transpose_apply]; ring

/-- If `Bᵀ C = 0` then `∑ᵢ (B x)ᵢ (C x)ᵢ = 0`. -/
theorem mulVec_dot_eq_zero_of_transpose_mul_zero (B C : RealMatrix n₁ n₂)
    (h : Bᵀ * C = 0) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i) = 0 := by
  rw [mulVec_dot_eq_transpose_mul, h]
  simp

/-! ## Euclidean norm-squared as a quadratic form. -/

/-- `‖a‖² = ∑ᵢ (ofLp a)ᵢ²`. -/
theorem normSq_eq_sum {N : ℕ} (a : EuclideanSpace ℝ (Fin N)) :
    ‖a‖ ^ 2 = ∑ i, (ofLp a) i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, eucl_inner_eq_sum]
  apply Finset.sum_congr rfl; intro i _; ring

/-- `‖B y‖² = ∑_{p,q} (Bᵀ B)_{pq} yₚ y_q` for the Euclidean image. -/
theorem normSq_image_eq_quad (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ^ 2
      = ∑ p, ∑ q, (Bᵀ * B) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  have : (∑ i, (ofLp ((toEuclideanLin B) y)) i ^ 2)
      = ∑ i, (B *ᵥ ofLp y) i * (B *ᵥ ofLp y) i := by
    apply Finset.sum_congr rfl; intro i _; rw [ofLp_image]; ring
  rw [this, mulVec_dot_eq_transpose_mul]

/-- `‖y‖² = ∑_{p,q} (1)_{pq} yₚ y_q`. -/
theorem normSq_eq_one_quad {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) :
    ‖y‖ ^ 2 = ∑ p, ∑ q, (1 : Matrix (Fin N) (Fin N) ℝ) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq]; ring
  · intro q _ hq; rw [Matrix.one_apply_ne (Ne.symm hq)]; ring
  · intro h; exact absurd (Finset.mem_univ p) h

/-- Pythagorean split for a symmetric idempotent square matrix `P`. -/
theorem pythagoras_split {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin P) y‖ ^ 2 + ‖(toEuclideanLin (1 - P)) y‖ ^ 2 = ‖y‖ ^ 2 := by
  have hPtP : Pᵀ * P = P := by rw [hsymm, hidem]
  have hQtQ : (1 - P)ᵀ * (1 - P) = 1 - P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hidem]
    abel
  rw [normSq_image_eq_quad, hPtP, normSq_image_eq_quad, hQtQ, normSq_eq_one_quad]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases h : p = q
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-! ## Operator-norm bound transport. -/

/-- `‖B y‖ ≤ spectralNorm B · ‖y‖`. -/
theorem norm_image_le (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ≤ spectralNorm B * ‖y‖ := by
  unfold MatrixCompletion.spectralNorm
  have h := (LinearMap.toContinuousLinearMap (toEuclideanLin B)).le_opNorm y
  simpa using h

/-- Orthogonal projection `1-P` (symmetric idempotent `P`) is a contraction. -/
theorem norm_compl_le {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin (1 - P)) y‖ ≤ ‖y‖ := by
  have hsplit := pythagoras_split P hsymm hidem y
  have hle : ‖(toEuclideanLin (1 - P)) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(toEuclideanLin P) y‖]
  have h1 := norm_nonneg ((toEuclideanLin (1 - P)) y)
  have h2 := norm_nonneg y
  nlinarith [hle, h1, h2]

/-! ## `toEuclideanLin` is multiplicative / additive (transported through `ofLp`). -/

theorem toEuclideanLin_mul_apply {n₀ : ℕ} (A : RealMatrix n₀ n₁) (B : RealMatrix n₁ n₂)
    (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A * B)) x = (toEuclideanLin A) ((toEuclideanLin B) x) := by
  apply ofLp_injective
  rw [ofLp_image, ofLp_image, ofLp_image, Matrix.mulVec_mulVec]

theorem toEuclideanLin_add_apply (A B : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A + B)) x = (toEuclideanLin A) x + (toEuclideanLin B) x := by
  apply ofLp_injective
  rw [ofLp_image]
  rw [show ofLp ((toEuclideanLin A) x + (toEuclideanLin B) x)
        = ofLp ((toEuclideanLin A) x) + ofLp ((toEuclideanLin B) x) from rfl]
  rw [ofLp_image, ofLp_image, Matrix.add_mulVec]


theorem normal_contraction (S : SVD M r) (N : RealMatrix n₁ n₂) :
    MatrixCompletion.spectralNorm (normalProjection S N) ≤ MatrixCompletion.spectralNorm N := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖(toEuclideanLin (normalProjection S N)) x‖ ≤ MatrixCompletion.spectralNorm N * ‖x‖
  rw [normalProjection_factor,toEuclideanLin_mul_apply,toEuclideanLin_mul_apply]
  calc ‖(toEuclideanLin (1-PUmat S)) ((toEuclideanLin N) ((toEuclideanLin (1-PVmat S)) x))‖
      ≤ ‖(toEuclideanLin N) ((toEuclideanLin (1-PVmat S)) x)‖ :=
        norm_compl_le _ (PU_symm S) (PU_idem S) _
    _ ≤ MatrixCompletion.spectralNorm N * ‖(toEuclideanLin (1-PVmat S)) x‖ := norm_image_le N _
    _ ≤ MatrixCompletion.spectralNorm N * ‖x‖ := mul_le_mul_of_nonneg_left
      (norm_compl_le _ (PV_symm S) (PV_idem S) x) (norm_nonneg _)
end NormalHelper
#print axioms NormalHelper.normal_contraction

open MatrixCompletion
open scoped BigOperators
namespace NoiseBase
lemma inner_self (m n : ℕ) (A : RealMatrix m n) : matrixInner A A = frobeniusNorm A ^ 2 := by
  rw [frobeniusNorm,Real.sq_sqrt]
  · simp [matrixInner,frobeniusNormSq,pow_two]
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
lemma cauchy {m n : ℕ} (A B : RealMatrix m n) :
    |matrixInner A B| ≤ frobeniusNorm A * frobeniusNorm B := by
  have hp := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
    (fun p => A p.1 p.2) (fun p => B p.1 p.2)
  have hm := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
    (fun p => -(A p.1 p.2)) (fun p => B p.1 p.2)
  simp only [Fintype.sum_prod_type,neg_mul,neg_sq,Finset.sum_neg_distrib] at hp hm
  exact abs_le.mpr ⟨by simpa [matrixInner,frobeniusNorm,frobeniusNormSq] using neg_le_neg hm,
    by simpa [matrixInner,frobeniusNorm,frobeniusNormSq] using hp⟩
lemma tangent_contraction {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (X : RealMatrix m n) :
    frobeniusNorm (tangentProjection S X) ≤ frobeniusNorm X := by
  have h := (le_abs_self (matrixInner X (tangentProjection S X))).trans (cauchy X (tangentProjection S X))
  rw [← TangentGeometry.energy] at h
  have hx := Real.sqrt_nonneg (frobeniusNormSq X)
  have hp := Real.sqrt_nonneg (frobeniusNormSq (tangentProjection S X))
  change 0 ≤ frobeniusNorm X at hx
  change 0 ≤ frobeniusNorm (tangentProjection S X) at hp
  nlinarith
lemma normal_zero {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) : normalProjection S A = 0 := by
  have hl : leftSingularProjection S A = A := by
    rw [TangentRank.left_eq]
    calc (TangentRank.U S * (TangentRank.U S).transpose) * A =
        (TangentRank.U S * (TangentRank.U S).transpose) *
          (TangentRank.U S * Matrix.diagonal S.sigma * (TangentRank.V S).transpose) :=
            congrArg (fun X : RealMatrix m n => (TangentRank.U S * (TangentRank.U S).transpose)*X) (TangentRank.factor S)
      _ = TangentRank.U S * (((TangentRank.U S).transpose * TangentRank.U S) *
            (Matrix.diagonal S.sigma * (TangentRank.V S).transpose)) := by
              simp only [Matrix.mul_assoc]
      _ = TangentRank.U S * Matrix.diagonal S.sigma * (TangentRank.V S).transpose := by
        rw [TangentRank.utu,Matrix.one_mul,Matrix.mul_assoc]
      _ = A := (TangentRank.factor S).symm
  have ht : twoSidedSingularProjection S A = rightSingularProjection S A := by
    rw [TangentRank.two_eq,← Matrix.mul_assoc,← TangentRank.left_eq,hl,← TangentRank.right_eq]
  simp [normalProjection,tangentProjection,hl,ht]
end NoiseBase
#print axioms NoiseBase.cauchy
#print axioms NoiseBase.tangent_contraction
#print axioms NoiseBase.normal_zero

/- Hartmann_Psi’s accepted self-adjointness proof, exposing its existing two-sided helper. -/
namespace PriorTwo
open MatrixCompletion
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000

/-
Self-adjointness (symmetry under the Frobenius inner product) of the tangent
projection `P_T = leftSingularProjection + rightSingularProjection -
twoSidedSingularProjection`:

    ⟨P_T A, B⟩_F = ⟨A, P_T B⟩_F  for all real matrices A, B.

This is the basic orthogonal-projection property the Candès–Recht tangent-space
analysis (arXiv:0805.4471 §3–§4) uses repeatedly: it underlies the
resolution-of-identity `X = ∑_{ab} ⟨P_T(e_ab), X⟩ P_T(e_ab)` for `X ∈ T`, and
the rank-one frame representation of the sampling fluctuation `P_T P_Ω P_T - p P_T`
used in the Rudelson selection lemma (Rudelson 1999, J. Funct. Anal. 164, Thm 1).

Proof: each of the three constituent projections is self-adjoint because its
kernel is symmetric (`∑_k u_k i u_k a` and `∑_l v_l b v_l j`).  The two-sided
projection equals `left ∘ right = right ∘ left`, so its self-adjointness follows
from composing the two self-adjoint factors.  matrixInner is bilinear, so
self-adjointness distributes over the `+`/`-`.  Uses only the SVD orthonormality
data implicitly (in fact only symmetry of the kernels, not orthonormality).
-/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    matrixInner (twoSidedSingularProjection S A) B
      = matrixInner A (twoSidedSingularProjection S B) := by
  -- inline helpers ----------------------------------------------------------
  -- kernel symmetry
  have PuK_symm_inline : ∀ (i a : Fin n1),
      (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    intro i a; apply Finset.sum_congr rfl; intro k _; ring
  have PvK_symm_inline : ∀ (b j : Fin n2),
      (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    intro b j; apply Finset.sum_congr rfl; intro l _; ring
  -- matrixInner bilinearity
  have matrixInner_add_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P + Q) C = matrixInner P C + matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [add_mul]
  have matrixInner_sub_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P - Q) C = matrixInner P C - matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [sub_mul]
  have matrixInner_add_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q + C) = matrixInner P Q + matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_add]
  have matrixInner_sub_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q - C) = matrixInner P Q - matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_sub]
  -- left self-adjoint
  have left_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (leftSingularProjection S P) Q
        = matrixInner P (leftSingularProjection S Q) := by
    intro P Q; unfold matrixInner leftSingularProjection
    rw [show (∑ i, ∑ j, (∑ a, (∑ k, S.u k i * S.u k a) * P a j) * Q i j)
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * P a j * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ a, (∑ k, S.u k i * S.u k a) * Q a j))
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * Q a j * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _; ring]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    rw [PuK_symm_inline i a]; ring
  -- right self-adjoint
  have right_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (rightSingularProjection S P) Q
        = matrixInner P (rightSingularProjection S Q) := by
    intro P Q; unfold matrixInner rightSingularProjection
    rw [show (∑ i, ∑ j, (∑ b, P i b * (∑ l, S.v l b * S.v l j)) * Q i j)
          = ∑ i, ∑ j, ∑ b, P i b * (∑ l, S.v l b * S.v l j) * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ b, Q i b * (∑ l, S.v l b * S.v l j)))
          = ∑ i, ∑ j, ∑ b, Q i b * (∑ l, S.v l b * S.v l j) * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
    apply Finset.sum_congr rfl; intro i _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    rw [PvK_symm_inline b j]; ring
  -- twoSided = left ∘ right and = right ∘ left
  have ts_lr : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = leftSingularProjection S (rightSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ a, (∑ k, S.u k i * S.u k a) * (∑ b, X a b * (∑ l, S.v l b * S.v l j)))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
  have ts_rl : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = rightSingularProjection S (leftSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
                = ∑ b, ∑ a, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
                apply Finset.sum_congr rfl; intro b _
                rw [Finset.sum_mul]]
          rw [Finset.sum_comm]]
  -- twoSided self-adjoint via composition
  have ts_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (twoSidedSingularProjection S P) Q
        = matrixInner P (twoSidedSingularProjection S Q) := by
    intro P Q
    rw [ts_lr, left_sa, right_sa, ← ts_rl]
  exact ts_sa A B

end PriorTwo
#print axioms PriorTwo.solution

open MatrixCompletion
open scoped BigOperators

namespace NoiseDecomposition
lemma inner_sub_left {m n : ℕ} (X Y Z : RealMatrix m n) :
    matrixInner (X-Y) Z = matrixInner X Z - matrixInner Y Z := by
  simp [matrixInner, sub_mul, Finset.sum_sub_distrib]
lemma inner_sub_right {m n : ℕ} (X Y Z : RealMatrix m n) :
    matrixInner X (Y-Z) = matrixInner X Y - matrixInner X Z := by
  simp [matrixInner, mul_sub, Finset.sum_sub_distrib]

lemma decomposition {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r)
    (X Y : RealMatrix m n) :
    matrixInner X Y = matrixInner (tangentProjection S X) (tangentProjection S Y) +
      matrixInner (normalProjection S X) (normalProjection S Y) := by
  have hxy := PriorAdj.solution S X Y
  have hpp := PriorAdj.solution S X (tangentProjection S Y)
  rw [PriorIdem.solution] at hpp
  simp only [normalProjection, inner_sub_left, inner_sub_right]
  linarith

lemma normal_sub {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r)
    (X Y : RealMatrix m n) :
    normalProjection S (X-Y) = normalProjection S X - normalProjection S Y := by
  simp only [NormalHelper.normalProjection_factor, Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma abs_duality {m n : ℕ} (X Y : RealMatrix m n) :
    |matrixInner X Y| ≤ spectralNorm X * nuclearNorm Y := by
  have hp := matrix_trace_duality_inequality X Y
  have hm := matrix_trace_duality_inequality (-X) Y
  have hn : spectralNorm (-X) = spectralNorm X := by simp [MatrixCompletion.spectralNorm]
  have hi : matrixInner (-X) Y = -matrixInner X Y := by
    simp [matrixInner, Finset.sum_neg_distrib]
  rw [hn,hi] at hm
  exact abs_le.mpr ⟨by linarith, hp⟩
end NoiseDecomposition

theorem solution {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂}
    (S : SVD A r) (N B : RealMatrix m₁ m₂) :
    2 * |matrixInner N (B - A)| ≤
        2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (tangentProjection S (B - A)) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ∧
      2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (tangentProjection S (B - A)) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ≤
        2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (B - A) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ∧
      2 * spectralNorm (normalProjection S N) ≤ 2 * spectralNorm N := by
  have hn : normalProjection S (B-A) = normalProjection S B := by
    rw [NoiseDecomposition.normal_sub, NoiseBase.normal_zero, sub_zero]
  have hd := NoiseDecomposition.decomposition S N (B-A)
  rw [hn] at hd
  have ht := NoiseBase.cauchy (tangentProjection S N) (tangentProjection S (B-A))
  have hq := NoiseDecomposition.abs_duality (normalProjection S N) (normalProjection S B)
  have ha := abs_add_le (matrixInner (tangentProjection S N) (tangentProjection S (B-A)))
    (matrixInner (normalProjection S N) (normalProjection S B))
  rw [← hd] at ha
  refine ⟨by nlinarith, ?_, ?_⟩
  · have hf : 0 ≤ frobeniusNorm (tangentProjection S N) := Real.sqrt_nonneg _
    have hc := NoiseBase.tangent_contraction S (B-A)
    nlinarith
  · exact mul_le_mul_of_nonneg_left (NormalHelper.normal_contraction S N) (by norm_num)

#print axioms solution

open MatrixCompletion
open scoped BigOperators Matrix
namespace TwoSidedBound
lemma idem {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (X : RealMatrix m n) :
    twoSidedSingularProjection S (twoSidedSingularProjection S X) =
      twoSidedSingularProjection S X := by
  simp only [NormalHelper.two_eq_PU_PV]
  calc NormalHelper.PUmat S * (NormalHelper.PUmat S * X * NormalHelper.PVmat S) *
        NormalHelper.PVmat S = (NormalHelper.PUmat S * NormalHelper.PUmat S) * X *
          (NormalHelper.PVmat S * NormalHelper.PVmat S) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [NormalHelper.PU_idem, NormalHelper.PV_idem]

lemma contraction {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (X : RealMatrix m n) :
    frobeniusNorm (twoSidedSingularProjection S X) ≤ frobeniusNorm X := by
  have he := PriorTwo.solution S X (twoSidedSingularProjection S X)
  rw [idem, NoiseBase.inner_self] at he
  have hc := (le_abs_self (matrixInner X (twoSidedSingularProjection S X))).trans
    (NoiseBase.cauchy X (twoSidedSingularProjection S X))
  rw [← he] at hc
  have hx : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
  have hp : 0 ≤ frobeniusNorm (twoSidedSingularProjection S X) := Real.sqrt_nonneg _
  nlinarith

lemma rank_bound {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (X : RealMatrix m n) :
    (twoSidedSingularProjection S X).rank ≤ A.rank := by
  rw [TangentRank.two_eq]
  calc ((TangentRank.U S * (TangentRank.U S).transpose) *
      (X * (TangentRank.V S * (TangentRank.V S).transpose))).rank
      ≤ (TangentRank.U S * (TangentRank.U S).transpose).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (TangentRank.U S).rank := Matrix.rank_mul_le_left _ _
    _ ≤ r := by simpa using (Matrix.rank_le_width (TangentRank.U S))
    _ ≤ A.rank := TangentRank.rank_lower S

lemma nuclear_bound {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (X : RealMatrix m n) :
    nuclearNorm (twoSidedSingularProjection S X) ≤ Real.sqrt (A.rank : ℝ) * frobeniusNorm X := by
  have hr : ((twoSidedSingularProjection S X).rank : ℝ) ≤ (A.rank : ℝ) :=
    Nat.cast_le.mpr (rank_bound S X)
  calc nuclearNorm (twoSidedSingularProjection S X)
      ≤ Real.sqrt ((twoSidedSingularProjection S X).rank : ℝ) *
        frobeniusNorm (twoSidedSingularProjection S X) := RectNuclear.nuclear_le _
    _ ≤ Real.sqrt (A.rank : ℝ) * frobeniusNorm (twoSidedSingularProjection S X) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (A.rank : ℝ) * frobeniusNorm X :=
      mul_le_mul_of_nonneg_left (contraction S X) (Real.sqrt_nonneg _)
end TwoSidedBound
#print axioms TwoSidedBound.nuclear_bound

open MeasureTheory MatrixCompletion KLTNuclear.Oracle
namespace SharpBridge
lemma norm_comparison {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n m₁ m₂ : ℕ} (X : Fin n → Ω → RealMatrix m₁ m₂)
    (𝔸 : Set (RealMatrix m₁ m₂)) (μ : ℝ) (hμ : Assumption1 P X 𝔸 μ)
    (B A : RealMatrix m₁ m₂) (hB : B ∈ 𝔸) (hA : A ∈ 𝔸) :
    frobeniusNorm (B-A) ≤ μ * l2Norm P X (B-A) := by
  have ha := hμ.2 (B-A) ⟨B,hB,A,hA,rfl⟩
  have hm : μ^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hμ.1)
  have hs : frobeniusNormSq (B-A) ≤ μ^2 * l2NormSq P X (B-A) := by
    have hh := mul_le_mul_of_nonneg_left ha (sq_nonneg μ)
    simpa only [← mul_assoc, mul_inv_cancel₀ hm, one_mul] using hh
  have hf0 : 0 ≤ frobeniusNormSq (B-A) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hl0 : 0 ≤ l2NormSq P X (B-A) :=
    (mul_nonneg (inv_nonneg.mpr (sq_nonneg μ)) hf0).trans ha
  have hf : frobeniusNorm (B-A)^2 = frobeniusNormSq (B-A) := Real.sq_sqrt hf0
  have hl : l2Norm P X (B-A)^2 = l2NormSq P X (B-A) := Real.sq_sqrt hl0
  have hfpos : 0 ≤ frobeniusNorm (B-A) := Real.sqrt_nonneg _
  have hlpos : 0 ≤ l2Norm P X (B-A) := Real.sqrt_nonneg _
  have hmul : 0 ≤ μ * l2Norm P X (B-A) := mul_nonneg hμ.1.le hlpos
  have hsq : frobeniusNorm (B-A)^2 ≤ (μ * l2Norm P X (B-A))^2 := by
    rw [mul_pow,hf,hl]; exact hs
  nlinarith

theorem from_eq_2_11 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (h𝔸 : Convex ℝ 𝔸) (μ : ℝ) (hμ : Assumption1 P X 𝔸 μ)
    (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat)
    (hbase : ∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
      l2NormSq P X (Ahat-A₀) + l2NormSq P X (Ahat-A) + lam*nuclearNorm (normalProjection S Ahat) ≤
        l2NormSq P X (A-A₀) + lam*nuclearNorm (twoSidedSingularProjection S (Ahat-A)) +
          2*matrixInner (noiseMatrix P X Y ω) (Ahat-A)) :
    ∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
      l2NormSq P X (Ahat - A₀) + l2NormSq P X (Ahat - A) + lam * nuclearNorm (normalProjection S Ahat) ≤
        l2NormSq P X (A - A₀) +
          μ * (lam * Real.sqrt (A.rank : ℝ) +
              2 * frobeniusNorm (tangentProjection S (noiseMatrix P X Y ω))) * l2Norm P X (Ahat - A) +
          2 * spectralNorm (normalProjection S (noiseMatrix P X Y ω)) *
            nuclearNorm (normalProjection S Ahat) := by
  intro A hA r S
  have hb := hbase A hA r S
  have hnoise := (solution S (noiseMatrix P X Y ω) Ahat).1.trans
    (solution S (noiseMatrix P X Y ω) Ahat).2.1
  have hpair : 2*matrixInner (noiseMatrix P X Y ω) (Ahat-A) ≤
      2*|matrixInner (noiseMatrix P X Y ω) (Ahat-A)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
  have hnu := mul_le_mul_of_nonneg_left (TwoSidedBound.nuclear_bound S (Ahat-A)) hlam.le
  have hf := norm_comparison P X 𝔸 μ hμ Ahat A hAhat.1 hA
  have hcoef : 0 ≤ lam*Real.sqrt (A.rank : ℝ) +
      2*frobeniusNorm (tangentProjection S (noiseMatrix P X Y ω)) :=
    add_nonneg (mul_nonneg hlam.le (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hc := mul_le_mul_of_nonneg_left hf hcoef
  nlinarith
end SharpBridge
#print axioms SharpBridge.norm_comparison
#print axioms SharpBridge.from_eq_2_11

end OldSharp

open MeasureTheory _root_.MatrixCompletion KLTNuclear.Oracle


/-- (2.17) (p. 9): for a convex 𝔸 under Assumption 1 with constant μ, every A ∈ 𝔸 with
support (S₁, S₂), Λ = 2‖𝒫_A(𝐌)‖₂ and Γ = 2‖P_{S₁⊥} 𝐌 P_{S₂⊥}‖∞. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (h𝔸 : Convex ℝ 𝔸) (μ : ℝ) (hμ : Assumption1 P X 𝔸 μ)
    (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat) :
    ∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
      l2NormSq P X (Ahat - A₀) + l2NormSq P X (Ahat - A) + lam * nuclearNorm (normalProjection S Ahat) ≤
        l2NormSq P X (A - A₀) +
          μ * (lam * Real.sqrt (A.rank : ℝ) +
              2 * frobeniusNorm (tangentProjection S (noiseMatrix P X Y ω))) * l2Norm P X (Ahat - A) +
          2 * spectralNorm (normalProjection S (noiseMatrix P X Y ω)) *
            nuclearNorm (normalProjection S Ahat) := by
  exact OldSharp.SharpBridge.from_eq_2_11 hn X Y hreg A₀ hmodel 𝔸 h𝔸 μ hμ lam hlam ω Ahat hAhat
    (Eq11.solution hn X Y hreg A₀ hmodel 𝔸 h𝔸 lam hlam ω Ahat hAhat)



#print axioms solution

end Prior

open _root_.MatrixCompletion
namespace Slow
open Prior.Eq11
open MeasureTheory MatrixCompletion KLTNuclear.Oracle
namespace SlowRate

lemma nuclear_nonneg {m k : ℕ} (A : RealMatrix m k) : 0 ≤ nuclearNorm A := by
  unfold nuclearNorm Finsupp.sum
  apply Finset.sum_nonneg
  intro i hi
  exact (Matrix.toEuclideanLin A).singularValues_nonneg i

lemma spectral_neg {m k : ℕ} (A : RealMatrix m k) : spectralNorm (-A) = spectralNorm A := by
  simp [MatrixCompletion.spectralNorm]

lemma inner_neg {m k : ℕ} (A B : RealMatrix m k) : matrixInner (-A) B = -matrixInner A B := by
  simp [matrixInner, Finset.sum_neg_distrib]

end SlowRate

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat)
    (hM : 2 * spectralNorm (noiseMatrix P X Y ω) ≤ lam) :
    ∀ A ∈ 𝔸, l2NormSq P X (Ahat - A₀) ≤ l2NormSq P X (A - A₀) + 2 * lam * nuclearNorm A := by
  intro A hA
  have hopt := hAhat.2 A hA
  unfold Ln at hopt
  rw [KLTWork.empirical_pairing hreg A₀ hmodel ω Ahat,
      KLTWork.empirical_pairing hreg A₀ hmodel ω A] at hopt
  have hh := matrix_trace_duality_inequality (noiseMatrix P X Y ω) Ahat
  have ha := matrix_trace_duality_inequality (-noiseMatrix P X Y ω) A
  rw [SlowRate.inner_neg,SlowRate.spectral_neg] at ha
  have hpenh := mul_le_mul_of_nonneg_right hM (SlowRate.nuclear_nonneg Ahat)
  have hpena := mul_le_mul_of_nonneg_right hM (SlowRate.nuclear_nonneg A)
  rw [KLTWork.l2_square_sub hreg Ahat A₀, KLTWork.l2_square_sub hreg A A₀,
      KLTWork.l2_comm Ahat A₀, KLTWork.l2_comm A A₀]
  nlinarith

#print axioms solution

end Slow

open MeasureTheory _root_.MatrixCompletion KLTNuclear.Oracle

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m₁ m₂ : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → RealMatrix m₁ m₂) (Y : Fin n → Ω → ℝ)
    (hreg : SampleRegularity P X Y)
    (A₀ : RealMatrix m₁ m₂) (hmodel : TraceRegressionModel P X Y A₀)
    (𝔸 : Set (RealMatrix m₁ m₂)) (lam : ℝ) (hlam : 0 < lam)
    (ω : Ω) (Ahat : RealMatrix m₁ m₂) (hAhat : IsEstimator P X Y lam ω 𝔸 Ahat)
    (hM : 2 * spectralNorm (noiseMatrix P X Y ω) ≤ lam) :
    (∀ A ∈ 𝔸, l2NormSq P X (Ahat - A₀) ≤ l2NormSq P X (A - A₀) + 2 * lam * nuclearNorm A) ∧
    (Convex ℝ 𝔸 → ∀ μ : ℝ, Assumption1 P X 𝔸 μ →
      (∀ A ∈ 𝔸, l2NormSq P X (Ahat - A₀) ≤
          l2NormSq P X (A - A₀) + ((1 + Real.sqrt 2) / 2) ^ 2 * μ ^ 2 * lam ^ 2 * (A.rank : ℝ)) ∧
      (∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
        l2NormSq P X (Ahat - A₀) +
            (lam - 2 * spectralNorm (noiseMatrix P X Y ω)) * nuclearNorm (normalProjection S Ahat) ≤
          l2NormSq P X (A - A₀) + ((1 + Real.sqrt 2) / 2) ^ 2 * μ ^ 2 * lam ^ 2 * (A.rank : ℝ))) := by
  constructor
  · exact Slow.solution hn X Y hreg A₀ hmodel 𝔸 lam hlam ω Ahat hAhat hM
  intro h𝔸 μ hμ
  have hpen : ∀ A ∈ 𝔸, ∀ (r : ℕ) (S : SVD A r),
      l2NormSq P X (Ahat - A₀) +
          (lam - 2 * spectralNorm (noiseMatrix P X Y ω)) * nuclearNorm (normalProjection S Ahat) ≤
        l2NormSq P X (A - A₀) + ((1 + Real.sqrt 2) / 2) ^ 2 * μ ^ 2 * lam ^ 2 * (A.rank : ℝ) := by
    intro A hA r S
    have hb := Prior.solution hn X Y hreg A₀ hmodel 𝔸 h𝔸 μ hμ lam hlam ω Ahat hAhat A hA r S
    have hΛ := Prior.OldSharp.prior_lambda S (noiseMatrix P X Y ω)
    have hΛ' := hΛ.2.1.trans (hΛ.2.2.1.trans (hΛ.2.2.2 lam hM))
    have hΓ := (Prior.OldSharp.solution S (noiseMatrix P X Y ω) Ahat).2.2
    have hu := Slow.SlowRate.nuclear_nonneg (normalProjection S Ahat)
    have hx0 : 0 ≤ l2Norm P X (Ahat-A) := Real.sqrt_nonneg _
    have hΓu := mul_le_mul_of_nonneg_right hΓ hu
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_left hΛ' (lam*Real.sqrt (A.rank:ℝ))) hμ.1.le) hx0
    let C : ℝ := μ*(1+Real.sqrt 2)*lam*Real.sqrt (A.rank:ℝ)
    have heq : μ*(Real.sqrt (2*(A.rank:ℝ))*lam + lam*Real.sqrt (A.rank:ℝ))*l2Norm P X (Ahat-A) =
        C*l2Norm P X (Ahat-A) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      dsimp [C]
      ring
    rw [heq] at hc
    have hx : l2Norm P X (Ahat-A)^2 = l2NormSq P X (Ahat-A) :=
      Real.sq_sqrt (Prior.Eq11.ConvexGap.l2_nonneg (Ahat-A))
    have hconst : (C/2)^2 = ((1+Real.sqrt 2)/2)^2*μ^2*lam^2*(A.rank:ℝ) := by
      calc
        (C/2)^2 = ((1+Real.sqrt 2)/2)^2*μ^2*lam^2*(Real.sqrt (A.rank:ℝ))^2 := by dsimp [C]; ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg A.rank)]
    have hsquare := sq_nonneg (l2Norm P X (Ahat-A)-C/2)
    nlinarith only [hb,hc,hΓu,hx,hconst,hsquare]
  refine ⟨?_,hpen⟩
  intro A hA
  obtain ⟨r,S,_⟩ := Prior.Eq11.matrix_svd_exists A
  have hp := hpen A hA r S
  have hnuc := Slow.SlowRate.nuclear_nonneg (normalProjection S Ahat)
  have hnonneg := mul_nonneg (sub_nonneg.mpr hM) hnuc
  linarith
#print axioms solution
