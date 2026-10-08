-- Prove2me | solution 1 for Matrix.IsHermitian.sorted_eigenvalues_le_add_of_re_dotProduct_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:56:34.373858+00:00
-- url     : https://prove2.me/submissions/d4820480-1242-4735-81bc-ea88f50668f1

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Matrix
open Module InnerProductSpace

/-!
# Leaf C2, part 1: Weyl's eigenvalue inequality

For symmetric operators `T`, `S` on a finite-dimensional inner product space with
`re ⟪T x, x⟫ ≤ re ⟪S x, x⟫ + ε ‖x‖²` for all `x`, the sorted eigenvalues satisfy
`λⱼ(T) ≤ λⱼ(S) + ε`. Proof by dimension count: the span of the first `j + 1` eigenvectors of `T`
meets the span of the last `m - j` eigenvectors of `S` only in `0`.
-/


namespace LinearMap.IsSymmetric

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E} {m : ℕ}

/-- Rayleigh expansion in an eigenbasis. -/
lemma re_inner_apply_eq_sum (hT : T.IsSymmetric) (hn : finrank 𝕜 E = m) (x : E) :
    RCLike.re (inner 𝕜 (T x) x) =
      ∑ k, hT.eigenvalues hn k * ‖inner 𝕜 (hT.eigenvectorBasis hn k) (x)‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  have h : inner 𝕜 (T x) (x) = ∑ k, (hT.eigenvalues hn k : 𝕜) * ((‖inner 𝕜 (b k) (x)‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← b.sum_inner_mul_inner (T x) x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hT (x) (b k), hT.apply_eigenvectorBasis hn k, inner_smul_right, mul_assoc]
    congr 1
    rw [← inner_conj_symm, RCLike.conj_mul]
    norm_cast
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← RCLike.ofReal_mul, RCLike.ofReal_re]

lemma inner_eigenvectorBasis_eq_zero_of_mem_span (hT : T.IsSymmetric) (hn : finrank 𝕜 E = m)
    {K : Set (Fin m)} {x : E} (hx : x ∈ Submodule.span 𝕜 (hT.eigenvectorBasis hn '' K))
    {k : Fin m} (hk : k ∉ K) : inner 𝕜 (hT.eigenvectorBasis hn k) (x) = 0 := by
  set b := hT.eigenvectorBasis hn
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    exact b.orthonormal.2 hki
  · simp
  · intro u v _ _ hu hv; rw [inner_add_right, hu, hv, add_zero]
  · intro c u _ hu; rw [inner_smul_right, hu, mul_zero]

lemma finrank_span_eigenvectorBasis (hT : T.IsSymmetric) (hn : finrank 𝕜 E = m)
    (K : Finset (Fin m)) :
    finrank 𝕜 (Submodule.span 𝕜 (hT.eigenvectorBasis hn '' (K : Set (Fin m)))) = K.card := by
  set b := hT.eigenvectorBasis hn
  have hli : LinearIndependent 𝕜 (fun i : (K : Set (Fin m)) => b i) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hr : Set.range (fun i : (K : Set (Fin m)) => b i) = b '' (K : Set (Fin m)) := by
    ext y; simp
  rw [← hr, finrank_span_eq_card hli]
  simp

/-- **Weyl's inequality** (sorted eigenvalues, decreasing order). -/
theorem eigenvalues_le_add_of_re_inner_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = m) (ε : ℝ)
    (h : ∀ x : E, RCLike.re (inner 𝕜 (T x) x) ≤ RCLike.re (inner 𝕜 (S x) x) + ε * ‖x‖ ^ 2) (j : Fin m) :
    hT.eigenvalues hn j ≤ hS.eigenvalues hn j + ε := by
  by_contra hlt
  push_neg at hlt
  set P := Submodule.span 𝕜 (hT.eigenvectorBasis hn '' ((Finset.Iic j : Finset (Fin m)) : Set (Fin m)))
  set R := Submodule.span 𝕜 (hS.eigenvectorBasis hn '' ((Finset.Ici j : Finset (Fin m)) : Set (Fin m)))
  have hPR : P ⊓ R = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxP, hxR⟩
    -- lower Rayleigh bound on `P`
    have h1 : hT.eigenvalues hn j * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x) x) := by
      rw [hT.re_inner_apply_eq_sum hn, ← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases hk : k ≤ j
      · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hk) (by positivity)
      · have : inner 𝕜 (hT.eigenvectorBasis hn k) (x) = 0 :=
          hT.inner_eigenvectorBasis_eq_zero_of_mem_span hn hxP (by simpa using hk)
        simp [this]
    -- upper Rayleigh bound on `R`
    have h2 : RCLike.re (inner 𝕜 (S x) x) ≤ hS.eigenvalues hn j * ‖x‖ ^ 2 := by
      rw [hS.re_inner_apply_eq_sum hn, ← (hS.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases hk : j ≤ k
      · exact mul_le_mul_of_nonneg_right (hS.eigenvalues_antitone hn hk) (by positivity)
      · have : inner 𝕜 (hS.eigenvectorBasis hn k) (x) = 0 :=
          hS.inner_eigenvectorBasis_eq_zero_of_mem_span hn hxR (by simpa using hk)
        simp [this]
    have h3 := h x
    have hx2 : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp this
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P R
  rw [hPR, finrank_bot, add_zero, hT.finrank_span_eigenvectorBasis hn,
    hS.finrank_span_eigenvectorBasis hn, Fin.card_Iic, Fin.card_Ici] at hdim
  have hle : finrank 𝕜 ↥(P ⊔ R) ≤ m := hn ▸ Submodule.finrank_le _
  omega

end LinearMap.IsSymmetric

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n 𝕜}

/-- **Weyl's inequality** for Hermitian matrices: if `A ≤ B + ε` as quadratic forms, then
`λⱼ(A) ≤ λⱼ(B) + ε` for the eigenvalues sorted in decreasing order. -/
theorem eigenvalues₀_le_add (hA : A.IsHermitian) (hB : B.IsHermitian) (ε : ℝ)
    (h : ∀ x : n → 𝕜, RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤
      RCLike.re (star x ⬝ᵥ (B *ᵥ x)) + ε * RCLike.re (star x ⬝ᵥ x))
    (j : Fin (Fintype.card n)) : hA.eigenvalues₀ j ≤ hB.eigenvalues₀ j + ε := by
  refine LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le _ _ _ ε (fun x => ?_) j
  have hx := h (WithLp.ofLp x)
  have key : ∀ M : Matrix n n 𝕜, RCLike.re (inner 𝕜 (Matrix.toEuclideanLin M x) x) =
      RCLike.re (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)) := by
    intro M
    rw [← inner_conj_symm, RCLike.conj_re, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm]
    rfl
  have hn : ‖x‖ ^ 2 = RCLike.re (star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x) := by
    rw [@norm_sq_eq_re_inner 𝕜, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hn]
  erw [key A, key B]
  exact hx

end Matrix.IsHermitian

open Matrix.IsHermitian

theorem solution {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) (ε : ℝ)
    (h : ∀ x : n → 𝕜, RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤
      RCLike.re (star x ⬝ᵥ (B *ᵥ x)) + ε * RCLike.re (star x ⬝ᵥ x))
    (j : Fin (Fintype.card n)) : hA.eigenvalues₀ j ≤ hB.eigenvalues₀ j + ε :=
  Matrix.IsHermitian.eigenvalues₀_le_add hA hB ε h j
