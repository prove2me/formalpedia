-- Prove2me | solution 1 for Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:11.372058+00:00
-- url     : https://prove2.me/submissions/5be98d92-c668-4f8d-a25a-469aed7e82f4

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Mathlib.Analysis.Matrix.PosDef
public import Definitions.Def_LeanPool_DistanceGeometry_SchoenbergHard
public import Theorems.Thm_DistanceGeometry_centeredGram_apply
public import Theorems.Thm_DistanceGeometry_sqDistMatrix_apply
attribute [local simp] DistanceGeometry.centeredGram_apply
attribute [local simp] DistanceGeometry.sqDistMatrix_apply


section
@[expose] public section
open Matrix
open scoped RealInnerProductSpace
namespace Matrix
variable {n k : ℕ}
section Factorization
variable {G : Matrix (Fin n) (Fin n) ℝ}
private theorem psd_factor_full (hG : G.PosSemidef)
    {N : Matrix (Fin n) (Fin n) ℝ}
    (hNdef : N = diagonal (fun r => Real.sqrt (hG.1.eigenvalues r))
      * (hG.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᴴ) :
    Nᴴ * N = G := by
  classical
  set hH := hG.1 with hHdef
  set s : Fin n → ℝ := fun r => Real.sqrt (hH.eigenvalues r) with hs
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  rw [hNdef]
  -- `s r * s r = eigenvalues r` because eigenvalues of a PSD matrix are nonneg
  have hssμ : (fun r => s r * s r) = hH.eigenvalues := by
    funext r
    rw [hs]
    exact Real.mul_self_sqrt (hG.eigenvalues_nonneg r)
  -- spectral theorem in `U D Uᴴ` form
  have hspec : G = U * diagonal hH.eigenvalues * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
    -- `RCLike.ofReal ∘ eigenvalues = eigenvalues` over ℝ
    have hcoe : (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℝ) = hH.eigenvalues := by
      rw [RCLike.ofReal_real_eq_id]; rfl
    rw [hcoe] at h
    exact h
  -- expand the factorization
  rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  -- star s = s since ℝ has trivial star
  have hstars : (star s : Fin n → ℝ) = s := by funext r; exact star_trivial _
  rw [hstars, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s) (diagonal s) Uᴴ,
      diagonal_mul_diagonal, hssμ]
  conv_rhs => rw [hspec, Matrix.mul_assoc]
end Factorization
section Scatter
variable {p : Fin n → Prop} [DecidablePred p]
private theorem scatter_conjTranspose_mul_self (ι : {r : Fin n // p r} ↪ Fin k) :
    (scatter ι)ᴴ * scatter ι = diagonal (fun r => if p r then (1 : ℝ) else 0) := by
  classical
  ext r r'
  rw [mul_apply]
  simp only [conjTranspose_apply, scatter, star_trivial, diagonal_apply]
  by_cases hr : p r
  · by_cases hr' : p r'
    · -- both in support: sum collapses via injectivity
      simp only [hr, hr', dif_pos]
      -- product of two indicators, summed over the column index
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ (ι ⟨r', hr'⟩)
        (fun x => if ι ⟨r, hr⟩ = x then (1 : ℝ) else 0)]
      simp only [Finset.mem_univ, ite_true, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
    · -- r in support, r' not: diagonal entry is 0, sum is 0
      have hrr' : r ≠ r' := fun h => hr' (h ▸ hr)
      simp [hr', hrr']
  · -- r not in support: everything 0
    simp [hr]
end Scatter
namespace PosSemidef
variable {G : Matrix (Fin n) (Fin n) ℝ}
end PosSemidef
end Matrix
namespace DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n k : ℕ} [NeZero n]
end DistanceGeometry
end
end

set_option autoImplicit true
@[expose] public section
public section
open Matrix
open scoped RealInnerProductSpace
open Matrix
variable {n k : ℕ}
open Matrix.PosSemidef
variable {G : Matrix (Fin n) (Fin n) ℝ}
namespace Matrix.PosSemidef
theorem _root_.solution (hG : G.PosSemidef) (hrank : G.rank ≤ k) :
    ∃ M : Matrix (Fin k) (Fin n) ℝ, Mᴴ * M = G := by
  classical
  set hH := hG.1 with hHdef
  set μ := hH.eigenvalues with hμ
  set s : Fin n → ℝ := fun r => Real.sqrt (μ r) with hs
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  set N : Matrix (Fin n) (Fin n) ℝ := diagonal s * Uᴴ with hN
  -- the full factorization `Nᴴ * N = G`
  have hNG : Nᴴ * N = G := psd_factor_full hG (by rw [hN, hs, hU, hμ])
  -- support predicate and injection into `Fin k`
  have hcard : Fintype.card {r : Fin n // μ r ≠ 0} ≤ Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    rw [← hH.rank_eq_card_non_zero_eigs]
    exact hrank
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  -- scatter matrix and the candidate `M`
  set S : Matrix (Fin k) (Fin n) ℝ := scatter (p := fun r => μ r ≠ 0) ι with hSdef
  refine ⟨S * N, ?_⟩
  -- `Sᴴ * S = diagonal indic`, and `diagonal indic * N = N`
  have hSS : Sᴴ * S = diagonal (fun r => if μ r ≠ 0 then (1 : ℝ) else 0) :=
    scatter_conjTranspose_mul_self ι
  have hdiagN : diagonal (fun r => if μ r ≠ 0 then (1 : ℝ) else 0) * N = N := by
    ext r j
    rw [diagonal_mul]
    by_cases hr : μ r ≠ 0
    · simp [hr]
    · simp only [hr, ite_false, zero_mul]
      -- row `r` of `N` is zero because `s r = √0 = 0`
      have hμ0 : μ r = 0 := not_not.mp hr
      have hsr : s r = 0 := by rw [hs]; simp [hμ0]
      rw [hN, diagonal_mul, hsr, zero_mul]
  -- assemble: `(S*N)ᴴ * (S*N) = Nᴴ * (Sᴴ*S) * N = Nᴴ * N = G`
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Sᴴ S N, hSS, hdiagN, hNG]
end Matrix.PosSemidef
