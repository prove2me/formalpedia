-- Prove2me | solution 1 for Matrix.det_eq_corner_mul_det_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:54.073099+00:00
-- url     : https://prove2.me/submissions/f8937e97-6d52-4e87-8127-024fe5772774

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Determinant
public import Definitions.Def_BasicResults_Determinant

set_option autoImplicit true
@[expose] public section
public section
open LinearMap
open scoped ComplexConjugate
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
namespace Matrix
theorem _root_.solution {R : Type*} [CommRing R] {k : ℕ}
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (w : Fin k → R)
    (hw : ∀ i : Fin k, M i.castSucc (Fin.last k)
      = ∑ j, M i.castSucc j.castSucc * w j) :
    M.det = (M (Fin.last k) (Fin.last k) - ∑ j, M (Fin.last k) j.castSucc * w j)
      * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  classical
  -- The coefficients of the column operation: keep the last column, subtract
  -- `wⱼ` times the `j`-th one.
  set c : Fin (k + 1) → R := Fin.lastCases 1 (fun j => -w j) with hc
  have hclast : c (Fin.last k) = 1 := by rw [hc]; simp
  have hccast : ∀ j : Fin k, c j.castSucc = -w j := fun j => by rw [hc]; simp
  -- The column obtained from the operation.
  have hcol : ∀ r : Fin (k + 1), (∑ i, c i • M r i)
      = M r (Fin.last k) - ∑ j, M r j.castSucc * w j := by
    intro r
    rw [Fin.sum_univ_castSucc, hclast, one_smul]
    have hterm : ∀ j : Fin k,
        c j.castSucc • M r j.castSucc = -(M r j.castSucc * w j) := by
      intro j
      rw [hccast j, neg_smul, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib]
    ring
  -- The matrix after the column operation; its determinant is unchanged.
  set M' := M.updateCol (Fin.last k) (fun r => ∑ i, c i • M r i) with hM'
  have hMM' : M'.det = M.det := by
    rw [hM', Matrix.det_updateCol_sum, hclast, one_smul]
  have hlastcol : ∀ r, M' r (Fin.last k)
      = M r (Fin.last k) - ∑ j, M r j.castSucc * w j := fun r => by
    rw [hM', Matrix.updateCol_self, hcol r]
  -- The last column of `M'` vanishes above the corner.
  have hzero : ∀ i : Fin k, M' i.castSucc (Fin.last k) = 0 := fun i => by
    rw [hlastcol, hw i, sub_self]
  -- The top-left block is unchanged.
  have hsub : M'.submatrix Fin.castSucc Fin.castSucc
      = M.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hM',
      Matrix.updateCol_ne (Fin.castSucc_lt_last j).ne]
  -- Laplace expansion along the last column of `M'`.
  have hsign : ((-1 : R)) ^ ((Fin.last k : ℕ) + (Fin.last k : ℕ)) = 1 := by
    rw [Fin.val_last]
    exact Even.neg_one_pow ⟨k, rfl⟩
  rw [← hMM', Matrix.det_succ_column M' (Fin.last k),
    Finset.sum_eq_single (Fin.last k)
      (fun i _ hi => by
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [hzero i', mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h),
    hsign, one_mul, Fin.succAbove_last, hsub, hlastcol]
end Matrix
