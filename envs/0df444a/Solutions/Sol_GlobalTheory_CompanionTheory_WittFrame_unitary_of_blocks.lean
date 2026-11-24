-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WittFrame.unitary_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:47.248793+00:00
-- url     : https://prove2.me/submissions/39185cf8-1391-4db6-a895-33d70af8dd45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryExtensionOfBlock
import Theorems.Thm_GlobalTheory_CompanionTheory_WittFrame_block_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WittFrame
namespace GlobalTheory.CompanionTheory.WittFrame
theorem _root_.solution {n D m : ℕ} (C H : Matrix (Fin n) (Fin D) ℂ)
    (G : Matrix (Fin n) (Fin m) ℂ)
    (hCC : Cᴴ * C = 1) (hCG : Cᴴ * G = 0) (hCH : Cᴴ * H = 0) (hGG : Gᴴ * G = 1)
    (hGH : Gᴴ * H = 0) (hHH : Hᴴ * H = 1) (hcard : D + (m + D) = n) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ)
      (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ),
      s * C = C * b → s * G = G * t → s * H = H * b' → b.BlockTriangular id →
      t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  have hGC : Gᴴ * C = 0 := by
    have := congrArg conjTranspose hCG
    simpa [conjTranspose_mul] using this
  have hHC : Hᴴ * C = 0 := by
    have := congrArg conjTranspose hCH
    simpa [conjTranspose_mul] using this
  have hHG : Hᴴ * G = 0 := by
    have := congrArg conjTranspose hGH
    simpa [conjTranspose_mul] using this
  set E : Matrix (Fin n) (Fin D ⊕ (Fin m ⊕ Fin D)) ℂ := fromCols C (fromCols G H) with hEdef
  have hE : Eᴴ * E = 1 := by
    rw [hEdef, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, fromRows_mul,
      fromRows_mul, mul_fromCols, mul_fromCols, mul_fromCols, fromRows_fromCols_eq_fromBlocks,
      hCC, hCG, hCH, hGC, hGG, hGH, hHC, hHG, hHH, fromCols_zero, fromRows_zero, fromBlocks_one,
      fromBlocks_one]
  have hT : Fintype.card (FrameIdx D m) = n := by
    rw [← hcard]
    simp [Fintype.card_congr (frameEquiv D m)]
  let g : Fin n ≃ Fin D ⊕ (Fin m ⊕ Fin D) :=
    (Fintype.orderIsoFinOfCardEq (FrameIdx D m) hT).toEquiv.trans (frameEquiv D m)
  refine ⟨E.submatrix id g, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (E.submatrix id g)ᴴ * E.submatrix id g = 1
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ g id g Function.bijective_id, hE,
      submatrix_one_equiv]
  · intro s b b' t h1 h2 h3 hb ht hb'
    have hs : s * E = E * fromBlocks b 0 0 (fromBlocks t 0 0 b') := by
      rw [hEdef, mul_fromCols, mul_fromCols, h1, h2, h3, fromCols_mul_fromBlocks,
        fromCols_mul_fromBlocks]
      simp
    have hΔ : Eᴴ * s * E = fromBlocks b 0 0 (fromBlocks t 0 0 b') := by
      rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, hE, Matrix.one_mul]
    have hM : (E.submatrix id g)ᴴ * s * E.submatrix id g =
        (fromBlocks b 0 0 (fromBlocks t 0 0 b')).submatrix g g := by
      rw [← hΔ, submatrix_mul _ _ g id g Function.bijective_id,
        submatrix_mul _ _ g id id Function.bijective_id, submatrix_id_id,
        conjTranspose_submatrix]
    rw [hM]
    intro x y hxy
    exact block_zero b b' t hb ht hb' _ _ ((Fintype.orderIsoFinOfCardEq (FrameIdx D m) hT).lt_iff_lt.2 hxy)
end GlobalTheory.CompanionTheory.WittFrame
