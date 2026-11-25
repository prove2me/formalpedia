-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:44.045335+00:00
-- url     : https://prove2.me/submissions/8b3d0ad7-8532-4f57-962f-0eead259a837

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_card_of_congr_diagonal
import Theorems.Thm_GlobalTheory_Inertia_exists_congr_diagonal_real
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
variable [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution [DecidableEq m] {G : Matrix n n ℂ} {H : Matrix m m ℂ}
    (hG : G.IsHermitian) (hH : H.IsHermitian) :
    posIndex (fromBlocks G 0 0 H) = posIndex G + posIndex H := by
  obtain ⟨P, d, hP, hd, -⟩ := exists_congr_diagonal_real hG
  obtain ⟨Q, e, hQ, he, -⟩ := exists_congr_diagonal_real hH
  have h : (fromBlocks P 0 0 Q)ᵀ * fromBlocks G 0 0 H * (fromBlocks P 0 0 Q).map conj =
      diagonal (Sum.elim (fun k => (d k : ℂ)) (fun k => (e k : ℂ))) := by
    rw [← fromBlocks_diagonal, ← hd, ← he, fromBlocks_transpose, fromBlocks_map,
      fromBlocks_multiply, fromBlocks_multiply]
    simp
  have hdet : (fromBlocks P 0 0 Q).det ≠ 0 := by
    rw [det_fromBlocks_zero₂₁]
    exact mul_ne_zero hP hQ
  rw [posIndex_eq_card_of_congr_diagonal hdet h, posIndex_eq_card_of_congr_diagonal hP hd,
    posIndex_eq_card_of_congr_diagonal hQ he]
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  rfl
end GlobalTheory.Inertia
