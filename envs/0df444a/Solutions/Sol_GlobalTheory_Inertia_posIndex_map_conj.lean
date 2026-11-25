-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:10.988026+00:00
-- url     : https://prove2.me/submissions/aef018df-5b2f-4f17-844c-d36400a63b26

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
theorem _root_.solution {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    posIndex (G.map conj) = posIndex G := by
  obtain ⟨P, d, hP, hd, -⟩ := exists_congr_diagonal_real hG
  have hm : (P.map conj).det = conj P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  have hd' : (P.map conj)ᵀ * G.map conj * (P.map conj).map conj =
      diagonal (fun k => (d k : ℂ)) := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hd, diagonal_map (map_zero _)]
    simp
  rw [posIndex_eq_card_of_congr_diagonal hP hd,
    posIndex_eq_card_of_congr_diagonal (hm ▸ (map_ne_zero _).2 hP) hd']
end GlobalTheory.Inertia
