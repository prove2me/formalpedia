-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_add_negIndex_eq_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:54.402184+00:00
-- url     : https://prove2.me/submissions/5869f040-e228-4db7-8a19-eda7ad2aa0cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_card_of_congr_diagonal
import Theorems.Thm_GlobalTheory_Inertia_negIndex_eq_card_of_congr_diagonal
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
    posIndex G + negIndex G = G.rank := by
  obtain ⟨P, d, hP, hd, -⟩ := exists_congr_diagonal_real hG
  have hr : (Pᵀ * G * P.map conj).rank = G.rank := by
    rw [rank_mul_eq_left_of_isUnit_det, rank_mul_eq_right_of_isUnit_det]
    · rw [det_transpose]
      exact hP.isUnit
    · have hm : (P.map conj).det = conj P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
      rw [hm]
      exact ((map_ne_zero _).2 hP).isUnit
  rw [posIndex_eq_card_of_congr_diagonal hP hd, negIndex_eq_card_of_congr_diagonal hP hd, ← hr, hd,
    rank_diagonal, Fintype.card_subtype, ← Finset.card_union_of_disjoint, ← Finset.filter_or]
  · congr 1
    ext k
    simp [lt_or_lt_iff_ne, eq_comm]
  · rw [Finset.disjoint_filter]
    exact fun k _ h1 h2 => lt_asymm h1 h2
end GlobalTheory.Inertia
