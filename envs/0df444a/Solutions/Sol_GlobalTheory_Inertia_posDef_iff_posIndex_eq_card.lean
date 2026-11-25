-- Prove2me | solution 1 for GlobalTheory.Inertia.posDef_iff_posIndex_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:56.247972+00:00
-- url     : https://prove2.me/submissions/438d2607-1f43-4924-ab5a-cbae1e604ca2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_eq_card_eigenvalues
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
open scoped ComplexOrder
namespace GlobalTheory.Inertia
theorem _root_.solution {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    G.PosDef ↔ posIndex G = Fintype.card n := by
  rw [hG.posDef_iff_eigenvalues_pos, posIndex_eq_card_eigenvalues hG, ← Finset.card_univ,
    Finset.card_filter_eq_iff]
  simp
end GlobalTheory.Inertia
