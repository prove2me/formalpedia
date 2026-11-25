-- Prove2me | solution 1 for GlobalTheory.Inertia.negIndex_eq_card_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:22.507734+00:00
-- url     : https://prove2.me/submissions/320f1212-d98b-42f6-8fda-75fbafc3b26b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_eq_card_of_congr_diagonal
import Theorems.Thm_GlobalTheory_Inertia_exists_congr_diagonal_eigenvalues
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
    negIndex G = (Finset.univ.filter fun k => hG.eigenvalues k < 0).card := by
  obtain ⟨P, hP, hd⟩ := exists_congr_diagonal_eigenvalues hG
  rw [negIndex_eq_card_of_congr_diagonal hP hd]
  simp
end GlobalTheory.Inertia
