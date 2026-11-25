-- Prove2me | solution 1 for GlobalTheory.HermWitt.congr_of_fromBlocks_congr_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:50.087733+00:00
-- url     : https://prove2.me/submissions/38c00f97-fe90-4d11-a939-4aa271bac2ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_congr_of_fromBlocks_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.HermWitt
theorem _root_.solution {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {D : Matrix m m E} (hD : ∀ a b, FD.cc (D a b) = D b a)
    (hdet : D.det ≠ 0) {G₁ G₂ : Matrix n n E} (hG : ∀ a b, FD.cc (G₁ a b) = G₁ b a)
    {P : Matrix (m ⊕ n) (m ⊕ n) E} (hP : P.det ≠ 0)
    (h : fromBlocks D 0 0 G₂ = Pᵀ * fromBlocks D 0 0 G₁ * P.map FD.cc) :
    ∃ Q : Matrix n n E, Q.det ≠ 0 ∧ G₂ = Qᵀ * G₁ * Q.map FD.cc :=
  congr_of_fromBlocks_congr (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hD hdet hG hP h
end GlobalTheory.HermWitt
