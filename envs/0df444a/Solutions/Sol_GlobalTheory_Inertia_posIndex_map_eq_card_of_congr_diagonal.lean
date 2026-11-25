-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_map_eq_card_of_congr_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:56.778503+00:00
-- url     : https://prove2.me/submissions/e6e5c82a-f892-43fe-9190-4982b18e93b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_diagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_map_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution (τ : E →+* ℂ) {G P : Matrix n n E} {d : n → E}
    (hP : P.det ≠ 0) (hd : Pᵀ * G * P.map FD.cc = diagonal d) :
    posIndex (G.map τ) = (Finset.univ.filter fun k => 0 < (τ (d k)).re).card := by
  rw [← posIndex_map_congr τ G hP, hd, diagonal_map (map_zero τ), posIndex_diagonal]
end GlobalTheory.Inertia
