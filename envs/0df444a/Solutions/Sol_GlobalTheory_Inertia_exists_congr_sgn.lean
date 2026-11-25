-- Prove2me | solution 1 for GlobalTheory.Inertia.exists_congr_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:50.293338+00:00
-- url     : https://prove2.me/submissions/6770fe85-d1c1-4c18-9c04-0d71b21c0d8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_exists_congr_diagonal_of_card_eq
import Theorems.Thm_GlobalTheory_Inertia_sgn_ne_zero
import Theorems.Thm_GlobalTheory_Inertia_card_filter_sgn_pos
import Theorems.Thm_GlobalTheory_Inertia_posIndex_le

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
variable {r s : ℕ}
namespace GlobalTheory.Inertia
theorem _root_.solution {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0) :
    ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn (posIndex G) a : ℝ) : ℂ) :=
  exists_congr_diagonal_of_card_eq hG hG0 (fun _ => sgn_ne_zero _ _)
    (card_filter_sgn_pos (posIndex_le G))
end GlobalTheory.Inertia
