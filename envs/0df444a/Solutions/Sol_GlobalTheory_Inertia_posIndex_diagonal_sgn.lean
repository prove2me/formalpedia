-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_diagonal_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:22:34.439725+00:00
-- url     : https://prove2.me/submissions/35e9fa7d-8075-4eb1-8e6f-45165144ed91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_diagonal
import Theorems.Thm_GlobalTheory_Inertia_card_filter_sgn_pos
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
variable {r s : ℕ}
namespace GlobalTheory.Inertia
theorem _root_.solution {p : ℕ} (hp : p ≤ r) :
    posIndex (diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) = p := by
  rw [posIndex_diagonal]
  simpa only [Complex.ofReal_re] using card_filter_sgn_pos hp
end GlobalTheory.Inertia
