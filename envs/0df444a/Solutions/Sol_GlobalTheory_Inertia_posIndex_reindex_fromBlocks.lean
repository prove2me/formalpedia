-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_reindex_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:59.788574+00:00
-- url     : https://prove2.me/submissions/25593280-48e3-4f7a-ae66-d22af1e954d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_submatrix_equiv
import Theorems.Thm_GlobalTheory_Inertia_posIndex_fromBlocks

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
theorem _root_.solution {G : Matrix (Fin r) (Fin r) ℂ} {H : Matrix (Fin s) (Fin s) ℂ}
    (hG : G.IsHermitian) (hH : H.IsHermitian) :
    posIndex (reindex finSumFinEquiv finSumFinEquiv (fromBlocks G 0 0 H)) =
      posIndex G + posIndex H := by
  rw [reindex_apply, posIndex_submatrix_equiv, posIndex_fromBlocks hG hH]
end GlobalTheory.Inertia
