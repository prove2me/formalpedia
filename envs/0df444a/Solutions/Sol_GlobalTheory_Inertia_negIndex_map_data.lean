-- Prove2me | solution 1 for GlobalTheory.Inertia.negIndex_map_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:27.240461+00:00
-- url     : https://prove2.me/submissions/77e35e8d-ac68-4b43-b933-49669005ed9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg_eq_sub
import Theorems.Thm_GlobalTheory_Inertia_isHermitian_map
import Theorems.Thm_GlobalTheory_Inertia_det_map_ne_zero
import Theorems.Thm_GlobalTheory_Inertia_posIndex_map_data
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution (X : FD.Data E r) (τ : E →+* ℂ) :
    negIndex (X.Gm.map τ) = r - X.p0 := by
  rw [← posIndex_neg,
    posIndex_neg_eq_sub (isHermitian_map τ X.Gm_herm) (det_map_ne_zero τ X.Gm_det),
    posIndex_map_data, Fintype.card_fin]
end GlobalTheory.Inertia
