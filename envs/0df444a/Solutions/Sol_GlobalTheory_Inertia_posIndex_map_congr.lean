-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_map_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:59:19.173362+00:00
-- url     : https://prove2.me/submissions/8f12b287-5043-40eb-abb0-448fba2af8f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_congr
import Theorems.Thm_GlobalTheory_Inertia_det_map_ne_zero
import Theorems.Thm_GlobalTheory_Inertia_map_congr

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
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix n n E) {P : Matrix n n E} (hP : P.det ≠ 0) :
    posIndex ((Pᵀ * G * P.map FD.cc).map τ) = posIndex (G.map τ) := by
  rw [map_congr, posIndex_congr _ (det_map_ne_zero τ hP)]
end GlobalTheory.Inertia
