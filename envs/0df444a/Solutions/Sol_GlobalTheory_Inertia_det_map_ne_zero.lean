-- Prove2me | solution 1 for GlobalTheory.Inertia.det_map_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:19.375371+00:00
-- url     : https://prove2.me/submissions/6f259260-c949-4db3-b9a0-6a011f241beb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal

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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.Inertia
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (τ : E →+* ℂ) {G : Matrix n n E}
    (hG0 : G.det ≠ 0) : (G.map τ).det ≠ 0 := by
  have h : (G.map τ).det = τ G.det := (RingHom.map_det τ G).symm
  rw [h]
  exact (map_ne_zero τ).2 hG0
end GlobalTheory.Inertia
