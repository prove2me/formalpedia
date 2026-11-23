-- Prove2me | solution 1 for GlobalTheory.Inertia.le_card_of_mem_posDims
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:15.805485+00:00
-- url     : https://prove2.me/submissions/3b2a9ea6-e09f-4d20-b391-465de4cb7ed1

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
variable {n m : Type*} [Fintype n] [Fintype m]
namespace GlobalTheory.Inertia
theorem _root_.solution {G : Matrix n n ℂ} {d : ℕ} (hd : d ∈ posDims G) :
    d ≤ Fintype.card n := by
  obtain ⟨W, rfl, -⟩ := hd
  simpa using W.finrank_le
end GlobalTheory.Inertia
