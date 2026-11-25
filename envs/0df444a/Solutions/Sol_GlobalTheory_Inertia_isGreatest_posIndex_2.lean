-- Prove2me | solution 2 for GlobalTheory.Inertia.isGreatest_posIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:06:55.078605+00:00
-- url     : https://prove2.me/submissions/7a93b368-e5bc-4362-ab05-1d36999186f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_zero_mem_posDims
import Theorems.Thm_GlobalTheory_Inertia_le_card_of_mem_posDims

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
theorem _root_.solution (G : Matrix n n ℂ) : IsGreatest (posDims G) (posIndex G) := by
  have hb : BddAbove (posDims G) := ⟨_, fun _ hd => le_card_of_mem_posDims hd⟩
  exact ⟨Nat.sSup_mem ⟨0, zero_mem_posDims G⟩ hb, fun _ hd => le_csSup hb hd⟩
end GlobalTheory.Inertia
