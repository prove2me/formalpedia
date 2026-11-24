-- Prove2me | solution 1 for GlobalTheory.SmGL.IndCoinv.smIndMap_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:33.323799+00:00
-- url     : https://prove2.me/submissions/ca4c93f3-2cc1-494e-a031-cbe4827d446a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
import Theorems.Thm_GlobalTheory_SmGL_IndDual_bump_mul
import Theorems.Thm_GlobalTheory_SmGL_IndDual_bump_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndCoinv
variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}
namespace GlobalTheory.SmGL.IndCoinv
theorem _root_.solution (β : σ.IntertwiningMap ρ) {J : Subgroup G} (hJ : IsOpen (J : Set G))
    (w : fixed σ (J.subgroupOf P)) (v : fixed ρ (J.subgroupOf P)) (hv : β w = v) :
    smIndMap β (bump σ hJ w) = bump ρ hJ v := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  show β ((bump σ hJ w).1.1 g) = _
  rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
  · rw [bump_zero _ _ _ h, bump_zero _ _ _ h, map_zero]
  · rw [bump_mul _ _ _ _ hj, bump_mul _ _ _ _ hj, β.isIntertwining, hv]
end GlobalTheory.SmGL.IndCoinv
