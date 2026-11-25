-- Prove2me | solution 1 for GlobalTheory.PDivGroup.toSpanSingleton_constGen_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:36.459832+00:00
-- url     : https://prove2.me/submissions/431d5bb9-f0f6-4943-ad75-c48e1c4f182e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ToSpanSingletonConstGenSurjective
import Theorems.Thm_GlobalTheory_PDivGroup_toSpanSingleton_constGen_surjective
import Theorems.Thm_GlobalTheory_PDivGroup_toSpanSingleton_constGen_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
variable (p : ℕ) (O : Type) [CommRing O] [Fact p.Prime]
variable [Nontrivial O]
namespace GlobalTheory.PDivGroup
theorem _root_.solution
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) :=
  ⟨toSpanSingleton_constGen_injective p O, toSpanSingleton_constGen_surjective p O hO⟩
end GlobalTheory.PDivGroup
