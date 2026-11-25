-- Prove2me | solution 1 for GlobalTheory.PDivGroup.constHom_constGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:58.563147+00:00
-- url     : https://prove2.me/submissions/3ce6ff7b-7e7b-4dbc-a87e-59f90623b654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ToSpanSingletonConstGenSurjective

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
namespace GlobalTheory.PDivGroup
theorem _root_.solution : constHom _ (constGen p O) = 𝟙 _ := by
  rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id]
end GlobalTheory.PDivGroup
