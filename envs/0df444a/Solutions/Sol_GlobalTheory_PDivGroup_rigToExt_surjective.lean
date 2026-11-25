-- Prove2me | solution 1 for GlobalTheory.PDivGroup.rigToExt_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:04:09.92615+00:00
-- url     : https://prove2.me/submissions/bd816881-14bf-4bc8-90d7-3229c743f72e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)
namespace GlobalTheory.PDivGroup
theorem _root_.solution : Function.Surjective G.rigToExt := fun x => by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  exact ⟨G.rigMk (c, 0), rfl⟩
end GlobalTheory.PDivGroup
