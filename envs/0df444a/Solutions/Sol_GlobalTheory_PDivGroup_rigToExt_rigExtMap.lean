-- Prove2me | solution 1 for GlobalTheory.PDivGroup.rigToExt_rigExtMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:18.601812+00:00
-- url     : https://prove2.me/submissions/5160c7e8-1a7a-43ad-ad82-a5ad6cad8c22

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
variable {G H K}
variable [Fact p.Prime]
namespace GlobalTheory.PDivGroup
theorem _root_.solution (f : G ⟶ H) (x : H.RigExt) :
    G.rigToExt (rigExtMap f x) = vecExtMap f (H.rigToExt x) := by
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl
end GlobalTheory.PDivGroup
