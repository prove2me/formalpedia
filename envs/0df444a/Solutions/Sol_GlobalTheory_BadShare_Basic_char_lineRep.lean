-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.char_lineRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:00:14.441721+00:00
-- url     : https://prove2.me/submissions/eed9281f-8479-4f17-9353-0de5af592953

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution (χ : (ZMod g)ˣ →* ℂˣ) (γ : GG g N) :
    (FDRep.of (lineRep χ)).character γ = ((χ (Matrix.GeneralLinearGroup.det γ) : ℂˣ) : ℂ) := by
  change LinearMap.trace ℂ ℂ (((χ (Matrix.GeneralLinearGroup.det γ) : ℂˣ) : ℂ) • LinearMap.id) = _
  simp
end GlobalTheory.BadShare.Basic
