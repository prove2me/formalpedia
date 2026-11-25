-- Prove2me | solution 1 for GlobalTheory.BadShare.EpsProj.pow_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:57.142827+00:00
-- url     : https://prove2.me/submissions/1ff47bd9-c14a-44e1-8175-3ab74e0e9c35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SubgroupCharacterIdempotentProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.EpsProj
variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}
omit [Fintype G]
namespace GlobalTheory.BadShare.EpsProj
theorem _root_.solution (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (n : ℕ) :
    S (u ^ n) ∧ χ (u ^ n) = χ u ^ n := by
  induction n with
  | zero => simp [h1, c1]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ⟨hm _ _ ih.1 hu, by rw [cm _ _ ih.1 hu, ih.2]⟩
end GlobalTheory.BadShare.EpsProj
