-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.tateMatch_not_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:28.580669+00:00
-- url     : https://prove2.me/submissions/b434e135-c767-4275-aa97-efcddf7389bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
namespace GlobalTheory.Ex.TateInh
theorem _root_.solution (r : ℂˣ) : ¬ (tateMatch (r ^ 3 ^ 1) 3 (by decide)).B (AddEquiv.neg ℤ) := by
  intro h
  obtain ⟨z, hz⟩ := h 1 (tateQ r _ 1) (tateQ r _ 1) (((tate _).qEq_equivalence _).refl _)
  have key : ∀ w : ℤ, ¬ (1 : ℤ) = -1 + (3 ^ 1 : ℕ) • w := fun w => by
    simp only [nsmul_eq_mul]; push_cast; omega
  exact key z hz
end GlobalTheory.Ex.TateInh
