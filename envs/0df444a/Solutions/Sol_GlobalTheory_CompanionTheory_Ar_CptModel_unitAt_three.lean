-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.unitAt_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:21.274467+00:00
-- url     : https://prove2.me/submissions/9d2cb6b6-4209-4ab2-bf6d-9ba5845542b7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_mem_regAt_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution : unitAt _ two (3 : ℚ) := by
  have h : ∀ n : ℤ, ¬ (2 : ℤ) ∣ n → n ∉ two.1.asIdeal := fun n hn hm =>
    hn (Ideal.mem_span_singleton.1 hm)
  refine ⟨by norm_num, (mem_regAt_iff _ _ _).2 ⟨3, 1, h 1 (by decide), by simp, by simp⟩,
    (mem_regAt_iff _ _ _).2 ⟨1, 3, h 3 (by decide), by simp, by simp⟩⟩
end GlobalTheory.CompanionTheory.Ar.CptModel
