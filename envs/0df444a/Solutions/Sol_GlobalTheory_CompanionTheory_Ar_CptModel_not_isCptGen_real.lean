-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.not_isCptGen_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:37.913451+00:00
-- url     : https://prove2.me/submissions/482d4393-41fd-415a-a028-02d39b8e89fa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_regAt_self
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
theorem _root_.solution : ¬ IsCptGen (pt (algebraMap ℤ ℝ)) := fun h => by
  have h1 : Real.sqrt 2 ∈ regAt _ (self (pt (algebraMap ℤ ℝ))) := by rw [regAt_self h]; trivial
  obtain ⟨a, s, -, h0, e⟩ := (mem_regAt_iff _ _ _).1 h1
  simp only [algebraMap_int_eq, eq_intCast] at h0 e
  exact irrational_sqrt_two ⟨(a : ℚ) / s, by push_cast; rw [← e, mul_div_cancel_right₀ _ h0]⟩
end GlobalTheory.CompanionTheory.Ar.CptModel
