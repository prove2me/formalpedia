-- Prove2me | solution 1 for GlobalTheory.LatticeBoundTests.trBil_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:51.307412+00:00
-- url     : https://prove2.me/submissions/ba485feb-5c38-4f59-8772-d142e72c8f81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited
import Theorems.Thm_GlobalTheory_LatticeBoundTests_trBil_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBoundTests
open NumberField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.LatticeBoundTests
theorem _root_.solution (x y : 𝓞 E) : trBil E x y = trBil E y x := by
  rw [trBil_apply, trBil_apply]
  exact Finset.sum_congr rfl fun σ _ => by simp [mul_comm]
end GlobalTheory.LatticeBoundTests
