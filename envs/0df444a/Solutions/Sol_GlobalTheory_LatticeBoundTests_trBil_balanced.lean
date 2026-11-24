-- Prove2me | solution 1 for GlobalTheory.LatticeBoundTests.trBil_balanced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:49.587814+00:00
-- url     : https://prove2.me/submissions/b5fdb380-9dc2-4a33-a323-73289249c058

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
namespace GlobalTheory.LatticeBoundTests
theorem _root_.solution (c c' : 𝓞 E) (hc : (c' : E) = IsCMField.complexConj E c) (x y : 𝓞 E) :
    trBil E (c • x) y = trBil E x (c' • y) := by
  rw [trBil_apply, trBil_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h : σ (c' : E) = starRingEnd ℂ (σ (c : E)) := by
    rw [hc]; exact IsCMField.complexEmbedding_complexConj E σ _
  rw [smul_eq_mul, smul_eq_mul]
  push_cast
  rw [map_mul, map_mul, h, map_mul, Complex.conj_conj]
  congr 1; ring
end GlobalTheory.LatticeBoundTests
