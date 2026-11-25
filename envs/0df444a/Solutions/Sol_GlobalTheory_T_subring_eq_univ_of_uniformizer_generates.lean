-- Prove2me | solution 1 for GlobalTheory.T.subring_eq_univ_of_uniformizer_generates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:42.865896+00:00
-- url     : https://prove2.me/submissions/17635960-233d-4688-94bb-da056ccfea1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrSubringEqTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrSubringEqTopStatement
import Theorems.Thm_GlobalTheory_dvrSubring_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (S : Subring V) (π : V), π ∈ S → π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V → (∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1) → (∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) → (∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) → S = ⊤ := by
  first | exact @GlobalTheory.dvrSubring_eq_top | exact GlobalTheory.dvrSubring_eq_top | (intros; apply GlobalTheory.dvrSubring_eq_top <;> assumption)
end _root_.GlobalTheory.T
