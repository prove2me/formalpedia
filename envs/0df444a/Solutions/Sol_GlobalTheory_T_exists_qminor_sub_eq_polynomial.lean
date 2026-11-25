-- Prove2me | solution 1 for GlobalTheory.T.exists_qminor_sub_eq_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:19.880521+00:00
-- url     : https://prove2.me/submissions/393c6d48-8130-4068-b996-2667dfb70a8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorPolyMap
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorPolyMapStatement
import Theorems.Thm_GlobalTheory_qminor_polyMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (s : ℂ), ∃ c : ℕ → A, ∀ u : ℂ, qminor E a b (u - s) = ∑ i ∈ Finset.range (t + 1), u ^ i • c i := by
  first | exact @GlobalTheory.qminor_polyMap | exact GlobalTheory.qminor_polyMap | (intros; apply GlobalTheory.qminor_polyMap <;> assumption)
end _root_.GlobalTheory.T
