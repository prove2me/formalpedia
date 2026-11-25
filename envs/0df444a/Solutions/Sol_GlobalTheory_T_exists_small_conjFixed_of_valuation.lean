-- Prove2me | solution 1 for GlobalTheory.T.exists_small_conjFixed_of_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:17:49.026414+00:00
-- url     : https://prove2.me/submissions/d3e9f545-dff4-48eb-a56f-8aee5a0d5026

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuationStatement
import Theorems.Thm_GlobalTheory_UnitLemma_exists_small_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (k : ℕ), 1 ≤ k → ∃ t : K.O, K.Small t ∧ GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k := by
  first | exact @GlobalTheory.UnitLemma.exists_small_val | exact GlobalTheory.UnitLemma.exists_small_val | (intros; apply GlobalTheory.UnitLemma.exists_small_val <;> assumption)
end _root_.GlobalTheory.T
