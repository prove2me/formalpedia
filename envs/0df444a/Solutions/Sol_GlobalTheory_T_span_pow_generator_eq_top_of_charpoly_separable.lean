-- Prove2me | solution 1 for GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:50.203818+00:00
-- url     : https://prove2.me/submissions/d216c12b-74cd-4aa7-92e9-f3ee812b2d95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanPowGeneratorEqTopOfCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanPowGeneratorEqTopOfCharpolySeparableStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_span_pow_eq_top_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  first | exact @GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable | exact GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable | (intros; apply GlobalTheory.UnitLemma.Unr.span_pow_eq_top_of_separable <;> assumption)
end _root_.GlobalTheory.T
