-- Prove2me | solution 1 for GlobalTheory.CMType.card_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:11.820368+00:00
-- url     : https://prove2.me/submissions/3f384c80-aaea-42b5-95c3-cd0f424155e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)
namespace GlobalTheory.CMType
theorem _root_.solution [IsCMField E] :
    Fintype.card Φ = Module.finrank ℚ (maximalRealSubfield E) := by
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two _ E, ← Φ.two_mul_card] at h
  omega
end GlobalTheory.CMType
