-- Prove2me | solution 1 for GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:22.7229+00:00
-- url     : https://prove2.me/submissions/7370811e-225a-4aa6-a941-99b5037f3d24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebraStatement
import Theorems.Thm_GlobalTheory_FinProjComplete_isAdicComplete_span_natCast_of_finite_projective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective | exact GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective <;> assumption)
end _root_.GlobalTheory.T
