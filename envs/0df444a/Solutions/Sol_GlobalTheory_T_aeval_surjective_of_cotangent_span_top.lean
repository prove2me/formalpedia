-- Prove2me | solution 1 for GlobalTheory.T.aeval_surjective_of_cotangent_span_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:14:30.624705+00:00
-- url     : https://prove2.me/submissions/ea755eea-b040-44cf-a33d-9c08486bb0f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalSurjectiveOfCotangentSpanTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalSurjectiveOfCotangentSpanTopStatement
import Theorems.Thm_GlobalTheory_NakAug_surj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first | exact @GlobalTheory.NakAug.surj | exact GlobalTheory.NakAug.surj | (intros; apply GlobalTheory.NakAug.surj <;> assumption)
end _root_.GlobalTheory.T
