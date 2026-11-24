-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertDoubling.isInt_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:06:32.818636+00:00
-- url     : https://prove2.me/submissions/ad6317cf-3490-41c8-bd76-870ad4d757a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.CompanionTheory.InertDoubling
theorem _root_.solution {m₁ m₂ p₁ p₂ : Type} {A : Matrix m₁ p₁ L} {B : Matrix m₁ p₂ L} {C : Matrix m₂ p₁ L}
    {D : Matrix m₂ p₂ L} (hA : IsInt A) (hB : IsInt B) (hC : IsInt C) (hD : IsInt D) : IsInt (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j
end GlobalTheory.CompanionTheory.InertDoubling
