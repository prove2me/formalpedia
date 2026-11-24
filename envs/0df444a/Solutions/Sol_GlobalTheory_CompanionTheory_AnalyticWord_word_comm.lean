-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.word_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:25.728663+00:00
-- url     : https://prove2.me/submissions/bb0070cc-b3d3-4ed6-b281-561d199309f3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution (Z : ι → Module.End ℂ V) (Ω : Module.End ℂ V) (hΩ : ∀ i, Ω * Z i = Z i * Ω)
    (l : List ι) : Ω * word Z l = word Z l * Ω := by
  induction l with
  | nil => rw [GlobalTheory.CompanionTheory.AnalyticWord.word_nil, mul_one, one_mul]
  | cons i l ih => rw [GlobalTheory.CompanionTheory.AnalyticWord.word_cons, ← mul_assoc, hΩ, mul_assoc, ih, mul_assoc]
end GlobalTheory.CompanionTheory.AnalyticWord
