-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IntCount.finite_and_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:24.135613+00:00
-- url     : https://prove2.me/submissions/da6a30d1-8ff1-49c8-904f-b0219b8e19ef

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FiniteAndNcardBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegersBoundedArchimedeanCount
import Theorems.Thm_UpperTheory_Reformulated_B_FiniteAndNcardBound_finite_and_ncard_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding Module
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IntCount
namespace GlobalTheory.CompanionTheory.IntCount
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E], ∃ (C : ℝ) (N : ℕ), ∀ R : ℝ, 1 ≤ R →
      {r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.Finite ∧
      ({r : 𝓞 E | ∀ w : InfinitePlace E, w (r : E) ≤ R}.ncard : ℝ) ≤ C * R ^ N :=
  _root_.UpperTheory.Reformulated.B.FiniteAndNcardBound.finite_and_ncard_le
end GlobalTheory.CompanionTheory.IntCount
