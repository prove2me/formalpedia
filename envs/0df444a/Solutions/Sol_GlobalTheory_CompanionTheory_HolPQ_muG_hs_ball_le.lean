-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolPQ.muG_hs_ball_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:19:01.726564+00:00
-- url     : https://prove2.me/submissions/cce408c1-62f7-49c6-a80c-8a1da7228726

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_OneAddHsInvPowLintegralLtTop
import Theorems.Thm_Formalism_REAL_volume_growth
import Theorems.Thm_UpperTheory_Reformulated_B_placeRankTwoOne_volume_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset PI.UpqRep
open scoped InnerProductSpace ENNReal ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolPQ
namespace GlobalTheory.CompanionTheory.HolPQ
theorem _root_.solution (n : ℕ) (ε : Fin n → Bool) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      muG ε {g | hs (umat g) ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2)) :=
  Formalism.REAL.volume_growth n ε
end GlobalTheory.CompanionTheory.HolPQ
