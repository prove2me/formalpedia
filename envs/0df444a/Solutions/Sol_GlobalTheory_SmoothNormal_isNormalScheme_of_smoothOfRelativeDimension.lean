-- Prove2me | solution 1 for GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:34.010432+00:00
-- url     : https://prove2.me/submissions/feaf65af-fee5-4546-9ebb-40d44b7f491c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalSchemeOfSmoothOverNormal
import Theorems.Thm_GlobalTheory_forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.SmoothNormal
namespace GlobalTheory.SmoothNormal
theorem _root_.solution :
    ∀ (B Y : Scheme.{0}) [IsLocallyNoetherian B] (π : Y ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n π],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro B Y _ π n _ hB
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  exact GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth π hB
end GlobalTheory.SmoothNormal
