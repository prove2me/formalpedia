-- Prove2me | solution 1 for GlobalTheory.ExtendRig.isRegularRing_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:51.076953+00:00
-- url     : https://prove2.me/submissions/f1bebfdc-91ac-4bc6-8a86-e2e99e339976

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExtendRig
namespace GlobalTheory.ExtendRig
theorem _root_.solution {B : Type} [CommRing B] [IsRegularRing B]
    (M : Submonoid B) (R : Type) [CommRing R] [Algebra B R] [IsLocalization M R] :
    IsRegularRing R := by
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing M R inferInstance
  rw [isRegularRing_iff]
  intro q hq
  have h : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap B R)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (q.comap (algebraMap B R)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap B R))) (Localization.AtPrime q)).toRingEquiv
end GlobalTheory.ExtendRig
