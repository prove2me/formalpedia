-- Prove2me | solution 1 for GlobalTheory.RegularFactorial.isRegularRing_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:11:20.22638+00:00
-- url     : https://prove2.me/submissions/52a2bb82-d2f5-44e5-9b25-0fb915a3deb8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_UniqueFactorizationMonoidOfIsRegularRingOfIsLoca

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
open GlobalTheory
open GlobalTheory.RegularFactorial
open IsLocalRing
namespace GlobalTheory.RegularFactorial
theorem _root_.solution {R : Type*} [CommRing R] [IsRegularRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsRegularRing S := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  rw [isRegularRing_iff]
  intro P hP
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime P) P
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (P.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (P.comap (algebraMap R S))) (Localization.AtPrime P)).toRingEquiv
end GlobalTheory.RegularFactorial
