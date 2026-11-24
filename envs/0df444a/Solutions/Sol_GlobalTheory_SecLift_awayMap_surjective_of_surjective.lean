-- Prove2me | solution 1 for GlobalTheory.SecLift.awayMap_surjective_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:29.426062+00:00
-- url     : https://prove2.me/submissions/5aec6faf-9b8a-453c-9044-c66774413bc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_SmLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSectionLiftBasicOpenAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecLift
variable {R R₀ : Type} [CommRing R] [CommRing R₀]
namespace GlobalTheory.SecLift
theorem _root_.solution (π : R →+* R₀) (hπ : Function.Surjective π) (f : R) :
    Function.Surjective (Localization.awayMap π f) :=
  Localization.awayMap_surjective_iff.2 fun a =>
    (hπ a).elim fun b hb => ⟨b, 0, by simp [hb]⟩
end GlobalTheory.SecLift
