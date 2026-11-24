-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.smooth_strHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:16.147803+00:00
-- url     : https://prove2.me/submissions/8a28f208-f255-4c2c-860f-a71369a366bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Pair
namespace GlobalTheory.SecGlue.Pair
theorem _root_.solution {R : Type} [CommRing R] (X : Over (Sp R)) [Smooth X.hom] {V : X.left.Opens}
    (hV : IsAffineOpen V) : (strHom X V).Smooth := by
  have h1 : RingHom.Smooth (X.hom.appLE ⊤ V le_top).hom :=
    X.hom.smooth_appLE (isAffineOpen_top (Sp R)) hV le_top
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  exact h2.comp h1
end GlobalTheory.SecGlue.Pair
