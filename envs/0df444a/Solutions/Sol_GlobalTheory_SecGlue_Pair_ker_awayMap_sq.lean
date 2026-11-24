-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.ker_awayMap_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:15.094142+00:00
-- url     : https://prove2.me/submissions/9f87d654-bfc6-40e8-af7b-15593f2eadd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
import Theorems.Thm_GlobalTheory_SecGlue_Pair_ker_awayMap

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
theorem _root_.solution {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hsq : RingHom.ker π ^ 2 = ⊥) (c : R) : RingHom.ker (Localization.awayMap π c) ^ 2 = ⊥ := by
  rw [ker_awayMap, ← Ideal.map_pow, hsq, Ideal.map_bot]
end GlobalTheory.SecGlue.Pair
