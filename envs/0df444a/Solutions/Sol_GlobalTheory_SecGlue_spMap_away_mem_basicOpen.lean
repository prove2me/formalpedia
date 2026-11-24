-- Prove2me | solution 1 for GlobalTheory.SecGlue.spMap_away_mem_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:24.122795+00:00
-- url     : https://prove2.me/submissions/11259872-112d-4ba3-a55c-f8111a025722

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenCoverAffineOpenSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue
namespace GlobalTheory.SecGlue
theorem _root_.solution {S : Type} [CommRing S] (s : S)
    (x : Sp (Localization.Away s)) :
    (spMap (algebraMap S (Localization.Away s))).base x ∈ PrimeSpectrum.basicOpen s := by
  show algebraMap S (Localization.Away s) s ∉ x.asIdeal
  intro h
  exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
end GlobalTheory.SecGlue
