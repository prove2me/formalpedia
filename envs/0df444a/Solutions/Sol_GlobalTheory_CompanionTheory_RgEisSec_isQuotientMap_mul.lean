-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisSec.isQuotientMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:04:48.997486+00:00
-- url     : https://prove2.me/submissions/25601d16-5d2a-4e00-9b07-52b7e80ca0b0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds
import Theorems.Thm_UpperTheory_Reformulated_B_DYhc7_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisSec
variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.CompanionTheory.RgEisSec
theorem _root_.solution [IsTopologicalGroup G] {K P : Subgroup G} (hK : IsCompact (K : Set G))
    (hP : IsClosed (P : Set G)) (hI : Iwa P K) :
    Topology.IsQuotientMap (fun x : P × K => (x.1 : G) * (x.2 : G)) :=
  _root_.UpperTheory.Reformulated.B.DYhc7.main hK hP hI
end GlobalTheory.CompanionTheory.RgEisSec
