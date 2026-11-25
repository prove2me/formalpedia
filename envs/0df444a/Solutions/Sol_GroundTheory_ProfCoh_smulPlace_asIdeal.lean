-- Prove2me | solution 1 for GroundTheory.ProfCoh.smulPlace_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:37.037487+00:00
-- url     : https://prove2.me/submissions/fe8bcf42-10b5-40e1-971e-a030229f6728

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise
variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]
omit [IsDedekindDomain B]
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : G) (w : HeightOneSpectrum B) :
    (smulPlace σ w).asIdeal = σ • w.asIdeal :=
  rfl
end GroundTheory.ProfCoh
