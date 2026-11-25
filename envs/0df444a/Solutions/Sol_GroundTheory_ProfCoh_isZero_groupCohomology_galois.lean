-- Prove2me | solution 1 for GroundTheory.ProfCoh.isZero_groupCohomology_galois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:58.469132+00:00
-- url     : https://prove2.me/submissions/2a821a1c-6773-49fa-be80-e3e1255630ba

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_AdditiveHilbert
import Theorems.Thm_GroundTheory_ProfCoh_isZero_groupCohomology

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
open CategoryTheory CategoryTheory.Limits
universe u
open groupCohomology
variable (k : Type u) (K L : Type u) [CommRing k] [Field K] [Field L] [Algebra K L]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L] [IsGalois K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    IsZero (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) :=
  isZero_groupCohomology K K L hn
end GroundTheory.ProfCoh
