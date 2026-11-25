-- Prove2me | solution 1 for GroundTheory.ProfCoh.subsingleton_groupCohomology_galois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:40.129659+00:00
-- url     : https://prove2.me/submissions/ba94deff-504d-42a8-abe5-f30fc9afa66a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_AdditiveHilbert
import Theorems.Thm_GroundTheory_ProfCoh_isZero_groupCohomology_galois

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
    Subsingleton (groupCohomology (Rep.ofDistribMulAction K Gal(L/K) L) n) :=
  ModuleCat.subsingleton_of_isZero (isZero_groupCohomology_galois K L hn)
end GroundTheory.ProfCoh
