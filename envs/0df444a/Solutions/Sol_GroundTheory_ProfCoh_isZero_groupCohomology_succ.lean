-- Prove2me | solution 1 for GroundTheory.ProfCoh.isZero_groupCohomology_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:46.503981+00:00
-- url     : https://prove2.me/submissions/0a946111-c3fa-4d39-982e-39d698e95fca

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_AdditiveHilbert

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
theorem _root_.solution (n : ℕ) :
    IsZero (groupCohomology (Rep.ofDistribMulAction k Gal(L/K) L) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton
      (Rep.trivial k (⊥ : Subgroup Gal(L/K)) K) n).of_iso
    ((groupCohomology.functor k Gal(L/K) (n + 1)).mapIso (galoisCoindIso k K L) ≪≫
      groupCohomology.coindIso _ (n + 1))
end GroundTheory.ProfCoh
