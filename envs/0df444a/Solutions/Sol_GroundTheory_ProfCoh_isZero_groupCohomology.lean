-- Prove2me | solution 1 for GroundTheory.ProfCoh.isZero_groupCohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:16.148109+00:00
-- url     : https://prove2.me/submissions/426c83fb-bfd3-4c1e-bce1-3d8185de2f8f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_AdditiveHilbert
import Theorems.Thm_GroundTheory_ProfCoh_isZero_groupCohomology_succ

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
    IsZero (groupCohomology (Rep.ofDistribMulAction k Gal(L/K) L) n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_groupCohomology_succ k K L m
end GroundTheory.ProfCoh
