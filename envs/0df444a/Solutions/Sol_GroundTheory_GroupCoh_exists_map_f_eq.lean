-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_map_f_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:57:20.988915+00:00
-- url     : https://prove2.me/submissions/5c9869a4-abac-4a2b-84d2-97284741cda9

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)
include hX
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ) (x : groupCohomology X.X₂ n)
    (hx : map (MonoidHom.id H) X.g n x = 0) : ∃ w, map (MonoidHom.id H) X.f n w = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (mapShortComplex₂_exact hX n) x hx
end GroundTheory.GroupCoh
