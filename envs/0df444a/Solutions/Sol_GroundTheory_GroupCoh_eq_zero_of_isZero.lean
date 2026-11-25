-- Prove2me | solution 1 for GroundTheory.GroupCoh.eq_zero_of_isZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:29:53.168105+00:00
-- url     : https://prove2.me/submissions/184a6118-8dff-48f2-9054-5da8e8686d18

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
namespace GroundTheory.GroupCoh
theorem _root_.solution {A : ModuleCat.{u} k} (h : IsZero A) (x : A) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero h).elim x 0
end GroundTheory.GroupCoh
