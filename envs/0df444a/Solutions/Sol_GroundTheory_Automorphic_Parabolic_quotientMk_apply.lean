-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.quotientMk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:49.131916+00:00
-- url     : https://prove2.me/submissions/59479b09-bd6c-4970-ab3c-667dd940bad1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
  {τ : Representation ℂ G U}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)) (x : U) :
    quotientMk Y hY x = Submodule.Quotient.mk x := rfl
end GroundTheory.Automorphic.Parabolic
