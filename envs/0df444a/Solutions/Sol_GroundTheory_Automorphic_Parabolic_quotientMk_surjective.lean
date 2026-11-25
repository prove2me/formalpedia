-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.quotientMk_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:48:15.683876+00:00
-- url     : https://prove2.me/submissions/d3368a0c-4a25-4561-b1d2-06ccc2ce5fea

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
theorem _root_.solution (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)) :
    Function.Surjective (quotientMk Y hY) :=
  Submodule.mkQ_surjective Y
end GroundTheory.Automorphic.Parabolic
