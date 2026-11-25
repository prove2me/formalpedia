-- Prove2me | solution 1 for GroundTheory.Automorphic.mulEquivHaarChar_conjCME_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:03.07782+00:00
-- url     : https://prove2.me/submissions/891b3850-62fe-466b-a299-c1fd8f3cc6ad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_conjCME_one
import Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution (a : G) :
    mulEquivHaarChar (conjCME a⁻¹) * mulEquivHaarChar (conjCME a) = 1 := by
  rw [← mulEquivHaarChar_conjCME_mul, inv_mul_cancel, conjCME_one, mulEquivHaarChar_refl]
end GroundTheory.Automorphic
