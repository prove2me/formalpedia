-- Prove2me | solution 1 for GroundTheory.Automorphic.mulEquivHaarChar_conjCME_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:09.351045+00:00
-- url     : https://prove2.me/submissions/aa4106a5-8aa5-4809-a92a-46bf0f35c1e1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_conjCME_mul

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
theorem _root_.solution (a b : G) :
    mulEquivHaarChar (conjCME (a * b)) =
      mulEquivHaarChar (conjCME a) * mulEquivHaarChar (conjCME b) := by
  rw [conjCME_mul, mulEquivHaarChar_trans, mul_comm]
end GroundTheory.Automorphic
