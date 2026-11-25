-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.translate_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:53.295892+00:00
-- url     : https://prove2.me/submissions/d7f87ea6-fb73-4240-a709-2e539c9b4b98

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.HaarSK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {S K : Subgroup G}
variable (hSK : Surjective (mulMap S K))
variable {hSK}
variable [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
namespace GroundTheory.Automorphic.HaarSK
theorem _root_.solution (s₀ : S) (v : CompactlySupportedContinuousMap S ℝ) (s : S) :
    translate s₀ v s = v (s₀ * s) := rfl
end GroundTheory.Automorphic.HaarSK
