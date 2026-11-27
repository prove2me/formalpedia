-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.lift_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:40.651286+00:00
-- url     : https://prove2.me/submissions/1686b7ec-ce6d-462c-9a89-ebb93ad9014c

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
namespace GroundTheory.Automorphic.HaarSK
theorem _root_.solution {u : S → ℝ} (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s) (s : S) (k : K) :
    lift hSK u ((s : G) * k) = u s :=
  lift_mulMap hu (s, k)
end GroundTheory.Automorphic.HaarSK
