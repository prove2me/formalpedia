-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.flat_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:34.4218+00:00
-- url     : https://prove2.me/submissions/80d6e3e3-2058-4510-a7d5-d329c56c0da6

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
variable {mL : Measure (inter S K)}
namespace GroundTheory.Automorphic.HaarSK
theorem _root_.solution [IsProbabilityMeasure mL] {u : S → ℝ}
    (hu : ∀ s, ∀ m ∈ inter S K, u (s * m) = u s) : flat mL u = u := by
  funext s
  simp only [flat]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun m : inter S K => hu s m m.2)]
  simp
end GroundTheory.Automorphic.HaarSK
