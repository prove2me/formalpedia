-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.funcL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:49.310655+00:00
-- url     : https://prove2.me/submissions/489f7b91-ce26-47cc-b788-ebd75d7ceab7

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
variable [LocallyCompactSpace S] [CompactSpace (inter S K)]
variable (hS : IsClosed (S : Set G)) (hK : IsCompact (K : Set G)) (hSK : Surjective (mulMap S K))
include hS hK
variable (mL) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasure mL]
  [mL.IsMulLeftInvariant]
namespace GroundTheory.Automorphic.HaarSK
theorem _root_.solution (v : CompactlySupportedContinuousMap S ℝ) :
    funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v = ∫ g, lift hSK (flat mL v) g ∂μ := rfl
end GroundTheory.Automorphic.HaarSK
