-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.integral_rmk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:49.165807+00:00
-- url     : https://prove2.me/submissions/7e455459-3ec0-4fa4-955b-6db94fa8e1ba

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
variable {mL : Measure (inter S K)} [LocallyCompactSpace S] [CompactSpace (inter S K)]
  [IsFiniteMeasure mL] [mL.IsMulLeftInvariant]
  {hS : IsClosed (S : Set G)} {hK : IsCompact (K : Set G)} {hSK : Surjective (mulMap S K)}
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
variable (mL hS hK hSK μ)
namespace GroundTheory.Automorphic.HaarSK
theorem _root_.solution (v : CompactlySupportedContinuousMap S ℝ) :
    ∫ s, v s ∂rmk mL hS hK hSK μ = funcL (mL := mL) (hS := hS) (hK := hK) (hSK := hSK) (μ := μ) v :=
  RealRMK.integral_rieszMeasure _ v
end GroundTheory.Automorphic.HaarSK
