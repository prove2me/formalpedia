-- Prove2me | solution 1 for GroundTheory.Automorphic.HaarSK.isMulLeftInvariant_rmk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:49.335594+00:00
-- url     : https://prove2.me/submissions/b0ebe353-6aa4-41f1-b5ff-388924e50d69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_funcL_translate
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_integral_rmk

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
theorem _root_.solution : (rmk mL hS hK hSK μ).IsMulLeftInvariant := by
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  constructor
  intro s₀
  have : IsFiniteMeasureOnCompacts (map (s₀ * ·) (rmk mL hS hK hSK μ)) :=
    IsFiniteMeasureOnCompacts.map _ (Homeomorph.mulLeft s₀)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro v
  rw [integral_map (measurable_const_mul s₀).aemeasurable (map_continuous v).aestronglyMeasurable]
  have h := integral_rmk mL hS hK hSK μ (translate s₀ v)
  rw [funcL_translate, ← integral_rmk] at h
  exact h
end GroundTheory.Automorphic.HaarSK
