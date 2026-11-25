-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.isPiSystem_smallCosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:23:59.708207+00:00
-- url     : https://prove2.me/submissions/b75ee40f-91eb-4e98-97ca-4ddd86247a51

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Measures_smul_coe_eq_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (K : Subgroup G)
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution : IsPiSystem (smallCosets K) := by
  rintro _ ⟨x, N₁, hN₁, rfl⟩ _ ⟨y, N₂, hN₂, rfl⟩ ⟨z, hz₁, hz₂⟩
  refine ⟨z, N₁ ⊓ N₂, ⟨hN₁.1.inter hN₂.1, inf_le_of_left_le hN₁.2.1,
    fun k hk w hw => ⟨hN₁.2.2 k hk w hw.1, hN₂.2.2 k hk w hw.2⟩⟩, ?_⟩
  rw [smul_coe_eq_of_mem hz₁, smul_coe_eq_of_mem hz₂, ← Set.smul_set_inter, Subgroup.coe_inf]
end GroundTheory.Automorphic.Measures
