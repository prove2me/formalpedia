-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.inv_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:59.8978+00:00
-- url     : https://prove2.me/submissions/8e59bb19-771d-42ac-983c-7404c2b786c9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {G : Type*} [Group G] (g : G) (K : Subgroup G) :
    (doubleCoset g (K : Set G) K)⁻¹ = doubleCoset g⁻¹ (K : Set G) K := by
  ext x
  rw [Set.mem_inv, mem_doubleCoset, mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨b⁻¹, K.inv_mem hb, a⁻¹, K.inv_mem ha, by rw [← inv_inv x, h]; group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b⁻¹, K.inv_mem hb, a⁻¹, K.inv_mem ha, by group⟩
end GroundTheory.Automorphic.Measures
