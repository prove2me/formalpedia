-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.borel_eq_generateFrom_smallCosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:09:28.090874+00:00
-- url     : https://prove2.me/submissions/c588f283-85a8-4c14-8c13-f866c069b69e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures

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
variable {K}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution
    (hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : Subgroup G, IsSmallNormal K N ∧ (N : Set G) ⊆ U) :
    ‹MeasurableSpace G› = MeasurableSpace.generateFrom (smallCosets K) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · rw [BorelSpace.measurable_eq (α := G)]
    refine MeasurableSpace.generateFrom_le fun U hU => ?_
    let ι := {q : G × Subgroup G // IsSmallNormal K q.2 ∧ q.1 • (q.2 : Set G) ⊆ U}
    let s : ι → Set G := fun q => q.1.1 • (q.1.2 : Set G)
    have hU' : U = ⋃ q, s q := by
      refine Subset.antisymm (fun y hy => ?_) (iUnion_subset fun q => q.2.2)
      have : y⁻¹ • U ∈ 𝓝 (1 : G) := by
        refine (hU.smul y⁻¹).mem_nhds ?_
        exact ⟨y, hy, inv_mul_cancel y⟩
      obtain ⟨N, hN, hNU⟩ := hN _ this
      refine mem_iUnion.2 ⟨⟨(y, N), hN, ?_⟩, ⟨1, N.one_mem, mul_one y⟩⟩
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨u, hu, hua⟩ := hNU ha
      rw [← hua]
      show y * (y⁻¹ * u) ∈ U
      rw [mul_inv_cancel_left]
      exact hu
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable s fun q => q.2.1.1.smul _
    rw [hU', ← hT]
    exact MeasurableSet.biUnion hTc fun q _ =>
      MeasurableSpace.measurableSet_generateFrom ⟨q.1.1, q.1.2, q.2.1, rfl⟩
  · rintro _ ⟨x, N, hN, rfl⟩
    exact (hN.1.smul x).measurableSet
end GroundTheory.Automorphic.Measures
