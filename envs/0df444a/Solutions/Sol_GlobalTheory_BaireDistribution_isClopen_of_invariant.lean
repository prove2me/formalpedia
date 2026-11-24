-- Prove2me | solution 1 for GlobalTheory.BaireDistribution.isClopen_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:23.86101+00:00
-- url     : https://prove2.me/submissions/5772e306-94af-4da7-9f62-c927969adff8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BaireDistribution
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.BaireDistribution
theorem _root_.solution {K : Subgroup G} (hK : IsOpen (K : Set G)) {C : Set G}
    (hC : ∀ a ∈ K, ∀ b ∈ K, ∀ g, a * g * b ∈ C ↔ g ∈ C) : IsClopen C := by
  have aux : ∀ S : Set G, (∀ a ∈ K, ∀ g ∈ S, a * g ∈ S) → IsOpen S := by
    intro S hS
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun y => y * g⁻¹) ⁻¹' K, fun y hy => ?_, hK.preimage (by fun_prop), by simp⟩
    simpa using hS _ hy g hg
  refine ⟨isOpen_compl_iff.1 (aux _ fun a ha g hg h => hg ?_), aux _ fun a ha g hg => ?_⟩
  · exact (hC a ha 1 K.one_mem g).1 (by simpa using h)
  · simpa using (hC a ha 1 K.one_mem g).2 hg
end GlobalTheory.BaireDistribution
