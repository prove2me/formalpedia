-- Prove2me | solution 1 for IsOpen.exists_iUnion_isClosed_of_pseudoMetrizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:13:38.682219+00:00
-- url     : https://prove2.me/submissions/52944fbe-cedc-40a1-87ba-cf800fc5fb8a

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC

set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
namespace IsOpen
theorem _root_.solution
    {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] {U : Set X} (hU : IsOpen U) :
    ∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ U = ⋃ n, C n := by
  obtain ⟨T, hTopen, hTcount, hTeq⟩ := hU.isClosed_compl.isGδ
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · -- Uᶜ = ⋂₀ ∅ = univ, so U = ∅
    refine ⟨fun _ => ∅, fun _ => isClosed_empty, ?_⟩
    have : U = ∅ := by
      have h1 : Uᶜ = univ := by rw [hTeq, Set.sInter_empty]
      simpa [Set.compl_univ] using congrArg compl h1
    simp [this]
  · obtain ⟨f, rfl⟩ := hTcount.exists_eq_range hTne
    refine ⟨fun n => (f n)ᶜ, fun n =>
      (hTopen (f n) (Set.mem_range_self n)).isClosed_compl, ?_⟩
    have h1 : Uᶜ = ⋂ n, f n := by rw [hTeq, Set.sInter_range]
    calc U = Uᶜᶜ := (compl_compl U).symm
      _ = (⋂ n, f n)ᶜ := by rw [h1]
      _ = ⋃ n, (f n)ᶜ := by rw [Set.compl_iInter]
end IsOpen
