-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobProd.exists_compact_clopen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:21.858021+00:00
-- url     : https://prove2.me/submissions/cdb68f65-7228-40e0-a1b4-aa52aa07e77e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobProd
namespace GlobalTheory.CompanionTheory.FrobProd
theorem _root_.solution {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] {x : X} {u : Set X} (hu : IsOpen u) (hx : x ∈ u) :
    ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ u := by
  obtain ⟨K, hK, hxK, hKu⟩ := exists_compact_subset hu hx
  obtain ⟨V, hV, hxV, hVK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := X)).exists_subset_of_mem_open
    hxK isOpen_interior
  have hVK' : V ⊆ K := hVK.trans interior_subset
  exact ⟨V, hK.of_isClosed_subset hV.isClosed hVK', hV, hxV, hVK'.trans hKu⟩
end GlobalTheory.CompanionTheory.FrobProd
