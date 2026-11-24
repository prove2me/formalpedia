-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobProd.isLocallyConstant_pattern
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:57.675582+00:00
-- url     : https://prove2.me/submissions/a2708183-24a4-4b3d-8792-cfb537919fe4

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
open Classical
namespace GlobalTheory.CompanionTheory.FrobProd
theorem _root_.solution {X ι : Type} [TopologicalSpace X] [Fintype ι] {U : ι → Set X}
    (hU : ∀ i, IsClopen (U i)) :
    IsLocallyConstant (fun x => Finset.univ.filter (fun i => x ∈ U i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : ∀ᶠ y in nhds x, ∀ i, (y ∈ U i ↔ x ∈ U i) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hx : x ∈ U i
    · filter_upwards [(hU i).isOpen.mem_nhds hx] with y hy
      exact iff_of_true hy hx
    · filter_upwards [(hU i).compl.isOpen.mem_nhds hx] with y hy
      exact iff_of_false hy hx
  filter_upwards [h] with y hy
  ext i
  simp [hy i]
end GlobalTheory.CompanionTheory.FrobProd
