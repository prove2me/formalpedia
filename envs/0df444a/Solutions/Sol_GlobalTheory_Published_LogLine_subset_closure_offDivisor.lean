-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.subset_closure_offDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:21:50.221516+00:00
-- url     : https://prove2.me/submissions/75cf873d-48aa-4ece-aa93-8c06d761102e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}
namespace GlobalTheory.Published.LogLine
theorem _root_.solution {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) :
    U ⊆ closure (offDivisor U S) := by
  have hd : Dense (Set.pi univ fun _ : Fin n => ({0}ᶜ : Set ℂ)) :=
    dense_pi univ fun _ _ => dense_compl_singleton 0
  refine (hd.open_subset_closure_inter hU).trans (closure_mono ?_)
  rintro z ⟨hz, hz'⟩
  exact ⟨hz, fun i _ => hz' i (mem_univ i)⟩
end GlobalTheory.Published.LogLine
