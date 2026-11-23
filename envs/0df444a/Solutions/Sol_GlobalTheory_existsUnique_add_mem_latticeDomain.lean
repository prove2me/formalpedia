-- Prove2me | solution 1 for GlobalTheory.existsUnique_add_mem_latticeDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:09.276274+00:00
-- url     : https://prove2.me/submissions/b8fb0cf5-2d0c-4b39-a14b-60712b5d23e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GlobalTheory
theorem _root_.solution (x : E) : ∃! a : L, x + a ∈ latticeDomain L := by
  have h := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) x
  have hs := (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L
  obtain ⟨⟨a, ha⟩, h1, h2⟩ := h
  refine ⟨⟨a, hs ▸ ha⟩, ?_, ?_⟩
  · simpa [latticeDomain, add_comm, Submodule.vadd_def] using h1
  · rintro ⟨b, hb⟩ hb'
    have := h2 ⟨b, hs.symm ▸ hb⟩ (by simpa [latticeDomain, add_comm, Submodule.vadd_def] using hb')
    exact Subtype.ext (by simpa using this)
end GlobalTheory
