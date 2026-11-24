-- Prove2me | solution 1 for GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:19.880357+00:00
-- url     : https://prove2.me/submissions/86a602df-8db9-41df-804a-bf1f0df86c20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
namespace GlobalTheory.WeilM.HaarUniq
namespace _root_.GlobalTheory.WeilM.HaarUniq
theorem _root_.solution [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] :
    ∃ K : OpenAddSubgroup V, IsCompact (K : Set V) := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  exact ⟨K, hC.of_isClosed_subset K.isClosed hK⟩
end _root_.GlobalTheory.WeilM.HaarUniq
end GlobalTheory.WeilM.HaarUniq
