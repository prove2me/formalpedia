-- Prove2me | solution 1 for GlobalTheory.RowFubini.finiteIndex_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:14.976801+00:00
-- url     : https://prove2.me/submissions/18bf0af3-94d3-4668-860d-deac9899ba67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
namespace GlobalTheory.RowFubini
theorem _root_.solution (H L : Subgroup G) (hH : IsOpen (H : Set G))
    (hL : IsCompact (L : Set G)) : (H.subgroupOf L).FiniteIndex := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((H.subgroupOf L : Subgroup L) : Set L) :=
    hH.preimage continuous_subtype_val
  have : Finite (L ⧸ H.subgroupOf L) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient
end GlobalTheory.RowFubini
