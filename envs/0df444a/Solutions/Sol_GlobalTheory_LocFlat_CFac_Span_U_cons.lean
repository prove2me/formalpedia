-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.Span.U_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:18.0858+00:00
-- url     : https://prove2.me/submissions/f69baa22-2083-4a1b-84d5-f8cc4bd05271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SpanSchwartzBruhatProductEqTop
import Theorems.Thm_GlobalTheory_LocFlat_CFac_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocFlat.CFac.mulLC_apply



set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac GlobalTheory.LocFlat.CFac.Span
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace GlobalTheory.LocFlat.CFac.Span
theorem _root_.solution (r : Set X × Set Y) (L : List (Set X × Set Y)) : U (r :: L) = r.1 ×ˢ r.2 ∪ U L := by
  simp [U]
end GlobalTheory.LocFlat.CFac.Span
