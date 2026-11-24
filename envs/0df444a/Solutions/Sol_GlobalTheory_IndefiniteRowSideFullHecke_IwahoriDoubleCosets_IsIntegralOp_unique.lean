-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:54:08.405012+00:00
-- url     : https://prove2.me/submissions/cdd19924-d1dd-4f19-86a0-22e868b93a17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BorelCasselman
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
variable {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
namespace IsIntegralOp
theorem _root_.solution {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {A B : V →ₗ[ℂ] V}
    (hA : IsIntegralOp μ π f A) (hB : IsIntegralOp μ π f B) : A = B := by
  ext v
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, (hA v l).2, (hB v l).2, sub_self]
end IsIntegralOp
end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
