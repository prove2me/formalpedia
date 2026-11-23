-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.twKer_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:49.821933+00:00
-- url     : https://prove2.me/submissions/c426134b-fafd-43d3-a894-22b748a85213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_sub_mem_twKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
namespace GlobalTheory.IwahoriInj
theorem _root_.solution {H K : Subgroup G} (hle : H ≤ K) : twKer π H 1 ≤ twKer π K 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, v, rfl⟩
  simpa using sub_mem_twKer (hle h.2) v
end GlobalTheory.IwahoriInj
