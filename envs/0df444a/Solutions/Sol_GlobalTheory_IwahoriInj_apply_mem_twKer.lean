-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.apply_mem_twKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:51.324928+00:00
-- url     : https://prove2.me/submissions/2fc89ff2-65bd-4878-8675-6d312b8f080c

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
theorem _root_.solution {H : Subgroup G} {h : G} (hh : h ∈ H) {v : V} (hv : v ∈ twKer π H 1) :
    π h v ∈ twKer π H 1 := by
  simpa using add_mem (sub_mem_twKer hh v) hv
end GlobalTheory.IwahoriInj
