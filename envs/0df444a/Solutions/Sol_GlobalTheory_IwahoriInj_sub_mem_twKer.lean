-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.sub_mem_twKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:35.655065+00:00
-- url     : https://prove2.me/submissions/2b1d5495-0bcd-4bdd-88b8-bddcfebb702a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit

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
theorem _root_.solution {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : π h v - v ∈ twKer π H 1 :=
  Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩
end GlobalTheory.IwahoriInj
