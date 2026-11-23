-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.mem_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:36.893376+00:00
-- url     : https://prove2.me/submissions/d91a4994-74d3-4bed-83d9-09732b0bc25a

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
theorem _root_.solution {H : Subgroup G} {v : V} : v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v :=
  ⟨fun hv h hh => by simpa using hv ⟨h, hh⟩, fun hv h => by simpa using hv h h.2⟩
end GlobalTheory.IwahoriInj
