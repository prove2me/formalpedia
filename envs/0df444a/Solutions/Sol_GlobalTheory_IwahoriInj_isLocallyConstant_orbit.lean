-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.isLocallyConstant_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:02.164804+00:00
-- url     : https://prove2.me/submissions/b450bda9-80e3-4028-a941-efdd33e30a50

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
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution (hπ : IsSmooth π) (v : V) : IsLocallyConstant fun g : G => π g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g v = v}) := (hπ v).preimage (by fun_prop)
  filter_upwards [h.mem_nhds (show x ∈ _ by simp)] with g hg
  have hg' : π (x⁻¹ * g) v = v := hg
  conv_rhs => rw [← hg']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
end GlobalTheory.IwahoriInj
