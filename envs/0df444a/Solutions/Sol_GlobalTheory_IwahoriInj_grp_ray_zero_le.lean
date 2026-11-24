-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.grp_ray_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:28.982063+00:00
-- url     : https://prove2.me/submissions/799d65c6-1e80-449d-accc-e2911b4a35b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_deep_one_iff

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
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable {g f f' : n → n → ℤ} {i j : n}
variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL n k) V}
variable [LinearOrder n]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution : grp k (chamber_ray (n := n) 0).1 ≤ iwahori k n := fun x hx => by
  have h0 : ∀ i j : n, 0 ≤ ray 0 i j := fun i j => by simp only [ray]; split_ifs <;> simp
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff x).2
    ⟨fun i j => deep_zero_iff.1 ((hx.1 i j).mono (h0 i j)),
      fun i j => deep_zero_iff.1 ((hx.2 i j).mono (h0 i j))⟩, fun i j h => ?_⟩
  exact deep_one_iff.1 ((hx.1 i j).mono (by simp [ray, h]))
end GlobalTheory.IwahoriInj
