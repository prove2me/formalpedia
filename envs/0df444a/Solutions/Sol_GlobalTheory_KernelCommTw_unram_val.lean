-- Prove2me | solution 1 for GlobalTheory.KernelCommTw.unram_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:24.414877+00:00
-- url     : https://prove2.me/submissions/8c3d70e7-650d-4438-ac14-3e5a93c495d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
open GlobalTheory GlobalTheory.KernelCommTw
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
variable {l' l : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
namespace GlobalTheory.KernelCommTw
theorem _root_.solution {χ : kˣ →* ℂˣ} (hχ : IsUnram χ) (u z : kˣ) (hz : valuation k ((z * u : kˣ) : k) = 1) :
    (χ z : ℂ) = (χ u : ℂ)⁻¹ := by
  have := congrArg (fun w : ℂˣ => (w : ℂ)) (hχ _ hz)
  simp only [map_mul, Units.val_mul, Units.val_one] at this
  exact eq_inv_of_mul_eq_one_left this
end GlobalTheory.KernelCommTw
