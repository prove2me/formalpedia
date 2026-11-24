-- Prove2me | solution 1 for GlobalTheory.KernelCommTw.KK_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:42.898949+00:00
-- url     : https://prove2.me/submissions/ebbd28f6-7a02-42c2-b99a-e2f6a3bb3434

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
import Theorems.Thm_GlobalTheory_KernelCommTw_unram_val
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_smul
import Theorems.Thm_GlobalTheory_KernelComm_KK_smul
import Theorems.Thm_GlobalTheory_LatPair_phiOne_smul


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
variable (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)
namespace GlobalTheory.KernelCommTw
theorem _root_.solution (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (u : kˣ) (g : GL n' k) (h : GL n k)
    (hg : valuation k ((Matrix.GeneralLinearGroup.det g * u : kˣ) : k) = 1)
    (hh : valuation k ((Matrix.GeneralLinearGroup.det h * u : kˣ) : k) = 1) :
    KK hl hθ P₀ Q₀ φ (h • Q₀) = ((l' u : ℂ) * (l u : ℂ))⁻¹ • θ (φ (g • P₀)) (phiOneSB (g • P₀) (h • Q₀)) := by
  rw [KK_smul, hφ g, ← map_smul]
  refine (hθ g h _ _ _ fun x => ?_).symm
  simp only [phiOneSB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, phiOne_smul, unram_val hl' u _ hg,
    unram_val hl u _ hh]
  rw [mul_inv]
end GlobalTheory.KernelCommTw
