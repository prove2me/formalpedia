-- Prove2me | solution 1 for GlobalTheory.KernelCommTw.KK_ram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:41:19.34087+00:00
-- url     : https://prove2.me/submissions/2809a826-d2e3-4a81-ab7b-ce949e0fe03d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_dia
import Theorems.Thm_GlobalTheory_KernelComm_KK_dia


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
theorem _root_.solution (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') :
    KK hl hθ P₀ Q₀ φ ∈ Mram k n V := by
  have : Nm (KK hl hθ P₀ Q₀ φ) = KK hl hθ P₀ Q₀ (Nm φ) := by
    simp only [Nm, LinearMap.sum_apply, map_sum, KK_dia hl hθ P₀ Q₀ hl' _ hφ]
  rw [show Nm φ = 0 from h, map_zero] at this
  exact this
end GlobalTheory.KernelCommTw
