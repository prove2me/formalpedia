-- Prove2me | solution 1 for GlobalTheory.KernelCommTw.KK_FFStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:13.863834+00:00
-- url     : https://prove2.me/submissions/1ef6e237-88b0-418b-964c-a9d28d4c01d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
import Theorems.Thm_GlobalTheory_KernelCommTw_FFStar_KK
import Theorems.Thm_GlobalTheory_KernelComm_FFStar_KK


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
theorem _root_.solution (hl' : IsUnram l') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π')
    (h : φ ∈ Mram k n' V') :
    KK hl hθ P₀ Q₀ (FFStar q χ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q χ (KK hl hθ P₀ Q₀ φ) := by
  rw [FFStar_KK hl hθ P₀ Q₀ hl' q χ hφ h, smul_smul, mul_inv_cancel₀ (mul_ne_zero (Units.ne_zero _)
    (Units.ne_zero _)), one_smul]
end GlobalTheory.KernelCommTw
