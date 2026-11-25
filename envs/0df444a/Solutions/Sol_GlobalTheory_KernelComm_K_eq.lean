-- Prove2me | solution 1 for GlobalTheory.KernelComm.K_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:42.432046+00:00
-- url     : https://prove2.me/submissions/401e84ec-3cc5-4bd7-879c-ec66afde2efa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity

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
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)
namespace GlobalTheory.KernelComm
theorem _root_.solution (φ : EqForm π') : (K hμ hθ P₀ Q₀ φ).1 = KK hμ hθ P₀ Q₀ φ.1 := rfl
end GlobalTheory.KernelComm
