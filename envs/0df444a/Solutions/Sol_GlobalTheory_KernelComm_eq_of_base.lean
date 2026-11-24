-- Prove2me | solution 1 for GlobalTheory.KernelComm.eq_of_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:07.623826+00:00
-- url     : https://prove2.me/submissions/697ef297-f305-4975-9199-e073fcabba71

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
theorem _root_.solution {φ φ' : Form k n V} (h : φ ∈ EqForm π) (h' : φ' ∈ EqForm π) (e : φ Q₀ = φ' Q₀) : φ = φ' := by
  ext Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [h g, h' g, e]
end GlobalTheory.KernelComm
