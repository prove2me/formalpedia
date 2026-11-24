-- Prove2me | solution 1 for GlobalTheory.KernelComm.KK_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:44:28.23514+00:00
-- url     : https://prove2.me/submissions/7e8e2d70-0c8a-4ac0-9072-c2d9edc0c907

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_KK_move
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one


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
theorem _root_.solution {φ : Form k n' V'} (hφ : φ ∈ EqForm π') {P : Pair k n'} {Q : Pair k n} (hP : P.lat = P₀.lat)
    (hQ : Q.lat = Q₀.lat) : KK hμ hθ P₀ Q₀ φ Q = θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [KK_move hμ hθ P₀ Q₀ hφ 1 g h (by simpa only [mul_one] using valuation_det_of_fix _ hP)
    (by simpa only [mul_one] using valuation_det_of_fix _ hQ)]
  simp [nabs_one]
end GlobalTheory.KernelComm
