-- Prove2me | solution 1 for GlobalTheory.KernelComm.KK_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:44:33.040425+00:00
-- url     : https://prove2.me/submissions/ded61fa6-e468-477b-901d-f8c31b5710e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_valuation_det
import Theorems.Thm_GlobalTheory_KernelComm_KK_move
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser


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
theorem _root_.solution {t : ℕ} (ht : Fintype.card n = Fintype.card n' + (t + 1)) (q : Unif k) {φ : Form k n' V'}
    (hφ : φ ∈ EqForm π') {P : Pair k n'} {Q : Pair k n} (hP : P.ker = P₀.lat)
    (hQ : Q.ker = Q₀.lat) : KK hμ hθ P₀ Q₀ φ Q = scal k t • θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [Pair.smul_ker] at hP hQ
  rw [KK_move hμ hθ P₀ Q₀ hφ q.unit g h (valuation_det q _ hP) (valuation_det q _ hQ),
    nabs_uniformiser q.2 (x := q.unit) rfl, inv_inv, ht, scal]
  congr 4
  push_cast
  ring
end GlobalTheory.KernelComm
