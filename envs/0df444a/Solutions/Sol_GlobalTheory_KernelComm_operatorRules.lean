-- Prove2me | solution 1 for GlobalTheory.KernelComm.operatorRules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:43.381918+00:00
-- url     : https://prove2.me/submissions/6905ef61-727e-49a7-ae70-bfbde3f04959

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_U_KK
import Theorems.Thm_GlobalTheory_KernelComm_KK_dia
import Theorems.Thm_GlobalTheory_KernelComm_KK_ram
import Theorems.Thm_GlobalTheory_KernelComm_FFStar_KK
import Theorems.Thm_GlobalTheory_KernelComm_FF_KK
import Theorems.Thm_GlobalTheory_LatPair_resChar_ne_one


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
theorem _root_.solution : OperatorRules :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ht q _ hψ _ hμ _ _ _ _ _ _ _ _ _ _ _ _ hθ P₀ Q₀ =>
    ⟨fun φ => U_KK hμ hθ P₀ Q₀ ht q φ.2, fun s φ => KK_dia hμ hθ P₀ Q₀ s φ.2, fun φ h =>
      ⟨KK_ram hμ hθ P₀ Q₀ φ.2 h, FF_KK hμ hθ P₀ Q₀ ht q (resChar_ne_one hψ q) φ.2 h,
        FFStar_KK hμ hθ P₀ Q₀ ht q _ φ.2 h⟩⟩
end GlobalTheory.KernelComm
