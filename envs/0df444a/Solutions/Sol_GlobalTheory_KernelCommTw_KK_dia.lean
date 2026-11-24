-- Prove2me | solution 1 for GlobalTheory.KernelCommTw.KK_dia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:23:34.9838+00:00
-- url     : https://prove2.me/submissions/b575e391-5f51-4a32-91cc-9c259626ed6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_mem
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_same
import Theorems.Thm_GlobalTheory_KernelComm_KK_mem
import Theorems.Thm_GlobalTheory_KernelComm_KK_same
import Theorems.Thm_GlobalTheory_KernelComm_eq_of_base
import Theorems.Thm_GlobalTheory_LatPair_dia_mem_EqForm
import Theorems.Thm_GlobalTheory_LatPair_phiOne_dia


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
theorem _root_.solution (hl' : IsUnram l') (s : 𝓀[k]ˣ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    KK hl hθ P₀ Q₀ (dia s φ) = dia s (KK hl hθ P₀ Q₀ φ) := by
  refine GlobalTheory.KernelComm.eq_of_base Q₀ (KK_mem hl hθ P₀ Q₀ _) (dia_mem_EqForm s (KK_mem hl hθ P₀ Q₀ φ)) ?_
  rw [dia_apply, KK_same hl hθ P₀ Q₀ hl' hφ (P := s • P₀) (Q := s • Q₀) rfl rfl,
    KK_same hl hθ P₀ Q₀ hl' (dia_mem_EqForm s hφ) rfl rfl, dia_apply]
  congr 1
  exact Subtype.ext (phiOne_dia s).symm
end GlobalTheory.KernelCommTw
