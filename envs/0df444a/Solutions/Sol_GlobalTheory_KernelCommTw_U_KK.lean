-- Prove2me | solution 1 for GlobalTheory.KernelCommTw.U_KK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:03.716804+00:00
-- url     : https://prove2.me/submissions/60fb13a4-bb1b-4538-8924-0be0dc13b71e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_mem
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_same
import Theorems.Thm_GlobalTheory_KernelCommTw_KK_up
import Theorems.Thm_GlobalTheory_KernelComm_KK_mem
import Theorems.Thm_GlobalTheory_KernelComm_KK_same
import Theorems.Thm_GlobalTheory_KernelComm_KK_up
import Theorems.Thm_GlobalTheory_KernelComm_card_withKer
import Theorems.Thm_GlobalTheory_KernelComm_eq_of_base
import Theorems.Thm_GlobalTheory_KernelComm_sum_source
import Theorems.Thm_GlobalTheory_KernelComm_sum_target
import Theorems.Thm_GlobalTheory_LatPair_U_apply
import Theorems.Thm_GlobalTheory_LatPair_U_mem_EqForm


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
theorem _root_.solution (hl' : IsUnram l') (q : Unif k) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    U q (KK hl hθ P₀ Q₀ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • KK hl hθ P₀ Q₀ (U q φ) := by
  classical
  refine GlobalTheory.KernelComm.eq_of_base Q₀ (U_mem_EqForm q (KK_mem hl hθ P₀ Q₀ φ))
    (Submodule.smul_mem _ _ (KK_mem hl hθ P₀ Q₀ _)) ?_
  have h1 : ∀ P₁ ∈ withKer P₀.lat, U q (KK hl hθ P₀ Q₀ φ) Q₀ =
      ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ •
        ∑ P ∈ withLat P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P₁ hP => by
    rw [mem_withKer] at hP
    rw [U_apply, Finset.sum_congr rfl fun Q₁ hQ =>
      KK_up hl hθ P₀ Q₀ hl' q hφ hP (mem_withKer.1 (Finset.mem_filter.1 hQ).1), ← Finset.smul_sum,
      ← Finset.sum_filter, ← map_sum, ← map_sum, ← hP]
    congr 2
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, phiOneSB]
    exact (GlobalTheory.KernelComm.sum_target q P₁.hasVal_vec Q₀ x).trans (GlobalTheory.KernelComm.sum_source q P₁.hasVal_vec Q₀ x)
  have h2 : ∀ P ∈ withLat P₀.lat, KK hl hθ P₀ Q₀ (U q φ) Q₀ =
      ∑ P₁ ∈ withKer P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P hP => by
    rw [mem_withLat] at hP
    rw [KK_same hl hθ P₀ Q₀ hl' (U_mem_EqForm q hφ) hP rfl, U_apply, map_sum, LinearMap.sum_apply, hP,
      Finset.sum_filter]
  have h3 := Finset.sum_congr rfl h1
  rw [← Finset.smul_sum, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    GlobalTheory.KernelComm.card_withKer q, smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  refine smul_right_injective V ?_ h3
  exact_mod_cast (Finset.card_pos.2 ⟨P₀, mem_withLat.2 rfl⟩).ne'
end GlobalTheory.KernelCommTw
