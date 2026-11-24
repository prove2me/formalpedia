-- Prove2me | solution 1 for GlobalTheory.KernelComm.U_KK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:48.395058+00:00
-- url     : https://prove2.me/submissions/f186a011-802b-444a-9b34-d238c6226bb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_KernelComm_sum_target
import Theorems.Thm_GlobalTheory_KernelComm_sum_source
import Theorems.Thm_GlobalTheory_KernelComm_card_withKer
import Theorems.Thm_GlobalTheory_KernelComm_KK_mem
import Theorems.Thm_GlobalTheory_KernelComm_eq_of_base
import Theorems.Thm_GlobalTheory_KernelComm_KK_same
import Theorems.Thm_GlobalTheory_KernelComm_KK_up
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
open GlobalTheory GlobalTheory.KernelComm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
  {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
  (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)
namespace GlobalTheory.KernelComm
theorem _root_.solution {t : ℕ} (ht : Fintype.card n = Fintype.card n' + (t + 1)) (q : Unif k) {φ : Form k n' V'}
    (hφ : φ ∈ EqForm π') : U q (KK hμ hθ P₀ Q₀ φ) = scal k t • KK hμ hθ P₀ Q₀ (U q φ) := by
  classical
  refine eq_of_base Q₀ (U_mem_EqForm q (KK_mem hμ hθ P₀ Q₀ φ)) (Submodule.smul_mem _ _ (KK_mem hμ hθ P₀ Q₀ _)) ?_
  have h1 : ∀ P₁ ∈ withKer P₀.lat, U q (KK hμ hθ P₀ Q₀ φ) Q₀ =
      scal k t • ∑ P ∈ withLat P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P₁ hP => by
    rw [mem_withKer] at hP
    rw [U_apply, Finset.sum_congr rfl fun Q₁ hQ =>
      KK_up hμ hθ P₀ Q₀ ht q hφ hP (mem_withKer.1 (Finset.mem_filter.1 hQ).1), ← Finset.smul_sum,
      ← Finset.sum_filter, ← map_sum, ← map_sum, ← hP]
    congr 2
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, phiOneSB]
    exact (sum_target q P₁.hasVal_vec Q₀ x).trans (sum_source q P₁.hasVal_vec Q₀ x)
  have h2 : ∀ P ∈ withLat P₀.lat, KK hμ hθ P₀ Q₀ (U q φ) Q₀ =
      ∑ P₁ ∈ withKer P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P hP => by
    rw [mem_withLat] at hP
    rw [KK_same hμ hθ P₀ Q₀ (U_mem_EqForm q hφ) hP rfl, U_apply, map_sum, LinearMap.sum_apply, hP,
      Finset.sum_filter]
  have h3 := Finset.sum_congr rfl h1
  rw [← Finset.smul_sum, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    card_withKer q, smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  refine smul_right_injective V ?_ h3
  exact_mod_cast (Finset.card_pos.2 ⟨P₀, mem_withLat.2 rfl⟩).ne'
end GlobalTheory.KernelComm
