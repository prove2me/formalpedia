-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.exists_int_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:04:40.537645+00:00
-- url     : https://prove2.me/submissions/7144dfef-cf1a-4598-8eea-259284413132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_exists_trace_one
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution (hH : Heis) (hU : IsUnramInv ϖ σ q) (ρ : Fin N → L) (hρ : ∀ j, ρ j ∈ intL L) :
    ∃ k ∈ radQ σ N, k ∈ KU σ (N + 2) ∧ rowOf k = ρ := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  have hσσ : ∀ x, σ (σ x) = x := hU.1
  have hσint : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    change Valued.v (σ x) ≤ 1
    rw [hU.2.1]
    exact hx
  have hσs : σ (-∑ j, ρ j * σ (ρ j.rev)) = -∑ j, ρ j * σ (ρ j.rev) := by
    rw [map_neg, map_sum]
    congr 1
    simp only [map_mul, hσσ]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp only [Fin.revPerm_apply, Fin.rev_rev]; ring)
  obtain ⟨u, hu, hrow, hcorner⟩ := (hH L ϖ σ q N hU).2.2 ρ (τ * -∑ j, ρ j * σ (ρ j.rev))
    (by rw [map_mul, hσs, ← add_mul, hτ1, one_mul])
  refine ⟨u, hu, ?_, hrow⟩
  rw [((hH L ϖ σ q N hU).1 u hu).2.2]
  refine ⟨fun j => by rw [hrow]; exact hρ j, ?_⟩
  rw [hcorner]
  exact mul_mem hτ (neg_mem (sum_mem fun j _ => mul_mem (hρ j) (hσint _ (hρ j.rev))))
end GlobalTheory.CompanionTheory.InertCount
