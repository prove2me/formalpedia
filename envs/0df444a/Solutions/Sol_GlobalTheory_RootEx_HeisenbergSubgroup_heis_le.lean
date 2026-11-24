-- Prove2me | solution 1 for GlobalTheory.RootEx.HeisenbergSubgroup.heis_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:18:04.995806+00:00
-- url     : https://prove2.me/submissions/1c3d74a2-64de-476f-8c95-5b758e142b3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutator
import Theorems.Thm_GlobalTheory_RootEx_HeisenbergSubgroup_rowE_eq
import Theorems.Thm_GlobalTheory_RootEx_HeisenbergSubgroup_mem_N_of_val
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_add
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_val
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
namespace GlobalTheory.RootEx.HeisenbergSubgroup
section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
private theorem eMat_mem_N_succ (u : n → k) : rowE c p u ∈ N k n c (p + 1) := by
  show rowE c p u ∈ Subgroup.closure {g | InN (p + 1) g}
  refine Subgroup.subset_closure ?_
  intro r s hrs
  rw [ExchangeSupport.rowE_val]
  rcases r with a | l <;> rcases s with b | i
  · simp [Matrix.one_apply]
  · simp
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    simp only [Matrix.fromBlocks_apply₂₁, ExchangeSupport.rowM, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · simp [Matrix.one_apply]
end
end GlobalTheory.RootEx.HeisenbergSubgroup
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.HeisenbergSubgroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.HeisenbergSubgroup
theorem _root_.solution : Heisenberg₂ k n c p ≤ NFJ k n c p := by
  rintro g ⟨u, β, t, hg⟩
  have hinv : rowE c p u * rowE c p (-u) = 1 := by
    rw [← ExchangeSupport.rowE_add, add_neg_cancel, ExchangeSupport.rowE_zero]
  have hsplit : g = rowE c p u * (rowE c p (-u) * g) := by
    rw [← mul_assoc, hinv, one_mul]
  have hrest : rowE c p (-u) * g ∈ N k n c p := by
    refine mem_N_of_val (β := β) (t := t - u ⬝ᵥ β) ?_
    rw [Units.val_mul, hg, rowE_eq, hM_mul]
    simp only [neg_add_cancel, zero_add, neg_dotProduct]
    ring_nf
  rw [hsplit]
  exact Subgroup.mul_mem _ (le_sup_right (a := N k n c p) (eMat_mem_N_succ u))
    (le_sup_left (b := N k n c (p + 1)) hrest)
end GlobalTheory.RootEx.HeisenbergSubgroup
