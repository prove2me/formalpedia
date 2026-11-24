-- Prove2me | solution 1 for GlobalTheory.RootEx.ExchangeSupport.conj_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:57:43.148784+00:00
-- url     : https://prove2.me/submissions/d6638220-79f4-4bd9-8984-e1d5914395b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_val
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_val
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_inv_val
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colM_mul_rowM
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowM_mul_colM
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_simpleSum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ExchangeSupport
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.ExchangeSupport
theorem _root_.solution (hp : 1 ≤ p) (hc : p < c) (u β : n → k) :
    colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹ ∈ N k n c (p + 1) ∧
      simpleSum (colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹) = -(u ⬝ᵥ β) := by
  have hv : (colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹).val =
      fromBlocks 1 0 (rowM c p u) (1 - rowM c p u * colM c (p + 1) β) := by
    rw [Units.val_mul, Units.val_mul, rowE_val, colE_val, colE_inv_val]
    simp [fromBlocks_multiply, colM_mul_rowM, sub_eq_add_neg, add_comm]
  refine ⟨Subgroup.subset_closure ?_, simpleSum_eq hp hc _ _ ?_⟩
  · intro r s hrs
    rw [hv, ← fromBlocks_one]
    rcases r with r | r <;> rcases s with s | s
    · rfl
    · rfl
    · have : r.val + 1 ≠ p := by simp [lev] at hrs; omega
      simp [rowM, this]
    · have : ¬ (r.val + 1 = p ∧ s.val = p) := by simp [lev] at hrs; omega
      simp [rowM_mul_colM, this]
  · intro i j
    rw [hv]; simp only [fromBlocks_apply₂₂, Matrix.sub_apply, rowM_mul_colM]
    split_ifs <;> simp [sub_eq_add_neg]
end GlobalTheory.RootEx.ExchangeSupport
