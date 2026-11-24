-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.rowLat_updateRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:05:48.948573+00:00
-- url     : https://prove2.me/submissions/4e198e93-2c77-4feb-94e6-38ef6fe840ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_AdditiveVectorExists
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_mem_intL_iff
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mem_rowLat
import Theorems.Thm_GlobalTheory_InertZeta_rowLat_le
import Theorems.Thm_GlobalTheory_InertZeta_row_mem_rowLat
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
open GlobalTheory.InertZeta Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution {M : Matrix (Fin n) (Fin n) L} {ρ : Fin n → L} {i : Fin n}
    (h0 : ρ i ≠ 0) (h1 : Valued.v (ρ i)⁻¹ ≤ 1) (h2 : ∀ j, Valued.v (ρ j) ≤ Valued.v (ρ i)) :
    rowLat M ⊔ Submodule.span (Formalism.UG.intL L) {ρ ᵥ* M} = rowLat (M.updateRow i (ρ ᵥ* M)) := by
  set w := ρ ᵥ* M with hw
  apply le_antisymm
  · refine sup_le (rowLat_le.2 fun j => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    · by_cases hj : j = i
      · subst hj
        refine mem_rowLat.2 ⟨fun l => if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹), fun l => ?_, ?_⟩
        · by_cases hl : l = j
          · simp only [if_pos hl]
            exact h1
          · simp only [hl, if_false]
            refine neg_mem ?_
            rw [mem_intL_iff, map_mul, map_inv₀]
            exact mul_inv_le_one_of_le₀ (h2 l) zero_le'
        · rw [Matrix.vecMul_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have e1 : ∑ l ∈ Finset.univ.erase j, (if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹)) • (M.updateRow j w) l
              = ∑ l ∈ Finset.univ.erase j, (-(ρ l * (ρ j)⁻¹)) • M l :=
            Finset.sum_congr rfl fun l hl => by
              have := Finset.ne_of_mem_erase hl
              simp [this, Matrix.updateRow_ne]
          have e2 : w = ρ j • M j + ∑ l ∈ Finset.univ.erase j, ρ l • M l := by
            rw [hw, Matrix.vecMul_eq_sum]
            exact (Finset.add_sum_erase _ (fun l => ρ l • M l) (Finset.mem_univ j)).symm
          rw [e1]
          simp only [if_true, Matrix.updateRow_self]
          rw [e2, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum, add_assoc,
            ← Finset.sum_add_distrib]
          simp only [smul_smul, neg_smul]
          have : ∀ l, (ρ j)⁻¹ * ρ l = ρ l * (ρ j)⁻¹ := fun l => mul_comm _ _
          simp [this]
      · have := row_mem_rowLat (M.updateRow i w) j
        rwa [Matrix.updateRow_ne hj] at this
    · have := row_mem_rowLat (M.updateRow i w) i
      rwa [Matrix.updateRow_self] at this
  · refine rowLat_le.2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [Matrix.updateRow_self]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [Matrix.updateRow_ne hj]
      exact Submodule.mem_sup_left (row_mem_rowLat M j)
end GlobalTheory.CompanionTheory.InertZeta
