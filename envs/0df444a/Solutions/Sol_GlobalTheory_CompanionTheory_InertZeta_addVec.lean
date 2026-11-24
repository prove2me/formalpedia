-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.addVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:25:59.93537+00:00
-- url     : https://prove2.me/submissions/85c06d7b-fd4c-42b4-9ab9-6ac9ab275d69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_AdditiveVectorExists
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_mem_intL_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_det_updateRow_one
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_rowLat_updateRow
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mem_rowLat
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
theorem _root_.solution : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  by_cases e0 : e = 0
  · subst e0
    refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact mem_intL_iff.2 (by simpa using hρ i)
  · obtain ⟨i, hi⟩ := he.resolve_left e0
    have h0 : ρ i ≠ 0 := fun h => by
      rw [h, map_zero] at hi
      exact WithZero.exp_ne_zero hi.symm
    have hone : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (e : ℤ) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have h1 : Valued.v (ρ i)⁻¹ ≤ 1 := by
      rw [map_inv₀, hi]
      exact inv_le_one_of_one_le₀ hone
    refine ⟨M.updateRow i (ρ ᵥ* M), ?_, rowLat_updateRow h0 h1 fun j => hi ▸ hρ j⟩
    have e1 : M.updateRow i (ρ ᵥ* M) = (1 : Matrix (Fin n) (Fin n) L).updateRow i ρ * M := by
      ext a b
      by_cases ha : a = i
      · subst ha
        simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
      · simp [Matrix.updateRow_ne ha, Matrix.mul_apply, Matrix.one_apply]
    rw [e1, Matrix.det_mul, det_updateRow_one, map_mul, hi, hM, ← WithZero.exp_add, add_comm]
end GlobalTheory.CompanionTheory.InertZeta
