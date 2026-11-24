-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.hasLen_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:33.529827+00:00
-- url     : https://prove2.me/submissions/2413bbf2-0e67-44be-946b-283a84018a80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_FractionExistsOfSmith
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_isInt_diagonal
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
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
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
open GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal fun i => ϖ ^ d i) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have h1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hpow : ∀ e : ℕ, ϖ ^ e ∈ Formalism.UG.intL L := fun e => by
    change Valued.v (ϖ ^ e) ≤ 1
    rw [map_pow]
    exact pow_le_one' h1 e
  have hnum : ∀ i, ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := fun i => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0]
    congr 1
    omega
  refine ⟨Matrix.diagonal fun i => if 0 ≤ d i then 1 else 0, Matrix.diagonal fun i => if 0 ≤ d i then 0 else 1,
    Matrix.diagonal fun i => ϖ ^ (-d i).toNat, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine isInt_diagonal fun i => ?_
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · refine isInt_diagonal fun i => ?_
    split_ifs
    · exact zero_mem _
    · exact one_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    rw [hnum]
    exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases h : 0 ≤ d i
    · have : (-d i).toNat = 0 := by omega
      simp [h, this]
    · have e : ϖ ^ d i * ϖ ^ (-d i).toNat = 1 := by
        rw [hnum, show (d i).toNat = 0 by omega, pow_zero]
      simp [h, e]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_pow_eq_pow_sum, ← WithZero.exp_nsmul]
    congr 1
    simp
end GlobalTheory.CompanionTheory.InertZeta
