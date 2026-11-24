-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.colOf_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:41.643416+00:00
-- url     : https://prove2.me/submissions/f1b3ae88-a45c-45e4-a38f-28681238f5a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_mid_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_mid_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_last_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
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


section
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
section Entries
variable {u : GU σ (N + 2)}
end Entries
private theorem mat_mul_eq_ite_of_hasMult (u u' : GU σ (N + 2)) (i j : Fin (N + 2)) :
    mat (u * u') i j = mat u i 0 * mat u' 0 j + ∑ m, mat u i (mid m) * mat u' (mid m) j +
      mat u i (Fin.last (N + 1)) * mat u' (Fin.last (N + 1)) j := by
  show (mat u * mat u') i j = _
  rw [Matrix.mul_apply, sum_idx]
section Values
variable (r b : Fin N → L) (c : L)
end Values
end GlobalTheory.CompanionTheory.InertHeis
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertHeis
theorem _root_.solution {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    colOf (u * u') = colOf u + colOf u' := by
  funext i
  show mat (u * u') (mid i) (Fin.last (N + 1)) =
    mat u (mid i) (Fin.last (N + 1)) + mat u' (mid i) (Fin.last (N + 1))
  rw [mat_mul_eq_ite_of_hasMult, rad_mid_zero hu i, rad_last_last hu']
  simp only [rad_mid_mid hu, Matrix.one_apply, ite_mul, one_mul, zero_mul, zero_add, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring
end GlobalTheory.CompanionTheory.InertHeis
