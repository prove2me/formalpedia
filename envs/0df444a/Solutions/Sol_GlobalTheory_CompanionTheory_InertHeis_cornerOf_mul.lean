-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.cornerOf_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:42.825905+00:00
-- url     : https://prove2.me/submissions/e188caba-7e52-4bb2-a0ea-ae6fa69f2cea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_zero_zero
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
    cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u' := by
  show mat (u * u') 0 (Fin.last (N + 1)) =
    mat u 0 (Fin.last (N + 1)) + mat u' 0 (Fin.last (N + 1)) + rowOf u ⬝ᵥ colOf u'
  rw [mat_mul_eq_ite_of_hasMult, rad_zero_zero hu, rad_last_last hu', dotProduct]
  simp only [rowOf, colOf, one_mul, mul_one]
  ring
end GlobalTheory.CompanionTheory.InertHeis
