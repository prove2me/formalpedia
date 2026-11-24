-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.rad_mid_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:52:01.345274+00:00
-- url     : https://prove2.me/submissions/eec2df5b-48fb-4e6b-a147-8182c9145aef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_injective
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
private theorem mat_apply_eq_one_apply_of_mem_radQ_of_blk_le (hu : u ∈ radQ σ N) (i j : Fin (N + 2)) (h : blk N j ≤ blk N i) :
    mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j :=
  hu i j h
end Entries
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
variable {u : GU σ (N + 2)}
namespace GlobalTheory.CompanionTheory.InertHeis
theorem _root_.solution (hu : u ∈ radQ σ N) (i j : Fin N) :
    mat u (mid i) (mid j) = (1 : Matrix (Fin N) (Fin N) L) i j := by
  rw [mat_apply_eq_one_apply_of_mem_radQ_of_blk_le hu _ _ (by simp [blk_mid])]
  simp only [Matrix.one_apply, mid_injective.eq_iff]
end GlobalTheory.CompanionTheory.InertHeis
