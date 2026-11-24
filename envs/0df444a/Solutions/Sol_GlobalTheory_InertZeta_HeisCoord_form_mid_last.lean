-- Prove2me | solution 1 for GlobalTheory.InertZeta.HeisCoord.form_mid_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:44.20606+00:00
-- url     : https://prove2.me/submissions/ddb5d3bf-e416-42d3-9e36-e4ed9ff4d95c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
import Theorems.Thm_GlobalTheory_InertZeta_HeisCoord_form_apply
import Theorems.Thm_GlobalTheory_InertZeta_HeisCoord_sum_rev_ite
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_rev
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_form_apply
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
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.HeisCoord
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.InertZeta.HeisCoord
theorem _root_.solution {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c)
    (j : Fin N) : (cT σ M * antiJ L (N + 2) * M) (mid j) (Fin.last (N + 1)) = b j.rev + σ (r j) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]
end GlobalTheory.InertZeta.HeisCoord
