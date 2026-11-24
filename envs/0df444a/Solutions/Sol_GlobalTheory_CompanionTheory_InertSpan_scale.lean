-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:21:22.420569+00:00
-- url     : https://prove2.me/submissions/e3050e06-b03d-4186-9de2-0583b8f8fe81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockVector_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_vec_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_first
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_middle
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_blockMatrix_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_UnitarySwap_mem_int
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


attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockVector_last
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_first
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_middle
attribute [local simp] GlobalTheory.CompanionTheory.InertSpan.blockMatrix_last

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertSpan
theorem _root_.solution (R : Submodule (intL L) (Fin (N + 2) → L)) {w t : L} (hw : w ≠ 0)
    (hv : Valued.v t ≤ Valued.v w) (h : vec3 (0 : L) 0 w ∈ R) : vec3 (0 : L) 0 t ∈ R := by
  have hi : t / w ∈ intL L := by
    rw [GlobalTheory.UnitarySwap.mem_int, map_div₀]
    exact div_le_one_of_le₀ hv zero_le'
  have e : vec3 (0 : L) (0 : Fin N → L) t = (t / w) • vec3 (0 : L) (0 : Fin N → L) w :=
    vec_ext (by simp) (fun j => by simp) (by simp [hw])
  rw [e]
  exact R.smul_mem ⟨t / w, hi⟩ h
end GlobalTheory.CompanionTheory.InertSpan
