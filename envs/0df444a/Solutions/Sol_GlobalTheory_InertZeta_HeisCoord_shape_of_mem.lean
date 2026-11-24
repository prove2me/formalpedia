-- Prove2me | solution 1 for GlobalTheory.InertZeta.HeisCoord.shape_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:22:18.138855+00:00
-- url     : https://prove2.me/submissions/a2b637e2-034e-4377-8c0e-92cb438ee5c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_last_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_injective
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero
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
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.HeisCoord
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.InertZeta.HeisCoord
theorem _root_.solution {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : Shape (mat u) (rowOf u) (colOf u) (cornerOf u) := by
  have h : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨?_, fun j => rfl, rfl, fun i => ?_, fun i j => ?_, fun i => rfl, ?_, fun j => ?_, ?_⟩
  · rw [h 0 0 le_rfl, Matrix.one_apply_eq]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  · rw [h _ _ (by simp)]; simp [Matrix.one_apply, mid_injective.eq_iff]
  · rw [h _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_last j).symm]
  · rw [h _ _ le_rfl, Matrix.one_apply_eq]
end GlobalTheory.InertZeta.HeisCoord
