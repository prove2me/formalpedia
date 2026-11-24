-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLen.entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:05:52.051818+00:00
-- url     : https://prove2.me/submissions/a6fe2703-eec4-4356-b5c0-c234696c7b1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
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



set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLen
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertLen
theorem _root_.solution {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m) {u : GU σ (N + 2)}
    (hu : u ∈ radQ σ N) :
    mat (m * u) 0 0 = ϖ ^ a ∧ (∀ j, mat (m * u) 0 (mid j) = ϖ ^ a * rowOf u j) ∧
    mat (m * u) 0 (Fin.last (N + 1)) = ϖ ^ a * cornerOf u ∧ (∀ i, mat (m * u) (mid i) 0 = 0) ∧
    (∀ i j, mat (m * u) (mid i) (mid j) = mat g₀ i j) ∧
    (∀ i, mat (m * u) (mid i) (Fin.last (N + 1)) = (mat g₀ *ᵥ colOf u) i) ∧
    mat (m * u) (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, mat (m * u) (Fin.last (N + 1)) (mid j) = 0) ∧
    mat (m * u) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) := by
  have hmul : ∀ i j, mat (m * u) i j = ∑ k, mat m i k * mat u k j := fun i j => by
    rw [show mat (m * u) = mat m * mat u from rfl, Matrix.mul_apply]
  have hL : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hm.1
  have hR : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  have hm00 : mat m 0 0 = ϖ ^ a := hm.2.1
  have hmll : mat m (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) := hm.2.2.1
  have hmmm : ∀ i j, mat m (mid i) (mid j) = mat g₀ i j := hm.2.2.2
  have h0mid : ∀ k, mat m 0 (mid k) = 0 := fun k => hL _ _ (by rw [blk_zero, blk_mid]; decide)
  have h0last : mat m 0 (Fin.last (N + 1)) = 0 := hL _ _ (by rw [blk_zero, blk_last]; decide)
  have hmid0 : ∀ i, mat m (mid i) 0 = 0 := fun i => hL _ _ (by rw [blk_zero, blk_mid]; decide)
  have hmidl : ∀ i, mat m (mid i) (Fin.last (N + 1)) = 0 := fun i => hL _ _ (by rw [blk_last, blk_mid]; decide)
  have hl0 : mat m (Fin.last (N + 1)) 0 = 0 := hL _ _ (by rw [blk_zero, blk_last]; decide)
  have hlmid : ∀ j, mat m (Fin.last (N + 1)) (mid j) = 0 := fun j => hL _ _ (by rw [blk_last, blk_mid]; decide)
  have hu00 : mat u 0 0 = 1 := by rw [hR 0 0 le_rfl, Matrix.one_apply_eq]
  have humid0 : ∀ k, mat u (mid k) 0 = 0 := fun k => by
    rw [hR _ _ (by rw [blk_zero]; exact Nat.zero_le _), Matrix.one_apply_ne (mid_ne_zero k)]
  have hul0 : mat u (Fin.last (N + 1)) 0 = 0 := by
    rw [hR _ _ (by rw [blk_zero]; exact Nat.zero_le _), Matrix.one_apply_ne last_ne_zero]
  have hummid : ∀ k j, mat u (mid k) (mid j) = if k = j then 1 else 0 := fun k j => by
    rw [hR _ _ (by rw [blk_mid, blk_mid])]
    simp only [Matrix.one_apply, mid_injective.eq_iff]
  have hulmid : ∀ j, mat u (Fin.last (N + 1)) (mid j) = 0 := fun j => by
    rw [hR _ _ (by rw [blk_last, blk_mid]; decide), Matrix.one_apply_ne (mid_ne_last j).symm]
  have hull : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by rw [hR _ _ le_rfl, Matrix.one_apply_eq]
  refine ⟨?_, fun j => ?_, ?_, fun i => ?_, fun i j => ?_, fun i => ?_, ?_, fun j => ?_, ?_⟩
  · rw [hmul, sum_idx]; simp [hm00, h0mid, h0last, hu00]
  · rw [hmul, sum_idx]; simp [hm00, h0mid, h0last, rowOf]
  · rw [hmul, sum_idx]; simp [hm00, h0mid, h0last, cornerOf]
  · rw [hmul, sum_idx]; simp [hmid0, humid0, hmidl]
  · rw [hmul, sum_idx]; simp [hmid0, hmmm, hummid, hmidl]
  · rw [hmul, sum_idx]; simp [hmid0, hmmm, hmidl, Matrix.mulVec, dotProduct, colOf]
  · rw [hmul, sum_idx]; simp [hl0, hlmid, hul0]
  · rw [hmul, sum_idx]; simp [hl0, hlmid, hulmid]
  · rw [hmul, sum_idx]; simp [hl0, hlmid, hmll, hull]
end GlobalTheory.CompanionTheory.InertLen
