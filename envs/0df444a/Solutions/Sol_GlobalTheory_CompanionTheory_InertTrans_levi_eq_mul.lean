-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertTrans.levi_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:54.708064+00:00
-- url     : https://prove2.me/submissions/4da2480f-7a05-4d1d-9c97-71034e7f05f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_levi_off
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertTrans
theorem _root_.solution {ϖ : L} {a : ℤ} {b k : GU σ N} {mb mk m : GU σ (N + 2)} (hb : IsLeviElt ϖ a b mb)
    (hk : IsLeviElt ϖ 0 k mk) (hm : IsLeviElt ϖ a (b * k) m) : m = mb * mk := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := levi_off hb
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := levi_off hk
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := levi_off hm
  apply mat_injective
  ext i j
  rw [mat_mul, Matrix.mul_apply, sum_idx]
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp only [b1, b2, b3, b4, b5, b6, k1, k2, k3, k4, k5, k6, m1, m2, m3, m4, m5, m6, hb.2.1, hb.2.2.1, hb.2.2.2,
      hk.2.1, hk.2.2.1, hk.2.2.2, hm.2.1, hm.2.2.1, hm.2.2.2, zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
      zero_add, zpow_zero, neg_zero, mul_one, mat_mul, Matrix.mul_apply]
end GlobalTheory.CompanionTheory.InertTrans
