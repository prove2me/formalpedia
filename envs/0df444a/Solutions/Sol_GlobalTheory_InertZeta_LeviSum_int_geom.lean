-- Prove2me | solution 1 for GlobalTheory.InertZeta.LeviSum.int_geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:07:08.355831+00:00
-- url     : https://prove2.me/submissions/1df393d2-0991-41d6-a4a9-e926b07a0e73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryLeviSummationGeometricSeries
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
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.LeviSum
namespace GlobalTheory.InertZeta.LeviSum
theorem _root_.solution (β y₀ : ℂ) (hβ : β ≠ 0) (h1 : ‖y₀ * β‖ < 1) (h2 : ‖y₀ / β‖ < 1) :
    HasSum (fun a : ℤ => β ^ a * y₀ ^ a.natAbs) ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · have e : ∀ n : ℕ, β ^ (n : ℤ) * y₀ ^ (n : ℤ).natAbs = (y₀ * β) ^ n := fun n => by
      simp [zpow_natCast, mul_pow, mul_comm]
    simp only [e]
    exact hasSum_geometric_of_norm_lt_one h1
  · have e : ∀ n : ℕ, β ^ (-((n : ℤ) + 1)) * y₀ ^ (-((n : ℤ) + 1)).natAbs = y₀ / β * (y₀ / β) ^ n := fun n => by
      rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        show (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 by omega, div_pow]
      field_simp
      ring
    simp only [e]
    exact (hasSum_geometric_of_norm_lt_one h2).mul_left (y₀ / β)
end GlobalTheory.InertZeta.LeviSum
