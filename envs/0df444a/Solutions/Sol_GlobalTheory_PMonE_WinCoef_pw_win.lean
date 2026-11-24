-- Prove2me | solution 1 for GlobalTheory.PMonE.WinCoef.pw_win
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:36.055708+00:00
-- url     : https://prove2.me/submissions/f28e5387-c340-4fd9-878e-18503059116e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum
import Theorems.Thm_GlobalTheory_PMonE_WinCoef_frob_pow_apply
import Theorems.Thm_GlobalTheory_PMonE_WinCoef_pw_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open Finset
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.WinCoef
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE.WinCoef
theorem _root_.solution (h r L : ℕ) (hr : r ≤ h) (hL : 1 ≤ L) (n : ℤ) (hn : -(L : ℤ) ≤ n) (z : F) :
    pw p ((r : ℤ) + n * h) (z ^ (p ^ h) ^ (L - 1)) ^ p ^ (h - r) = z ^ (p ^ h) ^ ((n + L).toNat) := by
  have e1 : z ^ (p ^ h) ^ (L - 1) = ((frobAut (F := F) p) ^ (((h * (L - 1) : ℕ)) : ℤ)) z := by
    rw [zpow_natCast, frob_pow_apply, pow_mul]
  have e2 : z ^ (p ^ h) ^ ((n + L).toNat) =
      ((frobAut (F := F) p) ^ (((h * (n + L).toNat : ℕ)) : ℤ)) z := by
    rw [zpow_natCast, frob_pow_apply, pow_mul]
  have e3 : ∀ y : F, y ^ p ^ (h - r) = ((frobAut (F := F) p) ^ (((h - r : ℕ)) : ℤ)) y := fun y => by
    rw [zpow_natCast, frob_pow_apply]
  rw [e3, pw_eq, e1, e2, ← RingAut.mul_apply, ← RingAut.mul_apply, ← zpow_add, ← zpow_add]
  congr 2
  have ht : ((n + L).toNat : ℤ) = n + L := Int.toNat_of_nonneg (by omega)
  push_cast [Nat.cast_sub hr, Nat.cast_sub hL, ht]
  ring
end GlobalTheory.PMonE.WinCoef
