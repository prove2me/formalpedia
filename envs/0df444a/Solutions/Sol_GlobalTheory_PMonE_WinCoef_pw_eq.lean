-- Prove2me | solution 1 for GlobalTheory.PMonE.WinCoef.pw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:07.858894+00:00
-- url     : https://prove2.me/submissions/40903851-128b-4d7f-88e4-82046cb95afa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSum
import Theorems.Thm_GlobalTheory_PMonE_WinCoef_frob_pow_apply
import Theorems.Thm_GlobalTheory_PMonE_WinCoef_frob_inv_pow_apply

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
theorem _root_.solution (k : ℤ) (x : F) : pw p k x = ((frobAut (F := F) p) ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frob_pow_apply]
    simp
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (le_of_lt (not_le.mp hk))
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, frob_inv_pow_apply]
    simp
end GlobalTheory.PMonE.WinCoef
