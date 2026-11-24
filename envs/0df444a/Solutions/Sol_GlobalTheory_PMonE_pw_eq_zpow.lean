-- Prove2me | solution 1 for GlobalTheory.PMonE.pw_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:37.662385+00:00
-- url     : https://prove2.me/submissions/1e24e56e-ada5-41a4-ad29-dd087c16287f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuter
import Theorems.Thm_GlobalTheory_PMonE_frobPerm_pow_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE
theorem _root_.solution (k : ℤ) (x : F) : pw p k x = (frobPerm (F := F) p ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frobPerm_pow_apply]
    simp
  · push_neg at hk
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow]
    simp only [neg_neg, Int.toNat_natCast]
    rfl
end GlobalTheory.PMonE
