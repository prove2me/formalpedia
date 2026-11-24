-- Prove2me | solution 1 for GlobalTheory.meets_cosets_nsmul_of_meets_cosets_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:59.121529+00:00
-- url     : https://prove2.me/submissions/e6ec991d-4a1d-40c7-bb4f-630aa8fd2026

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn
import Theorems.Thm_GlobalTheory_exists_eq_nsmul_of_nsmul_eq_zero_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory
variable {n k : ℕ}
namespace GlobalTheory
theorem _root_.solution {ι : Type*} (hn : n ≠ 0) (hk : 2 ≤ k)
    (T : Set (ι → ZMod (n ^ k))) (hT : ∀ x, ∃ t ∈ T, n • (x - t) = 0) (x : ι → ZMod (n ^ k)) :
    ∃ t ∈ T, ∃ a, x = t + n • a := by
  obtain ⟨t, ht, h⟩ := hT x
  choose a ha using fun i =>
    exists_eq_nsmul_of_nsmul_eq_zero_zmod hn hk ((x - t) i) (congrFun h i)
  exact ⟨t, ht, a, by rw [← sub_eq_iff_eq_add']; exact funext ha⟩
end GlobalTheory
