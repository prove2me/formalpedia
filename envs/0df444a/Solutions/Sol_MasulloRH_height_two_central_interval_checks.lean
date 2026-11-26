-- Prove2me | solution 1 for MasulloRH.height_two_central_interval_checks
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T14:29:47.637426+00:00
-- url     : https://prove2.me/submissions/5700692c-63aa-4485-8eab-27cddbe55836

import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_00
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_01
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_02
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_03
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_04
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_05
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_06
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_07
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_08
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_09
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_10
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_11
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_12
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_13
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_14
import Theorems.Thm_MasulloRH_height_two_interval_checks_mod16_15
import Mathlib.Tactic.FinCases

open MasulloRH.InteriorEvaluator

private theorem fromResidue {r k : ℕ}
    (passed : (List.range 51).all (fun i => passes (144+r+16*i)) = true)
    (hk : k < 816) (hr : k % 16 = r) : passes (144+k) = true := by
  have h := List.all_eq_true.mp passed (k/16) (List.mem_range.mpr (by omega))
  have he : 144+r+16*(k/16) = 144+k := by omega
  simpa only [he] using h

theorem solution :
    (List.range 816).all (fun k => passes (144+k)) = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 816 := List.mem_range.mp hk
  obtain ⟨r,hr⟩ : ∃ r : Fin 16, k % 16 = r.val :=
    ⟨⟨k % 16,Nat.mod_lt _ (by decide)⟩,rfl⟩
  fin_cases r
  · exact fromResidue (r := 0) MasulloRH.height_two_interval_checks_mod16_00 hk' hr
  · exact fromResidue (r := 1) MasulloRH.height_two_interval_checks_mod16_01 hk' hr
  · exact fromResidue (r := 2) MasulloRH.height_two_interval_checks_mod16_02 hk' hr
  · exact fromResidue (r := 3) MasulloRH.height_two_interval_checks_mod16_03 hk' hr
  · exact fromResidue (r := 4) MasulloRH.height_two_interval_checks_mod16_04 hk' hr
  · exact fromResidue (r := 5) MasulloRH.height_two_interval_checks_mod16_05 hk' hr
  · exact fromResidue (r := 6) MasulloRH.height_two_interval_checks_mod16_06 hk' hr
  · exact fromResidue (r := 7) MasulloRH.height_two_interval_checks_mod16_07 hk' hr
  · exact fromResidue (r := 8) MasulloRH.height_two_interval_checks_mod16_08 hk' hr
  · exact fromResidue (r := 9) MasulloRH.height_two_interval_checks_mod16_09 hk' hr
  · exact fromResidue (r := 10) MasulloRH.height_two_interval_checks_mod16_10 hk' hr
  · exact fromResidue (r := 11) MasulloRH.height_two_interval_checks_mod16_11 hk' hr
  · exact fromResidue (r := 12) MasulloRH.height_two_interval_checks_mod16_12 hk' hr
  · exact fromResidue (r := 13) MasulloRH.height_two_interval_checks_mod16_13 hk' hr
  · exact fromResidue (r := 14) MasulloRH.height_two_interval_checks_mod16_14 hk' hr
  · exact fromResidue (r := 15) MasulloRH.height_two_interval_checks_mod16_15 hk' hr
