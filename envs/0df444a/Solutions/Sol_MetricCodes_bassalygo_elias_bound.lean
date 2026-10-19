-- Prove2me | solution 1 for MetricCodes.bassalygo_elias_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/c4bd7d58-a291-4f47-99b5-772421b79a81

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_translateLocalizedCode_subset_weightShell
import Theorems.Thm_MetricCodes_card_translateLocalizedCode
import Theorems.Thm_MetricCodes_translateLocalizedCode_isBinaryCode
import Theorems.Thm_MetricCodes_localization_double_count

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n d w B : ℕ}
    (C : Finset (BinaryWord n)) (hC : IsBinaryCode d C)
    (hB : ∀ D : Finset (BinaryWord n),
      D ⊆ weightShell n w → IsBinaryCode d D → D.card ≤ B) :
    C.card * n.choose w ≤ 2 ^ n * B := by
  calc
    C.card * n.choose w =
        ∑ z : BinaryWord n, (localizedCode C z w).card :=
      (localization_double_count C w).symm
    _ ≤ ∑ _z : BinaryWord n, B := by
      apply Finset.sum_le_sum
      intro z hz
      rw [← card_translateLocalizedCode C z]
      exact hB (translateLocalizedCode C z w)
        (translateLocalizedCode_subset_weightShell C z)
        (translateLocalizedCode_isBinaryCode C z hC)
    _ = 2 ^ n * B := by
      simp
end MetricCodes
