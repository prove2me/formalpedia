-- Prove2me | solution 1 for MetricCodes.localization_double_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/5a6680a8-a89c-4c66-b857-a73b3811eef4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_hammingDist_comm
import Theorems.Thm_MetricCodes_binaryWeight_binaryTranslate
import Theorems.Thm_MetricCodes_card_hammingSphere

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ}
    (C : Finset (BinaryWord n)) (w : ℕ) :
    (∑ z : BinaryWord n, (localizedCode C z w).card) =
      C.card * n.choose w := by
  calc
    (∑ z : BinaryWord n, (localizedCode C z w).card) =
        ∑ z : BinaryWord n, ∑ x ∈ C,
          if binaryWeight (binaryTranslate z x) = w then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      change
        (C.filter fun x => binaryWeight (binaryTranslate z x) = w).card =
          ∑ x ∈ C,
            if binaryWeight (binaryTranslate z x) = w then 1 else 0
      exact Finset.card_filter
        (fun x => binaryWeight (binaryTranslate z x) = w) C
    _ = ∑ x ∈ C, ∑ z : BinaryWord n,
          if binaryWeight (binaryTranslate z x) = w then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ C, (hammingSphere x w).card := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ z : BinaryWord n,
            if binaryWeight (binaryTranslate z x) = w then 1 else 0) =
            (Finset.univ.filter fun z : BinaryWord n =>
              binaryWeight (binaryTranslate z x) = w).card :=
          (Finset.card_filter
            (fun z : BinaryWord n =>
              binaryWeight (binaryTranslate z x) = w)
            Finset.univ).symm
        _ = (hammingSphere x w).card := by
          congr 1
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            mem_hammingSphere, binaryWeight_binaryTranslate]
          rw [hammingDist_comm]
    _ = C.card * n.choose w := by
      simp [card_hammingSphere]
end MetricCodes
