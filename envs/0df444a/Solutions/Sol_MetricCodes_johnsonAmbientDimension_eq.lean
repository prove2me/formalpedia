-- Prove2me | solution 1 for MetricCodes.johnsonAmbientDimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/d1a62057-0352-4f7e-9aba-82d082da9297

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_choose_monotone_to_half

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution (n a L : ℕ)
    (haL : a ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n a L =
      n.choose L - precedingBinomial n a := by
  unfold johnsonAmbientDimension
  induction L generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp [booleanHarmonicDimension, precedingBinomial]
  | succ L ih =>
      by_cases htop : a = L + 1
      · subst a
        simp [booleanHarmonicDimension, precedingBinomial]
      · have ha' : a ≤ L := by omega
        have hhalf : L < n / 2 := by omega
        have hchoose : n.choose L ≤ n.choose (L + 1) :=
          Nat.choose_le_succ_of_lt_half_left hhalf
        have hbase : precedingBinomial n a ≤ n.choose L := by
          cases a with
          | zero => simp [precedingBinomial]
          | succ a =>
              apply choose_monotone_to_half n
              · omega
              · exact hhalf.le
        have hinter :
            Finset.Icc a (L + 1) =
              insert (L + 1) (Finset.Icc a L) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hinter, Finset.sum_insert (by simp),
          ih a ha' hhalf.le, booleanHarmonicDimension_succ]
        exact Nat.sub_add_sub_cancel hchoose hbase
end MetricCodes
