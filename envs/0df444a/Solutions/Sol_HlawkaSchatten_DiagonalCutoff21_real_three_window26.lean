-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.real_three_window26
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T15:18:17.817838+00:00
-- url     : https://prove2.me/submissions/bce2c548-93d4-401e-a205-56e74cb86c96

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_coarse_failure_window26
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_00
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_01
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_02
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_03
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_04
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_05
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_06
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_07
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_08
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_09
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_10
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_11
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_12
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_13
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_14
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_15
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_16
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_17
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_18
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_19
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_20
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_22
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_26_23
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group01
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 26 ≤ p → p ≤ 32 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp hpmax x y z
  by_contra hn
  have he : hlawkaDeficit p (cyclicConstant p) x y z =
      cyclicConstant p * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
    unfold hlawkaDeficit pairGapSum pairGap tripleGap
    ring
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [he]
    exact sub_neg.mpr (lt_of_not_ge hn)
  obtain ⟨X, hd, ho, hS, hT, hG, hfail⟩ := HlawkaSchatten.DiagonalCutoff21.coarse_failure_window26 p hp hpmax x y z hf
  norm_num at hT
  have hnonneg : 0 ≤ tripleDeficit p (cyclicConstant p) X := by
    rcases le_total p (29 : ℝ) with hl | hr
    ·
      rcases le_total p (55/2 : ℝ) with hll | hlr
      ·
        rcases le_total p (107/4 : ℝ) with hlll | hllr
        ·
          rcases le_total p (105/4 : ℝ) with hllll | hlllr
          ·
            have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_00 p (by linarith) (by linarith) X hd ho hS hT hG
            exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
              (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
              (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (53/2 : ℝ) with hlllrl | hlllrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_01 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_02 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (27 : ℝ) with hllrl | hllrr
          ·
            have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_03 p (by linarith) (by linarith) X hd ho hS hT hG
            exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
              (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
              (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (109/4 : ℝ) with hllrrl | hllrrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_04 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_05 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
      ·
        rcases le_total p (113/4 : ℝ) with hlrl | hlrr
        ·
          rcases le_total p (111/4 : ℝ) with hlrll | hlrlr
          ·
            have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_06 p (by linarith) (by linarith) X hd ho hS hT hG
            exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
              (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
              (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (28 : ℝ) with hlrlrl | hlrlrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_07 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_08 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (57/2 : ℝ) with hlrrl | hlrrr
          ·
            have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_09 p (by linarith) (by linarith) X hd ho hS hT hG
            exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
              (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
              (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (115/4 : ℝ) with hlrrrl | hlrrrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_10 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_11 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
    ·
      rcases le_total p (61/2 : ℝ) with hrl | hrr
      ·
        rcases le_total p (119/4 : ℝ) with hrll | hrlr
        ·
          rcases le_total p (117/4 : ℝ) with hrlll | hrllr
          ·
            have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_12 p (by linarith) (by linarith) X hd ho hS hT hG
            exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
              (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
              (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (59/2 : ℝ) with hrllrl | hrllrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_13 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_14 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (30 : ℝ) with hrlrl | hrlrr
          ·
            have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_15 p (by linarith) (by linarith) X hd ho hS hT hG
            exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
              (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
              (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (121/4 : ℝ) with hrlrrl | hrlrrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_16 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_17 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
      ·
        rcases le_total p (125/4 : ℝ) with hrrl | hrrr
        ·
          rcases le_total p (123/4 : ℝ) with hrrll | hrrlr
          ·
            have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_18 p (by linarith) (by linarith) X hd ho hS hT hG
            exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
              (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
              (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (31 : ℝ) with hrrlrl | hrrlrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_19 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_20 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (63/2 : ℝ) with hrrrl | hrrrr
          ·
            have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_21 p (by linarith) (by linarith) X hd ho hS hT hG
            exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
              (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
              (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (127/4 : ℝ) with hrrrrl | hrrrrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_22 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_26_23 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
  exact (not_lt_of_ge hnonneg) hfail

#print axioms solution
