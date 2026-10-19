-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.real_three_window21
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T14:52:21.239025+00:00
-- url     : https://prove2.me/submissions/465152fa-67f5-47de-b7ed-b3162388b39d

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_coarse_failure_window21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_00
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_01
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_02
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_03
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_04
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_05
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_06
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_07
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_08
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_09
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_10
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_11
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_12
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_13
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_14
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_15
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_16
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_17
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_18
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_19
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_20
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_21
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_22
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_23
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_24
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_25
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_26
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_27
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_28
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_29
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_30
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_31
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_32
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_33
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_34
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_35
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_36
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_37
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_38
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_39
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_localized_domain4_21_40
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group00
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_domain_nonneg_group01
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem solution :
    ∀ p : ℝ, 21 ≤ p → p ≤ 26 →
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
  obtain ⟨X, hd, ho, hS, hT, hG, hfail⟩ := HlawkaSchatten.DiagonalCutoff21.coarse_failure_window21 p hp hpmax x y z hf
  norm_num at hT
  have hnonneg : 0 ≤ tripleDeficit p (cyclicConstant p) X := by
    rcases le_total p (47/2 : ℝ) with hl | hr
    ·
      rcases le_total p (89/4 : ℝ) with hll | hlr
      ·
        rcases le_total p (173/8 : ℝ) with hlll | hllr
        ·
          rcases le_total p (85/4 : ℝ) with hllll | hlllr
          ·
            rcases le_total p (169/8 : ℝ) with hlllll | hllllr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_00 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_01 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (171/8 : ℝ) with hlllrl | hlllrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_02 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (43/2 : ℝ) with hlllrrl | hlllrrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_03 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_04 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (175/8 : ℝ) with hllrl | hllrr
          ·
            rcases le_total p (87/4 : ℝ) with hllrll | hllrlr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_05 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_06 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (22 : ℝ) with hllrrl | hllrrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_07 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (177/8 : ℝ) with hllrrrl | hllrrrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_08 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_09 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
      ·
        rcases le_total p (183/8 : ℝ) with hlrl | hlrr
        ·
          rcases le_total p (45/2 : ℝ) with hlrll | hlrlr
          ·
            rcases le_total p (179/8 : ℝ) with hlrlll | hlrllr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_10 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_11 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (181/8 : ℝ) with hlrlrl | hlrlrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_12 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (91/4 : ℝ) with hlrlrrl | hlrlrrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_13 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_14 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (185/8 : ℝ) with hlrrl | hlrrr
          ·
            rcases le_total p (23 : ℝ) with hlrrll | hlrrlr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_15 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_16 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (93/4 : ℝ) with hlrrrl | hlrrrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_17 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (187/8 : ℝ) with hlrrrrl | hlrrrrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_18 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_19 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
    ·
      rcases le_total p (395/16 : ℝ) with hrl | hrr
      ·
        rcases le_total p (385/16 : ℝ) with hrll | hrlr
        ·
          rcases le_total p (379/16 : ℝ) with hrlll | hrllr
          ·
            rcases le_total p (377/16 : ℝ) with hrllll | hrlllr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_20 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group00 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_21 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (381/16 : ℝ) with hrllrl | hrllrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_22 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (383/16 : ℝ) with hrllrrl | hrllrrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_23 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_24 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (389/16 : ℝ) with hrlrl | hrlrr
          ·
            rcases le_total p (387/16 : ℝ) with hrlrll | hrlrlr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_25 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_26 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (391/16 : ℝ) with hrlrrl | hrlrrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_27 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (393/16 : ℝ) with hrlrrrl | hrlrrrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_28 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_29 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
      ·
        rcases le_total p (405/16 : ℝ) with hrrl | hrrr
        ·
          rcases le_total p (399/16 : ℝ) with hrrll | hrrlr
          ·
            rcases le_total p (397/16 : ℝ) with hrrlll | hrrllr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_30 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_31 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (401/16 : ℝ) with hrrlrl | hrrlrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_32 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (403/16 : ℝ) with hrrlrrl | hrrlrrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_33 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_34 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
        ·
          rcases le_total p (411/16 : ℝ) with hrrrl | hrrrr
          ·
            rcases le_total p (407/16 : ℝ) with hrrrll | hrrrlr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_35 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (409/16 : ℝ) with hrrrlrl | hrrrlrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_36 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_37 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
          ·
            rcases le_total p (413/16 : ℝ) with hrrrrl | hrrrrr
            ·
              have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_38 p (by linarith) (by linarith) X hd ho hS hT hG
              exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
            ·
              rcases le_total p (415/16 : ℝ) with hrrrrrl | hrrrrrr
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_39 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
              ·
                have hh := HlawkaSchatten.DiagonalCutoff21.localized_domain4_21_40 p (by linarith) (by linarith) X hd ho hS hT hG
                exact HlawkaSchatten.DiagonalCutoff21.domain_nonneg_group01 p
                  (by linarith) (by linarith) X hh.1 hh.2.1 hh.2.2.1
                  (hT.le.trans (by norm_num)) hh.2.2.2.1 hh.2.2.2.2
  exact (not_lt_of_ge hnonneg) hfail

#print axioms solution
